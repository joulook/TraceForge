//! The graph store written beside an export (`export ... --graphs PATH`), through the public CLI.
//!
//! Expected bytes are derived from the programs below, not from the producer. A child-process
//! mode (`child_process_entry`) runs the CLI in a copy of this test binary, so that `argv[0]`,
//! the manifest beside the binary and stderr can be controlled and observed.
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use serde_json::Value;
use traceforge::program::{run_cli, run_cli_with_model, Entry, Program};
use traceforge::{ConsType, Nondet};

// ------------------------------------------------------------------ helpers --

fn scratch() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let p = std::env::temp_dir().join(format!(
        "tf-wgraphs-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = std::fs::remove_dir_all(&p);
    std::fs::create_dir_all(&p).unwrap();
    p
}

fn named<F: FnOnce() + Send + 'static>(name: &str, f: F) -> traceforge::thread::JoinHandle<()> {
    traceforge::thread::Builder::new().name(name.to_owned()).spawn(f).unwrap()
}

fn me() -> traceforge::thread::ThreadId {
    traceforge::thread::current().id()
}

/// The programs under test, by name (the child process selects one by name).
fn fixture(name: &str) -> (Entry, Vec<String>) {
    let vis = |v: &[&str]| v.iter().map(|s| s.to_string()).collect::<Vec<_>>();
    match name {
        // main: an unnamed thread, a daemon, a blocked visible thread `x`, then `v`, which
        // spawns `w`. Six executions, six distinct lines.
        "rich" => (Arc::new(|| rich(false, true)), vis(&["v", "x"])),
        // The same without the unnamed thread and without the float, so that the text witness
        // can print every execution.
        "rich-printable" => (Arc::new(|| rich(true, false)), vis(&["v", "x"])),
        // One choice over 0..=3; the line is the choice divided by two.
        "halves" => (Arc::new(|| {
            named("v", || {
                let x = (0..4).nondet();
                traceforge::send_msg(me(), x / 2);
            }).join().unwrap();
        }), vis(&["v"])),
        // A helper sends on a channel in one of two executions.
        "channel" => (Arc::new(|| {
            let flag = traceforge::nondet();
            let v = named("v", move || traceforge::send_msg(me(), flag));
            if flag {
                named("h", || {
                    let (tx, rx) = traceforge::channel::Builder::<usize>::new().build();
                    tx.send_msg(5);
                    let _ = rx.recv_msg_block();
                }).join().unwrap();
            }
            v.join().unwrap();
        }), vis(&["v"])),
        // A visible float: the export itself refuses.
        "visible-float" => (Arc::new(|| {
            named("v", || traceforge::send_msg(me(), 0.5f64)).join().unwrap();
        }), vis(&["v"])),
        // An invisible thread named with a line feed; nothing visible depends on it.
        "control-name" => (Arc::new(|| {
            let v = named("v", || traceforge::send_msg(me(), 1usize));
            named("bad\nname", || {}).join().unwrap();
            v.join().unwrap();
        }), vis(&["v"])),
        // Invisible messages carrying a named and an unnamed thread's identity.
        "ids" => (Arc::new(|| {
            let v = named("v", || traceforge::send_msg(me(), 1usize));
            let r = named("r", || {
                let _ = traceforge::recv_msg_block::<traceforge::thread::ThreadId>();
                let _ = traceforge::recv_msg_block::<traceforge::thread::ThreadId>();
            });
            let rid = r.thread().id();
            let u = traceforge::thread::spawn(|| {});
            let uid = u.thread().id();
            let s = named("s", move || {
                traceforge::send_msg(rid, me());
                traceforge::send_msg(rid, uid);
            });
            for h in [v, r, u, s] { h.join().unwrap(); }
        }), vis(&["v"])),
        // One execution whose graph is large and costly to encode: an invisible thread sends
        // many unread messages, each a long vector; the visible word is one send.
        "slow-graph" => (Arc::new(|| {
            let v = named("v", || traceforge::send_msg(me(), 1usize));
            named("h", || {
                for i in 0..900u64 { traceforge::send_msg(me(), vec![i; 2000]); }
            }).join().unwrap();
            v.join().unwrap();
        }), vis(&["v"])),
        // Exploration work and graph work together: the costly graph of `slow-graph`, and
        // tosses that multiply the executions without changing the line, so the store renders
        // one graph while every execution is explored and summarised.
        "slow-explore" => (Arc::new(|| {
            let v = named("v", || traceforge::send_msg(me(), 1usize));
            named("h", || {
                for i in 0..900u64 { traceforge::send_msg(me(), vec![i; 2000]); }
            }).join().unwrap();
            for _ in 0..TOSSES.load(Ordering::Relaxed) { let _ = traceforge::nondet(); }
            v.join().unwrap();
        }), vis(&["v"])),
        // Four tosses; the line is how many came up true, so most lines have several executions
        // and the store keeps whichever the exploration order meets first.
        "tosses" => (Arc::new(|| {
            named("v", || {
                let n = (0..4).filter(|_| traceforge::nondet()).count();
                traceforge::send_msg(me(), n);
            }).join().unwrap();
        }), vis(&["v"])),
        // Must not be explored.
        "panic" => (Arc::new(|| panic!("must not explore")), vis(&["v"])),
        other => panic!("unknown fixture {other}"),
    }
}

/// The number of tosses of the `slow-explore` fixture.
static TOSSES: AtomicUsize = AtomicUsize::new(7);

fn rich(name_helper: bool, float: bool) {
    let u = if name_helper { named("u", || {}) } else { traceforge::thread::spawn(|| {}) };
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
            if float { traceforge::send_msg(me(), 1.5f64); }
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

/// A specification whose visible threads do nothing.
fn spec_body(visible: Vec<String>) -> Entry {
    Arc::new(move || {
        let hs: Vec<_> = visible.iter().map(|n| named(n, || {})).collect();
        for h in hs { h.join().unwrap(); }
    })
}

/// The CLI in process: spec side = a body with an empty `v`, impl side = the fixture.
fn cli_model(name: &str, model: Option<ConsType>, args: &[&str]) -> (String, u8) {
    let (body, visible) = fixture(name);
    let p = Program {
        visible: &|_| visible.clone(),
        spec: &|_| spec_body(visible.clone()),
        imp: &|_| body.clone(),
    };
    let args: Vec<String> = args.iter().map(|s| s.to_string()).collect();
    match model {
        None => run_cli(&p, &args),
        Some(m) => run_cli_with_model(&p, m, &args),
    }
}

fn cli(name: &str, args: &[&str]) -> (String, u8) {
    cli_model(name, None, args)
}

/// Runs in a child process only: the CLI on `WG_ARGS` (separated by U+001F), its text to
/// `WG_OUT`, and its exit code as the process's.
#[test]
fn child_process_entry() {
    let Ok(name) = std::env::var("WG_CHILD") else { return };
    let args = std::env::var("WG_ARGS").unwrap();
    let args: Vec<&str> = if args.is_empty() { vec![] } else { args.split('\u{1f}').collect() };
    let (text, code) = cli(&name, &args);
    std::fs::write(std::env::var("WG_OUT").unwrap(), text).unwrap();
    std::process::exit(code.into());
}

/// Orders writing a copied binary against starting processes. While a copy is open for
/// writing, a process forked by another test inherits the descriptor until it executes, and
/// executing the copy in that window fails with "Text file busy". Copies take the write side;
/// every process start in this file takes the read side.
static SPAWN: std::sync::RwLock<()> = std::sync::RwLock::new(());

fn spawn_guard() -> std::sync::RwLockReadGuard<'static, ()> {
    SPAWN.read().unwrap_or_else(|e| e.into_inner())
}

/// A hard link of this test binary at `dir/<file>`, or a copy where links are not possible
/// (another file system, or a sandbox that forbids them). One per test, so that each test's
/// manifest beside it is its own.
fn child_binary(dir: &Path, file: &str) -> PathBuf {
    let exe = std::env::current_exe().unwrap();
    let to = dir.join(file);
    if let Err(e) = std::fs::hard_link(&exe, &to) {
        println!("child binary {}: no hard link ({e}); copying", to.display());
        let _w = SPAWN.write().unwrap_or_else(|e| e.into_inner());
        std::fs::copy(&exe, &to).unwrap();
    }
    to
}

/// Runs the CLI in the child binary `bin`: (CLI text, stderr, exit code). Everything the child
/// did is printed to this test's captured stdout, which the harness shows when the test fails
/// (the library's panic hook does not always let the assertion text through).
fn child(bin: &Path, name: &str, args: &[&str]) -> (String, String, i32) {
    let out_file = bin.with_extension("cli-out");
    let _ = std::fs::remove_file(&out_file);
    let started = {
        let _r = spawn_guard();
        Command::new(bin)
            .args(["--exact", "child_process_entry", "--nocapture", "--test-threads", "1"])
            .env("WG_CHILD", name)
            .env("WG_ARGS", args.join("\u{1f}"))
            .env("WG_OUT", &out_file)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
    };
    let out = started.and_then(|c| c.wait_with_output()).unwrap_or_else(|e| {
        println!("child {} {name} {args:?}: spawn failed: {e}", bin.display());
        panic!("child spawn failed: {e}")
    });
    let text = std::fs::read_to_string(&out_file).unwrap_or_default();
    let code = out.status.code().unwrap_or(-1);
    println!("child {} {name} {args:?}: status {:?}\n--- cli text\n{text}--- child stdout\n{}--- child stderr\n{}---",
        bin.display(), out.status, String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&out.stderr));
    (text, String::from_utf8(out.stderr).unwrap(), code)
}

fn read_lines(p: &Path) -> Vec<String> {
    std::fs::read_to_string(p).unwrap().lines().map(str::to_owned).collect()
}

fn json(s: &str) -> Value {
    serde_json::from_str(s).unwrap()
}

/// A JSON value that keeps its object keys in file order.
#[derive(Clone, Debug, PartialEq)]
enum J { Null, Bool(bool), Num(String), Str(String), Arr(Vec<J>), Obj(Vec<(String, J)>) }

impl J {
    fn get(&self, k: &str) -> &J {
        match self {
            J::Obj(m) => &m.iter().find(|(x, _)| x == k).unwrap_or_else(|| panic!("no key {k}")).1,
            _ => panic!("not an object"),
        }
    }
    fn at(&self, i: usize) -> &J {
        match self { J::Arr(xs) => &xs[i], _ => panic!("not an array") }
    }
    fn keys(&self) -> Vec<&str> {
        match self { J::Obj(m) => m.iter().map(|(k, _)| k.as_str()).collect(), _ => vec![] }
    }
}

/// Parses JSON text, keeping key order (enough for the producer's output).
fn parse(s: &str) -> J {
    fn ws(b: &[u8], i: &mut usize) { while *i < b.len() && b" \t\r\n".contains(&b[*i]) { *i += 1; } }
    fn val(s: &str, i: &mut usize) -> J {
        let b = s.as_bytes();
        ws(b, i);
        match b[*i] {
            b'n' => { *i += 4; J::Null }
            b't' => { *i += 4; J::Bool(true) }
            b'f' => { *i += 5; J::Bool(false) }
            b'"' => {
                let start = *i;
                *i += 1;
                while b[*i] != b'"' { if b[*i] == b'\\' { *i += 1; } *i += 1; }
                *i += 1;
                J::Str(serde_json::from_str(&s[start..*i]).unwrap())
            }
            b'[' => {
                *i += 1;
                let mut xs = Vec::new();
                ws(b, i);
                if b[*i] == b']' { *i += 1; return J::Arr(xs); }
                loop {
                    xs.push(val(s, i));
                    ws(b, i);
                    let c = b[*i];
                    *i += 1;
                    if c == b']' { return J::Arr(xs); }
                    assert_eq!(c, b',');
                }
            }
            b'{' => {
                *i += 1;
                let mut m = Vec::new();
                ws(b, i);
                if b[*i] == b'}' { *i += 1; return J::Obj(m); }
                loop {
                    let J::Str(k) = val(s, i) else { panic!("key") };
                    ws(b, i);
                    assert_eq!(b[*i], b':');
                    *i += 1;
                    m.push((k, val(s, i)));
                    ws(b, i);
                    let c = b[*i];
                    *i += 1;
                    if c == b'}' { return J::Obj(m); }
                    assert_eq!(c, b',');
                }
            }
            _ => {
                let start = *i;
                while *i < b.len() && (b[*i] == b'-' || b[*i] == b'.' || b[*i] == b'e'
                    || b[*i] == b'E' || b[*i] == b'+' || b[*i].is_ascii_digit()) { *i += 1; }
                J::Num(s[start..*i].to_owned())
            }
        }
    }
    let mut i = 0;
    let v = val(s, &mut i);
    ws(s.as_bytes(), &mut i);
    assert_eq!(i, s.len(), "trailing text");
    v
}

/// Writes a value in the byte form: compact, keys in their order, serde_json's escapes.
fn bytes(v: &J) -> String {
    match v {
        J::Null => "null".to_owned(),
        J::Bool(b) => b.to_string(),
        J::Num(n) => n.clone(),
        J::Str(s) => serde_json::to_string(s).unwrap(),
        J::Arr(xs) => format!("[{}]", xs.iter().map(bytes).collect::<Vec<_>>().join(",")),
        J::Obj(m) => format!("{{{}}}", m.iter().map(|(k, x)| format!(
            "{}:{}", serde_json::to_string(k).unwrap(), bytes(x))).collect::<Vec<_>>().join(",")),
    }
}

/// The measurement block's `key: value` lines, in order.
fn block(out: &str) -> Vec<(String, String)> {
    let Some((_, b)) = out.split_once("--- measurements\n") else { return vec![] };
    b.lines().filter_map(|l| l.split_once(": ")).map(|(k, v)| (k.to_owned(), v.to_owned())).collect()
}

fn block_value(out: &str, key: &str) -> Option<String> {
    block(out).into_iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

/// `tool_commit` as the build should have fixed it: `WG_EXPECT_COMMIT` when the build was given
/// `TRACEFORGE_COMMIT` (set both to the same value), else this checkout's git state.
fn expected_commit() -> String {
    if let Ok(c) = std::env::var("WG_EXPECT_COMMIT") { return c; }
    let dir = env!("CARGO_MANIFEST_DIR");
    let git = |args: &[&str]| {
        let o = {
            let _r = spawn_guard();
            Command::new("git").arg("-C").arg(dir).args(args).output().unwrap()
        };
        assert!(o.status.success());
        String::from_utf8(o.stdout).unwrap().trim_end().to_owned()
    };
    let head = git(&["rev-parse", "HEAD"]);
    if git(&["status", "--porcelain"]).is_empty() { head } else { format!("{head}-dirty") }
}

fn this_entry() -> String {
    Path::new(&std::env::args_os().next().unwrap()).file_name().unwrap().to_string_lossy().into_owned()
}

/// `run` as derived from the contract, keys in its order.
#[allow(clippy::too_many_arguments)]
fn expected_run(entry: &str, side: &str, args: &[&str], model: &str, options: &str,
    source: &str, iteration: Option<usize>) -> String {
    format!(
        "{{\"tool\":\"traceforge\",\"tool_commit\":{},\"entry\":{},\"side\":\"{side}\",\
         \"args\":[{}],\"model\":\"{model}\",\"options\":{{{options}}},\"source\":{source},\
         \"iteration\":{},\"producer\":\"export\",\"order\":\"first\"}}",
        serde_json::to_string(&expected_commit()).unwrap(),
        serde_json::to_string(entry).unwrap(),
        args.iter().map(|a| serde_json::to_string(a).unwrap()).collect::<Vec<_>>().join(","),
        iteration.map_or("null".to_owned(), |i| i.to_string()),
    )
}

/// The rich fixture's expected line for the choices `c` in 3..=5 and `b` in {0, 1}.
fn rich_line(c: usize, b: usize) -> String {
    let v = c * 2 + b;
    let r = v + 100;
    format!(concat!(
        "{{\"statuses\":{{\"v\":\"done\",\"x\":\"blocked\"}},",
        "\"words\":{{\"v\":[{{\"s\":{v}}},{{\"r\":{r}}},{{\"r\":null}},{{\"s\":{r}}}],",
        "\"x\":[{{\"r\":{r}}}]}},\"counts\":[0,0,0,0,4]}}"), v = v, r = r)
}

/// The rich fixture's expected `threads` (thread order: main, u, d, x, v, w).
fn rich_threads(c: usize, b: usize, name_helper: bool, float: Option<&str>) -> String {
    let v = c * 2 + b;
    let helper = if name_helper { "\"u\"" } else { "null" };
    let opaque = float.map_or(String::new(), |text| format!(
        ",{{\"e\":\"SEND\",\"to\":5,\"v\":{{\"opaque\":{}}}}}", serde_json::to_string(text).unwrap()));
    format!(concat!(
        "[{{\"name\":\"main\",\"daemon\":false,\"events\":[{{\"e\":\"BEGIN\"}},",
        "{{\"e\":\"TCREATE\",\"child\":1}},{{\"e\":\"TCREATE\",\"child\":2}},",
        "{{\"e\":\"TCREATE\",\"child\":3}},{{\"e\":\"TCREATE\",\"child\":4}},",
        "{{\"e\":\"TJOIN\",\"child\":4}},{{\"e\":\"TJOIN\",\"child\":1}},",
        "{{\"e\":\"TJOIN\",\"child\":2}},{{\"e\":\"END\"}}]}},",
        "{{\"name\":{helper},\"daemon\":false,\"events\":[{{\"e\":\"BEGIN\"}},{{\"e\":\"END\"}}]}},",
        "{{\"name\":\"d\",\"daemon\":true,\"events\":[{{\"e\":\"BEGIN\"}},{{\"e\":\"END\"}}]}},",
        "{{\"name\":\"x\",\"daemon\":false,\"events\":[{{\"e\":\"BEGIN\"}},",
        "{{\"e\":\"RECV\",\"mode\":\"block\",\"rf\":[4,7]}},{{\"e\":\"BLK\"}}]}},",
        "{{\"name\":\"v\",\"daemon\":false,\"events\":[{{\"e\":\"BEGIN\"}},",
        "{{\"e\":\"NONDET\",\"n\":3,\"i\":{ci},\"lo\":3}},{{\"e\":\"NONDET\",\"n\":2,\"i\":{b}}},",
        "{{\"e\":\"TCREATE\",\"child\":5}},{{\"e\":\"SEND\",\"to\":5,\"v\":{v}}},",
        "{{\"e\":\"RECV\",\"mode\":\"block\",\"rf\":[5,2]}},",
        "{{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":null}},{{\"e\":\"SEND\",\"to\":3,\"v\":{r}}},",
        "{{\"e\":\"TJOIN\",\"child\":5}},{{\"e\":\"END\"}}]}},",
        "{{\"name\":\"w\",\"daemon\":false,\"events\":[{{\"e\":\"BEGIN\"}},",
        "{{\"e\":\"RECV\",\"mode\":\"block\",\"rf\":[4,4]}},{{\"e\":\"SEND\",\"to\":4,\"v\":{r}}}",
        "{opaque},{{\"e\":\"END\"}}]}}]"),
        helper = helper, ci = c - 3, b = b, v = v, r = v + 100, opaque = opaque)
}

// --------------------------------------------------------------- projection --

/// The summary line of a graph, rebuilt from `threads` alone: statuses, words and porf counts
/// of the visible threads, in the byte form.
fn projection(raw: &str, visible: &[String]) -> String {
    let graph: Value = json(raw);
    let jg = parse(raw);
    let jv = |t: usize, k: usize| bytes(jg.get("threads").at(t).get("events").at(k).get("v"));
    let threads = graph["threads"].as_array().unwrap();
    let events: Vec<&Vec<Value>> = threads.iter().map(|t| t["events"].as_array().unwrap()).collect();
    let mut creator: HashMap<usize, (usize, usize)> = HashMap::new();
    for (t, evs) in events.iter().enumerate() {
        for (k, e) in evs.iter().enumerate() {
            if e["e"] == "TCREATE" {
                let c = e["child"].as_u64().unwrap() as usize;
                assert!(creator.insert(c, (t, k)).is_none(), "thread {c} is created twice");
            }
        }
    }
    // clock[(t, k)][u] = how many events of thread u are at or before (t, k) in porf.
    let mut memo: HashMap<(usize, usize), Vec<usize>> = HashMap::new();
    fn clock(t: usize, k: usize, ev: &[&Vec<Value>], creator: &HashMap<usize, (usize, usize)>,
        memo: &mut HashMap<(usize, usize), Vec<usize>>) -> Vec<usize> {
        if let Some(c) = memo.get(&(t, k)) { return c.clone(); }
        let mut preds = Vec::new();
        if k > 0 { preds.push((t, k - 1)); } else if let Some(&p) = creator.get(&t) { preds.push(p); }
        let e = &ev[t][k];
        if e["e"] == "RECV" && !e["rf"].is_null() {
            let rf = e["rf"].as_array().unwrap();
            preds.push((rf[0].as_u64().unwrap() as usize, rf[1].as_u64().unwrap() as usize));
        }
        if e["e"] == "TJOIN" {
            let c = e["child"].as_u64().unwrap() as usize;
            preds.push((c, ev[c].len() - 1));
        }
        let mut out = vec![0; ev.len()];
        for (pt, pk) in preds {
            for (u, n) in clock(pt, pk, ev, creator, memo).into_iter().enumerate() {
                out[u] = out[u].max(n);
            }
        }
        out[t] = out[t].max(k + 1);
        memo.insert((t, k), out.clone());
        out
    }
    let mut vis: Vec<(String, usize)> = threads.iter().enumerate()
        .filter_map(|(t, th)| th["name"].as_str().filter(|n| visible.iter().any(|v| v == n))
            .map(|n| (n.to_owned(), t)))
        .collect();
    vis.sort();
    let word = |t: usize| -> Vec<usize> {
        events[t].iter().enumerate().filter(|(_, e)| e["e"] == "SEND" || e["e"] == "RECV")
            .map(|(k, _)| k).collect()
    };
    let mut statuses = Vec::new();
    let mut words = Vec::new();
    let mut counts = Vec::new();
    for (name, t) in &vis {
        let last = events[*t].last().unwrap();
        let status = match last["e"].as_str().unwrap() {
            "END" => "done", "BLK" => "blocked", "ERROR" => "err", e => panic!("last event {e}"),
        };
        statuses.push(format!("{}:\"{status}\"", serde_json::to_string(name).unwrap()));
        let mut w = Vec::new();
        for k in word(*t) {
            let e = &events[*t][k];
            if e["e"] == "SEND" {
                w.push(format!("{{\"s\":{}}}", jv(*t, k)));
            } else if e["rf"].is_null() {
                w.push("{\"r\":null}".to_owned());
            } else {
                let rf = e["rf"].as_array().unwrap();
                let (st, sk) = (rf[0].as_u64().unwrap() as usize, rf[1].as_u64().unwrap() as usize);
                let s = &events[st][sk];
                assert_eq!(s["e"], "SEND", "rf names a send");
                assert_eq!(s["to"].as_u64().unwrap() as usize, *t, "the read send is addressed here");
                w.push(format!("{{\"r\":{}}}", jv(st, sk)));
            }
            let c = clock(*t, k, &events, &creator, &mut memo);
            for (_, u) in vis.iter().filter(|(_, u)| u != t) {
                counts.push(word(*u).iter().filter(|&&j| j < c[*u]).count().to_string());
            }
        }
        words.push(format!("{}:[{}]", serde_json::to_string(name).unwrap(), w.join(",")));
    }
    format!("{{\"statuses\":{{{}}},\"words\":{{{}}},\"counts\":[{}]}}",
        statuses.join(","), words.join(","), counts.join(","))
}

/// Structural checks every graph line must pass, and its parsed form.
fn check_graph_line(raw: &str, header: &str, export_lines: &[String]) -> Value {
    let g = json(raw);
    let jg = parse(raw);
    assert_eq!(bytes(&jg), raw, "compact byte form");
    assert_eq!(jg.keys(), ["witness", "line", "export", "run", "join", "nearest", "threads"]);
    assert_eq!(jg.get("witness"), &J::Num("1".to_owned()));
    assert_eq!(bytes(jg.get("export")), header, "the export header verbatim");
    assert_eq!((jg.get("join"), jg.get("nearest")), (&J::Null, &J::Null));
    assert_eq!(jg.get("run").keys(), RUN_KEYS);
    let J::Arr(threads) = jg.get("threads") else { panic!("threads") };
    for th in threads {
        assert_eq!(th.keys(), ["name", "daemon", "events"]);
        let J::Arr(evs) = th.get("events") else { panic!("events") };
        for e in evs {
            let J::Str(kind) = e.get("e") else { panic!("e") };
            let want: &[&str] = match kind.as_str() {
                "BEGIN" | "END" | "BLK" => &["e"],
                "TCREATE" | "TJOIN" => &["e", "child"],
                "SEND" => &["e", "to", "v"],
                "RECV" => &["e", "mode", "rf"],
                "NONDET" if e.keys().len() == 4 => &["e", "n", "i", "lo"],
                "NONDET" => &["e", "n", "i"],
                k => panic!("event kind {k}"),
            };
            assert_eq!(e.keys(), want, "{raw}");
        }
    }
    let line = g["line"].as_str().unwrap();
    assert!(export_lines[1..].iter().any(|l| l == line), "line not in the export: {line}");
    let visible: Vec<String> = g["export"]["visible"].as_array().unwrap().iter()
        .map(|v| v.as_str().unwrap().to_owned()).collect();
    assert_eq!(projection(raw, &visible), line, "projection of {raw}");
    g
}

const RUN_KEYS: [&str; 11] = ["tool", "tool_commit", "entry", "side", "args", "model", "options",
    "source", "iteration", "producer", "order"];

/// Runs an export (with optional extra flags) and returns (cli text, code, export lines, store
/// lines if any).
fn export(name: &str, dir: &Path, tag: &str, extra: &[&str], trailing: &[&str])
    -> (String, u8, Vec<String>, Option<Vec<String>>) {
    let out = dir.join(format!("{tag}.jsonl"));
    let store = dir.join(format!("{tag}.graphs.jsonl"));
    let out_s = out.to_str().unwrap().to_owned();
    let store_s = store.to_str().unwrap().to_owned();
    let mut args: Vec<&str> = vec!["export", "impl", "--out", &out_s];
    for a in extra {
        args.push(if *a == "@STORE" { &store_s } else { a });
    }
    if !trailing.is_empty() { args.push("--"); args.extend(trailing); }
    let (text, code) = cli(name, &args);
    let lines = if out.exists() { read_lines(&out) } else { vec![] };
    let st = store.exists().then(|| read_lines(&store));
    (text, code, lines, st)
}

// -------------------------------------------------------------------- tests --

#[test]
fn rich_store_bytes_match_the_derivation() {
    let dir = scratch();
    let (text, code, lines, store) =
        export("rich", &dir, "e", &["--graphs", "@STORE"], &["a", "b c"]);
    assert_eq!(code, 0, "{text}");
    let header = &lines[0];
    let mut expected_lines: Vec<String> =
        (3..6).flat_map(|c| (0..2).map(move |b| rich_line(c, b))).collect();
    expected_lines.sort();
    assert_eq!(&lines[1..], expected_lines.as_slice(), "the export's own lines");
    let store = store.expect("a store is written");
    assert_eq!(store.len(), 7, "identity line and six graphs");
    let entry = this_entry();
    let args = ["a", "b c"];
    assert_eq!(store[0], format!("{{\"witness_store\":1,\"export\":{header},\"run\":{}}}",
        expected_run(&entry, "impl", &args, "fifo", "", "\"unknown\"", None)));
    let mut seen = Vec::new();
    for (n, raw) in store[1..].iter().enumerate() {
        let g = check_graph_line(raw, header, &lines);
        // The opaque text is checked on its own below; here it is masked.
        let opaque = g["threads"][5]["events"][3]["v"]["opaque"].as_str().unwrap().to_owned();
        let raw = &raw.replace(&serde_json::to_string(&opaque).unwrap(), "\"<masked>\"");
        let line = g["line"].as_str().unwrap();
        let (c, b) = (3..6).flat_map(|c| (0..2).map(move |b| (c, b)))
            .find(|&(c, b)| rich_line(c, b) == line).expect("a derived line");
        let expected = format!(
            "{{\"witness\":1,\"line\":{},\"export\":{header},\"run\":{},\"join\":null,\
             \"nearest\":null,\"threads\":{}}}",
            serde_json::to_string(line).unwrap(),
            expected_run(&entry, "impl", &args, "fifo", "", "\"unknown\"", Some(n + 1)),
            rich_threads(c, b, false, Some("<masked>")));
        assert_eq!(raw.as_bytes(), expected.as_bytes());
        seen.push(line.to_owned());
    }
    seen.sort();
    seen.dedup();
    assert_eq!(seen.len(), 6, "no two graph lines carry the same line");
    assert!(!dir.join("e.graphs.jsonl.tmp").exists());
}

#[test]
fn export_file_and_cli_text_unchanged_by_the_store() {
    for name in ["rich", "halves", "channel"] {
        let dir = scratch();
        let (a, ac, al, ast) = export(name, &dir, "plain", &[], &["k"]);
        let (b, bc, bl, bst) = export(name, &dir, "with", &["--graphs", "@STORE"], &["k"]);
        assert_eq!((ac, bc), (0, 0), "{a}\n{b}");
        assert!(ast.is_none() && bst.is_some());
        assert_eq!(al, bl, "export file of {name}");
        let strip = |t: &str, file: &str| t.replace(file, "F");
        let (head_a, _) = a.split_once("--- measurements\n").unwrap();
        let (head_b, _) = b.split_once("--- measurements\n").unwrap();
        // The store adds one summary line right after the `exported:` line, nothing else.
        let summary = format!("graph_store: written={} refused={} ms={}\n",
            block_value(&b, "graphs_written").unwrap(), block_value(&b, "graphs_refused").unwrap(),
            block_value(&b, "graphs_ms").unwrap());
        let head_a = strip(head_a, "plain.jsonl");
        let (pre, post) = head_a.split_at(head_a.find("exported: ").unwrap());
        let (exported, rest) = post.split_at(post.find('\n').unwrap() + 1);
        assert_eq!(strip(head_b, "with.jsonl"), format!("{pre}{exported}{summary}{rest}"), "{name}");
        assert!(!a.contains("graph_store:"), "no summary line without the store");
        let keys_a: Vec<String> = block(&a).into_iter().map(|(k, _)| k).collect();
        let keys_b: Vec<String> = block(&b).into_iter().map(|(k, _)| k).collect();
        let mut extended = keys_a.clone();
        extended.extend(["graphs_written", "graphs_refused", "graphs_ms"].map(str::to_owned));
        assert_eq!(keys_b, extended, "three keys after the existing ones");
        // The non-timing values agree.
        for ((k, va), (_, vb)) in block(&a).into_iter().zip(block(&b)) {
            if !k.ends_with("_ms") && k != "peak_rss_kb" {
                assert_eq!(va, vb, "measurement {k} of {name}");
            }
        }
    }
}

#[test]
fn measurement_counts() {
    let dir = scratch();
    let (t, _, _, _) = export("rich", &dir, "r", &["--graphs", "@STORE"], &[]);
    assert_eq!(block_value(&t, "graphs_written").as_deref(), Some("6"), "{t}");
    assert_eq!(block_value(&t, "graphs_refused").as_deref(), Some("0"), "{t}");
    assert!(block_value(&t, "graphs_ms").unwrap().parse::<u64>().is_ok());
    let b = block(&t);
    assert_eq!(b.last().unwrap().0, "graphs_ms");
    let (t, _, _, _) = export("rich", &dir, "l", &["--graphs", "@STORE", "--graphs-limit", "2"], &[]);
    assert_eq!(block_value(&t, "graphs_written").as_deref(), Some("2"), "{t}");
    let (t, code, _, _) = export("channel", &dir, "ch", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 0, "{t}");
    assert_eq!(block_value(&t, "graphs_written").as_deref(), Some("1"), "{t}");
    assert_eq!(block_value(&t, "graphs_refused").as_deref(), Some("1"), "{t}");
}

#[test]
fn iteration_is_the_first_completion_with_the_line() {
    let dir = scratch();
    let (t, code, lines, store) = export("halves", &dir, "h", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 0, "{t}");
    let store = store.unwrap();
    assert_eq!(store.len(), 3, "{store:?}");
    // Choices are explored from the range's start: x = 0, 1, 2, 3; lines 0, 0, 1, 1.
    let g1 = check_graph_line(&store[1], &lines[0], &lines);
    let g2 = check_graph_line(&store[2], &lines[0], &lines);
    assert_eq!(g1["line"], "{\"statuses\":{\"v\":\"done\"},\"words\":{\"v\":[{\"s\":0}]},\"counts\":[]}");
    assert_eq!(g2["line"], "{\"statuses\":{\"v\":\"done\"},\"words\":{\"v\":[{\"s\":1}]},\"counts\":[]}");
    assert_eq!(g1["run"]["iteration"], 1);
    assert_eq!(g2["run"]["iteration"], 3);
    let nondet = |g: &Value| g["threads"][1]["events"][1].clone();
    assert_eq!(nondet(&g1), json("{\"e\":\"NONDET\",\"n\":4,\"i\":0,\"lo\":0}"));
    assert_eq!(nondet(&g2), json("{\"e\":\"NONDET\",\"n\":4,\"i\":2,\"lo\":0}"));
    assert!(json(&store[0])["run"]["iteration"].is_null());
}

#[test]
fn limit_keeps_the_first_lines() {
    let dir = scratch();
    let (_, _, _, full) = export("rich", &dir, "full", &["--graphs", "@STORE", "--seed", "1"], &[]);
    let full = full.unwrap();
    for (n, want) in [(0usize, 1usize), (1, 2), (2, 3), (6, 7), (100, 7)] {
        let limit = n.to_string();
        let (t, code, _, store) =
            export("rich", &dir, &format!("l{n}"),
                &["--graphs", "@STORE", "--graphs-limit", &limit, "--seed", "1"], &[]);
        assert_eq!(code, 0, "{t}");
        let store = store.unwrap();
        assert_eq!(store.len(), want, "limit {n}");
        assert_eq!(store[..], full[..want], "limit {n} keeps the first graphs");
        assert_eq!(block_value(&t, "graphs_written"), Some((want - 1).to_string()));
    }
}

#[test]
fn run_identity_fields() {
    let dir = scratch();
    let entry = this_entry();
    let cases: Vec<(Option<ConsType>, Vec<&str>, &str, &str)> = vec![
        (None, vec![], "fifo", ""),
        (Some(ConsType::Bag), vec![], "bag", ""),
        (Some(ConsType::Causal), vec![], "causal", ""),
        (None, vec!["--model", "bag"], "bag", ""),
        (Some(ConsType::Bag), vec!["--model", "fifo"], "fifo", ""),
        (None, vec!["--model", "causal"], "causal", ""),
        #[allow(deprecated)]
        (Some(ConsType::CD), vec![], "causal", ""),
        (None, vec!["--seed", "7"], "fifo", "\"seed\":7"),
        (None, vec!["--threshold", "9"], "fifo", "\"threshold\":9"),
        (None, vec!["--threshold", "9", "--seed", "7"], "fifo", "\"seed\":7,\"threshold\":9"),
    ];
    for (i, (model, flags, label, options)) in cases.into_iter().enumerate() {
        for side in ["spec", "impl"] {
            let out = dir.join(format!("{i}{side}.jsonl"));
            let store = dir.join(format!("{i}{side}.g"));
            let mut args = vec!["export", side, "--out", out.to_str().unwrap(),
                "--graphs", store.to_str().unwrap()];
            args.extend(flags.iter());
            args.extend(["--", "x\"y", "", "z"]);
            let (t, code) = cli_model("halves", model, &args);
            assert_eq!(code, 0, "{t}");
            let st = read_lines(&store);
            let header = read_lines(&out).remove(0);
            assert_eq!(st[0], format!("{{\"witness_store\":1,\"export\":{header},\"run\":{}}}",
                expected_run(&entry, side, &["x\"y", "", "z"], label, options, "\"unknown\"", None)),
                "case {i} {side}");
            for (n, raw) in st[1..].iter().enumerate() {
                let first = if side == "spec" { 1 } else { [1, 3][n] };
                assert_eq!(bytes(parse(raw).get("run")), expected_run(&entry, side, &["x\"y", "", "z"],
                    label, options, "\"unknown\"", Some(first)), "case {i} {side}");
            }
        }
    }
}

#[test]
fn refusals_before_any_run() {
    let dir = scratch();
    let out = dir.join("o");
    let o = out.to_str().unwrap();
    let usage = cli("panic", &[]).0.split_once('\n').unwrap().1.to_owned();
    let cases: Vec<(Vec<&str>, &str)> = vec![
        (vec!["export", "impl", "--out", o, "--graphs-limit", "3"], "--graphs-limit requires --graphs"),
        (vec!["export", "impl", "--out", o, "--graphs-limit", "0"], "--graphs-limit requires --graphs"),
        (vec!["count", "impl", "--graphs", "g"], "--graphs requires export"),
        (vec!["count", "impl", "--graphs", "g", "--graphs-limit", "0"], "--graphs requires export"),
        (vec!["conf", "--graphs", "g"], "--graphs requires export"),
        (vec!["conf", "--engine", "stateful", "--graphs", "g"], "--graphs requires export"),
        (vec!["export", "impl", "--out", o, "--graphs", "g", "--threads", "2"],
            "--graphs with --threads N>1 requires --graphs-limit 0"),
        (vec!["export", "impl", "--out", o, "--graphs", "g", "--threads", "3", "--graphs-limit", "1"],
            "--graphs with --threads N>1 requires --graphs-limit 0"),
    ];
    for (args, reason) in cases {
        assert_eq!(cli("panic", &args), (format!("program: {reason}\n{usage}"), 2), "{args:?}");
        assert!(!out.exists() && !Path::new("g").exists());
    }
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 0);
}

#[test]
fn graphs_on_online_and_row_are_refused_before_any_run() {
    // `online` takes `--graphs` only beside `--out`; `row` never takes it.
    let dir = scratch();
    let spec = dir.join("spec.jsonl");
    assert_eq!(cli("halves", &["export", "spec", "--out", spec.to_str().unwrap()]).1, 0);
    let g = dir.join("g");
    let gs = g.to_str().unwrap();
    let mut firsts = Vec::new();
    for args in [vec!["online", "--spec", spec.to_str().unwrap(), "--graphs", gs],
                 vec!["row", "--seed", "0", "--graphs", gs]] {
        let (t, code) = cli("panic", &args);
        assert_eq!(code, 2, "{t}");
        assert!(!g.exists());
        firsts.push(t.lines().next().unwrap().to_owned());
    }
    assert_eq!(firsts, ["program: --graphs with online requires --out",
        "program: row takes only --model, --seed, --threshold and --dump-large-graph, not `--graphs`"]);
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1, "only the specification file");
}

#[test]
fn parallel_export_with_limit_zero_writes_the_identity_line() {
    let dir = scratch();
    let (t, code, lines, store) =
        export("halves", &dir, "p", &["--threads", "2", "--graphs", "@STORE", "--graphs-limit", "0"], &[]);
    assert_eq!(code, 0, "{t}");
    let store = store.unwrap();
    assert_eq!(store, vec![format!("{{\"witness_store\":1,\"export\":{},\"run\":{}}}", lines[0],
        expected_run(&this_entry(), "impl", &[], "fifo", "", "\"unknown\"", None))]);
    assert_eq!(block_value(&t, "graphs_written").as_deref(), Some("0"), "{t}");
    assert_eq!(block_value(&t, "graphs_refused").as_deref(), Some("0"), "{t}");
    let (t2, _, lines2, _) = export("halves", &dir, "q", &["--threads", "2"], &[]);
    assert_eq!(lines, lines2, "{t2}");
}

#[test]
fn refused_export_writes_no_store() {
    for existing in [false, true] {
        let dir = scratch();
        let store = dir.join("s.graphs.jsonl");
        if existing { std::fs::write(&store, b"sentinel\n").unwrap(); }
        let (t, code, _, _) = export("visible-float", &dir, "s", &["--graphs", "@STORE"], &[]);
        assert_eq!(code, 2, "{t}");
        assert!(t.contains("export refused"), "{t}");
        if existing {
            assert_eq!(std::fs::read(&store).unwrap(), b"sentinel\n");
        } else {
            assert!(!store.exists());
        }
        assert!(!dir.join("s.graphs.jsonl.tmp").exists());
        assert!(block_value(&t, "graphs_written").is_none(), "{t}");
    }
}

#[test]
fn store_is_staged_beside_the_path() {
    // A directory at `<PATH>.tmp` makes the staged write fail; nothing appears at PATH.
    let dir = scratch();
    let store = dir.join("s.graphs.jsonl");
    std::fs::create_dir(dir.join("s.graphs.jsonl.tmp")).unwrap();
    let (t, code, lines, _) = export("halves", &dir, "s", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 2, "{t}");
    assert!(!store.exists());
    assert_eq!(lines.len(), 3, "the export itself is written");
    assert!(t.contains("the graph store was not"), "{t}");
    // An existing store is replaced whole.
    let dir = scratch();
    let store = dir.join("s.graphs.jsonl");
    std::fs::write(&store, "old\n".repeat(1000)).unwrap();
    let (t, code, _, st) = export("halves", &dir, "s", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 0, "{t}");
    assert_eq!(st.unwrap().len(), 3);
    assert!(!dir.join("s.graphs.jsonl.tmp").exists());
}

#[test]
fn text_witness_events_are_the_graph_events() {
    let dir = scratch();
    let (t, code, lines, store) = export("rich-printable", &dir, "e", &["--graphs", "@STORE", "--seed", "0"], &[]);
    assert_eq!(code, 0, "{t}");
    let store = store.unwrap();
    assert_eq!(store.len(), 7);
    // A specification that covers nothing: every distinct line gets a text witness.
    let spec = dir.join("spec.jsonl");
    assert_eq!(cli("rich-printable", &["export", "spec", "--out", spec.to_str().unwrap()]).1, 0);
    let wdir = format!("{}/w/", dir.display());
    let (t, code) = cli("rich-printable",
        &["online", "--spec", spec.to_str().unwrap(), "--witness", &wdir, "--seed", "0"]);
    assert_eq!(code, 0, "{t}");
    let mut texts: BTreeMap<String, (usize, String)> = BTreeMap::new();
    for n in 1..=6 {
        let text = std::fs::read_to_string(format!("{wdir}witness-{n}.txt")).unwrap();
        let (head, body) = text.split_once('\n').unwrap();
        let (it, line) = head.strip_prefix("uncovered summary (iteration ").unwrap()
            .split_once("): ").unwrap();
        texts.insert(line.to_owned(), (it.parse().unwrap(), body.to_owned()));
    }
    for (n, raw) in store[1..].iter().enumerate() {
        let g = check_graph_line(raw, &lines[0], &lines);
        let line = g["line"].as_str().unwrap();
        let (c, b) = (3..6).flat_map(|c| (0..2).map(move |b| (c, b)))
            .find(|&(c, b)| rich_line(c, b) == line).unwrap();
        assert_eq!(bytes(parse(raw).get("threads")), rich_threads(c, b, true, None));
        let (it, body) = &texts[line];
        assert_eq!(g["run"]["iteration"], *it as u64, "same first iteration");
        assert_eq!(g["run"]["iteration"], (n + 1) as u64);
        assert_eq!(&as_text(raw), body, "text witness of {line}");
    }
}

/// The text witness body (after its header line) that a graph's events stand for.
fn as_text(raw: &str) -> String {
    let g = &json(raw);
    let jg = parse(raw);
    let threads = g["threads"].as_array().unwrap();
    let name = |t: usize| threads[t]["name"].as_str().unwrap().to_owned();
    let mut s = String::new();
    for (t, th) in threads.iter().enumerate() {
        let daemon = if th["daemon"] == true { ", daemon" } else { "" };
        s.push_str(&format!("thread \"{}\"[tid={t}{daemon}]:\n", name(t)));
        for (k, e) in th["events"].as_array().unwrap().iter().enumerate() {
            let ev = match e["e"].as_str().unwrap() {
                "TCREATE" => {
                    let c = e["child"].as_u64().unwrap() as usize;
                    format!("TCREATE({c}:\"{}\")", name(c))
                }
                "TJOIN" => format!("TJOIN({})", e["child"]),
                "SEND" => format!("SEND({}, {})", name(e["to"].as_u64().unwrap() as usize),
                    bytes(jg.get("threads").at(t).get("events").at(k).get("v"))),
                "RECV" if e["rf"].is_null() => "RECV() [TIMEOUT]".to_owned(),
                "RECV" => {
                    let s = e["rf"][0].as_u64().unwrap() as usize;
                    format!("RECV() [({s}, {}) {}]", e["rf"][1], name(s))
                }
                "NONDET" => format!("NONDET {}", e["i"]),
                other => other.to_owned(),
            };
            s.push_str(&format!("\t({t}, {k}): {ev}\n"));
        }
    }
    s
}

#[test]
fn refused_graphs_are_reported_and_the_export_is_unchanged() {
    for (name, reason) in [("channel", "unsupported event send to a non-thread destination")] {
        let dir = scratch();
        let bin = child_binary(&dir, "tf_child");
        let out = dir.join("e.jsonl");
        let store = dir.join("e.g");
        let plain = dir.join("p.jsonl");
        let (t0, e0, c0) = child(&bin, name, &["export", "impl", "--out", plain.to_str().unwrap()]);
        assert_eq!((c0, e0.as_str()), (0, ""), "{t0}");
        let (t, err, code) = child(&bin, name, &["export", "impl", "--out", out.to_str().unwrap(),
            "--graphs", store.to_str().unwrap()]);
        assert_eq!(code, 0, "{t}\n{err}");
        assert_eq!(std::fs::read(&out).unwrap(), std::fs::read(&plain).unwrap());
        let lines = read_lines(&out);
        let refused_line = "{\"statuses\":{\"v\":\"done\"},\"words\":{\"v\":[{\"s\":true}]},\"counts\":[]}";
        let n = lines.iter().position(|l| l == refused_line).expect("the refused line is exported") + 1;
        assert_eq!(err, format!("graphs: refused {n}: {reason}\n"), "{name}");
        let st = read_lines(&store);
        assert_eq!(st.len(), 2, "{name}");
        let g = check_graph_line(&st[1], &lines[0], &lines);
        assert_eq!(g["line"], "{\"statuses\":{\"v\":\"done\"},\"words\":{\"v\":[{\"s\":false}]},\"counts\":[]}");
        assert_eq!(g["run"]["entry"], "tf_child");
        assert_eq!(block_value(&t, "graphs_refused").as_deref(), Some("1"));
    }
}

#[test]
fn control_characters_in_any_thread_name_refuse_the_graph() {
    let dir = scratch();
    let bin = child_binary(&dir, "tf_child");
    let out = dir.join("c.jsonl");
    let plain = dir.join("p.jsonl");
    let store = dir.join("c.g");
    let (t0, e0, c0) = child(&bin, "control-name", &["export", "impl", "--out", plain.to_str().unwrap()]);
    assert_eq!((c0, e0.as_str()), (0, ""), "{t0}");
    let (t, err, code) = child(&bin, "control-name", &["export", "impl", "--out", out.to_str().unwrap(),
        "--graphs", store.to_str().unwrap()]);
    assert_eq!(code, 0, "{t}\n{err}");
    assert_eq!(std::fs::read(&out).unwrap(), std::fs::read(&plain).unwrap(), "export unchanged");
    // The export holds the header and one line: the refused graph's line is line 2.
    assert_eq!(read_lines(&out).len(), 2);
    assert!(err.starts_with("graphs: refused 2: ") && err.lines().count() == 1, "{err:?}");
    assert_eq!(read_lines(&store).len(), 1, "the identity line only");
    assert_eq!(block_value(&t, "graphs_refused").as_deref(), Some("1"), "{t}");
    assert_eq!(block_value(&t, "graphs_written").as_deref(), Some("0"), "{t}");
}

#[test]
fn opaque_text_is_the_values_debug_text() {
    let dir = scratch();
    let (t, code, _, store) = export("rich", &dir, "o", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 0, "{t}");
    for raw in &store.unwrap()[1..] {
        let g = json(raw);
        assert_eq!(g["threads"][5]["events"][3]["v"], json("{\"opaque\":\"1.5\"}"),
            "Debug text of the sent value 1.5f64");
    }
}

// ------------------------------------------------------------------ manifest --

fn manifest_run(text: Option<&[u8]>, as_dir: bool) -> (J, String, PathBuf) {
    manifest_run_with(text, as_dir, None, &[])
}

/// [`manifest_run`] with the manifest's mtime set `age` seconds before (positive) or after
/// (negative) the binary's, and extra export flags.
fn manifest_run_with(text: Option<&[u8]>, as_dir: bool, age: Option<i64>, extra: &[&str])
    -> (J, String, PathBuf) {
    let dir = scratch();
    let bin = child_binary(&dir, "tf_mcp_x");
    let m = dir.join("tf_mcp_x.SOURCE.md5");
    if as_dir { std::fs::create_dir(&m).unwrap(); }
    if let Some(t) = text { std::fs::write(&m, t).unwrap(); }
    if let Some(age) = age {
        let bt = std::fs::metadata(&bin).unwrap().modified().unwrap();
        let d = std::time::Duration::from_secs(age.unsigned_abs());
        let mt = if age >= 0 { bt - d } else { bt + d };
        std::fs::File::options().write(true).open(&m).unwrap().set_modified(mt).unwrap();
        assert_eq!(std::fs::metadata(&m).unwrap().modified().unwrap(), mt);
    }
    let out = dir.join("e.jsonl");
    let store = dir.join("e.g");
    let mut args = vec!["export", "impl", "--out", out.to_str().unwrap(), "--graphs",
        store.to_str().unwrap()];
    args.extend(extra);
    let (t, err, code) = child(&bin, "halves", &args);
    assert_eq!(code, 0, "{t}\n{err}");
    let st = read_lines(&store);
    let run0 = parse(&st[0]).get("run").clone();
    for raw in &st[1..] {
        assert_eq!(parse(raw).get("run").get("source"), run0.get("source"));
    }
    assert_eq!(run0.get("entry"), &J::Str("tf_mcp_x".to_owned()));
    (run0.get("source").clone(), err, m)
}

#[test]
fn manifest_copied_sorted_and_never_hashed() {
    let a = "0123456789abcdef0123456789abcdef";
    let b = "ffffffffffffffffffffffffffffffff";
    let text = format!("# root benchmarks/x/rust\n{a}  src/main.rs\n{b}  Cargo.toml\n\
        {a}  src.rs\n{b}  a \"q\".rs\n{a}  does/not/exist.rs\n");
    let (src, err, _) = manifest_run(Some(text.as_bytes()), false);
    assert_eq!(err, "");
    assert_eq!(bytes(&src), format!("{{\"root\":\"benchmarks/x/rust\",\"files\":{{\
        \"Cargo.toml\":\"{b}\",\"a \\\"q\\\".rs\":\"{b}\",\"does/not/exist.rs\":\"{a}\",\
        \"src.rs\":\"{a}\",\"src/main.rs\":\"{a}\"}}}}"));
    // Key order in the file itself.
    let dir_order = ["Cargo.toml", "a \"q\".rs", "does/not/exist.rs", "src.rs", "src/main.rs"];
    assert_eq!(src.get("files").keys(), dir_order);
}

#[test]
fn manifest_key_order_is_bytes_in_the_store() {
    let a = "0123456789abcdef0123456789abcdef";
    let dir = scratch();
    let bin = child_binary(&dir, "tf_order");
    std::fs::write(dir.join("tf_order.SOURCE.md5"),
        format!("# root r\n{a}  b\n{a}  Z\n{a}  a\n{a}  _\n")).unwrap();
    let store = dir.join("g");
    let (t, err, code) = child(&bin, "halves", &["export", "impl", "--out",
        dir.join("e").to_str().unwrap(), "--graphs", store.to_str().unwrap()]);
    assert_eq!((code, err.as_str()), (0, ""), "{t}");
    let first = read_lines(&store).remove(0);
    let want = format!("\"source\":{{\"root\":\"r\",\"files\":{{\"Z\":\"{a}\",\"_\":\"{a}\",\
        \"a\":\"{a}\",\"b\":\"{a}\"}}}}");
    assert!(first.contains(&want), "{first}");
}

#[test]
fn missing_or_malformed_manifest_gives_unknown() {
    let a = "0123456789abcdef0123456789abcdef";
    let (src, err, _) = manifest_run(None, false);
    assert_eq!((src, err.as_str()), (J::Str("unknown".to_owned()), ""));
    let bad: Vec<(&str, String)> = vec![
        ("no root line", format!("{a}  src/main.rs\n")),
        ("empty file", String::new()),
        ("root line not first", format!("{a}  x\n# root r\n")),
        ("upper-case digest", format!("# root r\n{}  x\n", a.to_uppercase())),
        ("short digest", format!("# root r\n{}  x\n", &a[1..])),
        ("one space", format!("# root r\n{a} x\n")),
        ("non-hex digest", format!("# root r\n{}g  x\n", &a[1..])),
        ("no path", format!("# root r\n{a}  \n")),
        ("duplicate path", format!("# root r\n{a}  x\n{a}  y\n{a}  x\n")),
        ("no file lines", "# root r\n".to_owned()),
        ("empty interior line", format!("# root r\n\n{a}  a\n")),
        ("empty line before the end", format!("# root r\n{a}  a\n\n")),
    ];
    for (what, text) in bad {
        let (src, err, m) = manifest_run(Some(text.as_bytes()), false);
        assert_eq!(src, J::Str("unknown".to_owned()), "{what}");
        let prefix = format!("graphs: manifest {}: ", m.display());
        assert!(err.starts_with(&prefix) && err.ends_with('\n') && err.lines().count() == 1,
            "{what}: {err:?}");
        assert!(err.len() > prefix.len() + 1, "{what}: a reason is given");
    }
    // Not valid UTF-8, and a directory: unreadable.
    for (what, text, as_dir) in [("binary", Some(&b"# root r\n\xff\xfe  x\n"[..]), false),
                                 ("directory", None, true)] {
        let (src, err, m) = manifest_run(text, as_dir);
        assert_eq!(src, J::Str("unknown".to_owned()), "{what}");
        assert!(err.starts_with(&format!("graphs: manifest {}: ", m.display()))
            && err.lines().count() == 1, "{what}: {err:?}");
    }
}

#[test]
fn manifest_is_not_read_without_graphs() {
    let dir = scratch();
    let bin = child_binary(&dir, "tf_quiet");
    std::fs::write(dir.join("tf_quiet.SOURCE.md5"), b"not a manifest\n").unwrap();
    let out = dir.join("e.jsonl");
    let (t, err, code) = child(&bin, "halves", &["export", "impl", "--out", out.to_str().unwrap()]);
    assert_eq!((code, err.as_str()), (0, ""), "{t}");
}

// ------------------------------------------------------ comparison material --

/// Writes, for each listed fixture and flag set, the CLI text, stderr, exit code and export
/// file of a run without `--graphs` into `WG_DUMP`, for comparison across builds. Ignored.
#[test]
#[ignore]
fn dump_runs_without_graphs() {
    let Ok(dump) = std::env::var("WG_DUMP") else { return };
    let dump = PathBuf::from(dump);
    std::fs::create_dir_all(&dump).unwrap();
    let dir = scratch();
    let bin = child_binary(&dir, "tf_dump");
    let cases: Vec<(&str, Vec<&str>)> = vec![
        ("rich", vec!["export", "impl"]),
        ("rich", vec!["export", "spec"]),
        ("halves", vec!["export", "impl", "--seed", "3", "--threshold", "5"]),
        ("halves", vec!["export", "impl", "--model", "bag"]),
        ("halves", vec!["export", "impl", "--threads", "2"]),
        ("channel", vec!["export", "impl"]),
        ("visible-float", vec!["export", "impl"]),
        ("halves", vec!["export", "impl", "--audit-graphs"]),
    ];
    for (i, (name, args)) in cases.into_iter().enumerate() {
        let out = dir.join(format!("{i}.jsonl"));
        let mut a = args.clone();
        a.extend(["--out", out.to_str().unwrap(), "--", "q"]);
        let (text, err, code) = child(&bin, name, &a);
        let text = text.replace(dir.to_str().unwrap(), "DIR");
        std::fs::write(dump.join(format!("{i}.cli")), text).unwrap();
        std::fs::write(dump.join(format!("{i}.err")), err).unwrap();
        std::fs::write(dump.join(format!("{i}.code")), code.to_string()).unwrap();
        if out.exists() { std::fs::copy(&out, dump.join(format!("{i}.jsonl"))).unwrap(); }
    }
}

/// Checks every graph of the store `WG_STORE` against the export `WG_EXPORT` (byte form, key
/// order, lines in the export, distinct lines, projection). Ignored; for stores made elsewhere.
#[test]
#[ignore]
fn check_external_store() {
    let (Ok(store), Ok(export)) = (std::env::var("WG_STORE"), std::env::var("WG_EXPORT")) else {
        return;
    };
    let lines = read_lines(Path::new(&export));
    let store = read_lines(Path::new(&store));
    let head = parse(&store[0]);
    assert_eq!(head.keys(), ["witness_store", "export", "run"]);
    assert_eq!(bytes(head.get("export")), lines[0]);
    assert_eq!(head.get("run").get("iteration"), &J::Null);
    let mut seen = std::collections::HashSet::new();
    let mut last = 0;
    for raw in &store[1..] {
        let g = check_graph_line(raw, &lines[0], &lines);
        assert!(seen.insert(g["line"].as_str().unwrap().to_owned()), "a line twice");
        let it = g["run"]["iteration"].as_u64().unwrap();
        assert!(it > last, "graphs in first-occurrence order");
        last = it;
        assert_eq!(bytes(parse(raw).get("run")).replace(&format!("\"iteration\":{it}"),
            "\"iteration\":null"), bytes(head.get("run")));
    }
    assert_eq!(seen.len(), lines.len() - 1, "one graph per line");
}

#[test]
fn invisible_thread_identities_use_names_or_opaque() {
    let dir = scratch();
    let (t, code, lines, store) = export("ids", &dir, "i", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 0, "{t}");
    let store = store.unwrap();
    assert_eq!(store.len(), 2, "{t}");
    check_graph_line(&store[1], &lines[0], &lines);
    let g = parse(&store[1]);
    let s = g.get("threads").at(4);
    assert_eq!(bytes(s), "{\"name\":\"s\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},\
        {\"e\":\"SEND\",\"to\":2,\"v\":\"s\"},".to_owned()
        + &bytes(s.get("events").at(2)) + ",{\"e\":\"END\"}]}");
    let unnamed = s.get("events").at(2).get("v");
    assert_eq!(unnamed.keys(), ["opaque"]);
    assert!(matches!(unnamed.get("opaque"), J::Str(_)));
    assert_eq!(bytes(g.get("threads").at(3)),
        "{\"name\":null,\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},{\"e\":\"END\"}]}");
}

#[test]
fn manifest_final_newline_is_optional() {
    let a = "0123456789abcdef0123456789abcdef";
    for text in [format!("# root r\n{a}  a\n"), format!("# root r\n{a}  a")] {
        let (src, err, _) = manifest_run(Some(text.as_bytes()), false);
        assert_eq!(err, "", "{text:?}");
        assert_eq!(bytes(&src), format!("{{\"root\":\"r\",\"files\":{{\"a\":\"{a}\"}}}}"), "{text:?}");
    }
}

#[test]
fn overlapping_export_and_store_paths_are_refused_before_any_run() {
    let usage = cli("panic", &[]).0.split_once('\n').unwrap().1.to_owned();
    let reason = "--graphs must name another file than --out (and than either one's .tmp)";
    let dir = scratch();
    std::fs::create_dir(dir.join("x")).unwrap();
    std::fs::create_dir(dir.join("real")).unwrap();
    std::os::unix::fs::symlink(dir.join("F"), dir.join("L")).unwrap();
    std::os::unix::fs::symlink(dir.join("real"), dir.join("D")).unwrap();
    let p = |s: &str| format!("{}/{s}", dir.display());
    let cases: Vec<(String, String)> = vec![
        (p("F"), p("F")),
        (p("G.tmp"), p("G")),
        (p("G"), p("G.tmp")),
        (p("x/../F"), p("F")),
        (p("F"), p("./x/../F")),
        (p("F"), p("L")),
        (p("D/N"), p("real/N")),
        (p("D/N.tmp"), p("real/N")),
    ];
    for (out, graphs) in cases {
        for existing in [false, true] {
            for f in ["F", "G", "G.tmp", "real/N", "real/N.tmp"] {
                let _ = std::fs::remove_file(dir.join(f));
                // A link to an existing export only; a dangling link is tested on its own.
                if existing || (f == "F" && graphs.ends_with("/L")) { std::fs::write(dir.join(f), format!("sentinel {f}\n")).unwrap(); }
            }
            let before = listing(&dir);
            let (t, code) = cli("panic", &["export", "impl", "--out", &out, "--graphs", &graphs]);
            assert_eq!((t, code), (format!("program: {reason}\n{usage}"), 2), "{out} {graphs}");
            assert_eq!(listing(&dir), before, "{out} {graphs}: files untouched");
        }
    }
    // Distinct files are accepted.
    let (t, code) = cli("halves", &["export", "impl", "--out", &p("F"), "--graphs", &p("F.g")]);
    assert_eq!(code, 0, "{t}");
    let (t, code) = cli("halves", &["export", "impl", "--out", &p("x/../K"), "--graphs", &p("x/K")]);
    assert_eq!(code, 0, "{t}");
}

#[test]
fn overlap_through_a_link_to_a_new_file_is_refused() {
    // `L` points at `F`, which does not exist yet: writing either path creates the same file.
    let usage = cli("panic", &[]).0.split_once('\n').unwrap().1.to_owned();
    let reason = "--graphs must name another file than --out (and than either one's .tmp)";
    for (out, graphs) in [("L", "F"), ("F", "L")] {
        let dir = scratch();
        std::os::unix::fs::symlink(dir.join("F"), dir.join("L")).unwrap();
        let (o, g) = (dir.join(out), dir.join(graphs));
        let r = std::panic::catch_unwind(|| cli("panic", &["export", "impl", "--out", o.to_str().unwrap(),
            "--graphs", g.to_str().unwrap()]));
        assert_eq!(r.ok(), Some((format!("program: {reason}\n{usage}"), 2)), "--out {out} --graphs {graphs}");
        assert!(!dir.join("F").exists());
    }
}

/// Every file under `dir` with its bytes (symbolic links by target), sorted.
fn listing(dir: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for e in std::fs::read_dir(&d).unwrap() {
            let p = e.unwrap().path();
            let meta = std::fs::symlink_metadata(&p).unwrap();
            if meta.file_type().is_symlink() {
                out.push((p.clone(), std::fs::read_link(&p).unwrap().into_os_string().into_encoded_bytes()));
            } else if meta.is_dir() {
                stack.push(p);
            } else {
                out.push((p.clone(), std::fs::read(&p).unwrap()));
            }
        }
    }
    out.sort();
    out
}

fn ms(out: &str, key: &str) -> u64 {
    block_value(out, key).unwrap_or_else(|| panic!("no {key} in {out}")).parse().unwrap()
}

#[test]
fn store_time_is_counted_once_in_graphs_ms() {
    // `slow-explore` explores 2^7 executions of one line and renders one costly graph, so both
    // the exploration time and the store's time are large against the tolerance.
    TOSSES.store(7, Ordering::Relaxed);
    let dir = scratch();
    let _ = export("slow-explore", &dir, "w", &[], &[]);
    const REPS: usize = 7;
    let (mut plain, mut with) = (Vec::new(), Vec::new());
    for i in 0..REPS {
        let (a, ac, _, _) = export("slow-explore", &dir, &format!("p{i}"), &[], &[]);
        let (b, bc, _, st) = export("slow-explore", &dir, &format!("g{i}"), &["--graphs", "@STORE"], &[]);
        assert_eq!((ac, bc), (0, 0), "{a}\n{b}");
        assert_eq!(st.unwrap().len(), 2);
        plain.push((ms(&a, "explore_ms"), ms(&a, "summarise_ms")));
        with.push((ms(&b, "explore_ms"), ms(&b, "summarise_ms"), ms(&b, "graphs_ms")));
    }
    let min = |f: &dyn Fn(usize) -> u64| (0..REPS).map(f).min().unwrap();
    let (pe, ps) = (min(&|i| plain[i].0), min(&|i| plain[i].1));
    let (we, ws, g) = (min(&|i| with[i].0), min(&|i| with[i].1), min(&|i| with[i].2));
    let tol = 10 + pe.min(g) / 3;
    let seen = format!("plain (explore, summarise) {plain:?}; with (explore, summarise, graphs) {with:?}");
    // Printed for the failure report: the harness shows captured stdout of a failed test.
    println!("timing: tol {tol}; {seen}");
    // Both quantities must stand clear of the tolerance, or the test proves nothing.
    assert!(pe >= 2 * tol && g >= 2 * tol, "workload too small: {seen}");
    assert!(ws <= ps + tol, "the store's time is in summarise_ms: {seen}");
    assert!(we + tol >= pe, "the store's time came off explore_ms more than once: {seen}");
    assert!(we <= pe + tol, "the store's time is in explore_ms: {seen}");
}

/// Prints explore/summarise/graphs times of `slow-explore` for `WG_TOSSES` tosses. Ignored.
#[test]
#[ignore]
fn measure_slow_explore() {
    let n: usize = std::env::var("WG_TOSSES").map(|v| v.parse().unwrap()).unwrap_or(7);
    TOSSES.store(n, Ordering::Relaxed);
    let dir = scratch();
    for i in 0..3 {
        let (a, _, _, _) = export("slow-explore", &dir, &format!("p{i}"), &[], &[]);
        let (b, _, _, _) = export("slow-explore", &dir, &format!("g{i}"), &["--graphs", "@STORE"], &[]);
        eprintln!("plain e={} s={} | with e={} s={} g={}", ms(&a, "explore_ms"), ms(&a, "summarise_ms"),
            ms(&b, "explore_ms"), ms(&b, "summarise_ms"), ms(&b, "graphs_ms"));
    }
}

#[test]
fn hard_linked_paths_are_refused_before_any_run() {
    let usage = cli("panic", &[]).0.split_once('\n').unwrap().1.to_owned();
    let reason = "--graphs must name another file than --out (and than either one's .tmp)";
    // (existing file, its second name): the staging files, the targets, and across the pairs.
    for (first, second) in [("F.tmp", "G.tmp"), ("F", "G"), ("F", "G.tmp"), ("F.tmp", "G")] {
        let dir = scratch();
        std::fs::write(dir.join(first), b"sentinel\n").unwrap();
        std::fs::hard_link(dir.join(first), dir.join(second)).unwrap();
        let before = listing(&dir);
        let (o, g) = (dir.join("F"), dir.join("G"));
        let r = std::panic::catch_unwind(|| cli("panic", &["export", "impl", "--out", o.to_str().unwrap(),
            "--graphs", g.to_str().unwrap()]));
        assert_eq!(r.ok(), Some((format!("program: {reason}\n{usage}"), 2)), "{first} = {second}");
        assert_eq!(listing(&dir), before, "{first} = {second}: files untouched");
        assert_eq!(std::fs::read(dir.join(second)).unwrap(), b"sentinel\n");
    }
}

#[test]
fn a_manifest_older_than_the_binary_is_unknown() {
    let a = "0123456789abcdef0123456789abcdef";
    let text = format!("# root r\n{a}  a\n");
    let object = format!("{{\"root\":\"r\",\"files\":{{\"a\":\"{a}\"}}}}");
    for extra in [&[][..], &["--threads", "2", "--graphs-limit", "0"][..]] {
        // Older by a day, and by one second: stale.
        for age in [86400, 1] {
            let (src, err, m) = manifest_run_with(Some(text.as_bytes()), false, Some(age), extra);
            assert_eq!(src, J::Str("unknown".to_owned()), "{extra:?} {age}");
            assert_eq!(err, format!("graphs: manifest {}: older than the binary\n", m.display()),
                "{extra:?} {age}");
        }
        // Equal, and newer: used.
        for age in [0, -86400] {
            let (src, err, _) = manifest_run_with(Some(text.as_bytes()), false, Some(age), extra);
            assert_eq!((bytes(&src), err.as_str()), (object.clone(), ""), "{extra:?} {age}");
        }
        // A stale malformed manifest still gives one line.
        let (src, err, _) = manifest_run_with(Some(b"junk\n"), false, Some(86400), extra);
        assert_eq!(src, J::Str("unknown".to_owned()));
        assert_eq!(err.lines().count(), 1, "{err:?}");
    }
}

/// The `graph_store:` line of a CLI text, which must directly follow the `exported:` line.
fn summary_of(t: &str) -> String {
    let lines: Vec<&str> = t.lines().collect();
    let k = lines.iter().position(|l| l.starts_with("exported: ")).unwrap_or_else(|| panic!("{t}"));
    assert_eq!(lines.iter().filter(|l| l.starts_with("graph_store:")).count(), 1, "{t}");
    lines[k + 1].to_owned()
}

#[test]
fn the_export_prints_a_store_summary_line() {
    let dir = scratch();
    let want = |t: &str, w: &str, r: &str| {
        format!("graph_store: written={w} refused={r} ms={}", block_value(t, "graphs_ms").unwrap())
    };
    let (t, code, _, _) = export("rich", &dir, "r", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 0, "{t}");
    assert_eq!(summary_of(&t), want(&t, "6", "0"));
    let (t, _, _, _) = export("rich", &dir, "l", &["--graphs", "@STORE", "--graphs-limit", "2"], &[]);
    assert_eq!(summary_of(&t), want(&t, "2", "0"));
    let (t, code, _, _) = export("channel", &dir, "c", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 0, "{t}");
    assert_eq!(summary_of(&t), want(&t, "1", "1"));
    let (t, code, _, _) = export("halves", &dir, "p",
        &["--threads", "2", "--graphs", "@STORE", "--graphs-limit", "0"], &[]);
    assert_eq!(code, 0, "{t}");
    assert_eq!(summary_of(&t), want(&t, "0", "0"));
    // In a child process too, where the refusal goes to stderr beside the summary line.
    let bin = child_binary(&dir, "tf_child");
    let (t, err, code) = child(&bin, "channel", &["export", "impl", "--out",
        dir.join("k.jsonl").to_str().unwrap(), "--graphs", dir.join("k.g").to_str().unwrap()]);
    assert_eq!(code, 0, "{t}");
    assert_eq!(summary_of(&t), want(&t, "1", "1"));
    assert!(err.starts_with("graphs: refused "), "{err}");
    // Not without the store, nor on a refused export.
    let (t, _, _, _) = export("rich", &dir, "n", &[], &[]);
    assert!(!t.contains("graph_store:"), "{t}");
    let (t, code, _, _) = export("visible-float", &dir, "f", &["--graphs", "@STORE"], &[]);
    assert_eq!(code, 2);
    assert!(!t.contains("graph_store:"), "{t}");
}

#[test]
fn a_run_without_seed_has_one_exploration_order() {
    // Separate processes, no --seed: the stores must be byte-identical (iteration and line order
    // included). Three pairs, so that a random default seed would almost surely show.
    let dir = scratch();
    let bin = child_binary(&dir, "tf_seed");
    let run = |tag: &str, extra: &[&str]| -> (Vec<u8>, Vec<u8>) {
        let out = dir.join(format!("{tag}.jsonl"));
        let g = dir.join(format!("{tag}.g"));
        let mut args = vec!["export", "impl", "--out", out.to_str().unwrap(), "--graphs", g.to_str().unwrap()];
        args.extend(extra);
        let (t, e, c) = child(&bin, "tosses", &args);
        assert_eq!((c, e.as_str()), (0, ""), "{t}");
        (std::fs::read(&out).unwrap(), std::fs::read(&g).unwrap())
    };
    let (export0, store0) = run("a0", &[]);
    for i in 1..6 {
        let (e, s) = run(&format!("a{i}"), &[]);
        assert_eq!(e, export0, "run {i}: export");
        assert_eq!(s, store0, "run {i}: store");
    }
    // The first graph is the first execution: iterations run 1, 2, ... in store order.
    let st: Vec<String> = String::from_utf8(store0.clone()).unwrap().lines().map(str::to_owned).collect();
    assert_eq!(st.len(), 6, "an identity line and five lines (0 to 4 trues)");
    // --seed 7: the same export; a valid store of the same lines (iteration and order may differ).
    let (e7, s7) = run("s7", &["--seed", "7"]);
    assert_eq!(e7, export0, "--seed 7: export");
    let lines: Vec<String> = String::from_utf8(e7).unwrap().lines().map(str::to_owned).collect();
    let st7: Vec<String> = String::from_utf8(s7).unwrap().lines().map(str::to_owned).collect();
    assert_eq!(st7.len(), 6);
    let mut seen = std::collections::BTreeSet::new();
    let mut last = 0;
    for raw in &st7[1..] {
        let g = check_graph_line(raw, &lines[0], &lines);
        assert!(seen.insert(g["line"].as_str().unwrap().to_owned()));
        let it = g["run"]["iteration"].as_u64().unwrap();
        assert!(it > last, "first occurrences in order");
        last = it;
        assert_eq!(g["run"]["options"], serde_json::json!({"seed": 7}));
    }
    for raw in &st[1..] {
        check_graph_line(raw, &lines[0], &lines);
        assert_eq!(json(raw)["run"]["options"], serde_json::json!({}), "no seed recorded without --seed");
    }
}

// ---------------------------------------------------------------------- help --

/// The `const <name>: &str = "\` … `";` literal of a source file, unescaped (the help texts use
/// only `\` line continuations at their start).
fn source_literal(file: &str, name: &str) -> String {
    let src = std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(file)).unwrap();
    let head = format!("const {name}: &str = \"\\\n");
    let at = src.find(&head).unwrap_or_else(|| panic!("{name} in {file}")) + head.len();
    let end = at + src[at..].find("\";\n").unwrap();
    let text = &src[at..end];
    assert!(!text.contains('\\'), "{name}: only plain text is expected");
    text.to_owned()
}

/// The lines of `text` between the line `start` and the next line from `ends` (or the end).
fn section<'a>(text: &'a str, start: &str, ends: &[&str]) -> Vec<&'a str> {
    let mut on = false;
    let mut out = Vec::new();
    for l in text.lines() {
        if on && ends.iter().any(|e| l.starts_with(e)) { break; }
        if on { out.push(l); }
        if l.starts_with(start) { on = true; }
    }
    assert!(on, "section {start}");
    out
}

#[test]
fn help_lists_the_stable_and_the_experimental_surface() {
    let help = source_literal("src/program.rs", "HELP");
    let dir = scratch();
    let bin = child_binary(&dir, "tf_help");
    for arg in ["--help", "-h", "help"] {
        let (t, e, c) = child(&bin, "panic", &[arg]);
        assert_eq!((c, e.as_str()), (0, ""), "{arg}");
        assert_eq!(t, help, "{arg}: the HELP text");
    }
    let heads = ["Stable subcommands:", "Stable options:", "Exit codes", "Experimental (outputs and options may change):"];
    let subs = section(&help, heads[0], &heads[1..]).join("\n");
    let opts = section(&help, heads[1], &heads[2..]).join("\n");
    let exp = section(&help, heads[3], &[]).join("\n");
    let stable = format!("{subs}\n{opts}");
    // The stable subcommands, each a line starting with its name, and their options.
    let sub_line = |name: &str| subs.lines().find(|l| l.trim_start().starts_with(name)).map(str::to_owned)
        .unwrap_or_else(|| panic!("stable subcommand {name}"));
    let export = sub_line("export spec|impl");
    assert!(sub_line("count spec|impl").starts_with("  count"));
    assert!(export.contains("--graphs PATH") && export.contains("--out FILE"), "{export}");
    let online = subs.split("\n  online").nth(1).unwrap().split("\n  replay").next().unwrap();
    for o in ["--spec FILE", "--witness PATH", "--graphs PATH"] {
        assert!(online.contains(o), "online {o}: {online}");
    }
    assert!(sub_line("replay").contains("--graph FILE"));
    assert!(sub_line("conf").contains("--engine stateful"));
    for o in ["--model", "--seed", "--program", "--size"] {
        assert!(opts.lines().any(|l| l.trim_start().starts_with(o) || l.contains(&format!(", {o}"))), "stable option {o}");
    }
    // The experimental items, each its own line in that section, and none of them in a stable one.
    let items = ["conf --engine stateless", "conf --engine gated", "conf --engine enumerator",
        "--threads N (N > 1)", "--threshold N", "--dump-large-graph", "--audit-graphs"];
    for it in items {
        assert_eq!(exp.lines().filter(|l| l.trim_start().starts_with(it)).count(), 1, "experimental {it}: {exp}");
    }
    assert_eq!(exp.lines().filter(|l| !l.trim().is_empty()).count(), items.len(), "one line each: {exp}");
    for word in ["stateless", "gated", "enumerator", "--threads", "--threshold", "--dump-large-graph", "--audit-graphs"] {
        assert!(!stable.contains(word), "{word} is experimental, not stable");
    }
    // Nothing of the evaluation's own commands.
    let words: Vec<&str> = help.split(|c: char| !c.is_ascii_alphanumeric() && c != '-').collect();
    assert!(!words.contains(&"row") && !help.contains("EVAL"), "{help}");
}

#[test]
fn conf_join_help_lists_every_option() {
    let help = source_literal("src/bin/conf-join.rs", "HELP");
    for arg in ["--help", "-h"] {
        let out = {
            let _r = spawn_guard();
            Command::new(env!("CARGO_BIN_EXE_conf-join")).arg(arg).output().unwrap()
        };
        assert_eq!(out.status.code(), Some(0), "{arg}");
        assert!(out.stderr.is_empty(), "{arg}");
        assert_eq!(String::from_utf8(out.stdout).unwrap(), help, "{arg}");
    }
    for o in ["--merge", "--decide", "--decide-budget N", "--witness-dir D", "--impl-graphs P", "--spec-graphs Q",
              "--witness-limit N|all", "--witness-nearest N"] {
        let usage = help.split("\n\n").nth(1).unwrap();
        assert!(usage.contains(o), "usage lists {o}");
        assert!(help.lines().any(|l| l.trim_start().starts_with(o)), "a line describes {o}");
    }
    // --help is only help on its own; with files it is a usage error as before.
    let out = {
        let _r = spawn_guard();
        Command::new(env!("CARGO_BIN_EXE_conf-join")).args(["--help", "a", "b"]).output().unwrap()
    };
    assert_eq!(out.status.code(), Some(2));
    assert!(out.stdout.is_empty());
}

#[test]
fn error_usage_is_not_the_help() {
    // The error path prints the usage text on stderr-bound output with exit 2, not the help.
    let help = source_literal("src/program.rs", "HELP");
    for args in [vec![], vec!["nosuch"], vec!["--bogus"]] {
        let (t, c) = cli("panic", &args);
        assert_eq!(c, 2, "{args:?}");
        assert_ne!(t, help);
        assert!(t.lines().nth(1).is_some_and(|l| l.starts_with("usage: ")), "{args:?}: {t}");
    }
}

/// `src/<file>` as text.
fn source(file: &str) -> String {
    std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("src").join(file)).unwrap()
}

#[test]
fn help_exit_codes_are_the_ones_the_code_returns() {
    // The codes, read off the source.
    let program = source("program.rs");
    let online = source("conformance/online.rs");
    for (what, text, needle) in [
        ("conf conforms", &program, "ConfVerdict::Conforms(_) => 0,"),
        ("conf reported", &program, "ConfVerdict::Reported(_) => 1,"),
        ("conf inconclusive", &program, "ConfVerdict::Inconclusive(_) => 2,"),
        ("replay usage and refusals", &program, "let fail = |msg: String| (format!(\"{bin}: replay: {msg}\\n{usage}\\n\"), 2u8);"),
        ("replay failed run", &program, "return (format!(\"{bin}: replay failed: {e}\\n\"), 1),"),
        ("replay panic", &program, "return (format!(\"{bin}: replay failed: the program panicked: {msg}\\n\"), 1);"),
        ("replay report not written", &program, "return (format!(\"{line}{bin}: replay: {path}: {e}\\n\"), 2);"),
        ("export refused", &program, "(Err(e), _) => (format!(\"{bin}: export refused: {e}\\n\"), 2),"),
        ("online", &online, "if self.refused {\n            2\n        } else if self.end == End::Failed {\n            1\n        } else {\n            0\n        }"),
    ] {
        assert!(text.contains(needle), "{what}: the source holds {needle:?}");
    }
    // Replay: reproduced 0, a deviation 1.
    let rep = program.split("ReplayResult::Reproduced").nth(1).unwrap();
    assert!(rep.split("ReplayResult::Deviation").next().unwrap().contains("0u8,"), "reproduced is 0");
    assert!(rep.split("ReplayResult::Deviation").nth(1).unwrap().split("};").next().unwrap().contains("1u8,"), "a deviation is 1");
    // The help's section says the same.
    let help = source_literal("src/program.rs", "HELP");
    let codes = section(&help, "Exit codes", &["Experimental"]);
    let heading = help.lines().find(|l| l.starts_with("Exit codes")).unwrap();
    assert!(heading.contains("2") && heading.contains("usage error"), "{heading}");
    let line = |name: &str| codes.iter().find(|l| l.trim_start().starts_with(name)).copied()
        .unwrap_or_else(|| panic!("exit codes of {name}: {codes:?}"));
    let has = |l: &str, parts: &[&str]| parts.iter().all(|p| l.contains(p));
    let ce = line("count, export");
    assert!(has(ce, &["0", "2 refused"]) && !ce.contains(" 1 "), "{ce}");
    let on = line("online");
    assert!(has(on, &["0 a verdict", "conforms", "reports", "partial", "1 the run failed", "2 refused"]), "{on}");
    let rp = line("replay");
    assert!(has(rp, &["0 reproduced", "1 a deviation or a failed replay", "2 refused", "report not written"]), "{rp}");
    let cf = line("conf");
    assert!(has(cf, &["0 conforms", "1 reported", "2 inconclusive or refused"]), "{cf}");
    assert_eq!(codes.iter().filter(|l| !l.trim().is_empty()).count(), 4, "four command lines: {codes:?}");
}

#[test]
fn conf_join_help_says_nearest_needs_decide() {
    let help = source_literal("src/bin/conf-join.rs", "HELP");
    let lines: Vec<&str> = help.lines().collect();
    let i = lines.iter().position(|l| l.trim_start().starts_with("--witness-nearest N")).expect("the entry");
    let mut entry = vec![lines[i]];
    entry.extend(lines[i + 1..].iter().take_while(|l| l.starts_with("                    ")));
    assert!(entry.len() >= 2, "{entry:?}");
    assert!(entry[1..].join(" ").contains("--decide"), "{entry:?}");
}
