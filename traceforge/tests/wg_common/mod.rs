//! Helpers shared by the witness CLI tests (join, replay): scratch directories, child
//! processes of a test binary, and a JSON reader that keeps key order.
#![allow(dead_code)]

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use serde_json::Value;

pub fn scratch() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let p = std::env::temp_dir().join(format!(
        "tf-wgraphs-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = std::fs::remove_dir_all(&p);
    std::fs::create_dir_all(&p).unwrap();
    p
}

pub fn named<F: FnOnce() + Send + 'static>(name: &str, f: F) -> traceforge::thread::JoinHandle<()> {
    traceforge::thread::Builder::new().name(name.to_owned()).spawn(f).unwrap()
}

pub fn me() -> traceforge::thread::ThreadId {
    traceforge::thread::current().id()
}

/// The programs under test, by name (the child process selects one by name).
/// Orders writing a copied binary against starting processes. While a copy is open for
/// writing, a process forked by another test inherits the descriptor until it executes, and
/// executing the copy in that window fails with "Text file busy". Copies take the write side;
/// every process start in this file takes the read side.
pub static SPAWN: std::sync::RwLock<()> = std::sync::RwLock::new(());

pub fn spawn_guard() -> std::sync::RwLockReadGuard<'static, ()> {
    SPAWN.read().unwrap_or_else(|e| e.into_inner())
}

/// A hard link of this test binary at `dir/<file>`, or a copy where links are not possible
/// (another file system, or a sandbox that forbids them). One per test, so that each test's
/// manifest beside it is its own.
pub fn child_binary(dir: &Path, file: &str) -> PathBuf {
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
pub fn child(bin: &Path, name: &str, args: &[&str]) -> (String, String, i32) {
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

pub fn read_lines(p: &Path) -> Vec<String> {
    std::fs::read_to_string(p).unwrap().lines().map(str::to_owned).collect()
}

pub fn json(s: &str) -> Value {
    serde_json::from_str(s).unwrap()
}

/// A JSON value that keeps its object keys in file order.
#[derive(Clone, Debug, PartialEq)]
pub enum J { Null, Bool(bool), Num(String), Str(String), Arr(Vec<J>), Obj(Vec<(String, J)>) }

impl J {
    pub fn get(&self, k: &str) -> &J {
        match self {
            J::Obj(m) => &m.iter().find(|(x, _)| x == k).unwrap_or_else(|| panic!("no key {k}")).1,
            _ => panic!("not an object"),
        }
    }
    pub fn at(&self, i: usize) -> &J {
        match self { J::Arr(xs) => &xs[i], _ => panic!("not an array") }
    }
    pub fn keys(&self) -> Vec<&str> {
        match self { J::Obj(m) => m.iter().map(|(k, _)| k.as_str()).collect(), _ => vec![] }
    }
}

/// Parses JSON text, keeping key order (enough for the producer's output).
pub fn parse(s: &str) -> J {
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
pub fn bytes(v: &J) -> String {
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
pub fn block(out: &str) -> Vec<(String, String)> {
    let Some((_, b)) = out.split_once("--- measurements\n") else { return vec![] };
    b.lines().filter_map(|l| l.split_once(": ")).map(|(k, v)| (k.to_owned(), v.to_owned())).collect()
}

pub fn block_value(out: &str, key: &str) -> Option<String> {
    block(out).into_iter().find(|(k, _)| k == key).map(|(_, v)| v)
}

/// `tool_commit` as the build should have fixed it: `WG_EXPECT_COMMIT` when the build was given
/// `TRACEFORGE_COMMIT` (set both to the same value), else this checkout's git state.
pub fn expected_commit() -> String {
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

pub fn this_entry() -> String {
    Path::new(&std::env::args_os().next().unwrap()).file_name().unwrap().to_string_lossy().into_owned()
}

