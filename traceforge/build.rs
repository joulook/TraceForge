//! Build-time identity of this TraceForge build, for the witness graphs' `run.tool_commit`.
//!
//! `TRACEFORGE_COMMIT` from the environment if set and non-empty (node trees made by
//! `git archive` have no `.git`; their drivers set it from the pin file); otherwise
//! `git rev-parse HEAD` in this crate's directory, with `-dirty` when `git status --porcelain`
//! prints anything; otherwise `unknown`.

use std::path::Path;
use std::process::Command;

fn git(dir: &Path, args: &[&str]) -> Option<String> {
    let out = Command::new("git").arg("-C").arg(dir).args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8(out.stdout).ok()?.trim_end().to_owned())
}

fn main() {
    println!("cargo:rerun-if-env-changed=TRACEFORGE_COMMIT");
    let dir = std::env::var("CARGO_MANIFEST_DIR").expect("cargo sets CARGO_MANIFEST_DIR");
    let dir = Path::new(&dir);
    let commit = match std::env::var("TRACEFORGE_COMMIT") {
        Ok(c) if !c.trim().is_empty() => c.trim().to_owned(),
        _ => match git(dir, &["rev-parse", "HEAD"]) {
            Some(head) if !head.is_empty() => {
                // Rebuild when HEAD moves, the branch it names moves (a commit, a reset) or the
                // index changes (an add).
                let mut watched = vec!["HEAD".to_owned(), "index".to_owned(), "packed-refs".to_owned()];
                if let Some(r) = git(dir, &["symbolic-ref", "-q", "HEAD"]) {
                    watched.push(r);
                }
                for p in &watched {
                    if let Some(path) = git(dir, &["rev-parse", "--git-path", p.as_str()]) {
                        let path = dir.join(path);
                        println!("cargo:rerun-if-changed={}", path.display());
                    }
                }
                // A working-tree edit of what this library is built from also changes the `-dirty`
                // mark: its sources, its manifest, the macros crate and the workspace manifest.
                for p in ["src", "Cargo.toml", "../traceforge-macros", "../Cargo.toml"] {
                    println!("cargo:rerun-if-changed={p}");
                }
                let dirty = git(dir, &["status", "--porcelain"]).is_some_and(|s| !s.is_empty());
                if dirty {
                    format!("{head}-dirty")
                } else {
                    head
                }
            }
            _ => "unknown".to_owned(),
        },
    };
    println!("cargo:rustc-env=TRACEFORGE_TOOL_COMMIT={commit}");
}
