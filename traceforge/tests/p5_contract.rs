//! Contract refusals through the public CLI and the conf-join executable.
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use traceforge::program::{run_cli, Entry, Program};

fn scratch() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let p = std::env::temp_dir().join(format!(
        "tf-p5-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&p).unwrap();
    p
}

fn header(model: &str) -> String {
    format!(
        "{{\"format\":1,\"tool\":\"test\",\"program\":\"p\",\"size\":\"\",\
         \"visible\":[],\"model\":\"{model}\",\"enumeration\":\"complete\",\"encoding\":1}}\n"
    )
}

fn join(spec: &Path, imp: &Path, flags: &[&str]) -> std::process::Output {
    std::process::Command::new(env!("CARGO_BIN_EXE_conf-join"))
        .args(flags).arg(spec).arg(imp).output().unwrap()
}

fn cli(names: &[String], body: Entry, args: &[&str]) -> (String, u8) {
    run_cli(
        &Program {
            visible: &|_| names.to_vec(),
            spec: &|_| Arc::clone(&body),
            imp: &|_| Arc::clone(&body),
        },
        &args.iter().map(|s| s.to_string()).collect::<Vec<_>>(),
    )
}

#[test]
fn model_joins() {
    let dir = scratch();
    let spec = dir.join("s");
    let imp = dir.join("i");
    std::fs::write(&spec, header("p2p")).unwrap();
    for flags in [vec![], vec!["--merge"], vec!["--decide"], vec!["--merge", "--decide"]] {
        std::fs::write(&imp, header("asyn")).unwrap();
        let out = join(&spec, &imp, &flags);
        assert_eq!(out.status.code(), Some(2), "conformance: model exit");
        assert_eq!(String::from_utf8(out.stderr).unwrap(),
            "conf-join: refused: the two models differ: p2p and asyn\n",
            "conformance: model diagnostic");
        std::fs::write(&imp, header("p2p")).unwrap();
        assert_eq!(join(&spec, &imp, &flags).status.code(), Some(0),
            "conformance: same model");
    }
}

#[test]
fn model_online() {
    let dir = scratch();
    let spec = dir.join("s");
    for threads in ["1", "2"] {
        std::fs::write(&spec, header("asyn")).unwrap();
        let args = ["online", "--spec", spec.to_str().unwrap(), "--threads", threads];
        let (text, code) = cli(&[], Arc::new(|| {}), &args);
        assert_eq!(code, 2, "conformance: online model exit");
        assert_eq!(text.lines().next().unwrap(),
            "program: online refused: the two models differ: asyn and p2p",
            "conformance: online model diagnostic");
        std::fs::write(&spec, header("p2p")).unwrap();
        assert_eq!(cli(&[], Arc::new(|| {}), &args).1, 0,
            "conformance: online same model");
    }
}
