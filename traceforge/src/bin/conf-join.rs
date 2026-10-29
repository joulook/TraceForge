//! `conf-join spec.jsonl impl.jsonl` (`J3`): joins two compact summary files of
//! `plan/jmc-must/SUMMARY-FORMAT.md` — every implementation line against the
//! specification's on TraceForge's `Set` index — and prints the verdict and the
//! uncovered lines. Exit 0 conforms or no verdict, 1 violation, 2 refused input
//! (the reason on stderr).

use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let [spec, imp] = args.as_slice() else {
        eprintln!("usage: conf-join spec.jsonl impl.jsonl");
        return ExitCode::from(2);
    };
    match traceforge::conformance::conf_join(Path::new(spec), Path::new(imp)) {
        Ok(report) => {
            print!("{}", report.render());
            ExitCode::from(report.exit_code())
        }
        Err(e) => {
            eprintln!("conf-join: refused: {e}");
            ExitCode::from(2)
        }
    }
}
