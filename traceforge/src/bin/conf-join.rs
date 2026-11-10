//! `conf-join spec.jsonl impl.jsonl` (`J3`): joins two compact summary files of
//! `plan/jmc-must/SUMMARY-FORMAT.md` — every implementation line against the
//! specification's on TraceForge's `Set` index — and prints the verdict and the
//! uncovered lines. Exit 0 conforms or no verdict, 1 violation, 2 refused input
//! (the reason on stderr). `B`: after the report, or after a refusal, the
//! measurement block on stdout. `DECIDE`: `--decide` classifies each uncovered
//! line as a violation (with a witness), a false alarm or unresolved; the
//! verdict and exit code stay the join's.

use std::path::Path;
use std::process::ExitCode;

fn main() -> ExitCode {
    let started = std::time::Instant::now();
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    // `SORTED-JOIN`: `--merge` reads the two files as sorted streams.
    let merge = args.iter().position(|a| a == "--merge").map(|i| args.remove(i)).is_some();
    // `DECIDE`: `--decide` classifies every uncovered line; `--decide-budget N`
    // bounds the search states per line (implies `--decide`).
    let mut decide = args.iter().position(|a| a == "--decide").map(|i| args.remove(i)).is_some();
    let mut budget = traceforge::conformance::DEFAULT_DECIDE_BUDGET;
    if let Some(i) = args.iter().position(|a| a == "--decide-budget") {
        args.remove(i);
        match (i < args.len()).then(|| args.remove(i).parse::<u64>()) {
            Some(Ok(n)) => budget = n,
            _ => {
                eprintln!("conf-join: --decide-budget takes a non-negative integer");
                return ExitCode::from(2);
            }
        }
        decide = true;
    }
    let [spec, imp] = args.as_slice() else {
        eprintln!(
            "usage: conf-join [--merge] [--decide [--decide-budget N]] spec.jsonl impl.jsonl"
        );
        return ExitCode::from(2);
    };
    let (spec, imp) = (Path::new(spec), Path::new(imp));
    let joined = match (merge, decide) {
        (true, false) => traceforge::conformance::conf_join_merge(spec, imp),
        (false, false) => traceforge::conformance::conf_join(spec, imp),
        (true, true) => traceforge::conformance::conf_join_merge_decide(spec, imp, budget),
        (false, true) => traceforge::conformance::conf_join_decide(spec, imp, budget),
    };
    match joined {
        Ok(report) => {
            print!("{}", report.render());
            print!("{}", report.measurements(started.elapsed().as_millis()));
            ExitCode::from(report.exit_code())
        }
        Err(e) => {
            eprintln!("conf-join: refused: {e}");
            print!(
                "{}",
                traceforge::conformance::JoinReport::refused_measurements(
                    started.elapsed().as_millis()
                )
            );
            ExitCode::from(2)
        }
    }
}
