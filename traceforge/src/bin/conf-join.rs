//! `conf-join spec.jsonl impl.jsonl`: joins two summary files (the format of
//! daavar's `format/SUMMARY-FORMAT.md`) — every implementation line against the
//! specification's on TraceForge's `Set` index — and prints the verdict and the
//! uncovered lines. Exit 0 conforms or no verdict, 1 violation, 2 refused input
//! (the reason on stderr). After the report, or after a refusal, the measurement
//! block on stdout. `--merge` reads the two files as sorted streams. `--decide`
//! classifies each uncovered line as a violation (with a witness), a false alarm
//! or unresolved; the verdict and exit code stay the join's. `--witness-dir D` writes the witness graphs of the
//! uncovered lines, looked up in the exports' graph stores (`--impl-graphs P`, `--spec-graphs Q`,
//! by default `<file>.graphs.jsonl`), at most `--witness-limit N|all` of them (default 20), with
//! up to `--witness-nearest N` nearest specification graphs each (default 3).

use std::path::Path;
use std::process::ExitCode;

/// `--help`: the options, all stable.
const HELP: &str = "\
conf-join: join two summary files and report the implementation's uncovered lines.

usage: conf-join [--merge] [--decide [--decide-budget N]]
                 [--witness-dir D [--impl-graphs P] [--spec-graphs Q] [--witness-limit N|all]
                  [--witness-nearest N]]
                 spec.jsonl impl.jsonl

  --merge               read both files as sorted streams (bounded memory)
  --decide              classify each uncovered line: violation, false alarm or unresolved
  --decide-budget N     search states per line for --decide (default 10000000; implies --decide)
  --witness-dir D       write the witness graph of each uncovered line to D (D new or empty),
                        looked up in the exports' graph stores
  --impl-graphs P       the implementation's store (default: impl.jsonl.graphs.jsonl)
  --spec-graphs Q       the specification's store (default: spec.jsonl.graphs.jsonl)
  --witness-limit N|all at most N graphs (default 20)
  --witness-nearest N   at most N nearest specification graphs per line (default 3);
                        only with --decide, for the lines it finds no match for

Exit codes: 0 conforms (or no verdict), 1 a violation, 2 refused input.
";

fn main() -> ExitCode {
    let started = std::time::Instant::now();
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if matches!(args.as_slice(), [a] if a == "--help" || a == "-h") {
        print!("{HELP}");
        return ExitCode::SUCCESS;
    }
    // `--merge` reads the two files as sorted streams.
    let merge = args.iter().position(|a| a == "--merge").map(|i| args.remove(i)).is_some();
    // `--decide` classifies every uncovered line; `--decide-budget N`
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
    // `--witness-dir D` and its options (each takes one value).
    let mut take = |flag: &str| -> Result<Option<String>, String> {
        match args.iter().position(|a| a == flag) {
            None => Ok(None),
            Some(i) if i + 1 < args.len() => {
                args.remove(i);
                Ok(Some(args.remove(i)))
            }
            Some(_) => Err(format!("conf-join: {flag} takes a value")),
        }
    };
    let witness = (|| -> Result<Option<traceforge::conformance::WitnessJoinOpts>, String> {
        let dir = take("--witness-dir")?;
        let impl_graphs = take("--impl-graphs")?;
        let spec_graphs = take("--spec-graphs")?;
        let limit = take("--witness-limit")?;
        let nearest = take("--witness-nearest")?;
        let Some(dir) = dir else {
            if impl_graphs.is_some() || spec_graphs.is_some() || limit.is_some() || nearest.is_some() {
                return Err("conf-join: the witness options need --witness-dir".to_owned());
            }
            return Ok(None);
        };
        let mut o = traceforge::conformance::WitnessJoinOpts::new(dir.into());
        o.impl_graphs = impl_graphs.map(Into::into);
        o.spec_graphs = spec_graphs.map(Into::into);
        o.merge = merge;
        if let Some(l) = limit {
            o.limit = match l.as_str() {
                "all" => None,
                n => Some(n.parse().map_err(|_| "conf-join: --witness-limit takes N or all".to_owned())?),
            };
        }
        if let Some(n) = nearest {
            o.nearest = n.parse().map_err(|_| "conf-join: --witness-nearest takes N".to_owned())?;
        }
        Ok(Some(o))
    })();
    let witness = match witness {
        Ok(w) => w,
        Err(e) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let [spec, imp] = args.as_slice() else {
        // The usage line is unchanged; the witness options are listed in this file's header.
        eprintln!(
            "usage: conf-join [--merge] [--decide [--decide-budget N]] spec.jsonl impl.jsonl"
        );
        return ExitCode::from(2);
    };
    let (spec, imp) = (Path::new(spec), Path::new(imp));
    // The witness directory must not exist or be empty: checked before the join runs.
    if let Some(o) = &witness {
        if let Err(e) = traceforge::conformance::check_witness_dir(&o.dir) {
            eprintln!("conf-join: refused: {e}");
            print!(
                "{}",
                traceforge::conformance::JoinReport::refused_measurements(started.elapsed().as_millis())
            );
            return ExitCode::from(2);
        }
    }
    let joined = match (merge, decide) {
        (true, false) => traceforge::conformance::conf_join_merge(spec, imp),
        (false, false) => traceforge::conformance::conf_join(spec, imp),
        (true, true) => traceforge::conformance::conf_join_merge_decide(spec, imp, budget),
        (false, true) => traceforge::conformance::conf_join_decide(spec, imp, budget),
    };
    // `--witness-dir`: the graphs, after the join; an unusable store refuses the run.
    let joined = match (joined, &witness) {
        (Ok(mut report), Some(o)) => {
            traceforge::conformance::write_join_witnesses(&mut report, spec, imp, o).map(|()| report)
        }
        (r, _) => r,
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
