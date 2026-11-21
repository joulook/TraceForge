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
//! Before any join, the pairing check (`traceforge::conformance::check_pairing`)
//! verifies the restrictions a meaningful comparison needs; a failure refuses the
//! join (exit 2, the failed checks on stderr) unless `--no-pairing-check`.
//! `--check-pairing` runs only that check and prints its result on stdout.

use std::path::Path;
use std::process::ExitCode;

/// `--help`: the options, all stable.
const HELP: &str = "\
conf-join: join two summary files and report the implementation's uncovered lines.

usage: conf-join [--merge] [--decide [--decide-budget N]] [--no-pairing-check]
                 [--witness-dir D [--impl-graphs P] [--spec-graphs Q] [--witness-limit N|all]
                  [--witness-nearest N]]
                 spec.jsonl impl.jsonl
       conf-join --check-pairing [--merge] [--decide] spec.jsonl impl.jsonl

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
  --no-pairing-check    skip the pairing check that runs before every join
  --check-pairing       run only the pairing check and print one line per failed or
                        warned check, with its contract row (C2, C3, C4, C6, C10, C13,
                        C18), then `pairing: ok` or `pairing: failed (K checks)`

Exit codes: 0 conforms (or no verdict), 1 a violation, 2 refused input or a failed
pairing check. --check-pairing: 0 passed, 2 failed or unreadable input.
";

fn main() -> ExitCode {
    let started = std::time::Instant::now();
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if matches!(args.as_slice(), [a] if a == "--help" || a == "-h") {
        print!("{HELP}");
        return ExitCode::SUCCESS;
    }
    // `--check-pairing` runs only the pairing check; `--no-pairing-check`
    // skips it before the join.
    let check_only = args.iter().position(|a| a == "--check-pairing").map(|i| args.remove(i)).is_some();
    let no_check = args.iter().position(|a| a == "--no-pairing-check").map(|i| args.remove(i)).is_some();
    // `--merge` reads the two files as sorted streams.
    let merge = args.iter().position(|a| a == "--merge").map(|i| args.remove(i)).is_some();
    // `--decide` classifies every uncovered line; `--decide-budget N`
    // bounds the search states per line (implies `--decide`).
    let mut decide = args.iter().position(|a| a == "--decide").map(|i| args.remove(i)).is_some();
    let mut budget = traceforge::conformance::DEFAULT_DECIDE_BUDGET;
    let mut budget_given = false;
    if let Some(i) = args.iter().position(|a| a == "--decide-budget") {
        budget_given = true;
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
    let pairing_opts = traceforge::conformance::PairingOpts { merge, decide };
    if check_only {
        if no_check || budget_given || witness.is_some() {
            eprintln!("conf-join: --check-pairing takes only --merge and --decide");
            return ExitCode::from(2);
        }
        return match traceforge::conformance::check_pairing(spec, imp, pairing_opts) {
            Ok(r) => {
                print!("{}", r.render());
                ExitCode::from(if r.passed() { 0 } else { 2 })
            }
            Err(e) => {
                eprintln!("conf-join: refused: {e}");
                ExitCode::from(2)
            }
        };
    }
    // The pairing check, before anything is compared: failures refuse the join,
    // warnings go to stderr. Without `decide`: Decide itself refuses a count
    // above 65535 in a line it classifies, so that warning would only repeat it.
    if !no_check {
        let opts = traceforge::conformance::PairingOpts { decide: false, ..pairing_opts };
        match traceforge::conformance::check_pairing(spec, imp, opts) {
            Ok(r) if r.passed() => {
                for w in &r.warnings {
                    eprintln!("conf-join: pairing: warning: {}: {}", w.row, w.what);
                }
            }
            Ok(r) => {
                for f in &r.failures {
                    eprintln!("conf-join: pairing: {}: {}", f.row, f.what);
                }
                eprintln!(
                    "conf-join: refused: the pairing check failed ({} checks; --no-pairing-check skips it)",
                    r.failures.len()
                );
                print!(
                    "{}",
                    traceforge::conformance::JoinReport::refused_measurements(started.elapsed().as_millis())
                );
                return ExitCode::from(2);
            }
            Err(e) => {
                eprintln!("conf-join: refused: {e}");
                print!(
                    "{}",
                    traceforge::conformance::JoinReport::refused_measurements(started.elapsed().as_millis())
                );
                return ExitCode::from(2);
            }
        }
    }
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
