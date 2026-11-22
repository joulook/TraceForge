//! The shared main of a TraceForge benchmark binary: a specification program
//! and an implementation program, checked against each other.
//!
//! A program names only what is inherent to it — its visible threads and its
//! specification and implementation entry points, each built from the
//! program's own arguments — and gets the same subcommands as every other
//! program: `count`, `export`, `online`, `replay` and `conf`, listed with their
//! options and exit codes by `<bin> --help` (the `HELP` text, which also marks
//! the experimental engines and options).
//!
//! `ARGS` are everything after the options (or after `--`), passed verbatim to
//! the program's entry points: a program's size and variant reach it only this
//! way. `count` prints `execs=<c> blocked=<b>`; `export` writes the summary file
//! (daavar's `format/SUMMARY-FORMAT.md`) through [`crate::conformance::export`],
//! the generic encoder with no per-program code; `conf` runs
//! [`crate::conformance::verify`] and prints its verdict. A usage error exits 2.
//!
//! With the `eval` feature, `row` runs one evaluation row: it reads the row's
//! JSON from `EVAL_ROW` (label, tier, rep, run kind, family, knobs, `k`, variant,
//! twin key and the row's name, which is copied into the record and never
//! resolved) and the commit from `EVAL_COMMIT`, runs the row's engine on the
//! program's entry points built from `ARGS`, and prints `EVALROW\t` and the
//! schema-8 record (after the split line on an `Explore` row); exit 0 with a
//! record (also when the engine panicked, `end_class=panicked`), 2 without one.
//! Its options are `--model`, `--seed` (required), `--threshold` and
//! `--dump-large-graph`.
//!
//! **The default model**: without `--model`, a run uses the program's own
//! default, declared through [`main_with_model`]; [`main`] declares `fifo`. So
//! leaving out `--model` never changes the meaning of a benchmark.

use std::path::Path;
use std::process::ExitCode;
use std::sync::Arc;

use crate::conformance::config::IndexKind;
use crate::conformance::export_p;
use crate::conformance::interchange::{self, ExportError};
use crate::conformance::measure;
use crate::conformance::online::{self, Mode, OnlineOpts, OnlineOut};
use crate::conformance::online_p;
#[cfg(feature = "eval")]
use crate::conformance::record::{self, Subject};
use crate::conformance::witness_graph;
use crate::conformance::{self, ConfBuilder, ConfVerdict, Engine, ExportHeader};
use crate::{Config, ConsType};

/// One entry point of a program, ready to run.
pub type Entry = Arc<dyn Fn() + Send + Sync>;

/// What a program names: nothing but what is inherent to it.
pub struct Program<'a> {
    /// The visible threads, by name, from the program's arguments (a
    /// program's thread set may depend on its size, e.g. `c0 … c{k-1}`).
    pub visible: &'a dyn Fn(&[String]) -> Vec<String>,
    /// The specification's entry point, built from the program's arguments.
    pub spec: &'a dyn Fn(&[String]) -> Entry,
    /// The implementation's entry point, built from the program's arguments.
    pub imp: &'a dyn Fn(&[String]) -> Entry,
}

/// The program's `main`: reads `std::env::args`, runs the subcommand, prints
/// its output (on stderr when it exits 2) and returns its exit code.
pub fn main(p: Program) -> ExitCode {
    main_with_model(p, ConsType::FIFO)
}

/// [`main`] for a program whose default model is `default_model`: the one its
/// README names, used when a run leaves out `--model`.
pub fn main_with_model(p: Program, default_model: ConsType) -> ExitCode {
    main_with_payload_names(p, default_model, &|_| Vec::new())
}

/// As [`main_with_model`], declaring invisible payload-nameable threads for both sides.
/// The original three-field [`Program`] literal remains unchanged.
pub fn main_with_payload_names(
    p: Program, default_model: ConsType, payload_names: &dyn Fn(&[String]) -> Vec<String>,
) -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let bin = args
        .first()
        .and_then(|a| Path::new(a).file_name())
        .and_then(|n| n.to_str())
        .unwrap_or("program")
        .to_string();
    let mut block = String::new();
    let rest = args.get(1..).unwrap_or(&[]);
    let (out, code) = run_named_roles(&p, &bin, rest, default_model, &mut block, payload_names);
    if code == 2 {
        eprint!("{out}");
    } else {
        print!("{out}");
    }
    // `B` (MEAS-0.2): the measurement block, after the run's own output, on
    // stdout whatever the exit code.
    print!("{block}");
    ExitCode::from(code)
}

/// The same as [`main`] on given arguments (without the binary's name), for
/// tests: the text it would print and the exit code.
pub fn run_cli(p: &Program, args: &[String]) -> (String, u8) {
    run_cli_with_model(p, ConsType::FIFO, args)
}

/// [`run_cli`] for a program whose default model is `default_model`.
pub fn run_cli_with_model(p: &Program, default_model: ConsType, args: &[String]) -> (String, u8) {
    let mut block = String::new();
    let (out, code) = run_named(p, "program", args, default_model, &mut block);
    (format!("{out}{block}"), code)
}

/// [`run_cli_with_model`] with the shared payload-nameable declaration.
pub fn run_cli_with_payload_names(
    p: &Program, default_model: ConsType, args: &[String],
    payload_names: &dyn Fn(&[String]) -> Vec<String>,
) -> (String, u8) {
    let mut block = String::new();
    let (out, code) = run_named_roles(
        p, "program", args, default_model, &mut block, payload_names,
    );
    (format!("{out}{block}"), code)
}

/// The error usage text, with `row`'s line (`$row`) when the `eval` feature is on.
macro_rules! usage_text {
    ($row:literal) => {
        concat!(
            "usage: <bin> count spec|impl [--threads N] [options] [ARGS…]\n       \
    <bin> export spec|impl --out FILE [--threads N] [options] [ARGS…]\n       \
    <bin> conf [--engine stateful|stateless|gated|enumerator] [--threads N] \
    [--stop-at-first] [--distinct] [options] [ARGS…]\n\
    options: --model fifo|bag|causal (default: the program's), --seed N, --threshold N, \
    --dump-large-graph, --program S, --size S; \
    `--` ends the options\n       \
",
            $row,
            "<bin> online --spec FILE [--threads N] [--stop-at-first] [--out FILE [--program S] [--size S]] \
    [--no-pairing-check] [--budget N] [--model …] [--seed N] [--threshold N] [--dump-large-graph] [ARGS…]\n\
    \n--audit-graphs (export or online, any thread count): exact canonical graph audit.\n\
    Retains graphs; diagnostic only, not for timed rows.\n\
    \n--witness PATH (online or conf --engine stateful, --threads 1): write the first\n\
    uncovered execution to a file, or one per distinct summary to PATH ending in /.\n\
    Witnesses publish at run end; refusal discards staging and preserves existing files.\n\
    Unnamed threads, control characters in names/messages, and write errors stop the run\n\
    (online exit 1; conf exit 2). Online declaration refusals exit 2.\n\
    Positions count printed events; iterations count completions.\n"
        )
    };
}

#[cfg(feature = "eval")]
const USAGE: &str = usage_text!(
    "<bin> row [--model fifo|bag|causal] --seed N [--threshold N] [--dump-large-graph] -- ARGS   \
    (EVAL_ROW, EVAL_COMMIT)\n       "
);
#[cfg(not(feature = "eval"))]
const USAGE: &str = usage_text!("");

/// `--help`: the stable subcommands and options, then the experimental ones.
const HELP: &str = "\
A TraceForge benchmark binary: a specification program and an implementation program,
explored by TraceForge and compared through summary files.

usage: <bin> <subcommand> [options] [-- ARGS]
ARGS are passed to the program's entry points (its size, variant or reading).

Stable subcommands:
  count spec|impl [--model M] [--seed N] [-- ARGS]
      Explore one side and print its execution counts.
  export spec|impl --out FILE [--program S] [--size S] [--graphs PATH [--graphs-limit N]]
         [--model M] [--seed N] [-- ARGS]
      Write the side's summary file; with --graphs, also its witness graph store
      (one graph per summary line; --graphs-limit N keeps the first N).
  online --spec FILE [--out FILE [--program S] [--size S] [--graphs PATH [--graphs-limit N]]]
         [--witness PATH] [--stop-at-first] [--budget N] [--no-pairing-check] [--model M]
         [--seed N] [-- ARGS]
      Explore the implementation and look every execution up in the specification's
      summary file. --witness writes the first uncovered execution (one per summary if
      PATH ends in /); --out and --graphs write its summary file and graph store.
      Before the run, the file is checked against the program as the pairing check of
      the join checks two files, except that C3 only compares the models (cd included)
      and C13 is not checked; a failure refuses the run, and --no-pairing-check skips it.
  replay --graph FILE [--report FILE] [--allow-source-change] [--allow-tool-change] [-- ARGS]
      Re-run the program once along a witness graph; exit 0 reproduced, 1 a deviation.
  conf [--engine stateful] [--witness PATH] [--stop-at-first] [--distinct] [--model M]
       [--seed N] [-- ARGS]
      Check the implementation against the specification in one process.

Stable options:
  --model fifo|bag|causal   the communication model (default: the program's);
                            p2p, asyn and cd are aliases of fifo, bag and causal
  --seed N                  the exploration's seed (default 0; it fixes the order)
  --program S, --size S     the summary file header's program and size

Exit codes (2 is also every usage error):
  count, export   0 done, 2 refused.
  online          0 a verdict (conforms, reports or partial, as printed), 1 the run failed, 2 refused.
  replay          0 reproduced, 1 a deviation or a failed replay, 2 refused or the report not written.
  conf            0 conforms, 1 reported, 2 inconclusive or refused.

Experimental (outputs and options may change):
  conf --engine stateless   the complete-first checker: sweeps the specification per completion.
  conf --engine gated       the gated checker, which re-tests a witness at every visible event.
  conf --engine enumerator  the directed enumerator, which probes the specification as it goes.
  --threads N (N > 1)       parallel exploration of count, export, online and conf.
  --threshold N             stop the run when a thread exceeds N events (default 1000).
  --dump-large-graph        print the graph when a thread exceeds the threshold.
  --audit-graphs            check that every completion is a distinct graph (export, online).
";

/// The options of every subcommand, and the program's own arguments.
struct Opts {
    model: ConsType,
    seed: Option<u64>,
    threshold: Option<u32>,
    dump_large_graph: bool,
    engine: String,
    threads: usize,
    stop_at_first: bool,
    distinct: bool,
    out: Option<String>,
    witness: Option<String>,
    /// `--graphs PATH`: the graph store beside an export.
    graphs: Option<String>,
    /// `--graphs-limit N`.
    graphs_limit: Option<usize>,
    graph_audit: crate::conformance::graph_audit::OptionalAudit,
    program: Option<String>,
    size: Option<String>,
    spec: Option<String>,
    /// `online --no-pairing-check`: skip the pairing check before the run.
    no_pairing_check: bool,
    budget: Option<u64>,
    args: Vec<String>,
}

fn parse_opts(args: &[String], default_model: ConsType) -> Result<Opts, String> {
    let mut o = Opts {
        model: default_model,
        seed: None,
        threshold: None,
        dump_large_graph: false,
        engine: "stateful".to_string(),
        threads: 1,
        stop_at_first: false,
        distinct: false,
        out: None,
        witness: None,
        graphs: None,
        graphs_limit: None,
        graph_audit: None,
        program: None,
        size: None,
        spec: None,
        no_pairing_check: false,
        budget: None,
        args: Vec::new(),
    };
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let mut value = || -> Result<String, String> {
            i += 1;
            args.get(i)
                .cloned()
                .ok_or_else(|| format!("{a} needs a value"))
        };
        match a {
            "--" => {
                o.args = args[i + 1..].to_vec();
                return Ok(o);
            }
            "--model" => {
                o.model = match value()?.as_str() {
                    // The summary format's names (p2p, asyn, cd) are aliases.
                    "fifo" | "p2p" => ConsType::FIFO,
                    "bag" | "asyn" => ConsType::Bag,
                    "causal" | "cd" => ConsType::Causal,
                    m => {
                        return Err(format!(
                            "unknown model `{m}`: fifo, bag or causal (or p2p, asyn, cd)"
                        ))
                    }
                }
            }
            "--seed" => o.seed = Some(value()?.parse().map_err(|_| "--seed needs a number")?),
            "--threshold" => {
                o.threshold = Some(value()?.parse().map_err(|_| "--threshold needs a number")?)
            }
            "--dump-large-graph" => o.dump_large_graph = true,
            "--engine" => o.engine = value()?,
            "--threads" => {
                o.threads = value()?.parse().map_err(|_| "--threads needs a number")?;
                if o.threads == 0 {
                    return Err("--threads needs at least 1".to_string());
                }
            }
            "--stop-at-first" => o.stop_at_first = true,
            "--distinct" => o.distinct = true,
            "--audit-graphs" => {
                o.graph_audit = Some(Default::default());
            }
            "--witness" => o.witness = Some(value()?),
            "--graphs" => o.graphs = Some(value()?),
            "--graphs-limit" => {
                o.graphs_limit =
                    Some(value()?.parse().map_err(|_| "--graphs-limit needs a number")?)
            }
            "--out" => o.out = Some(value()?),
            "--program" => o.program = Some(value()?),
            "--size" => o.size = Some(value()?),
            "--spec" => o.spec = Some(value()?),
            "--no-pairing-check" => o.no_pairing_check = true,
            "--budget" => {
                let b: u64 = value()?.parse().map_err(|_| "--budget needs a number")?;
                if b == 0 {
                    return Err("--budget needs at least 1".to_string());
                }
                o.budget = Some(b);
            }
            _ if a.starts_with("--") => return Err(format!("unknown option `{a}`")),
            _ => {
                o.args = args[i..].to_vec();
                return Ok(o);
            }
        }
        i += 1;
    }
    Ok(o)
}

fn check_witness(cmd: &str, o: &Opts) -> Result<(), String> {
    if o.no_pairing_check && cmd != "online" {
        return Err("--no-pairing-check requires online".to_owned());
    }
    if o.graph_audit.is_some() && !matches!(cmd, "export" | "online") {
        return Err("--audit-graphs requires export or online; not for timed rows".to_owned());
    }
    if o.graphs_limit.is_some() && o.graphs.is_none() {
        return Err("--graphs-limit requires --graphs".to_owned());
    }
    if o.graphs.is_some() && !matches!(cmd, "export" | "online") {
        return Err("--graphs requires export".to_owned());
    }
    if o.graphs.is_some() && cmd == "online" && o.out.is_none() {
        return Err("--graphs with online requires --out".to_owned());
    }
    if o.graphs.is_some() && o.threads > 1 && o.graphs_limit != Some(0) {
        return Err("--graphs with --threads N>1 requires --graphs-limit 0".to_owned());
    }
    if o.witness.is_none() {
        return Ok(());
    }
    if !matches!(cmd, "online" | "conf") {
        return Err("--witness requires online or conf --engine stateful".to_owned());
    }
    if o.threads > 1 {
        return Err("--witness requires --threads 1".to_owned());
    }
    if cmd == "conf" && o.engine != "stateful" {
        return Err("--witness requires conf --engine stateful".to_owned());
    }
    Ok(())
}

/// Whether an export at `out` and a graph store at `graphs` would share a file: either path, or
/// the `.tmp` staging file of either, names the same file as one of the other's. Paths are made
/// absolute; an existing file, or the directory of a new one, is resolved through symbolic links,
/// and existing files are also compared by their filesystem identity (hard links).
fn overlapping_paths(out: &Path, graphs: &Path) -> bool {
    fn with_tmp(p: &Path) -> [std::path::PathBuf; 2] {
        let mut t = p.as_os_str().to_owned();
        t.push(".tmp");
        [p.to_path_buf(), t.into()]
    }
    fn resolved(p: &Path) -> std::path::PathBuf {
        let mut abs = std::path::absolute(p).unwrap_or_else(|_| p.to_path_buf());
        // A link whose target does not exist yet still names that target: follow it by hand
        // (a bounded number of times, against loops) before resolving the rest.
        for _ in 0..40 {
            if let Ok(c) = std::fs::canonicalize(&abs) {
                return c;
            }
            match std::fs::read_link(&abs) {
                Ok(target) => {
                    let base = abs.parent().map(Path::to_path_buf).unwrap_or_default();
                    abs = std::path::absolute(base.join(target)).unwrap_or_else(|_| abs.clone());
                }
                Err(_) => break,
            }
        }
        match (abs.parent(), abs.file_name()) {
            (Some(dir), Some(name)) => {
                std::fs::canonicalize(dir).map(|d| d.join(name)).unwrap_or(abs.clone())
            }
            _ => abs,
        }
    }
    let a: Vec<_> = with_tmp(out).iter().map(|p| resolved(p)).collect();
    let b: Vec<_> = with_tmp(graphs).iter().map(|p| resolved(p)).collect();
    if a.iter().any(|x| b.contains(x)) {
        return true;
    }
    // Hard links: two existing paths of the one file have different names but one identity.
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let id = |p: &std::path::PathBuf| std::fs::metadata(p).ok().map(|m| (m.dev(), m.ino()));
        let a: Vec<_> = a.iter().filter_map(id).collect();
        let b: Vec<_> = b.iter().filter_map(id).collect();
        if a.iter().any(|x| b.contains(x)) {
            return true;
        }
    }
    false
}

/// `replay --graph FILE [--report FILE] [--allow-source-change] [--allow-tool-change] [-- ARGS]`:
/// one guided execution of this program along a witness graph. Exit 0 reproduced, 1 a deviation,
/// 2 refused (before running) or bad arguments.
fn replay_command(p: &Program, bin: &str, args: &[String], block: &mut String) -> (String, u8) {
    let started = std::time::Instant::now();
    let usage = "usage: <bin> replay --graph FILE [--report FILE] [--allow-source-change] \
                 [--allow-tool-change] [-- ARGS]";
    let fail = |msg: String| (format!("{bin}: replay: {msg}\n{usage}\n"), 2u8);
    let (mut graph, mut report, mut allow_source, mut allow_tool, mut given) = (None, None, false, false, None);
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--graph" | "--report" if i + 1 < args.len() => {
                let v = args[i + 1].clone();
                if args[i] == "--graph" { graph = Some(v) } else { report = Some(v) }
                i += 2;
            }
            "--allow-source-change" => { allow_source = true; i += 1 }
            "--allow-tool-change" => { allow_tool = true; i += 1 }
            "--" => { given = Some(args[i + 1..].to_vec()); break }
            a => return fail(format!("unknown or incomplete option `{a}`")),
        }
    }
    let Some(graph) = graph else { return fail("--graph FILE is required".into()) };
    let text = match std::fs::read_to_string(&graph) {
        Ok(t) => t,
        Err(e) => return fail(format!("{graph}: {e}")),
    };
    let text = text.trim_end_matches('\n');
    let rec = match crate::conformance::witness_json::check_graph(text) {
        Ok(g) => g,
        Err(e) => return fail(format!("{graph}: refused: {e}")),
    };
    if rec.tool != "traceforge" {
        return fail(format!("refused: the graph is from {:?}, not traceforge", rec.tool));
    }
    let entry = witness_graph::RunIdentity::of_process("", &[], "", None, None);
    if rec.entry != entry.entry {
        return fail(format!("refused: the graph is of {:?}, this binary is {:?}", rec.entry, entry.entry));
    }
    let Some(side) = rec.side.clone() else {
        return fail("refused: the graph has no side".to_owned());
    };
    let gargs = rec.args.clone();
    if given.as_ref().is_some_and(|a| *a != gargs) {
        return fail(format!("refused: the ARGS differ from the graph's {gargs:?}"));
    }
    let model = match rec.model.as_deref() {
        Some("fifo") => ConsType::FIFO,
        Some("bag") => ConsType::Bag,
        Some("causal") => ConsType::Causal,
        m => return fail(format!("refused: the graph's model {m:?}")),
    };
    let mut warnings: Vec<String> = Vec::new();
    let commit = rec.tool_commit.clone();
    if commit != witness_graph::TOOL_COMMIT || commit == "unknown" {
        if !allow_tool {
            return fail(format!(
                "refused: the graph was made by TraceForge {commit:?}, this build is {:?} (--allow-tool-change)",
                witness_graph::TOOL_COMMIT
            ));
        }
        warnings.push(format!("tool-change: {commit} -> {}", witness_graph::TOOL_COMMIT));
    }
    if let Some(w) = &entry.warning {
        eprintln!("{w}");
    }
    // The two `files` maps are compared; the roots are not.
    use crate::conformance::witness_json::{parse_source, Source};
    let same_source = match (parse_source(&entry.source), &rec.source) {
        (Ok(Source::Known { files: a, .. }), Source::Known { files: b, .. }) => a == *b,
        _ => false,
    };
    if !same_source {
        if !allow_source {
            return fail("refused: the benchmark source differs from the graph's, or is unknown \
                         (--allow-source-change)".to_owned());
        }
        warnings.push("source-change".to_owned());
    }
    // The replay is guided, so its seed decides nothing; it is the run's (or the default) all the same.
    let mut b = Config::builder()
        .with_cons_type(model)
        .with_verbose(0)
        .with_seed(rec.seed.unwrap_or(DEFAULT_SEED));
    if let Some(t) = rec.threshold {
        b = b.with_thread_threshold(t);
    }
    let config = b.build();
    let f = match side_entry(p, Some(&side), &gargs) {
        Ok(f) => f,
        Err(e) => return fail(e),
    };
    // A program that panics during the replay is a failed run (exit 1), not a crash of this tool.
    let run = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        crate::conformance::witness_replay::replay(config, f, &rec)
    }));
    let out = match run {
        Ok(Ok(r)) => r,
        Ok(Err(e)) => return (format!("{bin}: replay failed: {e}\n"), 1),
        Err(p) => {
            let msg = p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| (*s).to_owned()))
                .unwrap_or_else(|| "a panic".to_owned());
            return (format!("{bin}: replay failed: the program panicked: {msg}\n"), 1);
        }
    };
    warnings.extend(out.warnings.iter().cloned());
    use crate::conformance::witness_replay::ReplayResult;
    let js = |o: &Option<String>| o.as_deref().map_or_else(|| "null".to_owned(), crate::conformance::interchange::json_string);
    let (line, code, report_json) = match &out.result {
        ReplayResult::Reproduced { events, threads } => (
            format!("replay: reproduced ({events} events, {threads} threads)\n"),
            0u8,
            "\"result\":\"reproduced\",\"at\":null,\"thread\":null,\"kind\":null,\"expected\":null,\"actual\":null".to_owned(),
        ),
        ReplayResult::Deviation(d) => (
            format!(
                "replay: deviation at ({}, {}) thread {}: {}: expected {}, got {}\n",
                d.at.0,
                d.at.1,
                d.thread.as_deref().map_or_else(|| "-".to_owned(), |n| format!("{n:?}")),
                d.kind,
                d.expected.as_deref().unwrap_or("nothing"),
                d.actual.as_deref().unwrap_or("nothing")
            ),
            1u8,
            format!(
                "\"result\":\"deviation\",\"at\":[{},{}],\"thread\":{},\"kind\":\"{}\",\"expected\":{},\"actual\":{}",
                d.at.0, d.at.1, js(&d.thread), d.kind, js(&d.expected), js(&d.actual)
            ),
        ),
    };
    if let Some(path) = report {
        let w: Vec<String> = warnings.iter().map(|w| crate::conformance::interchange::json_string(w)).collect();
        let body = format!(
            "{{\"replay\":1,\"graph\":{},{report_json},\"warnings\":[{}]}}\n",
            crate::conformance::interchange::json_string(&graph),
            w.join(",")
        );
        if let Err(e) = std::fs::write(&path, body) {
            return (format!("{line}{bin}: replay: {path}: {e}\n"), 2);
        }
    }
    let events: usize = rec.events.iter().map(Vec::len).sum();
    *block = format!(
        "--- measurements\nwall_ms: {}\npeak_rss_kb: {}\nreplay_events: {events}\n",
        started.elapsed().as_millis(),
        crate::conformance::measure::peak_rss_kb().map_or_else(String::new, |k| k.to_string())
    );
    (line, code)
}

/// The seed of a run without `--seed`. The library's default seed is random, and the seed decides
/// the first value of every `nondet()` toss, so it decides the order in which a sequential
/// exploration meets its executions (not which executions it meets). A fixed default makes that
/// order, and with it every graph store's `iteration` and line order, the same on every run.
const DEFAULT_SEED: u64 = 0;

fn config_of(o: &Opts) -> Config {
    let mut b = Config::builder()
        .with_cons_type(o.model)
        .with_verbose(0)
        .with_seed(o.seed.unwrap_or(DEFAULT_SEED));
    if let Some(t) = o.threshold {
        b = b.with_thread_threshold(t);
    }
    let mut config = b.with_dump_large_graph(o.dump_large_graph).build();
    config.graph_audit = o.graph_audit.clone();
    config
}

/// `count`'s configuration. Plain Must explores past an assertion failure, as
/// the plain-Must baseline (`Explore`) does, so `count spec` is the sequential
/// specification-side row (G3); above one thread it is the partitioned Must, at
/// the runner's default warmup, split and batch sizes, as the T3c `ExploreP` rows.
fn count_config(o: &Opts) -> Config {
    let mut config = config_of(o);
    config.keep_going_after_error = true;
    if o.threads > 1 {
        config.partitioned_parallelization = true;
        config.partitioned_num_threads = Some(o.threads);
    }
    config
}

#[cfg(feature = "eval")]
/// `row`'s model, seed, thread threshold and optional large-graph diagnostic.
fn row_config(o: &Opts, seed: u64) -> Config {
    let mut b = Config::builder().with_cons_type(o.model).with_seed(seed);
    if let Some(t) = o.threshold {
        b = b.with_thread_threshold(t);
    }
    b.with_dump_large_graph(o.dump_large_graph).build()
}

/// The first option of `args` that a subcommand does not take, if any:
/// `valued` options take a value, `flags` do not.
fn foreign_option<'a>(args: &'a [String], valued: &[&str], flags: &[&str]) -> Option<&'a str> {
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--" => return None,
            a if valued.contains(&a) => i += 2,
            a if flags.contains(&a) => i += 1,
            a if a.starts_with("--") => return Some(a),
            _ => return None,
        }
    }
    None
}

#[cfg(feature = "eval")]
/// The first option of `args` that `row` does not take, if any; `row`'s
/// settings come from the row's label.
fn row_foreign_option(args: &[String]) -> Option<&str> {
    foreign_option(
        args, &["--model", "--seed", "--threshold"], &["--dump-large-graph"],
    )
}

fn builder_of(p: &Program, o: &Opts) -> ConfBuilder {
    ConfBuilder::new()
        .config(config_of(o))
        .cons_type(o.model)
        .visible_threads((p.visible)(&o.args))
}

fn side_entry(p: &Program, side: Option<&String>, args: &[String]) -> Result<Entry, String> {
    match side.map(String::as_str) {
        Some("spec") => Ok((p.spec)(args)),
        Some("impl") => Ok((p.imp)(args)),
        _ => Err("the side is `spec` or `impl`".to_string()),
    }
}

/// The subcommand's own text and exit code; `block` receives `B`'s
/// measurement block when the subcommand ran (empty after a refusal before any
/// run).
fn run_named(
    p: &Program,
    bin: &str,
    args: &[String],
    default_model: ConsType,
    block: &mut String,
) -> (String, u8) {
    run_named_roles(p, bin, args, default_model, block, &|_| Vec::new())
}

fn run_named_roles(
    p: &Program,
    bin: &str,
    args: &[String],
    default_model: ConsType,
    block: &mut String,
    payload_names: &dyn Fn(&[String]) -> Vec<String>,
) -> (String, u8) {
    // `B` (MEAS-1): a block's `wall_ms` runs from here (the start of `main`'s
    // work) to the block.
    let started = std::time::Instant::now();
    let fail = |msg: String| (format!("{bin}: {msg}\n{USAGE}"), 2u8);
    let Some(cmd) = args.first() else {
        return fail("no subcommand".to_string());
    };
    match cmd.as_str() {
        "--help" | "-h" | "help" => (HELP.to_owned(), 0),
        "count" => {
            let o = match parse_opts(&args[2.min(args.len())..], default_model) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
            if let Err(e) = check_witness(cmd, &o) {
                return fail(e);
            }
            let f = match side_entry(p, args.get(1), &o.args) {
                Ok(f) => f,
                Err(e) => return fail(e),
            };
            let config = count_config(&o);
            let side = if args[1] == "spec" {
                measure::Side::Spec
            } else {
                measure::Side::Impl
            };
            let explore_started = std::time::Instant::now();
            let stats = crate::verify(config, move || f());
            let explore_ms = explore_started.elapsed().as_millis();
            *block =
                measure::of_count(&stats, side, explore_ms, started.elapsed().as_millis()).render();
            (
                format!("execs={} blocked={}\n{}", stats.execs, stats.block,
                    stats.threshold.as_ref().map(|r| format!("{r}\n")).unwrap_or_default()),
                0,
            )
        }
        "export" => {
            let o = match parse_opts(&args[2.min(args.len())..], default_model) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
            if let Err(e) = check_witness(cmd, &o) {
                return fail(e);
            }
            let f = match side_entry(p, args.get(1), &o.args) {
                Ok(f) => f,
                Err(e) => return fail(e),
            };
            let Some(out) = o.out.clone() else {
                return fail("export needs --out FILE".to_string());
            };
            let engine = if o.threads > 1 {
                Engine::SverifyP
            } else {
                Engine::Stateful
            };
            let cc = match builder_of(p, &o).payload_names(payload_names(&o.args))
                .engine(engine)
                .threads(o.threads)
                .index(IndexKind::Set)
                .build()
            {
                Ok(cc) => cc,
                Err(e) => return (format!("{bin}: the configuration is refused: {e:?}\n"), 2),
            };
            let header = ExportHeader {
                program: o
                    .program
                    .clone()
                    .unwrap_or_else(|| format!("{bin}:{}", args[1])),
                size: o.size.clone().unwrap_or_else(|| o.args.join(",")),
            };
            let side = if args[1] == "spec" {
                measure::Side::Spec
            } else {
                measure::Side::Impl
            };
            if let Some(g) = &o.graphs {
                if overlapping_paths(Path::new(&out), Path::new(g)) {
                    return fail(
                        "--graphs must name another file than --out (and than either one's .tmp)"
                            .to_owned(),
                    );
                }
            }
            let store = o.graphs.as_ref().map(|g| witness_graph::GraphStoreOpts {
                path: g.into(),
                limit: o.graphs_limit,
                run: witness_graph::RunIdentity::of_process(
                    &args[1],
                    &o.args,
                    &witness_graph::model_label(o.model),
                    o.seed,
                    o.threshold,
                ),
            });
            if let Some(w) = store.as_ref().and_then(|s| s.run.warning.as_ref()) {
                eprintln!("{w}");
            }
            let (r, report) = if o.threads > 1 {
                let r = export_p::export_partitioned(&cc, move || f(), &header, Path::new(&out));
                // `--graphs-limit 0` (checked above): the identity line, with the export's header.
                let report = match (&r, &store) {
                    (Ok(_), Some(st)) => Some(
                        std::fs::read_to_string(&out)
                            .map_err(|e| format!("graphs: {out}: {e}"))
                            .and_then(|t| {
                                let h = t.lines().next().unwrap_or_default().to_owned();
                                witness_graph::write_identity_only(st, &h)
                            }),
                    ),
                    _ => None,
                };
                (r, report)
            } else {
                interchange::export_with_store(
                    &cc,
                    move || f(),
                    &header,
                    Path::new(&out),
                    interchange::ExportSeams::default(),
                    store,
                )
            };
            // A refusal before the run (`NotSet`, `Model`) prints no block.
            if !matches!(r, Err(ExportError::NotSet) | Err(ExportError::Model(_))) {
                *block = measure::of_export(&r, side, started.elapsed().as_millis()).render();
                if r.is_ok() {
                    if let Some(warning) =
                        crate::conformance::graph_audit::append(&o.graph_audit, block)
                    {
                        eprintln!("{warning}");
                    }
                }
            }
            match (r, report) {
                (Ok(_), Some(Err(e))) => {
                    (format!("{bin}: the export was written; the graph store was not: {e}\n"), 2)
                }
                (Ok(s), report) => {
                    let mut text =
                        format!("exported: {} lines from {} graphs to {out}\n", s.lines, s.spec_graphs);
                    if let Some(Ok(rep)) = report {
                        for m in &rep.messages {
                            eprintln!("{m}");
                        }
                        text.push_str(&rep.summary_line());
                        rep.append(block);
                    }
                    (text, 0)
                }
                (Err(e), _) => (format!("{bin}: export refused: {e}\n"), 2),
            }
        }
        "conf" => {
            let o = match parse_opts(&args[1..], default_model) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
            if let Err(e) = check_witness(cmd, &o) {
                return fail(e);
            }
            let (engine, set) = match (o.engine.as_str(), o.threads) {
                ("stateful", 1) => (Engine::Stateful, true),
                ("stateful", _) => (Engine::SverifyP, true),
                ("stateless", 1) => (Engine::CompleteFirst, true),
                ("stateless", _) => (Engine::CFirstP, true),
                ("gated", _) => (Engine::Gated, false),
                ("enumerator", _) => (Engine::Enumerator, false),
                (e, _) => {
                    return fail(format!(
                        "unknown engine `{e}`: stateful, stateless, gated or enumerator"
                    ))
                }
            };
            let mut b = builder_of(p, &o).payload_names(payload_names(&o.args))
                .engine(engine)
                .threads(o.threads)
                .stop_at_first_report(o.stop_at_first)
                .impl_distinct(o.distinct);
            if set {
                b = b.index(IndexKind::Set);
            }
            let mut cc = match b.build() {
                Ok(cc) => cc,
                Err(e) => return (format!("{bin}: the configuration is refused: {e:?}\n"), 2),
            };
            cc.witness = o.witness.clone();
            let imp = (p.imp)(&o.args);
            let spec = (p.spec)(&o.args);
            let r = conformance::verify(cc, move || imp(), move || spec());
            // `B` (MEAS-1 K6): the block from the outcome; the process wall and
            // `VmHWM` are this side's.
            let mut m = measure::of_verdict(&r);
            m.n("wall_ms", started.elapsed().as_millis());
            m.set(
                "peak_rss_kb",
                measure::opt(measure::peak_rss_kb().map(u128::from)),
            );
            *block = m.render();
            match r {
                Ok(v) => {
                    let code = match v {
                        ConfVerdict::Conforms(_) => 0,
                        ConfVerdict::Reported(_) => 1,
                        ConfVerdict::Inconclusive(_) => 2,
                    };
                    (format!("{v}\n"), code)
                }
                Err(e) => (format!("{bin}: {e}\n"), 2),
            }
        }
        "online" => {
            let valued = [
                "--threads",
                "--spec",
                "--witness",
                "--out",
                "--program",
                "--size",
                "--budget",
                "--model",
                "--seed",
                "--threshold",
                "--graphs",
                "--graphs-limit",
            ];
            let flags = ["--stop-at-first", "--dump-large-graph", "--audit-graphs", "--no-pairing-check"];
            if let Some(a) = foreign_option(&args[1..], &valued, &flags) {
                return fail(format!("online does not take `{a}`"));
            }
            let o = match parse_opts(&args[1..], default_model) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
            if let Err(e) = check_witness(cmd, &o) {
                return fail(e);
            }
            let Some(spec) = o.spec.clone() else {
                return fail("online needs --spec FILE".to_string());
            };
            if o.threads > 1 && (o.stop_at_first || o.budget.is_some()) {
                return fail(
                    "online above one thread is full mode and unbounded: it does not take \
                     --stop-at-first or --budget"
                        .to_string(),
                );
            }
            if o.out.is_none() && (o.program.is_some() || o.size.is_some()) {
                return fail(
                    "--program and --size name the --out file's implementation".to_string(),
                );
            }
            let mode = if o.stop_at_first {
                Mode::BugFinder
            } else {
                Mode::Full
            };
            let out = o.out.clone().map(|path| OnlineOut {
                path: path.into(),
                header: ExportHeader {
                    program: o.program.clone().unwrap_or_else(|| format!("{bin}:impl")),
                    size: o.size.clone().unwrap_or_else(|| o.args.join(",")),
                },
            });
            let visible = (p.visible)(&o.args);
            // The pairing check, as before `conf-join`: failures refuse the run
            // (exit 2, no usage text), warnings go to stderr. A program whose
            // names or model the run would refuse is left to that refusal.
            if !o.no_pairing_check {
                let names = crate::conformance::interchange::checked_names(&visible);
                let roles = crate::conformance::interchange::declared_roles(&visible, &payload_names(&o.args));
                if let (Ok(names), Ok(roles)) = (names, roles) {
                    let side = crate::conformance::ProgramSide {
                        visible: names,
                        roles,
                        model: crate::conformance::interchange::model_name(o.model).ok().map(str::to_owned),
                    };
                    let opts = crate::conformance::PairingOpts::default();
                    match crate::conformance::check_pairing_program(Path::new(&spec), &side, opts) {
                        Ok(r) if r.passed() => {
                            for w in &r.warnings {
                                eprintln!("{bin}: pairing: warning: {}: {}", w.row, w.what);
                            }
                        }
                        Ok(r) => {
                            let mut text = String::new();
                            for f in &r.failures {
                                text.push_str(&format!("{bin}: pairing: {}: {}\n", f.row, f.what));
                            }
                            text.push_str(&format!(
                                "{bin}: refused: the pairing check failed ({} checks; --no-pairing-check skips it)\n",
                                r.failures.len()
                            ));
                            return (text, 2);
                        }
                        Err(e) => return (format!("{bin}: online refused: {e}\n"), 2),
                    }
                }
            }
            if let (Some(g), Some(out)) = (&o.graphs, &o.out) {
                if overlapping_paths(Path::new(out), Path::new(g)) {
                    return fail(
                        "--graphs must name another file than --out (and than either one's .tmp)"
                            .to_owned(),
                    );
                }
            }
            let store_opts = o.graphs.as_ref().map(|g| {
                let mut run = witness_graph::RunIdentity::of_process(
                    "impl",
                    &o.args,
                    &witness_graph::model_label(o.model),
                    o.seed,
                    o.threshold,
                );
                run.producer = "online";
                witness_graph::GraphStoreOpts { path: g.into(), limit: o.graphs_limit, run }
            });
            if let Some(w) = store_opts.as_ref().and_then(|s| s.run.warning.as_ref()) {
                eprintln!("{w}");
            }
            // The sequential check fills the store as it runs; the partitioned one writes the
            // identity line only (`--graphs-limit 0`, checked above).
            let store: Option<witness_graph::SharedStore> = store_opts
                .as_ref()
                .filter(|_| o.threads == 1)
                .map(|s| Arc::new(std::sync::Mutex::new(Some(witness_graph::StoreBuilder::new(s.clone(), &visible)))));
            let imp = (p.imp)(&o.args);
            let r = if o.threads > 1 {
                online_p::online_partitioned_roles(
                    &config_of(&o),
                    o.threads,
                    &visible,
                    imp,
                    Path::new(&spec),
                    out,
                    online_p::OnlinePSeams::default(),
                    &payload_names(&o.args),
                ).map(|r| r.report)
            } else {
                online::online(
                    &config_of(&o),
                    &visible,
                    imp,
                    Path::new(&spec),
                    {
                        let mut opts = OnlineOpts::new(mode, o.budget, out);
                        opts.payload_names = payload_names(&o.args);
                        opts.witness = o.witness.clone();
                        opts.graphs = store.clone();
                        opts
                    },
                )
            };
            match r {
                Ok(r) => {
                    *block = measure::of_online(&r, started.elapsed().as_millis()).render();
                    if let Some(warning) =
                        crate::conformance::graph_audit::append(&o.graph_audit, block)
                    {
                        eprintln!("{warning}");
                    }
                    let mut text = r.render();
                    // `--graphs`: the store, once the --out file is written, from that file's
                    // header (without the online fields) and lines.
                    if let (Some(st), Some((out, _))) = (&store_opts, &r.out_written) {
                        let report = std::fs::read_to_string(out)
                            .map_err(|e| format!("graphs: {out}: {e}"))
                            .and_then(|t| {
                                let mut ls = t.lines();
                                let h = ls.next().unwrap_or_default();
                                let h = crate::conformance::witness_join::without_fields(
                                    h,
                                    &crate::conformance::witness_join::ONLINE_FIELDS,
                                )
                                .ok_or_else(|| format!("graphs: {out}: the header is not JSON"))?;
                                let lines: Vec<String> = ls.map(str::to_owned).collect();
                                match store.as_ref().and_then(|s| s.lock().ok()?.take()) {
                                    Some(b) => b.finish(&h, &lines),
                                    None => witness_graph::write_identity_only(st, &h),
                                }
                            });
                        match report {
                            Ok(rep) => {
                                for m in &rep.messages {
                                    eprintln!("{m}");
                                }
                                text.push_str(&rep.summary_line());
                                rep.append(block);
                            }
                            Err(e) => {
                                text.push_str(&format!("{bin}: the graph store was not written: {e}\n"));
                                return (text, 2);
                            }
                        }
                    }
                    (text, r.exit_code())
                }
                Err(e) => fail(format!("online refused: {e}")),
            }
        }
        "replay" => replay_command(p, bin, &args[1..], block),
        #[cfg(feature = "eval")]
        "row" => {
            if let Some(a) = row_foreign_option(&args[1..]) {
                return fail(format!(
                    "row takes only --model, --seed, --threshold and --dump-large-graph, not `{a}`"
                ));
            }
            let o = match parse_opts(&args[1..], default_model) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
            if let Err(e) = check_witness(cmd, &o) {
                return fail(e);
            }
            let Some(seed) = o.seed else {
                return fail("row needs --seed N".to_string());
            };
            let Ok(json) = std::env::var("EVAL_ROW") else {
                return fail("row needs the row's JSON in EVAL_ROW".to_string());
            };
            let commit = std::env::var("EVAL_COMMIT").unwrap_or_default();
            let config = row_config(&o, seed);
            let visible = (p.visible)(&o.args);
            let implementation = (p.imp)(&o.args);
            let specification = (p.spec)(&o.args);
            let subject = |name: &str| Subject {
                name: name.to_string(),
                config,
                visible,
                implementation,
                specification,
            };
            match record::run_row(&json, &commit, subject) {
                Ok(lines) => {
                    *block = lines.measurements.render();
                    (
                        format!("{}{}", lines.xbase.unwrap_or_default(), lines.record),
                        0,
                    )
                }
                Err(e) => (format!("{bin}: row refused: {e}\n"), 2),
            }
        }
        other => fail(format!("unknown subcommand `{other}`")),
    }
}

#[cfg(test)]
#[path = "program_count_tests.rs"]
mod count_tests;
