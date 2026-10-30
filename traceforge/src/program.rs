//! `G1`: the shared main of a Must program (`criteria/G1.md` G1-5).
//!
//! A program names only what is inherent to it — its visible threads and its
//! specification and implementation entry points, each built from the
//! program's own arguments — and gets the same subcommands as every other
//! program:
//!
//! ```text
//! <bin> count  spec|impl [--model fifo|bag|causal] [--seed N] [--threshold N] [ARGS…]
//! <bin> export spec|impl --out FILE [--model …] [--program S] [--size S] [ARGS…]
//! <bin> conf   [--engine stateful|stateless|gated|enumerator] [--threads N]
//!              [--stop-at-first] [--distinct] [--model …] [ARGS…]
//! <bin> online …                                    (reserved; not implemented)
//! <bin> row    --model … --seed N [--threshold N] -- ARGS   (with EVAL_ROW, EVAL_COMMIT)
//! ```
//!
//! `ARGS` are everything after the options (or after `--`), passed verbatim to
//! the program's entry points: a program's size and variant reach it only this
//! way. `count` prints `execs=<c> blocked=<b>`; `export` writes the summary file
//! through [`crate::conformance::export`] (the generic encoder: no per-program
//! code); `conf` runs [`crate::conformance::verify`] and prints its verdict,
//! exit 0 when it conforms, 1 when it reports, 2 otherwise (an inconclusive
//! run or an error). A usage error exits 2.
//!
//! `row` (`H`, criteria `H.md` H-0.2) runs one evaluation row: it reads the
//! row's JSON from `EVAL_ROW` (label, tier, rep, run kind, family, knobs, `k`,
//! variant, twin key and the row's name, which is copied into the record and
//! never resolved) and the commit from `EVAL_COMMIT`, runs the row's engine on
//! the program's entry points built from `ARGS`, and prints `EVALROW\t` and the
//! schema-8 record (after the split line on an `Explore` row); exit 0 with a
//! record (also when the engine panicked, `end_class=panicked`), 2 without one.
//! Only `--model`, `--seed` (required) and `--threshold` are options of `row`.

use std::path::Path;
use std::process::ExitCode;
use std::sync::Arc;

use crate::conformance::config::IndexKind;
use crate::conformance::record::{self, Subject};
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
    let args: Vec<String> = std::env::args().collect();
    let bin = args
        .first()
        .and_then(|a| Path::new(a).file_name())
        .and_then(|n| n.to_str())
        .unwrap_or("program")
        .to_string();
    let (out, code) = run_named(&p, &bin, args.get(1..).unwrap_or(&[]));
    if code == 2 {
        eprint!("{out}");
    } else {
        print!("{out}");
    }
    ExitCode::from(code)
}

/// The same as [`main`] on given arguments (without the binary's name), for
/// tests: the text it would print and the exit code.
pub fn run_cli(p: &Program, args: &[String]) -> (String, u8) {
    run_named(p, "program", args)
}

const USAGE: &str = "usage: <bin> count spec|impl [options] [ARGS…]\n       \
    <bin> export spec|impl --out FILE [options] [ARGS…]\n       \
    <bin> conf [--engine stateful|stateless|gated|enumerator] [--threads N] \
    [--stop-at-first] [--distinct] [options] [ARGS…]\n\
    options: --model fifo|bag|causal, --seed N, --threshold N, --program S, --size S; \
    `--` ends the options\n       \
    <bin> row --model fifo|bag|causal --seed N [--threshold N] -- ARGS   \
    (EVAL_ROW, EVAL_COMMIT)\n";

/// The options of every subcommand, and the program's own arguments.
struct Opts {
    model: ConsType,
    seed: Option<u64>,
    threshold: Option<u32>,
    engine: String,
    threads: usize,
    stop_at_first: bool,
    distinct: bool,
    out: Option<String>,
    program: Option<String>,
    size: Option<String>,
    args: Vec<String>,
}

fn parse_opts(args: &[String]) -> Result<Opts, String> {
    let mut o = Opts {
        model: ConsType::FIFO,
        seed: None,
        threshold: None,
        engine: "stateful".to_string(),
        threads: 1,
        stop_at_first: false,
        distinct: false,
        out: None,
        program: None,
        size: None,
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
                    "fifo" => ConsType::FIFO,
                    "bag" => ConsType::Bag,
                    "causal" => ConsType::Causal,
                    m => return Err(format!("unknown model `{m}`: fifo, bag or causal")),
                }
            }
            "--seed" => o.seed = Some(value()?.parse().map_err(|_| "--seed needs a number")?),
            "--threshold" => {
                o.threshold = Some(value()?.parse().map_err(|_| "--threshold needs a number")?)
            }
            "--engine" => o.engine = value()?,
            "--threads" => {
                o.threads = value()?.parse().map_err(|_| "--threads needs a number")?;
                if o.threads == 0 {
                    return Err("--threads needs at least 1".to_string());
                }
            }
            "--stop-at-first" => o.stop_at_first = true,
            "--distinct" => o.distinct = true,
            "--out" => o.out = Some(value()?),
            "--program" => o.program = Some(value()?),
            "--size" => o.size = Some(value()?),
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

fn config_of(o: &Opts) -> Config {
    let mut b = Config::builder().with_cons_type(o.model).with_verbose(0);
    if let Some(s) = o.seed {
        b = b.with_seed(s);
    }
    if let Some(t) = o.threshold {
        b = b.with_thread_threshold(t);
    }
    b.build()
}

/// `row`'s configuration: the model, the seed and the thread threshold and
/// nothing else, as the evaluation's fixtures built theirs (`H.derived.md`
/// §2.2).
fn row_config(o: &Opts, seed: u64) -> Config {
    let mut b = Config::builder().with_cons_type(o.model).with_seed(seed);
    if let Some(t) = o.threshold {
        b = b.with_thread_threshold(t);
    }
    b.build()
}

/// The first option of `args` that `row` does not take, if any; `row`'s
/// settings come from the row's label.
fn row_foreign_option(args: &[String]) -> Option<&str> {
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--" => return None,
            "--model" | "--seed" | "--threshold" => i += 2,
            a if a.starts_with("--") => return Some(a),
            _ => return None,
        }
    }
    None
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

fn run_named(p: &Program, bin: &str, args: &[String]) -> (String, u8) {
    let fail = |msg: String| (format!("{bin}: {msg}\n{USAGE}"), 2u8);
    let Some(cmd) = args.first() else {
        return fail("no subcommand".to_string());
    };
    match cmd.as_str() {
        "count" => {
            let o = match parse_opts(&args[2.min(args.len())..]) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
            let f = match side_entry(p, args.get(1), &o.args) {
                Ok(f) => f,
                Err(e) => return fail(e),
            };
            // Plain Must explores past an assertion failure, as the plain-Must
            // baseline (`Explore`) does, so `count spec` is the sequential
            // specification-side row (G3).
            let mut config = config_of(&o);
            config.keep_going_after_error = true;
            let stats = crate::verify(config, move || f());
            (
                format!("execs={} blocked={}\n", stats.execs, stats.block),
                0,
            )
        }
        "export" => {
            let o = match parse_opts(&args[2.min(args.len())..]) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
            let f = match side_entry(p, args.get(1), &o.args) {
                Ok(f) => f,
                Err(e) => return fail(e),
            };
            let Some(out) = o.out.clone() else {
                return fail("export needs --out FILE".to_string());
            };
            let cc = match builder_of(p, &o)
                .engine(Engine::Stateful)
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
            match conformance::export(&cc, move || f(), &header, Path::new(&out)) {
                Ok(s) => (
                    format!(
                        "exported: {} lines from {} graphs to {out}\n",
                        s.lines, s.spec_graphs
                    ),
                    0,
                ),
                Err(e) => (format!("{bin}: export refused: {e}\n"), 2),
            }
        }
        "conf" => {
            let o = match parse_opts(&args[1..]) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
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
            let mut b = builder_of(p, &o)
                .engine(engine)
                .threads(o.threads)
                .stop_at_first_report(o.stop_at_first)
                .impl_distinct(o.distinct);
            if set {
                b = b.index(IndexKind::Set);
            }
            let cc = match b.build() {
                Ok(cc) => cc,
                Err(e) => return (format!("{bin}: the configuration is refused: {e:?}\n"), 2),
            };
            let imp = (p.imp)(&o.args);
            let spec = (p.spec)(&o.args);
            match conformance::verify(cc, move || imp(), move || spec()) {
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
        "online" => (format!("{bin}: online: not implemented\n"), 2),
        "row" => {
            if let Some(a) = row_foreign_option(&args[1..]) {
                return fail(format!(
                    "row takes only --model, --seed and --threshold, not `{a}`"
                ));
            }
            let o = match parse_opts(&args[1..]) {
                Ok(o) => o,
                Err(e) => return fail(e),
            };
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
                Ok(lines) => (
                    format!("{}{}", lines.xbase.unwrap_or_default(), lines.record),
                    0,
                ),
                Err(e) => (format!("{bin}: row refused: {e}\n"), 2),
            }
        }
        other => fail(format!("unknown subcommand `{other}`")),
    }
}
