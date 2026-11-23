# Changelog

## Unreleased

### Changed

- **Pairing check and reader, C6.** A repeated line names the line it repeats: `line N repeats line M`, in the
  pairing check (with and without `--merge`), in both readers' refusals (`<file>: line N repeats line M`; before:
  `<file>: line N: the line repeats line M (each line is one distinct summary)`) and in JMC.
- **Reader, `n`.** The value of a line's `n` is held to the domain of every other value in the file, as JMC's
  reader holds it: a number that is not an integer literal (`1.5`), an integer outside signed 64 bits
  (`18446744073709551616`, and from `9223372036854775808` on) and an object with a repeated key
  (`{"x":1,"x":2}`) are refused, naming the line. Before, they were accepted and emptied the join's total, and
  an `n` from 2^63 to 2^64−1 was summed. The join's total now sums `n` in 1 ..= 2^63−1.
- **`online --spec` runs the pairing check.** Before the run, the specification file is checked against the
  program as `conf-join` checks it against an implementation file: the program's visible names, roles and model
  stand for the implementation header's (C2, C3, C4, C6, C10, C18). C3 checks only that the models are equal,
  since `online` also runs under `cd`. C13 is not checked: a program's tags are known only from what it sends.
  This differs from JMC, which checks C13 against the tags the program declares. A failure refuses the run
  (exit 2) without the usage text; `--no-pairing-check` skips the check, as in `conf-join` and JMC. The
  reader's own refusals keep their text.
- **`online` exit codes.** They are now JMC's named `online`'s: 0 `conforms`, 1 `reports` or a failed run,
  2 refused, 3 `partial`. The verdict `reports` (an uncovered summary was found) exits 1, as `conf-join`'s
  violation and `conf`'s `reports`; before, it exited 0. The verdict `partial` exits 3; before, it exited 0.
  `partial` is an exploration bounded or ended early with no uncovered summary, or a run that ended at a
  threshold, even after an uncovered summary (the threshold end takes precedence over `reports`). `conforms`
  exits 0, a failed run 1 and a refusal 2, as before.
- **`online` refusals without the usage text.** A refusal of the specification file or of the program's names
  (`online refused: …`) prints only the refusal, as the pairing refusal does and as JMC prints it; before, the
  usage text followed it. Usage errors still print it.
- **Pairing check, refused header.** A header the reader refuses stops the pairing check: the reader's refusal
  is printed once, and the one-sided C13 warnings that used to precede it are gone.

## 0.3.0

### Added

- **The conformance checker.** `traceforge::conformance` checks that an implementation program's client-visible
  behaviour is allowed by a specification program. A benchmark binary built on `traceforge::program::main` (or
  `main_with_model`) gets the subcommands `count`, `export`, `online`, `replay` and `conf`. The `conf-join` binary
  joins two summary files and lists the implementation's uncovered lines. Summary files follow daavar's
  `format/SUMMARY-FORMAT.md`, the format JMC also implements. `<bin> --help` and `conf-join --help` list the
  stable surface and mark the experimental engines and options.
- **Witness graphs and replay.** `export --graphs PATH` and `online --graphs PATH` write a graph store beside the
  summary file, with one execution graph per summary line. `conf-join --witness-dir D` writes the witness graph of
  each uncovered line, with `--impl-graphs`, `--spec-graphs`, `--witness-limit` and `--witness-nearest`. `online`
  and `conf --engine stateful` take `--witness PATH`. `<bin> replay --graph FILE` re-runs the program once along a
  witness graph and reports the first deviation.
- **Decide.** `conf-join --decide` classifies each uncovered line as a violation (with a witness), a false alarm or
  unresolved. `--decide-budget N` bounds the search states per line (default 10 000 000). The join's verdict and
  exit code are unchanged.
- **The `eval` feature.** The evaluation-only code is compiled only with the `eval` cargo feature, which is off by
  default. That code is the `row` subcommand (with `EVAL_ROW` and `EVAL_COMMIT`) and the schema-8 record it
  prints. `fixture-tests` turns `eval` on.
- `--model` accepts the summary format's names `p2p`, `asyn` and `cd` as aliases of `fifo`, `bag` and `causal`.

### Changed

- **Deterministic sequential order.** Without `--seed`, a benchmark binary's subcommands use seed 0, so a
  sequential exploration visits its executions in one order on every run. Before, the seed was random.
- The workspace's `Cargo.lock` is committed. It is the lock that builds offline (`--offline --locked`).
