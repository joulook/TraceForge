# Changelog

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
