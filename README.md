## TraceForge: Systematic Concurrency Exploration for Distributed Systems

TraceForge is a library to perform systematic exploration of the space of concurrent
message interleavings in distributed systems and their specifications directly in Rust.
A TraceForge test models a distributed system by spawning a set of threads (representing
processes in a distributed system) that communicate via message passing using TraceForge's API. 
TraceForge implements a specialized runtime to control the scheduling of messages and 
to perform systematic exploration of possible message interleavings.
By default, TraceForge looks for assertion violations in the code, but one can also write more complex
specifications given as state machines or those that check a property on termination.


## Getting started

Consider the following message passing implementation:

```
use traceforge::thread;

#[derive(Clone, Debug, PartialEq)]
enum Msg {
    Work,
    Terminate,
}

fn example() {
    let t1 = thread::spawn(move || {
        let mut ready = true;
        let mut i = 0;
        loop {
            let m = traceforge::recv_msg_block();
            match m {
                Msg::Work => assert!(ready),
                Msg::Terminate => ready = false,
            }
            i = i + 1;
            if i == 2 {
                break;
            }
        }
    });
    let t1_id = t1.thread().id();

    let t2 = thread::spawn(move || {
        traceforge::send_msg(t1_id, Msg::Work);
    });
    traceforge::send_msg(t1_id.clone(), Msg::Terminate);

    let _ = t1.join();
    let _ = t2.join();
}

```

Here, `thread::spawn` is a TraceForge API call to spawn a process, `send_msg` is a call to send a message, and `recv_msg_block`
is a blocking message receive.
The assertion can fail because the two messages to `t1` can race, and `Terminate` can be received before `Work`.
However, finding and reproducing these kinds of bugs using standard testing techniques are difficult: they depend on a precise scheduling
of message deliveries that may be missed in random testing.

In contrast, TraceForge systematically explores all relevant message orderings to find such bugs; moreover, the specific schedules that lead to a bug
are reproducible.

TraceForge tests the function by wrapping the execution to the `verify` function:

```
fn test_example() {
    let stats = traceforge::verify(
        traceforge::Config::builder().build(),
        example,
    );
    println!("Stats = {}, {}", stats.execs, stats.block);
}
```

The test will detect the assertion violation.

## Building TraceForge

To build TraceForge, run

```
cargo build
```

To run the unit tests, run
```
cargo test
```
We have put the above simple example in `traceforge/examples`. You can run it by executing
```
cd traceforge
cargo run --example simple -- --random 
cargo run --example simple -- --forge
```
The `--random` option runs a random test. The `--forge` option runs systematic tests (and should always panic).
While testing is very likely to find the assertion violation in this simple test, you can try running the `hard_to_find` example
in `examples` by running:
```
cd traceforge
cargo run --example hard_to_find -- --random 
cargo run --example hard_to_find -- --forge
```
Random testing rarely finds the violation, but traceforge always does.

## Scaling Systematic Exploration

In order to scale, TraceForge implements an [optimal dynamic partial order reduction algorithm](https://dl.acm.org/doi/10.1145/3689778).
The algorithm defines an equivalence relation among executions and  only explores one representative
from each equivalence class.
The equivalence relation considers two executions as equivalent if they agree on the messages received by each process
(technically, a reads-from equivalence).

When a specification is violated, TraceForge provides a trace listing the order of messages sent
which led to the violation. The trace can be replayed under a debugger to investigate it further.
Importantly, if TraceForge finishes without finding a counterexample, we know that no counterexample exists, 
under the assumptions of the test scenario.

## Conformance checking

TraceForge also checks that an implementation program conforms to a specification program: every client-visible
behaviour of the implementation must be one the specification allows. Both are ordinary TraceForge programs; their
visible behaviour is compared through summary files in a shared format (daavar's `format/SUMMARY-FORMAT.md`), so a
TraceForge program can also be checked against a program of another tool that writes the same format.

A benchmark binary is built around `traceforge::program::main` (or `main_with_model`), which gives it these
subcommands (`<bin> --help` lists them with their options):

| subcommand | what it does |
|---|---|
| `count spec\|impl` | explore one side and print its execution counts |
| `export spec\|impl --out FILE [--graphs PATH]` | write the side's summary file; with `--graphs`, its witness graph store |
| `online --spec FILE [--witness PATH] [--out FILE [--graphs PATH]]` | explore the implementation and look every execution up in a specification summary file |
| `replay --graph FILE` | re-run the program once along a witness graph and report the first deviation |
| `conf --engine stateful` | check the implementation against the specification in one process |

`--model` takes the communication model by either of its names; summary file headers always carry the summary
format's name, and witness graphs the TraceForge name:

| TraceForge name | summary format name (alias) | meaning |
|---|---|---|
| `fifo` | `p2p` | each sender's messages to one receiver arrive in order |
| `bag` | `asyn` | messages arrive in any order |
| `causal` | `cd` | causal delivery |

Exit codes (2 is also every usage error):

| subcommand | 0 | 1 | 2 |
|---|---|---|---|
| `count`, `export` | done | — | refused |
| `online` | a verdict: conforms, reports or partial (printed) | the run failed | refused |
| `replay` | reproduced | a deviation, or the replay failed | refused, or the report not written |
| `conf` | conforms | reported | inconclusive or refused |

The `conf-join` binary (`conf-join [options] spec.jsonl impl.jsonl`) joins two summary files and lists the
implementation's uncovered lines. Its options (`conf-join --help`):

| option | meaning |
|---|---|
| `--merge` | read both files as sorted streams (bounded memory) |
| `--decide` | classify each uncovered line: a violation (with a witness), a false alarm or unresolved; the verdict and exit code stay the join's |
| `--decide-budget N` | the search states per line for `--decide` (default 10 000 000; implies `--decide`) |
| `--witness-dir D` | write the witness graph of each uncovered line to `D` (new or empty), looked up in the exports' graph stores |
| `--impl-graphs P` | with `--witness-dir`: the implementation's store (default `impl.jsonl.graphs.jsonl`) |
| `--spec-graphs Q` | with `--witness-dir`: the specification's store (default `spec.jsonl.graphs.jsonl`) |
| `--witness-limit N\|all` | with `--witness-dir`: at most `N` graphs (default 20) |
| `--witness-nearest N` | with `--witness-dir`: at most `N` nearest specification graphs per line (default 3); written only with `--decide`, for the lines it finds no match for |

`conf-join` exits 0 when the files conform or there is no verdict, 1 on a violation, 2 on refused input.

Experimental, and subject to change: the `conf` engines `stateless`, `gated` and `enumerator`; parallel exploration
(`--threads N` above 1); `--threshold`, `--dump-large-graph` and `--audit-graphs`.

## Related Tools

TraceForge is inspired by other tools for checking concurrent Rust code, such as [Loom](http://github.com/tokio-rs/loom) and [Shuttle](https://github.com/awslabs/shuttle).


## Contributing

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This project is licensed under the Apache-2.0 License.

