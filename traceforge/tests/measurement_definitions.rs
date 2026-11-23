//! Hand-derived measurement definitions through the public command dispatcher.
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

use traceforge::program::{run_cli, Entry, Program};
use traceforge::Nondet;

fn scratch() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "tf-measure-{}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

fn named<F: FnOnce() + Send + 'static>(name: &str, f: F) -> traceforge::thread::JoinHandle<()> {
    traceforge::thread::Builder::new().name(name.to_owned()).spawn(f).unwrap()
}

fn cli(body: Entry, args: &[&str]) -> (String, u8) {
    run_cli(&Program {
        visible: &|_| vec!["v".to_owned()],
        spec: &|_| body.clone(),
        imp: &|_| body.clone(),
    }, &args.iter().map(|s| s.to_string()).collect::<Vec<_>>())
}

fn expect(out: &str, values: &[(&str, &str)]) {
    let block = out.split_once("--- measurements\n").unwrap().1;
    for (key, value) in values {
        assert!(block.lines().any(|l| l == format!("{key}: {value}")),
            "conformance: expected {key}: {value} in {out}");
    }
}

fn weighted() {
    let n = (0..3).nondet();
    let v = named("v", move || {
        let _ = (9..10).nondet();
        let _ = (5..6).nondet();
        let me = traceforge::thread::current().id();
        traceforge::send_msg(me, 1usize);
        if n == 2 { traceforge::send_msg(me, 1usize); }
    });
    let h = named("h", || {
        let me = traceforge::thread::current().id();
        traceforge::send_msg(me, 7usize);
        let _ = traceforge::recv_msg_block::<usize>();
    });
    v.join().unwrap();
    h.join().unwrap();
}

fn blocked() {
    named("v", || { let _ = traceforge::recv_msg_block::<usize>(); }).join().unwrap();
}

#[test]
fn execution_weighted_shapes_on_all_four_paths() {
    // Three canonical graphs: main's choice is 0, 1 or 2, even though the first
    // two have the same summary. Main has 7 lines (BEGIN, NONDET, two creates,
    // two joins, END), helper has 4 (BEGIN, SEND, RECV, END), v has 3, 3, 4
    // (BEGIN, one or two SENDs, END). Its two singleton choices contribute no lines.
    // Graph sizes 14,14,15; messages 3,3,4; visible words 1,1,2; two summaries.
    // Mutants: fold shape only on a vacant summary entry; count every label;
    // count only visible sends/receives; count distinct summaries as graphs.
    let dir = scratch();
    let spec = dir.join("spec");
    let values = [
        ("graphs_complete", "3"), ("graphs_blocked", "0"),
        ("max_graph_events", "15"), ("mean_graph_events", "14.333"),
        ("max_message_events", "4"), ("max_visible_events", "2"),
        ("mean_visible_events", "1.333"), ("summaries_distinct", "2"),
    ];
    for threads in ["1", "2"] {
        let (out, code) = cli(Arc::new(weighted), &["export", "spec", "--out",
            spec.to_str().unwrap(), "--threads", threads]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &values);
        let (out, code) = cli(Arc::new(weighted), &["online", "--spec",
            spec.to_str().unwrap(), "--threads", threads, "--out",
            dir.join("impl").to_str().unwrap()]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &values);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn blocked_graph_has_no_synthetic_end_or_completed_receive() {
    // One blocked graph: main BEGIN, TCREATE, BLK; v BEGIN, BLK. A pending
    // blocking receive has no RECV line and no visible observation: 5, 0, 0.
    // Mutants: append END unconditionally; classify blocked graphs as complete.
    let dir = scratch();
    let spec = dir.join("spec");
    let values = [
        ("graphs_complete", "0"), ("graphs_blocked", "1"),
        ("max_graph_events", "5"), ("mean_graph_events", "5.000"),
        ("max_message_events", "0"), ("max_visible_events", "0"),
        ("mean_visible_events", "0.000"),
    ];
    for threads in ["1", "2"] {
        let (out, code) = cli(Arc::new(blocked), &["export", "spec", "--out",
            spec.to_str().unwrap(), "--threads", threads]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &values);
        let (out, code) = cli(Arc::new(blocked), &["online", "--spec",
            spec.to_str().unwrap(), "--threads", threads]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &values);
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn witness_file_agrees_with_measurement() {
    // One complete graph: main BEGIN, TCREATE, TJOIN, END; v BEGIN,
    // SEND, RECV, END. A singleton choice is omitted. All eight lines count.
    // Mutant: omit main's synthetic END from the measurement iterator.
    let dir = scratch();
    let spec = dir.join("spec");
    let witness = dir.join("witness");
    let (out, code) = cli(Arc::new(|| { named("v", || {}).join().unwrap(); }),
        &["export", "spec", "--out", spec.to_str().unwrap()]);
    assert_eq!(code, 0, "conformance: {out}");
    let body: Entry = Arc::new(|| {
        named("v", || {
            let _ = (3..4).nondet();
            let me = traceforge::thread::current().id();
            traceforge::send_msg(me, 4usize);
            let _ = traceforge::recv_msg_block::<usize>();
        }).join().unwrap();
    });
    let (out, code) = cli(body, &["online", "--spec", spec.to_str().unwrap(),
        "--witness", witness.to_str().unwrap()]);
    assert_eq!(code, 1, "conformance: a witness is a miss, `reports`: {out}");
    let text = std::fs::read_to_string(witness).unwrap();
    let lines = text.lines().filter(|l| l.starts_with('\t')).count();
    assert_eq!(lines, 8, "conformance: hand-derived event lines");
    expect(&out, &[("max_graph_events", &lines.to_string()),
        ("mean_graph_events", "8.000"), ("max_message_events", "2")]);
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn refused_summary_contributes_to_no_graph_or_shape_counter() {
    // Each run sends an undeclared unnamed thread identity from v, then either
    // completes or blocks. Neither completion class may include the refusal.
    // Summary encoding refuses it: classes stay zero, shapes are empty online.
    // Export refuses the entire run and leaves the measurements unmeasured.
    // Mutants: count classes before encoding; fill empty-population shapes with zeros.
    let dir = scratch();
    let spec = dir.join("spec");
    let (out, code) = cli(Arc::new(|| { named("v", || {}).join().unwrap(); }),
        &["export", "spec", "--out", spec.to_str().unwrap()]);
    assert_eq!(code, 0, "conformance: {out}");
    for block in [false, true] {
        let body: Entry = Arc::new(move || {
            let h = traceforge::thread::spawn(|| {});
            let id = h.thread().id();
            let v = named("v", move || {
                traceforge::send_msg(id, id);
                traceforge::assume!(!block);
            });
            v.join().unwrap();
            h.join().unwrap();
        });
        for threads in ["1", "2"] {
            let (out, code) = cli(body.clone(), &["online", "--spec", spec.to_str().unwrap(),
                "--threads", threads]);
            assert_eq!(code, 1, "conformance: {out}");
            expect(&out, &[("graphs_complete", "0"), ("graphs_blocked", "0"),
                ("max_graph_events", ""), ("mean_graph_events", ""),
                ("max_message_events", ""), ("max_visible_events", ""),
                ("mean_visible_events", ""), ("iterations", "1")]);
            let (out, code) = cli(body.clone(), &["export", "impl", "--out",
                dir.join("refused").to_str().unwrap(), "--threads", threads]);
            assert_eq!(code, 2, "conformance: {out}");
            expect(&out, &[("graphs_complete", ""), ("graphs_blocked", ""),
                ("max_graph_events", ""), ("mean_graph_events", ""),
                ("max_message_events", ""), ("max_visible_events", ""),
                ("mean_visible_events", "")]);
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn unrenderable_witness_still_has_defined_counts() {
    // Invisible helper is unnamed, or sends an unencodable NaN. Summary
    // encoding never sees it; witness rendering refuses it. Main has 6 lines,
    // helper 3, v 2: 11 witness-shaped events, 1 message, 0 visible events.
    // Mutant: obtain graph counts by rendering the witness and counting lines.
    let dir = scratch();
    let spec = dir.join("spec");
    let empty = dir.join("empty");
    let witness = dir.join("witness");
    let (out, code) = cli(Arc::new(blocked),
        &["export", "spec", "--out", empty.to_str().unwrap()]);
    assert_eq!(code, 0, "conformance: {out}");
    for unnamed in [true, false] {
        let body: Entry = Arc::new(move || {
            let helper = move || {
                traceforge::send_msg(traceforge::thread::current().id(),
                    if unnamed { 1.0 } else { f64::NAN });
            };
            let h = if unnamed { traceforge::thread::spawn(helper) }
                else { named("h", helper) };
            let v = named("v", || {});
            h.join().unwrap();
            v.join().unwrap();
        });
        let values = [("max_graph_events", "11"), ("mean_graph_events", "11.000"),
            ("max_message_events", "1"), ("mean_visible_events", "0.000")];
        for threads in ["1", "2"] {
            let (out, code) = cli(body.clone(), &["export", "spec", "--out",
                spec.to_str().unwrap(), "--threads", threads]);
            assert_eq!(code, 0, "conformance: {out}");
            expect(&out, &values);
            let (out, code) = cli(body.clone(), &["online", "--spec",
                empty.to_str().unwrap(), "--threads", threads]);
            assert_eq!(code, 1, "conformance: the empty specification: `reports`: {out}");
            expect(&out, &values);
        }
        let (out, code) = cli(body, &["online", "--spec", empty.to_str().unwrap(),
            "--witness", witness.to_str().unwrap()]);
        assert_eq!(code, 1, "conformance: {out}");
        expect(&out, &values);
        assert!(!witness.exists(), "conformance: refused witness leaves no file");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn in_process_counts_only_measured_summary_completions() {
    // The same three-choice family has three complete canonical graphs and
    // two summaries. Sequential stateful does not measure completion classes;
    // partitioned stateful counts all three after summarisation.
    // Mutants: use summary cardinality; expose raw pruned counts as measurements.
    let (out, code) = cli(Arc::new(weighted), &["conf", "--engine", "stateful",
        "--threads", "2"]);
    assert_eq!(code, 0, "conformance: {out}");
    expect(&out, &[("graphs_complete", "3"), ("graphs_blocked", "0")]);
    let (out, code) = cli(Arc::new(blocked), &["conf", "--engine", "stateful",
        "--threads", "2"]);
    assert_eq!(code, 0, "conformance: {out}");
    expect(&out, &[("graphs_complete", "0"), ("graphs_blocked", "1")]);
    for engine in ["stateful", "stateless", "enumerator"] {
        let (out, code) = cli(Arc::new(weighted), &["conf", "--engine", engine]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &[("graphs_complete", ""), ("graphs_blocked", ""),
            ("max_graph_events", ""), ("mean_graph_events", "")]);
    }
}

#[test]
fn sampling_cannot_duplicate_a_conformance_enumeration() {
    // Sampling a one-value distribution twice would repeat a graph. All four
    // measurement paths reject sample at handler entry, before summarisation.
    // Mutant: remove reject_out_of_scope("sample") from handle_sample.
    let dir = scratch();
    let spec = dir.join("spec");
    let (out, code) = cli(Arc::new(blocked),
        &["export", "spec", "--out", spec.to_str().unwrap()]);
    assert_eq!(code, 0, "conformance: {out}");
    let body: Entry = Arc::new(|| {
        let _: i64 = traceforge::sample(rand::distr::Uniform::new(0i64, 1i64).unwrap(), 2);
        named("v", || {}).join().unwrap();
    });
    for threads in ["1", "2"] {
        for online in [false, true] {
            let dest = dir.join("sample");
            let args = if online {
                vec!["online", "--spec", spec.to_str().unwrap(), "--threads", threads]
            } else {
                vec!["export", "impl", "--out", dest.to_str().unwrap(), "--threads", threads]
            };
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                cli(body.clone(), &args)
            }));
            let text = match result {
                Ok((text, code)) => {
                    assert_ne!(code, 0, "conformance: sampling must be refused");
                    text
                }
                Err(p) => p.downcast_ref::<String>().cloned()
                    .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                    .expect("conformance: scope refusal has a string diagnostic"),
            };
            assert!(text.contains("`sample` is outside conformance scope"),
                "conformance: expected scope refusal: {text}");
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn count_keeps_raw_totals_out_of_summary_measurements() {
    // Three complete executions; no execution is summarised. The raw total is
    // available as impl_complete, while the seven shared measurements are empty.
    // Mutant: copy Stats::max_graph_events into the shared measurement block.
    for threads in ["1", "2"] {
        let (out, code) = cli(Arc::new(weighted), &["count", "impl", "--threads", threads]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &[("impl_complete", "3"), ("graphs_complete", ""),
            ("graphs_blocked", ""), ("max_graph_events", ""), ("mean_graph_events", ""),
            ("max_message_events", ""), ("max_visible_events", ""),
            ("mean_visible_events", "")]);
    }
}

#[test]
fn one_empty_execution_has_numeric_zero_shapes() {
    // One completed graph: main BEGIN/TCREATE/TJOIN/END, v BEGIN/END.
    // Mutant: leave message/visible measurements empty when their sum is zero.
    let dir = scratch();
    let spec = dir.join("spec");
    let body: Entry = Arc::new(|| { named("v", || {}).join().unwrap(); });
    let values = [("graphs_complete", "1"), ("graphs_blocked", "0"),
        ("max_graph_events", "6"), ("mean_graph_events", "6.000"),
        ("max_message_events", "0"), ("max_visible_events", "0"),
        ("mean_visible_events", "0.000")];
    for threads in ["1", "2"] {
        let (out, code) = cli(body.clone(), &["export", "spec", "--out",
            spec.to_str().unwrap(), "--threads", threads]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &values);
        assert!(!out.contains("audit_graph"), "conformance: audit defaults off");
        let (out, code) = cli(body.clone(), &["online", "--spec",
            spec.to_str().unwrap(), "--threads", threads]);
        assert_eq!(code, 0, "conformance: {out}");
        expect(&out, &values);
        assert!(!out.contains("audit_graph"), "conformance: audit defaults off");
    }
    std::fs::remove_dir_all(dir).unwrap();
}

fn toss_revisit(receiver_tosses: usize, sender_tosses: usize) -> Entry {
    Arc::new(move || {
        let v = named("v", move || {
            let _ = traceforge::recv_msg::<usize>();
            for _ in 0..receiver_tosses {
                let _: bool = traceforge::nondet();
            }
        });
        let id = v.thread().id();
        let h = named("h", move || {
            for _ in 0..sender_tosses {
                let _: bool = traceforge::nondet();
            }
            traceforge::send_msg(id, 1usize);
        });
        v.join().unwrap();
        h.join().unwrap();
    })
}

#[test]
fn toss_revisits_have_distinct_completions_on_all_four_paths() {
    // Receive reads bottom or the sole send; every Boolean result is canonical.
    // The initial left-to-right receive precedes h's send: its backward revisit
    // deletes the following tosses. Counts: 2*2=4, 2*8=16, 2*4*4=32.
    // Mutant: omit an audit record on any completion path (or omit CToss results).
    let dir = scratch();
    let spec = dir.join("spec");
    for (r, s, count) in [(1, 0, "4"), (3, 0, "16"), (2, 2, "32")] {
        for seed in ["0", "1", "7"] {
            for threads in ["1", "2"] {
                let body = toss_revisit(r, s);
                let (out, code) = cli(body.clone(), &["export", "spec", "--out",
                    spec.to_str().unwrap(), "--threads", threads, "--seed", seed,
                    "--audit-graphs"]);
                assert_eq!(code, 0, "conformance: {out}");
                let values = [("graphs_complete", count), ("graphs_blocked", "0"),
                    ("audit_graph_completions", count), ("audit_graphs_distinct", count)];
                expect(&out, &values);
                let (out, code) = cli(body, &["online", "--spec", spec.to_str().unwrap(),
                    "--threads", threads, "--seed", seed, "--audit-graphs"]);
                assert_eq!(code, 0, "conformance: {out}");
                expect(&out, &values);
            }
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}

#[test]
fn graph_audit_is_refused_on_timed_commands() {
    // Mutant: remove the diagnostic-command guard or allow the flag in row.
    let body: Entry = Arc::new(|| { named("v", || {}).join().unwrap(); });
    let mut cases = vec![vec!["count", "impl", "--audit-graphs"], vec!["conf", "--audit-graphs"]];
    // `row` exists only in the eval build.
    if cfg!(feature = "eval") { cases.insert(0, vec!["row", "--audit-graphs"]); }
    for args in cases
    {
        let (out, code) = cli(body.clone(), &args);
        assert_eq!(code, 2, "conformance: {out}");
        assert!(out.contains("--audit-graphs"), "conformance: diagnostic names option");
    }
}
