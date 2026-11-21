//! `conf-join --witness-dir` and `online --out --graphs`, through the binaries and the CLI.
//!
//! The programs are a request/reply exchange: clients `A` and `B` (visible) each send their
//! identity to an invisible server and receive a reply. How the server replies (after both
//! requests, after each, from two servers, or not at all) gives lines of every miss class.
mod wg_common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use traceforge::program::{run_cli, Program};
use traceforge::thread::ThreadId;
use traceforge::Nondet;
use wg_common::*;

fn client(server: ThreadId) {
    traceforge::send_msg(server, me());
    let _ = traceforge::recv_msg_block::<&'static str>();
}

/// The server's reply to the `i`-th request (0 or 1) in a mode, `None` for no reply.
fn reply(mode: usize, i: usize) -> Option<&'static str> {
    match (mode, i) {
        (1, 1) => None,
        (2, 1) => Some("no"),
        (3, 1) => Some("zz"),
        _ => Some("ok"),
    }
}

/// `wait`: the server replies after both requests. `each`: after each. `split`: two servers,
/// one per client. `mix`: a choice between `each` (0), no reply to the second request (1) and
/// the reply "no" to it (2). `each2`: a choice between `each` and the reply "zz" to the second
/// request. `split2`: two servers, where `B`'s replies "ok" or "zz". `heavy`: `each`, with an
/// invisible thread sending many large unread messages and tosses that repeat the executions.
fn req(variant: &str) {
    let mode = match variant {
        "mix" => (0..3).nondet(),
        "each2" => if traceforge::nondet() { 3 } else { 0 },
        "eachwait" => if traceforge::nondet() { 4 } else { 0 },
        _ => 0,
    };
    let zz = variant == "split2" && traceforge::nondet();
    let waits = variant == "wait" || mode == 4;
    let servers: Vec<_> = match variant {
        _ if waits => vec![named("S", || {
            let a = traceforge::recv_msg_block::<ThreadId>();
            let b = traceforge::recv_msg_block::<ThreadId>();
            traceforge::send_msg(a, "ok");
            traceforge::send_msg(b, "ok");
        })],
        "split" | "split2" => (0..2).map(|i| named(&format!("S{i}"), move || {
            let a = traceforge::recv_msg_block::<ThreadId>();
            traceforge::send_msg(a, if i == 1 && zz { "zz" } else { "ok" });
        })).collect(),
        _ => vec![named("S", move || {
            for i in 0..2 {
                let x = traceforge::recv_msg_block::<ThreadId>();
                if let Some(r) = reply(mode, i) { traceforge::send_msg(x, r); }
            }
        })],
    };
    let ids: Vec<ThreadId> = servers.iter().map(|s| s.thread().id()).collect();
    let (sa, sb) = (ids[0], ids[ids.len() - 1]);
    let a = named("A", move || client(sa));
    let b = named("B", move || client(sb));
    a.join().unwrap();
    if mode != 1 { b.join().unwrap(); }
    if mode != 1 { for s in servers { s.join().unwrap(); } }
    if variant == "heavy" {
        named("h", || {
            for i in 0..900u64 { traceforge::send_msg(me(), vec![i; 2000]); }
        }).join().unwrap();
        for _ in 0..7 { let _ = traceforge::nondet(); }
    }
}

fn program() -> Program<'static> {
    Program {
        visible: &|_| vec!["A".to_owned(), "B".to_owned()],
        spec: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || req(&v)) },
        imp: &|a| { let v = a.first().cloned().unwrap_or_default(); Arc::new(move || req(&v)) },
    }
}

fn cli(args: &[&str]) -> (String, u8) {
    run_cli(&program(), &args.iter().map(|s| s.to_string()).collect::<Vec<_>>())
}

/// Runs in a child process only (see `wg_common::child`).
#[test]
fn child_process_entry() {
    let Ok(_) = std::env::var("WG_CHILD") else { return };
    let args = std::env::var("WG_ARGS").unwrap();
    let args: Vec<&str> = if args.is_empty() { vec![] } else { args.split('\u{1f}').collect() };
    let (text, code) = cli(&args);
    std::fs::write(std::env::var("WG_OUT").unwrap(), text).unwrap();
    std::process::exit(code.into());
}

/// `export <side> --out <dir>/<tag>.jsonl [--graphs <...>.graphs.jsonl] -- <variant>`.
fn export(dir: &Path, tag: &str, side: &str, variant: &str, store: bool, extra: &[&str]) -> PathBuf {
    let out = dir.join(format!("{tag}.jsonl"));
    let g = dir.join(format!("{tag}.jsonl.graphs.jsonl"));
    let mut args = vec!["export", side, "--out", out.to_str().unwrap(), "--seed", "1"];
    if store { args.extend(["--graphs", g.to_str().unwrap()]); }
    args.extend(extra);
    args.extend(["--", variant]);
    let (t, code) = cli(&args);
    assert_eq!(code, 0, "{t}");
    out
}

/// conf-join: (stdout, stderr, exit code).
fn conf_join(args: &[&str]) -> (String, String, i32) {
    let out = {
        let _r = spawn_guard();
        Command::new(env!("CARGO_BIN_EXE_conf-join")).args(args).output().unwrap()
    };
    let r = (String::from_utf8(out.stdout).unwrap(), String::from_utf8(out.stderr).unwrap(),
        out.status.code().unwrap_or(-1));
    println!("conf-join {args:?}: exit {}\n--- stdout\n{}--- stderr\n{}---", r.2, r.0, r.1);
    r
}


/// One printed uncovered line: its class, line and the indented lines under it.
#[derive(Debug, Clone)]
struct Printed { class: String, line: String, under: Vec<String> }

fn printed(stdout: &str) -> Vec<Printed> {
    let mut out: Vec<Printed> = Vec::new();
    let body = stdout.split("--- measurements").next().unwrap();
    for l in body.lines() {
        if let Some((c, rest)) = l.split_once(' ') {
            if ["no-bucket", "no-slot", "not-found"].contains(&c) {
                out.push(Printed { class: c.to_owned(), line: rest.to_owned(), under: vec![] });
                continue;
            }
        }
        if l.starts_with("  ") {
            if let Some(p) = out.last_mut() { p.under.push(l.to_owned()); }
        }
    }
    out
}

/// The `join` object a graph must carry, derived from what conf-join printed for the line.
fn expected_join(p: &Printed, mode: &str, decide: bool, against: &str, against_run: &str) -> String {
    let decide = if !decide { "null".to_owned() } else {
        let d = p.under.iter().find_map(|u| u.strip_prefix("  decide: ")).expect("a decide line");
        let mut it = d.split(' ');
        let outcome = it.next().unwrap();
        let num = |k: &str| d.split(' ').find_map(|x| x.strip_prefix(k)).unwrap().to_owned();
        let witness = match p.under.iter().find_map(|u| u.strip_prefix("  witness: ")) {
            None => "null".to_owned(),
            Some(w) => {
                let mut seen: std::collections::HashMap<String, usize> = Default::default();
                let items: Vec<String> = w.split(" ; ").next().unwrap().split(' ').map(|tok| {
                    let role = tok.split_once(':').unwrap().0.to_owned();
                    let i = seen.entry(role.clone()).or_insert(0);
                    let item = format!("[{},{}]", serde_json::to_string(&role).unwrap(), i);
                    *i += 1;
                    item
                }).collect();
                format!("[{}]", items.join(","))
            }
        };
        format!("{{\"outcome\":\"{outcome}\",\"k\":{},\"k_min\":{},\"states\":{},\"witness\":{witness}}}",
            num("k="), num("k_min="), num("states="))
    };
    format!("{{\"tool\":\"traceforge\",\"tool_commit\":{},\"mode\":\"{mode}\",\"class\":\"{}\",\
        \"decide\":{decide},\"against\":{against},\"against_run\":{against_run}}}",
        serde_json::to_string(&expected_commit()).unwrap(), p.class)
}

/// The store's graph line whose `line` is `line`.
fn store_graph(store: &Path, line: &str) -> Option<String> {
    read_lines(store).into_iter().skip(1).find(|g| parse(g).get("line") == &J::Str(line.to_owned()))
}

fn with(graph: &str, join: &str, nearest: &str) -> String {
    let old = ",\"join\":null,\"nearest\":null,";
    assert_eq!(graph.matches(old).count(), 1, "{graph}");
    graph.replace(old, &format!(",\"join\":{join},\"nearest\":{nearest},"))
}

fn files(dir: &Path) -> Vec<String> {
    let mut v: Vec<String> = std::fs::read_dir(dir).map(|r| r.map(|e| e.unwrap().file_name()
        .into_string().unwrap()).collect()).unwrap_or_default();
    v.sort();
    v
}

/// The spec `wait` (one line, counts 0,1,0,1) against the impl `mix` (six uncovered lines of
/// the three classes), with both stores.
struct Mix { dir: PathBuf, spec: PathBuf, imp: PathBuf }

fn mix(impl_extra: &[&str], spec_extra: &[&str]) -> Mix {
    let dir = scratch();
    let spec = export(&dir, "spec", "spec", "wait", true, spec_extra);
    let imp = export(&dir, "impl", "impl", "mix", true, impl_extra);
    Mix { dir, spec, imp }
}

impl Mix {
    fn join(&self, flags: &[&str], w: &str) -> (String, String, i32, PathBuf) {
        let w = self.dir.join(w);
        let mut args: Vec<&str> = flags.to_vec();
        let ws = w.to_str().unwrap().to_owned();
        args.extend(["--witness-dir", &ws, self.spec.to_str().unwrap(), self.imp.to_str().unwrap()]);
        let (o, e, c) = conf_join(&args);
        (o, e, c, w)
    }
    fn spec_store(&self) -> PathBuf { PathBuf::from(format!("{}.graphs.jsonl", self.spec.display())) }
    fn impl_store(&self) -> PathBuf { PathBuf::from(format!("{}.graphs.jsonl", self.imp.display())) }
}

const SPEC_LINE: &str = concat!("{\"statuses\":{\"A\":\"done\",\"B\":\"done\"},\"words\":{\"A\":[{\"s\":\"A\"},",
    "{\"r\":\"ok\"}],\"B\":[{\"s\":\"B\"},{\"r\":\"ok\"}]},\"counts\":[0,1,0,1]}");

/// Checks every printed line, graph file, `index.tsv` row and key against the derivation.
/// `reasons[n-1]` is the reason expected for line `n`.
fn check_witness_dir(m: &Mix, out: &str, w: &Path, mode: &str, decide: bool, reasons: &[&str],
    spec_store: Option<&Path>, impl_store: &Path) {
    let lines = printed(out);
    assert_eq!(lines.len(), reasons.len(), "{out}");
    let spec_header = &read_lines(&m.spec)[0];
    let against_run = spec_store.map_or("null".to_owned(), |s| bytes(parse(&read_lines(s)[0]).get("run")));
    let mut index = String::from("n\tclass\tdecide\tgraph\treason\tline\n");
    let mut want_files: Vec<String> = vec!["index.tsv".to_owned()];
    let (mut written, mut missing, mut refused) = (0, 0, 0);
    for (j, p) in lines.iter().enumerate() {
        let n = j + 1;
        let reason = reasons[j];
        let graph_line = p.under.last().unwrap();
        let word = if decide {
            p.under.iter().find_map(|u| u.strip_prefix("  decide: ")).unwrap().split(' ').next().unwrap()
        } else { "-" };
        if reason == "ok" {
            assert_eq!(graph_line, &format!("  graph: {n}.graph.json"), "{out}");
            let nearest = if p.class == "not-found" && decide {
                let g = spec_store.and_then(|s| store_graph(s, SPEC_LINE));
                let name = format!("{n}.nearest-1.graph.json");
                let graph = match &g {
                    Some(text) => {
                        assert_eq!(std::fs::read_to_string(w.join(&name)).unwrap(), format!("{text}\n"));
                        want_files.push(name.clone());
                        serde_json::to_string(&name).unwrap()
                    }
                    None => "null".to_owned(),
                };
                format!("[{{\"line\":{},\"graph\":{graph}}}]", serde_json::to_string(SPEC_LINE).unwrap())
            } else { "null".to_owned() };
            let base = store_graph(impl_store, &p.line).expect("the store holds the line");
            let want = with(&base, &expected_join(p, mode, decide, spec_header, &against_run), &nearest);
            assert_eq!(std::fs::read_to_string(w.join(format!("{n}.graph.json"))).unwrap(),
                format!("{want}\n"), "graph {n}");
            want_files.push(format!("{n}.graph.json"));
            index.push_str(&format!("{n}\t{}\t{word}\t{n}.graph.json\tok\t{}\n", p.class, p.line));
            written += 1;
        } else {
            assert_eq!(graph_line, &format!("  graph: - ({reason})"), "{out}");
            index.push_str(&format!("{n}\t{}\t{word}\t-\t{reason}\t{}\n", p.class, p.line));
            match reason { "no-store" | "no-graph" => missing += 1, "refused" => refused += 1, _ => {} }
        }
    }
    want_files.sort();
    assert_eq!(files(w), want_files);
    let tsv = std::fs::read_to_string(w.join("index.tsv")).unwrap();
    assert_eq!(tsv, index, "index.tsv: every row ends with a newline");
    let b = block(out);
    let tail: Vec<(String, String)> = b[b.len() - 3..].to_vec();
    assert_eq!(tail, vec![("witness_written".to_owned(), written.to_string()),
        ("witness_missing".to_owned(), missing.to_string()), ("witness_refused".to_owned(), refused.to_string())]);
}

const ALL_OK: [&str; 6] = ["ok"; 6];

#[test]
fn graphs_and_index_match_the_join_byte_for_byte() {
    let m = mix(&[], &[]);
    for (merge, mode) in [(false, "plain"), (true, "merge")] {
        for decide in [true, false] {
            let mut flags = vec![];
            if merge { flags.push("--merge"); }
            if decide { flags.push("--decide"); }
            let (o, e, c, w) = m.join(&flags, &format!("w-{mode}-{decide}"));
            assert_eq!((c, e.as_str()), (1, ""), "{o}");
            check_witness_dir(&m, &o, &w, mode, decide, &ALL_OK, Some(&m.spec_store()), &m.impl_store());
        }
    }
}

#[test]
fn index_tsv_rows_all_end_with_a_newline() {
    let m = mix(&[], &[]);
    let (_, _, c, w) = m.join(&["--decide"], "w");
    assert_eq!(c, 1);
    let tsv = String::from_utf8(std::fs::read(w.join("index.tsv")).unwrap()).unwrap();
    assert!(tsv.ends_with('\n') && !tsv.ends_with("\n\n"), "{tsv:?}");
    assert_eq!(tsv.matches('\n').count(), 7, "header and six rows");
}

#[test]
fn stdout_and_exit_code_are_the_join_plus_graph_lines() {
    // The output with --witness-dir is the output without it, plus one `  graph:` line per
    // uncovered line and the three keys at the end; timing values aside.
    let m = mix(&[], &[]);
    let mask = |t: &str| t.lines().filter(|l| !l.starts_with("  graph: ") && !l.starts_with("witness_"))
        .map(|l| match l.split_once(": ") { Some((k, _)) if k.ends_with("_ms") || k == "peak_rss_kb" => k.to_owned(), _ => l.to_owned() })
        .map(|l| match l.find(" decide_ms=") { Some(i) => format!("{} decide_ms=<masked>", &l[..i]), None => l })
        .collect::<Vec<_>>().join("\n");
    for flags in [vec![], vec!["--decide"], vec!["--merge"], vec!["--merge", "--decide"]] {
        let mut args = flags.clone();
        args.extend([m.spec.to_str().unwrap(), m.imp.to_str().unwrap()]);
        let (a, ae, ac) = conf_join(&args);
        let (b, be, bc, _) = m.join(&flags, &format!("w{}", flags.join("")));
        assert_eq!((ac, ae.as_str()), (bc, be.as_str()));
        assert_eq!(mask(&a), mask(&b), "{flags:?}");
        assert!(!a.contains("  graph: ") && !a.contains("witness_"));
    }
}

#[test]
fn reasons_limit_no_store_no_graph_refused() {
    let m = mix(&[], &[]);
    // limit
    let (o, _, c, w) = m.join(&["--decide", "--witness-limit", "2"], "lim");
    assert_eq!(c, 1);
    check_witness_dir(&m, &o, &w, "plain", true, &["ok", "ok", "limit", "limit", "limit", "limit"],
        Some(&m.spec_store()), &m.impl_store());
    let (o, _, _, w) = m.join(&["--decide", "--witness-limit", "0"], "lim0");
    check_witness_dir(&m, &o, &w, "plain", true, &["limit"; 6], Some(&m.spec_store()), &m.impl_store());
    let (o, _, _, w) = m.join(&["--decide", "--witness-limit", "all"], "all");
    check_witness_dir(&m, &o, &w, "plain", true, &ALL_OK, Some(&m.spec_store()), &m.impl_store());
    // no-store: no default store, and none given
    let bare = mix(&[], &[]);
    std::fs::remove_file(bare.impl_store()).unwrap();
    let (o, _, c, w) = bare.join(&["--decide"], "ns");
    assert_eq!(c, 1);
    check_witness_dir(&bare, &o, &w, "plain", true, &["no-store"; 6], Some(&bare.spec_store()), &bare.impl_store());
    // no-graph: a store limited to its first two lines (the first two executions' lines)
    let lim = mix(&["--graphs-limit", "2"], &[]);
    let held: Vec<String> = read_lines(&lim.impl_store()).iter().skip(1)
        .map(|g| match parse(g).get("line") { J::Str(s) => s.clone(), _ => unreachable!() }).collect();
    assert_eq!(held.len(), 2);
    let (o, _, _, w) = lim.join(&["--decide"], "ng");
    let reasons: Vec<&str> = printed(&o).iter().map(|p| if held.contains(&p.line) { "ok" } else { "no-graph" }).collect();
    check_witness_dir(&lim, &o, &w, "plain", true, &reasons, Some(&lim.spec_store()), &lim.impl_store());
    // refused: one stored graph broken (thread 0 not named main, G2), the others intact
    let bad = mix(&[], &[]);
    let st = read_lines(&bad.impl_store());
    let target = printed(&bad.join(&[], "probe").0)[2].line.clone();
    let text: Vec<String> = st.iter().enumerate().map(|(i, g)| if i > 0 && parse(g).get("line") == &J::Str(target.clone()) {
        g.replacen("{\"name\":\"main\"", "{\"name\":\"boss\"", 1) } else { g.clone() }).collect();
    std::fs::write(bad.impl_store(), text.join("\n") + "\n").unwrap();
    let (o, _, c, w) = bad.join(&["--decide"], "rf");
    assert_eq!(c, 1, "the verdict stands");
    check_witness_dir(&bad, &o, &w, "plain", true, &["ok", "ok", "refused", "ok", "ok", "ok"],
        Some(&bad.spec_store()), &bad.impl_store());
}

/// Each G-rule break of one stored graph gives `refused` for that line only.
#[test]
fn every_rule_break_on_reading_is_refused() {
    let base = mix(&[], &[]);
    let target = printed(&base.join(&["--decide"], "probe").0)[4].line.clone();
    let graph = store_graph(&base.impl_store(), &target).unwrap();
    let breaks: Vec<(&str, String)> = vec![
        ("G1 extra top key", graph.replacen("{\"witness\":1,", "{\"witness\":1,\"x\":0,", 1)),
        ("G1 witness 2", graph.replacen("{\"witness\":1,", "{\"witness\":2,", 1)),
        ("G1 unknown event key", graph.replacen("{\"e\":\"BEGIN\"}", "{\"e\":\"BEGIN\",\"x\":1}", 1)),
        ("G2 main daemon", graph.replacen("\"name\":\"main\",\"daemon\":false", "\"name\":\"main\",\"daemon\":true", 1)),
        ("G3 no begin", graph.replacen("\"events\":[{\"e\":\"BEGIN\"},", "\"events\":[", 1)),
        ("G5 rf to nothing", graph.replacen("\"mode\":\"block\",\"rf\":[", "\"mode\":\"block\",\"rf\":[9", 1)),
        ("G5 null rf on a block", replace_first_rf_with_null(&graph)),
        ("G7 i out of range", graph.replacen("\"e\":\"NONDET\",\"n\":3,\"i\":0", "\"e\":\"NONDET\",\"n\":3,\"i\":3", 1)),
        ("G10 model", graph.replacen("\"model\":\"p2p\"", "\"model\":\"other\"", 1)),
        ("G11 control in a name", graph.replacen("\"name\":\"S\"", "\"name\":\"S\\n\"", 1)),
        ("G12 order", graph.replacen("\"order\":\"first\"", "\"order\":\"best\"", 1)),
        ("G12 null iteration", replace_iteration_null(&graph)),
        ("G8 opaque visible", graph.replacen("\"v\":\"ok\"", "\"v\":{\"opaque\":\"x\"}", 1)),
    ];
    for (what, broken) in breaks {
        assert_ne!(broken, graph, "{what}: the break applies");
        let m = mix(&[], &[]);
        let st: Vec<String> = read_lines(&m.impl_store()).into_iter()
            .enumerate().map(|(i, g)| if i > 0 && parse(&g).get("line") == &J::Str(target.clone()) { broken.clone() } else { g }).collect();
        std::fs::write(m.impl_store(), st.join("\n") + "\n").unwrap();
        let (o, _, c, _) = m.join(&["--decide"], "w");
        assert_eq!(c, 1, "{what}");
        let p = printed(&o);
        assert_eq!(p[4].under.last().unwrap(), "  graph: - (refused)", "{what}: {o}");
        assert_eq!(block_value(&o, "witness_refused").as_deref(), Some("1"), "{what}");
    }
}

fn replace_first_rf_with_null(g: &str) -> String {
    let at = g.find("\"mode\":\"block\",\"rf\":[").unwrap() + "\"mode\":\"block\",\"rf\":".len();
    let end = at + g[at..].find(']').unwrap() + 1;
    format!("{}null{}", &g[..at], &g[end..])
}

fn replace_iteration_null(g: &str) -> String {
    let at = g.find("\"iteration\":").unwrap() + "\"iteration\":".len();
    let end = at + g[at..].find(',').unwrap();
    format!("{}null{}", &g[..at], &g[end..])
}

#[test]
fn false_alarms_get_no_graph_and_do_not_count_towards_the_limit() {
    let dir = scratch();
    let spec = export(&dir, "spec", "spec", "each2", true, &[]);
    let imp = export(&dir, "impl", "impl", "split2", true, &[]);
    let w = dir.join("w");
    let (o, _, c) = conf_join(&["--decide", "--witness-limit", "1", "--witness-dir", w.to_str().unwrap(),
        spec.to_str().unwrap(), imp.to_str().unwrap()]);
    assert_eq!(c, 1, "{o}");
    let p = printed(&o);
    assert_eq!(p.len(), 2, "{o}");
    let fa = p.iter().position(|x| x.under[0].starts_with("  decide: false-alarm")).expect("a false alarm");
    let v = 1 - fa;
    assert!(p[v].under[0].starts_with("  decide: violation"), "{o}");
    assert_eq!(p[fa].under.last().unwrap(), "  graph: - (false-alarm)");
    assert_eq!(p[v].under.last().unwrap(), &format!("  graph: {}.graph.json", v + 1));
    assert_eq!(files(&w), vec![format!("{}.graph.json", v + 1), format!("{}.nearest-1.graph.json", v + 1),
        "index.tsv".to_owned()]);
    let tsv = std::fs::read_to_string(w.join("index.tsv")).unwrap();
    assert!(tsv.lines().any(|l| l.starts_with(&format!("{}\tnot-found\tfalse-alarm\t-\tfalse-alarm\t", fa + 1))), "{tsv}");
    assert_eq!(block_value(&o, "witness_written").as_deref(), Some("1"));
    assert_eq!(block_value(&o, "witness_missing").as_deref(), Some("0"));
    // the false alarm's rank in the printed order, for the record
    println!("false alarm rank {}, violation rank {}", fa + 1, v + 1);
}

#[test]
fn nearest_graphs_need_the_spec_store_and_obey_the_limit() {
    // Without a spec store: nearest items name no graph, against_run is null.
    let m = mix(&[], &[]);
    std::fs::remove_file(m.spec_store()).unwrap();
    let (o, _, _, w) = m.join(&["--decide"], "nospec");
    check_witness_dir(&m, &o, &w, "plain", true, &ALL_OK, None, &m.impl_store());
    // A spec store that does not hold the line (identity line only).
    let m = mix(&[], &["--graphs-limit", "0"]);
    let (o, _, _, w) = m.join(&["--decide"], "lim0");
    check_witness_dir(&m, &o, &w, "plain", true, &ALL_OK, Some(&m.spec_store()), &m.impl_store());
    // --witness-nearest 0: no nearest item.
    let m = mix(&[], &[]);
    let (o, _, _, w) = m.join(&["--decide", "--witness-nearest", "0"], "n0");
    let p = printed(&o);
    for (j, x) in p.iter().enumerate() {
        let g = parse(&std::fs::read_to_string(w.join(format!("{}.graph.json", j + 1))).unwrap().trim_end().to_owned());
        let want = if x.class == "not-found" { "[]" } else { "null" };
        assert_eq!(bytes(g.get("nearest")), want, "{}", x.class);
    }
    assert!(!files(&w).iter().any(|f| f.contains("nearest")));
    // An explicit spec store path is used instead of the default.
    let m = mix(&[], &[]);
    let moved = m.dir.join("elsewhere.g");
    std::fs::rename(m.spec_store(), &moved).unwrap();
    let (o, _, _, w) = m.join(&["--decide", "--spec-graphs", moved.to_str().unwrap()], "expl");
    check_witness_dir(&m, &o, &w, "plain", true, &ALL_OK, Some(&moved), &m.impl_store());
    let moved_i = m.dir.join("elsewhere-impl.g");
    std::fs::rename(m.impl_store(), &moved_i).unwrap();
    let (o, _, _, w) = m.join(&["--decide", "--impl-graphs", moved_i.to_str().unwrap(),
        "--spec-graphs", moved.to_str().unwrap()], "expl2");
    check_witness_dir(&m, &o, &w, "plain", true, &ALL_OK, Some(&moved), &moved_i);
}

#[test]
fn option_and_directory_refusals_exit_two_before_the_join() {
    let m = mix(&[], &[]);
    let (sp, ip) = (m.spec.to_str().unwrap().to_owned(), m.imp.to_str().unwrap().to_owned());
    let w = m.dir.join("w");
    let ws = w.to_str().unwrap().to_owned();
    for (args, msg) in [
        (vec!["--impl-graphs", "x"], "conf-join: the witness options need --witness-dir"),
        (vec!["--spec-graphs", "x"], "conf-join: the witness options need --witness-dir"),
        (vec!["--witness-limit", "3"], "conf-join: the witness options need --witness-dir"),
        (vec!["--witness-nearest", "3"], "conf-join: the witness options need --witness-dir"),
        (vec!["--witness-dir", &ws, "--witness-limit", "x"], "conf-join: --witness-limit takes N or all"),
        (vec!["--witness-dir", &ws, "--witness-limit", "-1"], "conf-join: --witness-limit takes N or all"),
        (vec!["--witness-dir", &ws, "--witness-nearest", "x"], "conf-join: --witness-nearest takes N"),
    ] {
        let mut a = args.clone();
        a.extend([sp.as_str(), ip.as_str()]);
        let (o, e, c) = conf_join(&a);
        assert_eq!((c, e.as_str()), (2, format!("{msg}\n").as_str()), "{args:?}: {o}");
        assert!(!w.exists());
    }
    // A missing value: the option is last.
    for flag in ["--witness-dir", "--impl-graphs", "--witness-limit"] {
        let (_, e, c) = conf_join(&[sp.as_str(), ip.as_str(), flag]);
        assert_eq!(c, 2, "{flag}: {e}");
    }
    // A non-empty directory: refused before the join, left as it was.
    std::fs::create_dir(&w).unwrap();
    std::fs::write(w.join("keep"), b"x").unwrap();
    let (o, e, c) = conf_join(&["--witness-dir", &ws, &sp, &ip]);
    assert_eq!(c, 2);
    assert_eq!(e, format!("conf-join: refused: {}: the witness directory is not empty\n", w.display()));
    assert!(!o.contains("verdict:"), "no join ran: {o}");
    assert_eq!(files(&w), vec!["keep".to_owned()]);
    // An empty existing directory is accepted.
    let e2 = m.dir.join("empty");
    std::fs::create_dir(&e2).unwrap();
    assert_eq!(conf_join(&["--witness-dir", e2.to_str().unwrap(), &sp, &ip]).2, 1);
}

#[test]
fn unusable_stores_exit_two() {
    let cases: Vec<(&str, Box<dyn Fn(&Mix) -> Vec<String>>)> = vec![
        ("explicit store missing", Box::new(|m: &Mix| vec!["--impl-graphs".into(), m.dir.join("nope").display().to_string()])),
        ("explicit spec store missing", Box::new(|m: &Mix| vec!["--spec-graphs".into(), m.dir.join("nope").display().to_string()])),
        ("not an identity line", Box::new(|m: &Mix| { edit(&m.impl_store(), 0, |_| "{\"witness\":1}".into()); vec![] })),
        ("store version 2", Box::new(|m: &Mix| { edit(&m.impl_store(), 0, |l| l.replacen("{\"witness_store\":1", "{\"witness_store\":2", 1)); vec![] })),
        ("another export", Box::new(|m: &Mix| { edit(&m.impl_store(), 0, |l| l.replacen("\"size\":\"mix\"", "\"size\":\"other\"", 1)); vec![] })),
        ("another export (spec side)", Box::new(|m: &Mix| { edit(&m.spec_store(), 0, |l| l.replacen("\"size\":\"wait\"", "\"size\":\"other\"", 1)); vec![] })),
        ("a graph line without a string line", Box::new(|m: &Mix| { edit(&m.impl_store(), 1, |l| l.replacen("{\"witness\":1,\"line\":\"", "{\"witness\":1,\"line\":[\"", 1).replacen("\",\"export\":", "\"],\"export\":", 1)); vec![] })),
        ("a repeated line", Box::new(|m: &Mix| { let l = read_lines(&m.impl_store()); let mut t = l.clone(); t.push(l[1].clone()); std::fs::write(m.impl_store(), t.join("\n") + "\n").unwrap(); vec![] })),
        ("the store of the other side", Box::new(|m: &Mix| vec!["--impl-graphs".into(), m.spec_store().display().to_string()])),
    ];
    for (what, setup) in cases {
        let m = mix(&[], &[]);
        let extra = setup(&m);
        let mut flags: Vec<&str> = vec!["--decide"];
        flags.extend(extra.iter().map(String::as_str));
        let (o, e, c, w) = m.join(&flags, "w");
        assert_eq!(c, 2, "{what}: {o}");
        assert!(e.starts_with("conf-join: refused: "), "{what}: {e}");
        assert!(files(&w).is_empty(), "{what}: no file is written");
    }
    // `run` is never compared: a store whose run differs is used.
    let m = mix(&[], &[]);
    edit(&m.impl_store(), 0, |l| l.replacen("\"side\":\"impl\"", "\"side\":\"spec\"", 1));
    let (_, _, c, w) = m.join(&["--decide"], "w");
    assert_eq!(c, 1);
    assert_eq!(files(&w).iter().filter(|f| f.ends_with(".graph.json") && !f.contains("nearest")).count(), 6);
}

fn edit(path: &Path, n: usize, f: impl Fn(&str) -> String) {
    let mut l = read_lines(path);
    l[n] = f(&l[n]);
    std::fs::write(path, l.join("\n") + "\n").unwrap();
}

// ------------------------------------------------------------------- online --

fn online(dir: &Path, spec: &Path, tag: &str, variant: &str, extra: &[&str]) -> (String, u8, PathBuf, PathBuf) {
    let f = dir.join(format!("{tag}.jsonl"));
    let g = dir.join(format!("{tag}.jsonl.graphs.jsonl"));
    let mut args = vec!["online", "--spec", spec.to_str().unwrap(), "--out", f.to_str().unwrap(),
        "--graphs", g.to_str().unwrap(), "--seed", "1"];
    args.extend(extra);
    args.extend(["--", variant]);
    let (t, c) = cli(&args);
    (t, c, f, g)
}

const ONLINE_FIELDS: [&str; 3] = ["first_miss_iteration", "first_miss_wall_ms", "uncovered_total"];

#[test]
fn online_store_and_its_join() {
    let dir = scratch();
    let spec = export(&dir, "spec", "spec", "wait", true, &[]);
    let (t, c, f, g) = online(&dir, &spec, "on", "mix", &[]);
    assert_eq!(c, 0, "{t}");
    let flines = read_lines(&f);
    // The header without the online fields, key order kept.
    let hj = parse(&flines[0]);
    let J::Obj(fields) = &hj else { panic!() };
    let kept = J::Obj(fields.iter().filter(|(k, _)| !ONLINE_FIELDS.contains(&k.as_str())).cloned().collect());
    let st = read_lines(&g);
    let head = parse(&st[0]);
    assert_eq!(head.keys(), ["witness_store", "export", "run"]);
    assert_eq!(bytes(head.get("export")), bytes(&kept));
    let run = head.get("run");
    assert_eq!(run.get("producer"), &J::Str("online".into()));
    assert_eq!(run.get("iteration"), &J::Null);
    assert_eq!(run.get("side"), &J::Str("impl".into()));
    let mut seen = std::collections::HashSet::new();
    let mut last = 0u64;
    for raw in &st[1..] {
        let gj = parse(raw);
        let J::Str(line) = gj.get("line") else { panic!() };
        assert!(flines[1..].contains(line), "a stored line is in the --out file: {line}");
        assert!(seen.insert(line.clone()), "distinct");
        assert_eq!(bytes(gj.get("export")), bytes(&kept));
        assert_eq!(gj.get("run").get("producer"), &J::Str("online".into()));
        let J::Num(it) = gj.get("run").get("iteration") else { panic!("iteration") };
        let it: u64 = it.parse().unwrap();
        assert!(it > last, "first occurrences in order");
        last = it;
    }
    assert_eq!(seen.len(), flines.len() - 1, "a graph for every line of the --out file");
    let summary = t.lines().find(|l| l.starts_with("graph_store: ")).expect("summary line");
    assert_eq!(summary, format!("graph_store: written={} refused=0 ms={}", seen.len(), block_value(&t, "graphs_ms").unwrap()));
    let keys: Vec<String> = block(&t).into_iter().map(|(k, _)| k).collect();
    assert_eq!(keys[keys.len() - 3..], ["graphs_written", "graphs_refused", "graphs_ms"]);
    // conf-join reads the online store (its header comparison ignores the online fields).
    let w = dir.join("w");
    let (o, e, c) = conf_join(&["--decide", "--witness-dir", w.to_str().unwrap(), spec.to_str().unwrap(), f.to_str().unwrap()]);
    assert_eq!((c, e.as_str()), (1, ""), "{o}");
    let p = printed(&o);
    assert!(!p.is_empty());
    for (j, x) in p.iter().enumerate() {
        assert_eq!(x.under.last().unwrap(), &format!("  graph: {}.graph.json", j + 1), "{o}");
        let written = std::fs::read_to_string(w.join(format!("{}.graph.json", j + 1))).unwrap();
        let base = store_graph(&g, &x.line).unwrap();
        let wj = parse(written.trim_end());
        assert_eq!(bytes(wj.get("run")), bytes(parse(&base).get("run")));
        assert_eq!(bytes(wj.get("join").get("against")), read_lines(&spec)[0]);
    }
}

#[test]
fn online_store_refusals_and_parallel_identity_line() {
    let dir = scratch();
    let spec = export(&dir, "spec", "spec", "wait", true, &[]);
    let g = dir.join("g");
    let usage_of = |t: &str| t.lines().next().unwrap().to_owned();
    let (t, c) = cli(&["online", "--spec", spec.to_str().unwrap(), "--graphs", g.to_str().unwrap(), "--", "mix"]);
    assert_eq!((usage_of(&t), c), ("program: --graphs with online requires --out".to_owned(), 2));
    let f = dir.join("f");
    for (out, graphs) in [(f.clone(), f.clone()), (f.clone(), dir.join("f.tmp")), (dir.join("x/../f"), f.clone())] {
        if !dir.join("x").exists() { std::fs::create_dir(dir.join("x")).unwrap(); }
        let (t, c) = cli(&["online", "--spec", spec.to_str().unwrap(), "--out", out.to_str().unwrap(),
            "--graphs", graphs.to_str().unwrap(), "--", "mix"]);
        assert_eq!(c, 2, "{t}");
        assert_eq!(usage_of(&t), "program: --graphs must name another file than --out (and than either one's .tmp)");
        assert!(!f.exists());
    }
    let (t, c) = cli(&["online", "--spec", spec.to_str().unwrap(), "--out", f.to_str().unwrap(),
        "--graphs", g.to_str().unwrap(), "--threads", "2", "--", "mix"]);
    assert_eq!(c, 2, "{t}");
    assert!(!f.exists() && !g.exists());
    let (t, c, f, g) = online(&dir, &spec, "par", "mix", &["--threads", "2", "--graphs-limit", "0"]);
    assert_eq!(c, 0, "{t}");
    let st = read_lines(&g);
    assert_eq!(st.len(), 1, "identity line only");
    let head = parse(&st[0]);
    assert_eq!(head.get("run").get("producer"), &J::Str("online".into()));
    let fl = read_lines(&f);
    let J::Obj(fields) = parse(&fl[0]) else { panic!() };
    let kept = J::Obj(fields.into_iter().filter(|(k, _)| !ONLINE_FIELDS.contains(&k.as_str())).collect());
    assert_eq!(bytes(head.get("export")), bytes(&kept));
    assert!(t.lines().any(|l| l.starts_with("graph_store: written=0 refused=0 ms=")), "{t}");
}

#[test]
fn online_store_time_is_not_exploration() {
    let dir = scratch();
    let spec = export(&dir, "spec", "spec", "wait", false, &[]);
    let ms = |t: &str, k: &str| -> u64 { block_value(t, k).unwrap().parse().unwrap() };
    let run = |tag: &str, store: bool| {
        let f = dir.join(format!("{tag}.jsonl"));
        let g = dir.join(format!("{tag}.g"));
        let mut args = vec!["online", "--spec", spec.to_str().unwrap(), "--out", f.to_str().unwrap(), "--seed", "1"];
        if store { args.extend(["--graphs", g.to_str().unwrap()]); }
        args.extend(["--", "heavy"]);
        let (t, c) = cli(&args);
        assert_eq!(c, 0, "{t}");
        t
    };
    let _ = run("warm", false);
    const REPS: usize = 7;
    let (mut pe, mut we, mut g) = (u64::MAX, u64::MAX, u64::MAX);
    let mut seen = Vec::new();
    for i in 0..REPS {
        let a = run(&format!("p{i}"), false);
        let b = run(&format!("g{i}"), true);
        pe = pe.min(ms(&a, "explore_ms"));
        we = we.min(ms(&b, "explore_ms"));
        g = g.min(ms(&b, "graphs_ms"));
        seen.push((ms(&a, "explore_ms"), ms(&b, "explore_ms"), ms(&b, "graphs_ms")));
    }
    let tol = 10 + pe.min(g) / 3;
    println!("online timing: tol {tol}; (plain explore, with explore, graphs) {seen:?}");
    assert!(pe >= 2 * tol && g >= 2 * tol, "workload too small: {seen:?}");
    assert!(we <= pe + tol, "the store's time is in explore_ms: {seen:?}");
    assert!(we + tol >= pe, "the store's time came off explore_ms more than once: {seen:?}");
}

/// Writes the `wait`/`mix` exports (with stores) into `WG_DUMP`, for comparing conf-join
/// builds outside this suite. Ignored.
#[test]
#[ignore]
fn dump_join_inputs() {
    let Ok(d) = std::env::var("WG_DUMP") else { return };
    let d = PathBuf::from(d);
    std::fs::create_dir_all(&d).unwrap();
    export(&d, "spec", "spec", "wait", true, &[]);
    export(&d, "impl", "impl", "mix", true, &[]);
    export(&d, "spec2", "spec", "each", true, &[]);
    export(&d, "impl2", "impl", "split", true, &[]);
}

// ------------------------------------------------------------- round-01 review --

#[test]
fn malformed_store_identity_lines_exit_two_and_write_nothing() {
    let edits: Vec<(&str, Box<dyn Fn(&str) -> String>)> = vec![
        ("run is not JSON", Box::new(|l: &str| format!("{},\"run\":BROKEN}}", &l[..l.find(",\"run\":").unwrap()]))),
        ("run is a string", Box::new(|l: &str| format!("{},\"run\":\"x\"}}", &l[..l.find(",\"run\":").unwrap()]))),
        ("run is null", Box::new(|l: &str| format!("{},\"run\":null}}", &l[..l.find(",\"run\":").unwrap()]))),
        ("trailing text", Box::new(|l: &str| format!("{l}x"))),
        ("an extra key", Box::new(|l: &str| format!("{},\"x\":1}}", &l[..l.len() - 1]))),
        ("not an object", Box::new(|_: &str| "[1,2]".to_owned())),
    ];
    for side in ["spec", "impl"] {
        for (what, edit) in &edits {
            let m = mix(&[], &[]);
            let store = if side == "spec" { m.spec_store() } else { m.impl_store() };
            let mut l = read_lines(&store);
            l[0] = edit(&l[0]);
            std::fs::write(&store, l.join("\n") + "\n").unwrap();
            let (o, e, c, w) = m.join(&["--decide"], "w");
            assert_eq!(c, 2, "{side} {what}: {o}");
            assert!(e.starts_with("conf-join: refused: "), "{side} {what}: {e}");
            assert!(files(&w).is_empty(), "{side} {what}: no file is written");
        }
    }
}

/// The 5th uncovered line's stored graph (a not-found line), and the store with it replaced.
fn with_graph(edit: &dyn Fn(&str) -> String) -> (Mix, String) {
    let m = mix(&[], &[]);
    let target = printed(&m.join(&["--decide"], "probe").0)[4].line.clone();
    let st: Vec<String> = read_lines(&m.impl_store()).into_iter().enumerate()
        .map(|(i, g)| if i > 0 && parse(&g).get("line") == &J::Str(target.clone()) { edit(&g) } else { g }).collect();
    std::fs::write(m.impl_store(), st.join("\n") + "\n").unwrap();
    std::fs::remove_dir_all(m.dir.join("probe")).unwrap();
    (m, target)
}

/// The reason conf-join gives for the 5th line after `edit` of its stored graph.
fn reason_after(edit: &dyn Fn(&str) -> String) -> String {
    let (m, _) = with_graph(edit);
    let (o, _, c, _) = m.join(&["--decide"], "w");
    assert_eq!(c, 1, "{o}");
    printed(&o)[4].under.last().unwrap().clone()
}

fn set_run(g: &str, key: &str, value: &str) -> String {
    let run = g.find(",\"run\":{").unwrap();
    let at = run + g[run..].find(&format!("\"{key}\":")).unwrap() + key.len() + 3;
    let rest = &g[at..];
    let end = if rest.starts_with('"') { rest[1..].find('"').unwrap() + 2 }
        else if rest.starts_with('{') || rest.starts_with('[') { matching(rest) } else { rest.find(',').unwrap() };
    format!("{}{value}{}", &g[..at], &g[at + end..])
}

/// The length of the bracketed value at the start of `s`.
fn matching(s: &str) -> usize {
    let mut depth = 0;
    let mut in_str = false;
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'\\' if in_str => i += 1,
            b'"' => in_str = !in_str,
            b'{' | b'[' if !in_str => depth += 1,
            b'}' | b']' if !in_str => { depth -= 1; if depth == 0 { return i + 1; } }
            _ => {}
        }
        i += 1;
    }
    panic!("unbalanced")
}

fn remove_run_key(g: &str, key: &str) -> String {
    let run = g.find(",\"run\":{").unwrap();
    let at = run + g[run..].find(&format!(",\"{key}\":")).unwrap();
    let start = at + key.len() + 4;
    let rest = &g[start..];
    let len = if rest.starts_with('"') { rest[1..].find('"').unwrap() + 2 }
        else if rest.starts_with('{') || rest.starts_with('[') { matching(rest) } else { rest.find(',').unwrap() };
    format!("{}{}", &g[..at], &g[start + len..])
}

const HEX: &str = "0123456789abcdef0123456789abcdef";

#[test]
fn schema_breaks_of_one_graph_are_refused_for_that_graph() {
    let refused_cases: Vec<(&str, Box<dyn Fn(&str) -> String>)> = vec![
        ("missing run.entry", Box::new(|g: &str| remove_run_key(g, "entry"))),
        ("string iteration", Box::new(|g: &str| set_run(g, "iteration", "\"1\""))),
        ("zero iteration", Box::new(|g: &str| set_run(g, "iteration", "0"))),
        ("non-hex digest", Box::new(|g: &str| set_run(g, "source", &format!("{{\"root\":\"r\",\"files\":{{\"a\":\"{}\"}}}}", HEX.to_uppercase())))),
        ("short digest", Box::new(|g: &str| set_run(g, "source", "{\"root\":\"r\",\"files\":{\"a\":\"0123\"}}"))),
        ("non-string digest", Box::new(|g: &str| set_run(g, "source", "{\"root\":\"r\",\"files\":{\"a\":1}}"))),
        ("unsorted files", Box::new(|g: &str| set_run(g, "source", &format!("{{\"root\":\"r\",\"files\":{{\"b\":\"{HEX}\",\"a\":\"{HEX}\"}}}}")))),
        ("source keys reordered", Box::new(|g: &str| set_run(g, "source", &format!("{{\"files\":{{\"a\":\"{HEX}\"}},\"root\":\"r\"}}")))),
        ("event keys reordered", Box::new(|g: &str| g.replacen("{\"e\":\"SEND\",\"to\":", "{\"to\":", 1).replacen(",\"v\":\"ok\"}", ",\"e\":\"SEND\",\"v\":\"ok\"}", 1))),
        ("run keys reordered", Box::new(|g: &str| g.replacen("\"run\":{\"tool\":\"traceforge\",\"tool_commit\":", "\"run\":{\"tool_commit\":", 1)
            .replacen(",\"entry\":", ",\"tool\":\"traceforge\",\"entry\":", 1))),
        ("bad producer", Box::new(|g: &str| set_run(g, "producer", "\"other\""))),
        ("non-string arg", Box::new(|g: &str| set_run(g, "args", "[\"mix\",false]"))),
        ("args not an array", Box::new(|g: &str| set_run(g, "args", "\"mix\""))),
        ("seed beyond u64", Box::new(|g: &str| set_run(g, "options", "{\"seed\":18446744073709551616}"))),
        ("threshold beyond u32", Box::new(|g: &str| set_run(g, "options", "{\"threshold\":4294967296}"))),
        ("an unknown run key", Box::new(|g: &str| g.replacen(",\"order\":\"first\"}", ",\"order\":\"first\",\"x\":1}", 1))),
    ];
    for (what, edit) in &refused_cases {
        let probe = edit(&store_graph(&mix(&[], &[]).impl_store(), &printed(&mix(&[], &[]).join(&["--decide"], "p").0)[4].line).unwrap());
        assert!(serde_json::from_str::<serde_json::Value>(&probe).is_ok(), "{what}: still JSON: {probe}");
        assert_eq!(reason_after(edit.as_ref()), "  graph: - (refused)", "{what}");
    }
    let accepted_cases: Vec<(&str, Box<dyn Fn(&str) -> String>)> = vec![
        ("a valid source object", Box::new(|g: &str| set_run(g, "source", &format!("{{\"root\":\"r\",\"files\":{{\"a\":\"{HEX}\",\"b\":\"{HEX}\"}}}}")))),
        ("an unknown key in run.options", Box::new(|g: &str| set_run(g, "options", "{\"seed\":1,\"zz\":[1,{\"q\":2}]}"))),
        ("a valid join object with unknown members", Box::new(|g: &str| g.replacen(",\"join\":null,", &format!(",\"join\":{},", valid_join(true)), 1))),
        ("a valid nearest list", Box::new(|g: &str| g.replacen(",\"nearest\":null,", ",\"nearest\":[{\"line\":\"x\",\"graph\":null},{\"line\":\"y\",\"graph\":\"1.g\"}],", 1))),
        ("producer conf", Box::new(|g: &str| set_run(g, "producer", "\"conf\""))),
    ];
    for (what, edit) in &accepted_cases {
        assert_eq!(reason_after(edit.as_ref()), "  graph: 5.graph.json", "{what}");
    }
}

#[test]
fn nondet_bounds_are_exact_integers() {
    // main's choice of mode, `(0..3).nondet()`: {"e":"NONDET","n":3,"i":<m>,"lo":0}
    let swap = |n: &'static str, i: &'static str| move |g: &str| {
        let at = g.find("{\"e\":\"NONDET\",\"n\":3,\"i\":").unwrap();
        let end = at + g[at..].find('}').unwrap() + 1;
        format!("{}{{\"e\":\"NONDET\",\"n\":{n},\"i\":{i},\"lo\":0}}{}", &g[..at], &g[end..])
    };
    for (n, i, ok) in [
        ("3", "0", true),
        ("9007199254740993", "9007199254740992", true),
        ("18446744073709551616", "18446744073709551615", true),
        ("9007199254740993", "9007199254740993", false),
        ("18446744073709551616", "18446744073709551616", false),
        ("1", "0", false),
        ("18446744073709551617", "0", false),
        ("3", "-1", false),
        ("3.0", "0", false),
        ("3", "1e0", false),
    ] {
        let got = reason_after(&swap(n, i));
        let want = if ok { "  graph: 5.graph.json" } else { "  graph: - (refused)" };
        assert_eq!(got, want, "n={n} i={i}");
    }
}

/// A spaced spec header (`{ "k": v, ... }`, with or without the online fields) is not in the form
/// the writers emit. The reader refuses it before the join, so no witness is written; the header
/// is never carried into a graph's `against`.
#[test]
fn a_spaced_spec_header_is_refused_before_any_witness() {
    let online = ", \"first_miss_iteration\": 3, \"first_miss_wall_ms\": 7, \"uncovered_total\": 1";
    for with_online in [false, true] {
        let m = mix(&[], &[]);
        let mut l = read_lines(&m.spec);
        let v = parse(&l[0]);
        let J::Obj(fields) = v else { panic!() };
        let mut parts = Vec::new();
        for (k, x) in &fields {
            parts.push(format!("{}: {}", serde_json::to_string(k).unwrap(), bytes(x)));
            if with_online && k == "enumeration" { parts.push(online[2..].to_owned()); }
        }
        l[0] = format!("{{ {} }}", parts.join(", "));
        std::fs::write(&m.spec, l.join("\n") + "\n").unwrap();
        let (o, e, c, w) = m.join(&["--decide"], "w");
        assert_eq!((c, e), (2, format!(concat!("conf-join: refused: {}: line 1: the header is not in the form the ",
            "writers emit (compact, each key once, in the order format, minor, tool, program, size, visible, roles, ",
            "model, enumeration, seed, iterations, the online fields, encoding): it differs at byte 1\n"),
            m.spec.display())), "online {with_online}: {o}");
        let entries = std::fs::read_dir(&w).map(|d| d.count()).unwrap_or(0);
        assert_eq!(entries, 0, "online {with_online}: the witness directory stays empty");
    }
}

#[test]
fn nearest_with_two_effective_orders() {
    // spec `each`: the orders 0,0,0,1 and 0,1,0,0; impl `split`: 0,0,0,0. Budget 0 leaves the
    // line unresolved with k = k_min = 2.
    let words = concat!("{\"statuses\":{\"A\":\"done\",\"B\":\"done\"},\"words\":{\"A\":[{\"s\":\"A\"},",
        "{\"r\":\"ok\"}],\"B\":[{\"s\":\"B\"},{\"r\":\"ok\"}]},\"counts\":");
    let near = |c: &str| format!("{words}{c}}}");
    for spec_variant in ["each", "eachwait"] {
        let dir = scratch();
        let spec = export(&dir, "spec", "spec", spec_variant, true, &[]);
        let imp = export(&dir, "impl", "impl", "split", true, &[]);
        let spec_store = PathBuf::from(format!("{}.graphs.jsonl", spec.display()));
        let mut outs = Vec::new();
        for (merge, nearest_n) in [(false, "3"), (true, "3"), (false, "1"), (true, "1")] {
            let w = dir.join(format!("w-{merge}-{nearest_n}"));
            let mut args = vec![];
            if merge { args.push("--merge"); }
            args.extend(["--decide-budget", "0", "--witness-nearest", nearest_n, "--witness-dir", w.to_str().unwrap(),
                spec.to_str().unwrap(), imp.to_str().unwrap()]);
            let (o, e, c) = conf_join(&args);
            assert_eq!((c, e.as_str()), (1, ""), "{o}");
            let p = printed(&o);
            assert_eq!(p.len(), 1, "{o}");
            let k = if spec_variant == "each" { 2 } else { 3 };
            assert!(p[0].under[0].starts_with(&format!("  decide: unresolved k={k} k_min=2 ")), "{o}");
            assert!(!p[0].under.iter().any(|u| u.starts_with("  witness:")), "{o}");
            let g = parse(std::fs::read_to_string(w.join("1.graph.json")).unwrap().trim_end());
            assert_eq!(g.get("join").get("decide").get("witness"), &J::Null);
            assert_eq!(g.get("join").get("decide").get("outcome"), &J::Str("unresolved".into()));
            // The minimal orders only (0,1,0,1 of `wait` contains both and is left out).
            let all = [near("[0,0,0,1]"), near("[0,1,0,0]")];
            let n: usize = nearest_n.parse().unwrap();
            let want: Vec<String> = all.iter().take(n).enumerate().map(|(j, l)| {
                let name = format!("1.nearest-{}.graph.json", j + 1);
                let stored = store_graph(&spec_store, l).expect("the spec store holds the order");
                assert_eq!(std::fs::read_to_string(w.join(&name)).unwrap(), format!("{stored}\n"));
                format!("{{\"line\":{},\"graph\":{}}}", serde_json::to_string(l).unwrap(), serde_json::to_string(&name).unwrap())
            }).collect();
            assert_eq!(bytes(g.get("nearest")), format!("[{}]", want.join(",")), "{spec_variant} merge {merge} n {n}");
            let mut fs = files(&w);
            fs.retain(|f| f.contains("nearest"));
            assert_eq!(fs.len(), want.len());
            let text = std::fs::read_to_string(w.join("1.graph.json")).unwrap();
            outs.push((nearest_n, merge, text.replace("\"mode\":\"merge\"", "\"mode\":\"plain\"")));
        }
        // plain and merge give the same files but for `mode`
        assert_eq!(outs[0].2, outs[1].2);
        assert_eq!(outs[2].2, outs[3].2);
    }
}

// ------------------------------------------------------------- round-02 review --

/// A valid specification header (the `wait` export's).
const SPEC_HDR: &str = "{\"format\":1,\"minor\":1,\"tool\":\"traceforge\",\"program\":\"program:spec\",\"size\":\"wait\",\"visible\":[\"A\",\"B\"],\"roles\":[\"A\",\"B\"],\"model\":\"p2p\",\"enumeration\":\"complete\",\"encoding\":1}";

/// A join object of §1.5, valid; with `extra`, unknown members among the known ones.
fn valid_join(extra: bool) -> String {
    let (x, y) = if extra { (",\"zz\":[1]", ",\"yy\":{\"q\":null}") } else { ("", "") };
    format!("{{\"tool\":\"traceforge\"{x},\"tool_commit\":\"c\",\"mode\":\"plain\",\"class\":\"not-found\",\
        \"decide\":{{\"outcome\":\"violation\",\"k\":1,\"k_min\":1,\"states\":0,\"witness\":[[\"A\",0],[\"B\",1]]}},\
        \"against\":{SPEC_HDR},\"against_run\":null{y}}}")
}

/// `text` with the first number after `key` (`"to":`, `"child":`, …) raised by 2^64.
pub(crate) fn plus_2_64(text: &str, key: &str) -> String {
    let at = text.find(key).unwrap_or_else(|| panic!("{key}")) + key.len();
    let end = at + text[at..].find(|c: char| !c.is_ascii_digit()).unwrap();
    let n: u128 = text[at..end].parse().unwrap();
    format!("{}{}{}", &text[..at], n + (1u128 << 64), &text[end..])
}

#[test]
fn round_two_schema_breaks_are_refused_per_graph() {
    let join_break = |j: &'static str| move |g: &str| g.replacen(",\"join\":null,", &format!(",\"join\":{j},"), 1);
    let vj = valid_join(false);
    let cases: Vec<(String, Box<dyn Fn(&str) -> String>)> = vec![
        ("SEND to + 2^64".into(), Box::new(|g: &str| plus_2_64(g, "{\"e\":\"SEND\",\"to\":"))),
        ("TCREATE child + 2^64".into(), Box::new(|g: &str| plus_2_64(g, "{\"e\":\"TCREATE\",\"child\":"))),
        ("TJOIN child + 2^64".into(), Box::new(|g: &str| plus_2_64(g, "{\"e\":\"TJOIN\",\"child\":"))),
        ("rf thread + 2^64".into(), Box::new(|g: &str| plus_2_64(g, "\"mode\":\"block\",\"rf\":["))),
        ("rf index + 2^64".into(), Box::new(|g: &str| {
            let at = g.find("\"mode\":\"block\",\"rf\":[").unwrap();
            let comma = at + g[at..].find(',').unwrap();
            let comma = comma + 1 + g[comma + 1..].find(',').unwrap();
            format!("{}{}", &g[..comma], plus_2_64(&g[comma..], ","))
        })),
        ("model garbage".into(), Box::new(|g: &str| set_run(g, "model", "\"garbage\""))),
        ("model null in a TraceForge graph".into(), Box::new(|g: &str| set_run(g, "model", "null"))),
        ("side null in a TraceForge graph".into(), Box::new(|g: &str| set_run(g, "side", "null"))),
        ("a JMC graph with a model".into(), Box::new(|g: &str| set_run(&set_run(g, "tool", "\"jmc\""), "side", "null"))),
        ("join {tool:17}".into(), Box::new(join_break("{\"tool\":17}"))),
        ("join with only unknown members".into(), Box::new(join_break("{\"anything\":1}"))),
        ("join a string".into(), Box::new(join_break("\"x\""))),
        ("nearest [17]".into(), Box::new(|g: &str| g.replacen(",\"nearest\":null,", ",\"nearest\":[17],", 1))),
        ("nearest item keys reordered".into(), Box::new(|g: &str| g.replacen(",\"nearest\":null,", ",\"nearest\":[{\"graph\":null,\"line\":\"x\"}],", 1))),
        ("nearest an object".into(), Box::new(|g: &str| g.replacen(",\"nearest\":null,", ",\"nearest\":{},", 1))),
        ("export with an unknown key".into(), Box::new(|g: &str| g.replacen(",\"encoding\":1},\"run\":", ",\"encoding\":1,\"x\":1},\"run\":", 1))),
        ("export with an online field".into(), Box::new(|g: &str| g.replacen(",\"encoding\":1},\"run\":", ",\"first_miss_iteration\":0,\"encoding\":1},\"run\":", 1))),
    ];
    let mut cases = cases;
    for (what, j) in [
        ("join missing against_run", vj.replacen(",\"against_run\":null", "", 1)),
        ("join missing decide", vj.replacen(",\"decide\":{\"outcome\":\"violation\",\"k\":1,\"k_min\":1,\"states\":0,\"witness\":[[\"A\",0],[\"B\",1]]}", "", 1)),
        ("join members reordered", vj.replacen("\"tool\":\"traceforge\",\"tool_commit\":\"c\"", "\"tool_commit\":\"c\",\"tool\":\"traceforge\"", 1)),
        ("join mode bad", vj.replacen("\"mode\":\"plain\"", "\"mode\":\"fast\"", 1)),
        ("join class bad", vj.replacen("\"class\":\"not-found\"", "\"class\":\"lost\"", 1)),
        ("join class null under plain", vj.replacen("\"class\":\"not-found\"", "\"class\":null", 1)),
        ("decide outcome false-alarm", vj.replacen("\"outcome\":\"violation\"", "\"outcome\":\"false-alarm\"", 1)),
        ("decide witness position malformed", vj.replacen("[[\"A\",0],[\"B\",1]]", "[[\"A\",0],[\"B\"]]", 1)),
        ("decide witness position index a string", vj.replacen("[[\"A\",0],[\"B\",1]]", "[[\"A\",0],[\"B\",\"1\"]]", 1)),
        ("decide violation without witness", vj.replacen("\"witness\":[[\"A\",0],[\"B\",1]]", "\"witness\":null", 1)),
        ("decide k negative", vj.replacen("\"k\":1,", "\"k\":-1,", 1)),
        ("against not an object", vj.replacen(SPEC_HDR, "1", 1)),
        ("against {format:1}", vj.replacen(SPEC_HDR, "{\"format\":1}", 1)),
        ("against with an unknown key", vj.replacen(SPEC_HDR, &SPEC_HDR.replacen(",\"encoding\":1}", ",\"encoding\":1,\"x\":1}", 1), 1)),
        ("against with an online field", vj.replacen(SPEC_HDR, &SPEC_HDR.replacen(",\"encoding\":1}", ",\"uncovered_total\":0,\"encoding\":1}", 1), 1)),
        ("against keys reordered", vj.replacen(SPEC_HDR, &SPEC_HDR.replacen("{\"format\":1,\"minor\":1,", "{\"minor\":1,\"format\":1,", 1), 1)),
        ("against_run {tool:17}", vj.replacen("\"against_run\":null", "\"against_run\":{\"tool\":17}", 1)),
        ("online join with a decide", vj.replacen("\"mode\":\"plain\",\"class\":\"not-found\"", "\"mode\":\"online\",\"class\":null", 1)),
        ("online join with a class", vj.replacen("\"mode\":\"plain\"", "\"mode\":\"online\"", 1)
            .replacen("\"decide\":{\"outcome\":\"violation\",\"k\":1,\"k_min\":1,\"states\":0,\"witness\":[[\"A\",0],[\"B\",1]]}", "\"decide\":null", 1)),
    ] {
        let j: &'static str = Box::leak(j.into_boxed_str());
        cases.push((what.into(), Box::new(join_break(j))));
    }
    let mut bad = Vec::new();
    for (what, edit) in &cases {
        let r = reason_after(edit.as_ref());
        if r != "  graph: - (refused)" { bad.push(format!("{what}: {r}")); }
    }
    assert!(bad.is_empty(), "{}", bad.join("\n"));
    // the valid join (no unknown members) is accepted, and so are a valid online join and a
    // join whose against_run is a store's run
    let online = vj.replacen("\"mode\":\"plain\",\"class\":\"not-found\"", "\"mode\":\"online\",\"class\":null", 1)
        .replacen("\"decide\":{\"outcome\":\"violation\",\"k\":1,\"k_min\":1,\"states\":0,\"witness\":[[\"A\",0],[\"B\",1]]}", "\"decide\":null", 1);
    let m = mix(&[], &[]);
    let spec_run = bytes(parse(&read_lines(&m.spec_store())[0]).get("run"));
    let with_run = vj.replacen("\"against_run\":null", &format!("\"against_run\":{spec_run}"), 1);
    for j in [vj, online, with_run] {
        let js: &'static str = Box::leak(j.into_boxed_str());
        assert_eq!(reason_after(&join_break(js)), "  graph: 5.graph.json", "{js}");
    }
}

#[test]
fn an_incompatible_order_is_not_among_the_nearest() {
    // impl `each`: candidates 0,0,0,1 (A's send before B's receive) and 0,1,0,0. A hand-made
    // specification of the same words holds Z = 0,0,1,1 (A's send before B's send) and
    // Y = 2,2,0,0 (B's receive before A's send). Y contradicts the first candidate and is not
    // among its nearest; for the second candidate both are compatible and minimal.
    let dir = scratch();
    let imp = export(&dir, "impl", "impl", "each", true, &[]);
    let real_spec = export(&dir, "real", "spec", "wait", false, &[]);
    let header = read_lines(&real_spec).remove(0);
    let words = concat!("{\"statuses\":{\"A\":\"done\",\"B\":\"done\"},\"words\":{\"A\":[{\"s\":\"A\"},",
        "{\"r\":\"ok\"}],\"B\":[{\"s\":\"B\"},{\"r\":\"ok\"}]},\"counts\":");
    let line = |c: &str| format!("{words}{c}}}");
    let (z, y) = (line("[0,0,1,1]"), line("[2,2,0,0]"));
    let spec = dir.join("hand.jsonl");
    std::fs::write(&spec, format!("{header}\n{z}\n{y}\n")).unwrap();
    let w = dir.join("w");
    let (o, e, c) = conf_join(&["--decide", "--witness-dir", w.to_str().unwrap(), spec.to_str().unwrap(), imp.to_str().unwrap()]);
    assert_eq!((c, e.as_str()), (1, ""), "{o}");
    let p = printed(&o);
    assert_eq!(p.len(), 2, "{o}");
    let item = |l: &str| format!("{{\"line\":{},\"graph\":null}}", serde_json::to_string(l).unwrap());
    for (j, x) in p.iter().enumerate() {
        assert_eq!(x.class, "not-found", "{o}");
        let g = parse(std::fs::read_to_string(w.join(format!("{}.graph.json", j + 1))).unwrap().trim_end());
        let want = if x.line == line("[0,0,0,1]") { format!("[{}]", item(&z)) }
            else if x.line == line("[0,1,0,0]") { format!("[{},{}]", item(&z), item(&y)) }
            else { panic!("unexpected line {}", x.line) };
        assert_eq!(bytes(g.get("nearest")), want, "{}: {o}", x.line);
    }
}

#[test]
fn a_store_run_with_unknown_keys_is_refused() {
    // The store's run is copied into join.against_run, so it must pass the run check: a run with
    // an unknown key makes the store unusable, for either side.
    for side in ["spec", "impl"] {
        for merge in [false, true] {
            let m = mix(&[], &[]);
            let store = if side == "spec" { m.spec_store() } else { m.impl_store() };
            let mut l = read_lines(&store);
            l[0] = l[0].replacen(",\"order\":\"first\"}", ",\"order\":\"first\",\"x\":1}", 1);
            std::fs::write(&store, l.join("\n") + "\n").unwrap();
            let flags: Vec<&str> = if merge { vec!["--merge", "--decide"] } else { vec!["--decide"] };
            let (o, e, c, w) = m.join(&flags, "w");
            assert_eq!(c, 2, "{side} merge {merge}: {o}");
            assert!(e.starts_with(&format!("conf-join: refused: {}: ", store.display())), "{side}: {e}");
            assert!(!o.contains("verdict:"), "{side}: no report: {o}");
            assert!(files(&w).is_empty(), "{side}: no file is written");
        }
    }
}

// ------------------------------------------------------------- round-04 review --

#[test]
fn a_spec_header_that_cannot_be_against_refuses_the_witness_run() {
    // Each variant is a header that also cannot be a witness graph's `against`; none is in the
    // form the writers emit any more, so the reader refuses each at line 1 first (an unknown
    // key; reordered keys; a `seed`, here a string, in a file that is not sampled), with or
    // without --witness-dir, and no witness file is written. No variant is left that the reader
    // accepts and only the witness identity check refuses.
    let form = concat!("the header is not in the form the writers emit (compact, each key once, in the order ",
        "format, minor, tool, program, size, visible, roles, model, enumeration, seed, iterations, the online ",
        "fields, encoding): it differs at byte 2");
    let edits: Vec<(&str, Box<dyn Fn(&str) -> String>, &str)> = vec![
        ("an unknown key", Box::new(|h: &str| format!("{},\"x\":1}}", &h[..h.len() - 1])),
            "unknown header key `x` (neither writer emits it)"),
        ("reordered keys", Box::new(|h: &str| h.replacen("{\"format\":1,\"minor\":1,", "{\"minor\":1,\"format\":1,", 1)),
            form),
        ("a string seed", Box::new(|h: &str| h.replacen(",\"enumeration\":\"complete\",", ",\"enumeration\":\"complete\",\"seed\":\"1\",", 1)),
            "the header has `seed` in a file that is not `sampled`"),
    ];
    for (what, edit, why) in &edits {
        for merge in [false, true] {
            let m = mix(&[], &[]);
            // No spec store: the header itself is what is judged.
            std::fs::remove_file(m.spec_store()).unwrap();
            let mut l = read_lines(&m.spec);
            let before = l[0].clone();
            l[0] = edit(&l[0]);
            assert_ne!(l[0], before, "{what}: the edit applies");
            assert!(serde_json::from_str::<serde_json::Value>(&l[0]).is_ok(), "{what}: still JSON");
            std::fs::write(&m.spec, l.join("\n") + "\n").unwrap();
            let flags: Vec<&str> = if merge { vec!["--merge", "--decide"] } else { vec!["--decide"] };
            let (o, e, c, w) = m.join(&flags, "w");
            let want = format!("conf-join: refused: {}: line 1: {why}\n", m.spec.display());
            assert_eq!((c, e.as_str()), (2, want.as_str()), "{what} merge {merge}: {o}");
            assert!(files(&w).is_empty(), "{what}: no file is written");
            let mut a: Vec<&str> = if merge { vec!["--merge"] } else { vec![] };
            a.extend([m.spec.to_str().unwrap(), m.imp.to_str().unwrap()]);
            let (_, e2, c2) = conf_join(&a);
            assert_eq!((c2, e2), (2, want), "{what} merge {merge}: without --witness-dir");
        }
    }
}

#[test]
fn every_graph_conf_join_writes_replays() {
    let m = mix(&[], &[]);
    let (o, e, c, w) = m.join(&["--decide"], "w");
    assert_eq!((c, e.as_str()), (1, ""), "{o}");
    let graphs: Vec<String> = files(&w).into_iter().filter(|f| f.ends_with(".graph.json")).collect();
    assert_eq!(graphs.len(), 8, "six graphs and two nearest graphs: {graphs:?}");
    for f in graphs {
        let p = w.join(&f);
        let (t, c) = cli(&["replay", "--graph", p.to_str().unwrap(), "--allow-source-change"]);
        assert_eq!(c, 0, "{f}: {t}");
        assert!(t.starts_with("replay: reproduced ("), "{f}: {t}");
    }
}
