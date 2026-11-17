// Invalid Decide budgets are refused before any file is opened.
#[test]
fn decide_invalid_budget_exits_two_with_diagnostic_and_empty_stdout() {
    for merge in [false, true] {
        for value in [None, Some("-1"), Some("abc"), Some("18446744073709551616")] {
            let mut command = std::process::Command::new(env!("CARGO_BIN_EXE_conf-join"));
            if merge {
                command.arg("--merge");
            }
            command.arg("--decide-budget");
            if let Some(value) = value {
                command.args([value, "spec.jsonl", "impl.jsonl"]);
            }
            let output = command.output().unwrap();
            let stderr = String::from_utf8(output.stderr).unwrap();
            assert_eq!(
                output.status.code(),
                Some(2),
                "conformance: decide: {merge:?} {value:?}: {stderr}"
            );
            assert!(output.stdout.is_empty());
            assert_eq!(
                stderr,
                "conf-join: --decide-budget takes a non-negative integer\n"
            );
        }
    }
}

use serde_json::{json, Value};
use std::path::PathBuf;
use std::process::{Command, Output};

struct Fixture(PathBuf);
impl Fixture {
    fn new(name: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("decide-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        Self(dir)
    }

    fn file(&self, name: &str, mut lines: Vec<Value>) -> PathBuf {
        let head = json!({"format":1,"minor":1,"tool":"traceforge","program":"req","size":"2",
            "visible":["A","B"],"roles":["A","B"],
            "model":"p2p","enumeration":"complete","encoding":1});
        // Merge order is the canonical statuses/words/counts order, not JSON map order.
        lines.sort_by_key(|v| format!("{}{}{}", v["statuses"], v["words"], v["counts"]));
        let mut text = format!("{head}\n");
        for line in lines {
            text.push_str(&format!("{line}\n"));
        }
        let path = self.0.join(name);
        std::fs::write(&path, text).unwrap();
        path
    }

    fn run(&self, merge: bool, flags: &[&str], spec: &[Value], imp: &[Value]) -> Output {
        let s = self.file("s.jsonl", spec.to_vec());
        let i = self.file("i.jsonl", imp.to_vec());
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_conf-join"));
        if merge {
            cmd.arg("--merge");
        }
        cmd.args(flags).arg(s).arg(i).output().unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        std::fs::remove_dir_all(&self.0).unwrap();
    }
}

fn row(counts: [u16; 4]) -> Value {
    json!({"statuses":{"A":"done","B":"done"},
        "words":{"A":[{"s":"A"},{"r":"ok"}],"B":[{"s":"B"},{"r":"ok"}]},
        "counts":counts})
}

fn stdout(out: &Output, code: i32) -> String {
    assert_eq!(
        out.status.code(),
        Some(code),
        "conformance: decide: {:?}",
        out
    );
    assert!(out.stderr.is_empty(), "conformance: decide: {:?}", out);
    String::from_utf8(out.stdout.clone()).unwrap()
}

fn decisions(text: &str) -> Vec<&str> {
    text.lines()
        .filter(|l| {
            l.starts_with("  decide:")
                || l.starts_with("  witness:")
                || (l.starts_with("decide_") && !l.starts_with("decide_ms:"))
        })
        .collect()
}

#[test]
fn decide_paths_agree_including_missing_bucket_and_signature() {
    let f = Fixture::new("parity");
    let mut missing_sig = row([0, 0, 0, 0]);
    missing_sig["words"]["B"][1] = json!({"r":"other"});
    let mut missing_bucket = row([0, 0, 0, 0]);
    missing_bucket["statuses"]["B"] = json!("blocked");
    let cases = [
        (vec![row([0, 1, 0, 1])], row([0, 0, 0, 1]), "not-found", 1),
        (
            vec![row([0, 0, 0, 1]), row([0, 1, 0, 0])],
            row([0, 0, 0, 0]),
            "not-found",
            2,
        ),
        (vec![row([0, 1, 0, 1])], missing_sig, "no-slot", 0),
        (vec![row([0, 1, 0, 1])], missing_bucket, "no-bucket", 0),
    ];
    for (spec, imp, class, k) in cases {
        let a = stdout(&f.run(false, &["--decide"], &spec, &[imp.clone()]), 1);
        let b = stdout(&f.run(true, &["--decide"], &spec, &[imp]), 1);
        assert_eq!(decisions(&a), decisions(&b));
        for text in [&a, &b] {
            assert!(
                text.lines().any(|l| l.starts_with(&format!("{class} "))),
                "conformance: decide: {text}"
            );
            assert!(
                text.contains(&format!(" k={k} k_min={k}")),
                "conformance: decide: {text}"
            );
            assert!(
                text.contains(if k == 2 {
                    "decide_false_alarms: 1\n"
                } else {
                    "decide_violations: 1\n"
                }),
                "conformance: decide: {text}"
            );
        }
    }
}

#[test]
fn decide_cli_preserves_exit_codes_including_all_false_alarms() {
    let f = Fixture::new("exits");
    for merge in [false, true] {
        stdout(
            &f.run(
                merge,
                &["--decide"],
                &[row([0, 0, 0, 0])],
                &[row([0, 1, 0, 1])],
            ),
            0,
        );
        let text = stdout(
            &f.run(
                merge,
                &["--decide"],
                &[row([0, 0, 0, 1]), row([0, 1, 0, 0])],
                &[row([0, 0, 0, 0])],
            ),
            1,
        );
        assert!(text.contains("decide_false_alarms: 1\n"));
        let out = f.run(merge, &["--decide"], &[json!({})], &[row([0, 0, 0, 0])]);
        assert_eq!(out.status.code(), Some(2));
        assert!(String::from_utf8(out.stderr)
            .unwrap()
            .starts_with("conf-join: refused:"));
    }
}

#[test]
fn decide_budget_implies_decide_and_zero_renders_and_counts_unresolved() {
    let f = Fixture::new("budget");
    for merge in [false, true] {
        for budget in ["0", "1"] {
            let text = stdout(
                &f.run(
                    merge,
                    &["--decide-budget", budget],
                    &[row([0, 0, 0, 1]), row([0, 1, 0, 0])],
                    &[row([0, 0, 0, 0])],
                ),
                1,
            );
            assert!(
                text.contains("  decide: unresolved k=2 k_min=2"),
                "conformance: decide: {text}"
            );
            assert!(
                text.contains("violations=0 false_alarms=0 unresolved=1"),
                "conformance: decide: {text}"
            );
            assert!(
                text.contains("decide_unresolved: 1\n"),
                "conformance: decide: {text}"
            );
            assert!(!text.contains("  witness:"));
        }
    }
}

#[test]
fn decide_measurement_keys_preserve_legacy_order_and_append_exactly_seven() {
    let f = Fixture::new("keys");
    let legacy = include_str!("decide_legacy_keys.txt")
        .lines()
        .collect::<Vec<_>>();
    assert_eq!(legacy.len(), 41);
    let extra = [
        "decide_uncovered",
        "decide_violations",
        "decide_false_alarms",
        "decide_unresolved",
        "decide_max_group",
        "decide_states",
        "decide_ms",
    ];
    for merge in [false, true] {
        let text = stdout(
            &f.run(
                merge,
                &["--decide"],
                &[row([0, 1, 0, 1])],
                &[row([0, 0, 0, 1])],
            ),
            1,
        );
        let block = text.split_once("--- measurements\n").unwrap().1;
        let keys = block
            .lines()
            .map(|l| l.split_once(": ").unwrap().0)
            .collect::<Vec<_>>();
        let expected = legacy.iter().copied().chain(extra).collect::<Vec<_>>();
        assert_eq!(keys, expected);
    }
}

// Decode labelled positions and check edges directly, without production `extends`.
#[test]
fn decide_printed_witness_extends_candidate_and_breaks_every_reference() {
    let f = Fixture::new("witness");
    let candidate = [0, 0, 0, 1];
    let group = [[0, 2, 0, 1], [0, 1, 0, 2]];
    for merge in [false, true] {
        let spec = group.iter().map(|&c| row(c)).collect::<Vec<_>>();
        let text = stdout(&f.run(merge, &["--decide"], &spec, &[row(candidate)]), 1);
        let w = text
            .lines()
            .find_map(|l| l.strip_prefix("  witness: "))
            .unwrap();
        let (word, statuses) = w.split_once(" ; statuses: ").unwrap();
        assert_eq!(statuses, "A=done B=done");
        let mut positions = [[usize::MAX; 2]; 2];
        for (rank, token) in word.split_whitespace().enumerate() {
            let (role, obs) = token.split_once(':').unwrap();
            let t = match role {
                "A" => 0,
                "B" => 1,
                _ => panic!("conformance: decide: unknown role"),
            };
            let obs: Value = serde_json::from_str(obs).unwrap();
            let i = if obs == row(candidate)["words"][role][0] {
                0
            } else {
                assert_eq!(obs, row(candidate)["words"][role][1]);
                1
            };
            assert_eq!(
                positions[t][i],
                usize::MAX,
                "conformance: decide: duplicate position"
            );
            positions[t][i] = rank;
        }
        assert_eq!(word.split_whitespace().count(), 4);
        for p in positions {
            assert!(
                p[0] < p[1] && p[1] < 4,
                "conformance: decide: within-thread order or missing position"
            );
        }
        let contains = |counts: [u16; 4]| {
            (0..2).all(|t| {
                (0..2).all(|i| {
                    (0..counts[2 * t + i] as usize).all(|j| positions[1 - t][j] < positions[t][i])
                })
            })
        };
        assert!(contains(candidate));
        assert!(
            group.iter().all(|&order| !contains(order)),
            "conformance: decide: {text}"
        );
    }
}

// Run explicitly with an archived 367cdc6 binary and the external metrics shim.
#[test]
#[ignore = "requires DECIDE_BASE_BIN and DECIDE_METRICS_SHIM; see d1b/REPORT.md"]
fn decide_disabled_matches_pinned_base_bytes() {
    let base = std::env::var("DECIDE_BASE_BIN").expect("conformance: decide: archived base binary");
    let shim = std::env::var("DECIDE_METRICS_SHIM")
        .expect("conformance: decide: fixed clock and RSS inputs");
    let f = Fixture::new("legacy");
    for merge in [false, true] {
        for (spec, imp, code) in [
            (vec![row([0, 0, 0, 0])], vec![row([0, 1, 0, 1])], 0),
            (vec![row([0, 1, 0, 1])], vec![row([0, 0, 0, 1])], 1),
            (vec![json!({})], vec![row([0, 0, 0, 0])], 2),
        ] {
            let s = f.file("s.jsonl", spec);
            let i = f.file("i.jsonl", imp);
            let run = |binary: &str| {
                let mut cmd = Command::new(binary);
                cmd.env("LD_PRELOAD", &shim);
                if merge {
                    cmd.arg("--merge");
                }
                cmd.arg(&s).arg(&i).output().unwrap()
            };
            let old = run(&base);
            let new = run(env!("CARGO_BIN_EXE_conf-join"));
            assert_eq!(old.status.code(), Some(code));
            assert_eq!(new.status.code(), old.status.code());
            assert_eq!(new.stderr, old.stderr);
            assert_eq!(
                new.stdout, old.stdout,
                "conformance: decide: merge={merge}, exit={code}"
            );
            let text = String::from_utf8(new.stdout).unwrap();
            assert!(
                text.contains("peak_rss_kb: 1024\n"),
                "conformance: decide: shim must be active"
            );
            assert!(
                text.contains("wall_ms: 0\n"),
                "conformance: decide: shim must be active"
            );
        }
    }
}

// Generated long words exercise U32 storage without a checked-in large fixture.
fn long_row(len: usize, count: u32) -> Value {
    let mut counts = vec![0u32; len];
    counts.push(count);
    json!({"statuses":{"A":"done","B":"done"},
        "words":{"A":vec![json!({"s":"A"}); len],"B":[{"s":"B"}]},
        "counts":counts,"n":7})
}

fn stable_output(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("conformance: UTF-8 output")
        .lines()
        .map(|l| {
            let key = l.split(':').next().unwrap_or("");
            if key == "wall_ms" || key == "peak_rss_kb" {
                format!("{key}: <measured>")
            } else {
                l.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn count_refusal(f: &Fixture, merge: bool, spec: &[Value], imp: &[Value], line: &str) {
    let out = f.run(merge, &["--decide"], spec, imp);
    assert_eq!(out.status.code(), Some(2), "conformance: count refusal exit");
    let err = String::from_utf8(out.stderr.clone()).expect("conformance: UTF-8 diagnostic");
    assert!(err.starts_with("conf-join: refused: decide:"), "conformance: {err}");
    assert!(err.contains("count 65536 exceeds 65535"), "conformance: {err}");
    assert!(err.contains(line), "conformance: diagnostic identifies line");
    if line == "a normal-form line:" {
        let v = &imp[0];
        let key = format!(
            "{{\"statuses\":{},\"words\":{},\"counts\":{}}}",
            v["statuses"], v["words"], v["counts"]
        );
        assert!(err.ends_with(&format!(": {key}\n")), "conformance: offending line");
    }
    let ordinary = f.run(merge, &[], &[json!({})], imp);
    assert_eq!(ordinary.status.code(), Some(2), "conformance: ordinary refusal");
    assert_eq!(
        stable_output(&out.stdout), stable_output(&ordinary.stdout),
        "conformance: usual refused stdout and measurement block"
    );
}

// Mutant: accept U32 specification counts with `Ok(c as u16)`.
#[test]
fn decide_refuses_used_specification_count_in_both_modes() {
    let f = Fixture::new("used-spec-count");
    let spec = [long_row(65536, 65536)];
    let imp = [long_row(65536, 0)];
    for merge in [false, true] {
        let plain = stdout(&f.run(merge, &[], &spec, &imp), 1);
        assert!(plain.contains("uncovered_total: 7\n"), "conformance: total retained");
        count_refusal(&f, merge, &spec, &imp, "s.jsonl: line 2:");
    }
}

// Mutants: restore `c as u16`; reject 65535 too (change checked bound to >=).
#[test]
fn decide_candidate_count_boundary_in_both_modes() {
    let f = Fixture::new("candidate-count-boundary");
    for merge in [false, true] {
        let imp = [long_row(65535, 65535)];
        let text = stdout(&f.run(merge, &["--decide"], &[], &imp), 1);
        assert!(text.contains("decide_violations: 1\n"), "conformance: 65535 decided");
        assert!(text.contains("  witness:"), "conformance: boundary witness");
        let imp = [long_row(65536, 65536)];
        stdout(&f.run(merge, &[], &[], &imp), 1);
        count_refusal(&f, merge, &[], &imp, "a normal-form line:");
        let mut spec = long_row(65536, 0);
        spec["counts"][0] = json!(1);
        count_refusal(&f, merge, &[spec], &imp, "a normal-form line:");
    }
}

// Mutants: eagerly reject every U32 group; reject covered implementation counts.
#[test]
fn decide_unused_large_counts_are_not_refused_in_both_modes() {
    let f = Fixture::new("unused-counts");
    let large = long_row(65536, 65536);
    for merge in [false, true] {
        stdout(&f.run(merge, &[], &[large.clone()], &[large.clone()]), 0);
        let text = stdout(
            &f.run(merge, &["--decide"], &[large.clone()], &[large.clone()]), 0,
        );
        assert!(text.contains("decide_uncovered: 0\n"), "conformance: covered large row");
        // These groups straddle the small miss, exercising both load and drain.
        let mut before = large.clone();
        before["statuses"]["A"] = json!("blocked");
        let mut after = large.clone();
        after["statuses"]["A"] = json!("err");
        let spec = [before, after, row([0, 1, 0, 1])];
        let imp = [row([0, 0, 0, 1])];
        let text = stdout(&f.run(merge, &["--decide"], &spec, &imp), 1);
        assert!(text.contains("decide_violations: 1\n"), "conformance: unused groups");
    }
}

// Mutants: reject all U32 storage; cap can_add at self.lens[t].min(65535).
#[test]
fn decide_long_words_with_small_used_counts_are_decided() {
    let f = Fixture::new("long-small-counts");
    for merge in [false, true] {
        let spec = [long_row(65537, 65535)];
        let imp = [long_row(65537, 65534)];
        let text = stdout(&f.run(merge, &["--decide"], &spec, &imp), 1);
        assert!(text.contains("decide_violations: 1\n"), "conformance: small used counts");
        assert!(text.contains("uncovered_total: 7\n"), "conformance: decided total retained");
        let witness = text.lines().find(|l| l.starts_with("  witness:"))
            .expect("conformance: long witness");
        assert_eq!(witness.matches("A:").count(), 65537, "conformance: all A positions");
        assert_eq!(witness.matches("B:").count(), 1, "conformance: all B positions");
    }
}

// Mutant: remove `uncovered_total = add_n(uncovered_total, n)` from the merge miss.
// The lead supplies a binary built from 1c4354d and the fixed clock/RSS shim.
#[test]
#[ignore = "requires MERGE_ENGINE_FIXES_BIN (1c4354d) and DECIDE_METRICS_SHIM"]
fn merge_decide_disabled_matches_engine_fixes_bytes() {
    let base = std::env::var("MERGE_ENGINE_FIXES_BIN")
        .expect("conformance: archived 1c4354d binary");
    let shim = std::env::var("DECIDE_METRICS_SHIM")
        .expect("conformance: fixed clock and RSS inputs");
    let f = Fixture::new("engine-fixes-bytes");
    for merge in [false, true] {
        for (spec, imp, code) in [
            (vec![long_row(65536, 65536)], vec![long_row(65536, 65536)], 0),
            (vec![long_row(65536, 65536)], vec![long_row(65536, 0)], 1),
            (vec![], vec![long_row(65536, 65536)], 1),
            (vec![json!({})], vec![long_row(65536, 65536)], 2),
        ] {
            let s = f.file("s.jsonl", spec);
            let i = f.file("i.jsonl", imp);
            let run = |binary: &str| {
                let mut cmd = Command::new(binary);
                cmd.env("LD_PRELOAD", &shim);
                if merge {
                    cmd.arg("--merge");
                }
                cmd.arg(&s).arg(&i).output().expect("conformance: run join")
            };
            let old = run(&base);
            let new = run(env!("CARGO_BIN_EXE_conf-join"));
            assert_eq!(old.status.code(), Some(code), "conformance: base exit");
            assert_eq!(new.status.code(), old.status.code(), "conformance: exit parity");
            assert_eq!(new.stderr, old.stderr, "conformance: diagnostic byte parity");
            assert_eq!(new.stdout, old.stdout, "conformance: stdout byte parity");
            let text = String::from_utf8(new.stdout).expect("conformance: UTF-8 output");
            assert!(text.contains("peak_rss_kb: 1024\n"), "conformance: active RSS shim");
            assert!(text.contains("wall_ms: 0\n"), "conformance: active clock shim");
        }
    }
}
