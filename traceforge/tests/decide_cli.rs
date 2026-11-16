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
        let head = json!({"format":1,"tool":"traceforge","program":"req","size":"2",
            "visible":["A","B"],"model":"p2p","enumeration":"complete","encoding":1});
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
