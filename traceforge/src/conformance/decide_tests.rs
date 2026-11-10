//! `DECIDE`'s tests: the paper's two examples (early answer: violation with
//! its witness; first request: false alarm), the shortcuts `k = 0` and
//! `k = 1`, a randomized cross-check against brute-force enumeration of linear
//! extensions, and `conf-join --decide` on scratch files (the in-memory and the
//! merge paths). Orders are written as the exports' count vectors.

use crate::conformance::decide::{contained, decide, extends, Outcome, Pos};
use crate::conformance::interchange::{conf_join_decide, conf_join_merge_decide, MissClass};
use std::path::{Path, PathBuf};

// Four one-event threads, sorted names `a`, `b`, `ra`, `rb`: `a` sends A, `b`
// sends B, `ra` receives A, `rb` receives B. Count vector, event-major: `a`'s
// counts of (b, ra, rb), `b`'s of (a, ra, rb), `ra`'s of (a, b, rb), `rb`'s
// of (a, b, ra).
const LENS4: [usize; 4] = [1, 1, 1, 1];
/// Σ0 = {a<rA, b<rB}.
const S0: [u16; 12] = [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0];
/// Σ1 = {a<rA, b<rB, a<rB}.
const S1: [u16; 12] = [0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0];
/// Σ2 = {a<rA, b<rB, b<rA}.
const S2: [u16; 12] = [0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0];
/// Σ = all four pairs.
const SALL: [u16; 12] = [0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0];
const A: Pos = (0, 0);
const B: Pos = (1, 0);
const RA: Pos = (2, 0);
const RB: Pos = (3, 0);

#[test]
fn decide_early_answer_is_a_violation_with_its_witness() {
    assert!(
        !contained(&SALL, &S1),
        "conformance: decide: Σ1 is uncovered"
    );
    let d = decide(&LENS4, &S1, &[SALL.to_vec()], 1000);
    assert_eq!(
        d.outcome,
        Outcome::Violation(vec![A, RA, B, RB]),
        "conformance: decide: snd A, rcv A, snd B, rcv B"
    );
    assert_eq!(d.group, 1);
}

#[test]
fn decide_first_request_is_a_false_alarm() {
    assert!(!contained(&S1, &S0) && !contained(&S2, &S0));
    let d = decide(&LENS4, &S0, &[S1.to_vec(), S2.to_vec()], 1000);
    assert_eq!(
        d.outcome,
        Outcome::FalseAlarm,
        "conformance: decide: first request"
    );
    assert_eq!((d.group, d.effective), (2, 2));
}

#[test]
fn decide_k0_is_a_violation() {
    let d = decide(&LENS4, &S0, &[], 1000);
    let Outcome::Violation(w) = &d.outcome else {
        panic!("conformance: decide: k = 0: {d:?}");
    };
    assert!(
        extends(&LENS4, &S0, w),
        "conformance: decide: k = 0: an extension of Σ0"
    );
    assert_eq!((d.group, d.states), (0, 0));
}

#[test]
fn decide_k1_uncovered_is_a_violation() {
    // Every one-order group against every candidate it does not cover.
    let all = [S0, S1, S2, SALL];
    for cand in &all {
        for r in &all {
            if contained(r, cand) {
                continue;
            }
            let d = decide(&LENS4, cand, &[r.to_vec()], 1000);
            let Outcome::Violation(w) = &d.outcome else {
                panic!("conformance: decide: k = 1: {cand:?} vs {r:?}: {d:?}");
            };
            assert!(extends(&LENS4, cand, w) && !extends(&LENS4, r, w));
            assert_eq!(d.states, 0, "conformance: decide: k = 1 is a shortcut");
        }
    }
}

#[test]
fn decide_budget_exhausted_is_unresolved() {
    // Σ0 against {Σ1, Σ2} needs more than one state.
    let d = decide(&LENS4, &S0, &[S1.to_vec(), S2.to_vec()], 1);
    assert_eq!(d.outcome, Outcome::Unresolved);
}

// The paper's examples as written (Astra r1): two clients, sorted roles `A`,
// `B`, each `[snd, rcv ok]`. Count vector: `A`'s two events' counts of `B`,
// then `B`'s two events' counts of `A`.
const LENS2: [usize; 2] = [2, 2];
/// Σ0: no cross edge.
const P0: [u16; 4] = [0, 0, 0, 0];
/// Σ1: snd A before rcv B.
const P1: [u16; 4] = [0, 0, 0, 1];
/// Σ2: snd B before rcv A.
const P2: [u16; 4] = [0, 1, 0, 0];
/// Σ: both.
const PALL: [u16; 4] = [0, 1, 0, 1];

#[test]
fn decide_paper_early_answer_two_clients() {
    assert!(!contained(&PALL, &P1));
    let d = decide(&LENS2, &P1, &[PALL.to_vec()], 1000);
    assert_eq!(
        d.outcome,
        Outcome::Violation(vec![(0, 0), (0, 1), (1, 0), (1, 1)]),
        "conformance: decide: early answer: snd A, rcv A, snd B, rcv B"
    );
}

#[test]
fn decide_paper_first_request_two_clients() {
    assert!(!contained(&P1, &P0) && !contained(&P2, &P0));
    let d = decide(&LENS2, &P0, &[P1.to_vec(), P2.to_vec()], 1000);
    assert_eq!(
        d.outcome,
        Outcome::FalseAlarm,
        "conformance: decide: first request"
    );
    assert_eq!((d.group, d.effective), (2, 2));
}

/// The count vector of the total order `seq` (every position once).
fn total(lens: &[usize], seq: &[Pos]) -> Vec<u16> {
    let t = lens.len();
    let mut seen = vec![0u16; t];
    let mut row: Vec<Vec<Vec<u16>>> = lens.iter().map(|&l| vec![vec![0; t]; l]).collect();
    for &(u, i) in seq {
        row[u][i] = seen.clone();
        seen[u] += 1;
    }
    let mut out = Vec::new();
    for u in 0..t {
        for i in 0..lens[u] {
            for v in 0..t {
                if v != u {
                    out.push(row[u][i][v]);
                }
            }
        }
    }
    out
}

/// Every interleaving of `lens`, in lexicographic order of thread choices.
fn interleavings(lens: &[usize]) -> Vec<Vec<Pos>> {
    fn go(lens: &[usize], c: &mut Vec<usize>, w: &mut Vec<Pos>, out: &mut Vec<Vec<Pos>>) {
        if w.len() == lens.iter().sum::<usize>() {
            out.push(w.clone());
            return;
        }
        for t in 0..lens.len() {
            if c[t] < lens[t] {
                w.push((t, c[t]));
                c[t] += 1;
                go(lens, c, w, out);
                c[t] -= 1;
                w.pop();
            }
        }
    }
    let mut out = Vec::new();
    go(lens, &mut vec![0; lens.len()], &mut Vec::new(), &mut out);
    out
}

#[test]
fn decide_multiword_live_set_matches_brute_force() {
    // Three two-event threads, no cross edge in the candidate; the group is
    // made of distinct total orders (pairwise incomparable, each compatible
    // with the candidate and none contained in it), so none is pruned and
    // the live set spans two u64 words.
    let lens = [2usize, 2, 2];
    let cand = vec![0u16; 12];
    let all: Vec<Vec<u16>> = interleavings(&lens)
        .iter()
        .map(|w| total(&lens, w))
        .collect();
    assert_eq!(all.len(), 90);
    for k in [70usize, 90] {
        let group = all[..k].to_vec();
        assert!(group.iter().all(|r| !contained(r, &cand)));
        let d = decide(&lens, &cand, &group, 10_000_000);
        assert_eq!(d.effective, k, "conformance: decide: no order pruned");
        let want = brute(&lens, &cand, &group);
        match &d.outcome {
            Outcome::Violation(w) => {
                assert!(
                    want && k == 70,
                    "conformance: decide: k = {k}: brute says false alarm"
                );
                assert!(extends(&lens, &cand, w));
                assert!(!group.iter().any(|r| extends(&lens, r, w)));
            }
            Outcome::FalseAlarm => {
                assert!(
                    !want && k == 90,
                    "conformance: decide: k = {k}: brute says violation"
                )
            }
            Outcome::Unresolved => panic!("conformance: decide: k = {k}: unresolved"),
        }
    }
}

// ------------------------------------------------- randomized cross-check --

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// A random order over `lens` as its count vector: a random interleaving
/// (a linear extension of `base` if given) and random cross edges along it,
/// with `base`'s edges, closed transitively.
fn gen(lens: &[usize], rng: &mut Rng, base: Option<&[u16]>) -> Vec<u16> {
    let t = lens.len();
    let n: usize = lens.iter().sum();
    let mut c = vec![0u16; t];
    let mut seq: Vec<Pos> = Vec::with_capacity(n);
    while seq.len() < n {
        let ok: Vec<usize> = (0..t)
            .filter(|&u| {
                (c[u] as usize) < lens[u]
                    && base.map_or(true, |b| {
                        let mut w = seq.clone();
                        w.push((u, c[u] as usize));
                        prefix_ok(lens, b, &w)
                    })
            })
            .collect();
        let u = ok[rng.below(ok.len())];
        seq.push((u, c[u] as usize));
        c[u] += 1;
    }
    let base_pred = base.map(|b| pred_table(lens, b));
    // pc[(t, i)][u]: u-events before (t, i).
    let mut pc: Vec<Vec<Vec<u16>>> = lens.iter().map(|&l| vec![vec![0u16; t]; l]).collect();
    for (k, &(et, ei)) in seq.iter().enumerate() {
        let mut row = vec![0u16; t];
        row[et] = ei as u16;
        for &(ft, fi) in &seq[..k] {
            let in_base = base_pred
                .as_ref()
                .map_or(false, |bp| bp[et][ei][ft] as usize > fi);
            let po = ft == et;
            if po || in_base || rng.below(10) < 3 {
                row[ft] = row[ft].max(fi as u16 + 1);
                let f = pc[ft][fi].clone();
                for u in 0..t {
                    row[u] = row[u].max(f[u]);
                }
            }
        }
        pc[et][ei] = row;
    }
    let mut out = Vec::new();
    for u in 0..t {
        for i in 0..lens[u] {
            for v in 0..t {
                if v != u {
                    out.push(pc[u][i][v]);
                }
            }
        }
    }
    out
}

fn pred_table(lens: &[usize], counts: &[u16]) -> Vec<Vec<Vec<u16>>> {
    let t = lens.len();
    let mut it = counts.iter();
    (0..t)
        .map(|u| {
            (0..lens[u])
                .map(|i| {
                    (0..t)
                        .map(|v| {
                            if v == u {
                                i as u16
                            } else {
                                *it.next().unwrap()
                            }
                        })
                        .collect()
                })
                .collect()
        })
        .collect()
}

/// Whether `w` is a prefix of some linear extension of `counts`.
fn prefix_ok(lens: &[usize], counts: &[u16], w: &[Pos]) -> bool {
    let p = pred_table(lens, counts);
    let mut c = vec![0u16; lens.len()];
    for &(t, i) in w {
        if (0..lens.len()).any(|u| u != t && p[t][i][u] > c[u]) {
            return false;
        }
        c[t] += 1;
    }
    true
}

/// Brute force: whether some linear extension of `cand` extends no order of
/// `group`.
fn brute(lens: &[usize], cand: &[u16], group: &[Vec<u16>]) -> bool {
    fn go(
        lens: &[usize],
        cand: &[u16],
        group: &[Vec<u16>],
        w: &mut Vec<Pos>,
        c: &mut Vec<usize>,
    ) -> bool {
        if w.len() == lens.iter().sum::<usize>() {
            return !group.iter().any(|r| extends(lens, r, w));
        }
        for t in 0..lens.len() {
            if c[t] < lens[t] {
                w.push((t, c[t]));
                if prefix_ok(lens, cand, w) {
                    c[t] += 1;
                    let hit = go(lens, cand, group, w, c);
                    c[t] -= 1;
                    if hit {
                        w.pop();
                        return true;
                    }
                }
                w.pop();
            }
        }
        false
    }
    go(lens, cand, group, &mut Vec::new(), &mut vec![0; lens.len()])
}

#[test]
fn decide_matches_brute_force_on_random_instances() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let (mut cases, mut violations, mut false_alarms) = (0, 0, 0);
    for _ in 0..20_000 {
        if cases == 600 {
            break;
        }
        let t = 2 + rng.below(2);
        let mut lens: Vec<usize> = (0..t).map(|_| rng.below(4)).collect();
        while lens.iter().sum::<usize>() > 6 {
            let u = rng.below(t);
            lens[u] = lens[u].saturating_sub(1);
        }
        let cand = gen(&lens, &mut rng, None);
        let k = rng.below(4);
        let group: Vec<Vec<u16>> = (0..k)
            .map(|_| {
                if rng.below(2) == 0 {
                    gen(&lens, &mut rng, Some(&cand))
                } else {
                    gen(&lens, &mut rng, None)
                }
            })
            .collect();
        if group.iter().any(|r| contained(r, &cand)) {
            continue; // covered: not a candidate of the post-pass
        }
        cases += 1;
        let d = decide(&lens, &cand, &group, 1_000_000);
        let want = brute(&lens, &cand, &group);
        match &d.outcome {
            Outcome::Violation(w) => {
                assert!(
                    want,
                    "conformance: decide: {lens:?} {cand:?} {group:?}: brute says false alarm"
                );
                assert!(
                    extends(&lens, &cand, w),
                    "conformance: decide: witness not an extension"
                );
                assert!(
                    !group.iter().any(|r| extends(&lens, r, w)),
                    "conformance: decide: witness extends a group order"
                );
                violations += 1;
            }
            Outcome::FalseAlarm => {
                assert!(
                    !want,
                    "conformance: decide: {lens:?} {cand:?} {group:?}: brute says violation"
                );
                false_alarms += 1;
            }
            Outcome::Unresolved => panic!("conformance: decide: unresolved on a small instance"),
        }
    }
    eprintln!("decide random: {cases} cases, {violations} violations, {false_alarms} false alarms");
    assert_eq!(cases, 600, "conformance: decide: enough uncovered cases");
    assert!(
        false_alarms >= 10 && violations >= 10,
        "conformance: decide: both outcomes exercised"
    );
}

// ------------------------------------------------------------ conf-join --

const HEAD4: &str = r#"{"format":1,"tool":"traceforge","program":"req","size":"2","visible":["a","b","ra","rb"],"model":"p2p","enumeration":"complete","encoding":1}"#;

fn line4(counts: &[u16]) -> String {
    let cs: Vec<String> = counts.iter().map(u16::to_string).collect();
    format!(
        concat!(
            r#"{{"statuses":{{"a":"done","b":"done","ra":"done","rb":"done"}},"#,
            r#""words":{{"a":[{{"s":"A"}}],"b":[{{"s":"B"}}],"ra":[{{"r":"A"}}],"rb":[{{"r":"B"}}]}},"#,
            r#""counts":[{}]}}"#
        ),
        cs.join(",")
    )
}

fn write(dir: &Path, name: &str, lines: &[String]) -> PathBuf {
    let mut l = lines.to_vec();
    l.sort_unstable();
    let p = dir.join(name);
    std::fs::write(&p, format!("{HEAD4}\n{}\n", l.join("\n"))).unwrap();
    p
}

#[test]
fn decide_conf_join_both_paths() {
    let dir = std::env::temp_dir().join(format!("decide-tests-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    // Early answer: Σ1 against {Σ}; first request: Σ0 against {Σ1, Σ2}.
    let early = (
        write(&dir, "s1.jsonl", &[line4(&SALL)]),
        write(&dir, "i1.jsonl", &[line4(&S1)]),
    );
    let first = (
        write(&dir, "s2.jsonl", &[line4(&S1), line4(&S2)]),
        write(&dir, "i2.jsonl", &[line4(&S0)]),
    );
    for merge in [false, true] {
        let run = |s: &Path, i: &Path| {
            if merge {
                conf_join_merge_decide(s, i, 1000)
            } else {
                conf_join_decide(s, i, 1000)
            }
            .unwrap()
        };
        let r = run(&early.0, &early.1);
        assert_eq!(r.exit_code(), 1);
        assert_eq!(r.uncovered[0].0, MissClass::NotFound);
        let d = r.decide.as_ref().unwrap();
        assert_eq!(
            (d.violations, d.false_alarms, d.unresolved, d.max_group),
            (1, 0, 0, 1)
        );
        let text = r.render();
        assert!(
            text.contains(
                r#"  witness: a:{"s":"A"} ra:{"r":"A"} b:{"s":"B"} rb:{"r":"B"} ; statuses: a=done b=done ra=done rb=done"#
            ),
            "{text}"
        );
        assert!(r.measurements(0).contains("decide_violations: 1\n"));
        let r = run(&first.0, &first.1);
        assert_eq!(
            r.exit_code(),
            1,
            "conformance: decide: the exit code is the join's"
        );
        let d = r.decide.as_ref().unwrap();
        assert_eq!((d.violations, d.false_alarms, d.max_group), (0, 1, 2));
        assert!(
            r.render().contains("  decide: false-alarm k=2 k_min=2"),
            "{}",
            r.render()
        );
        // A signature the specification lacks (no-slot) is k = 0: a violation.
        let other = write(
            &dir,
            "i3.jsonl",
            &[line4(&S0).replace(r#"{"r":"B"}"#, r#"{"r":"C"}"#)],
        );
        let r = run(&first.0, &other);
        assert_eq!(r.uncovered[0].0, MissClass::NoSlot);
        let d = r.decide.as_ref().unwrap();
        assert_eq!((d.violations, d.max_group), (1, 0));
    }
    // Without --decide the report is unchanged.
    let plain = crate::conformance::interchange::conf_join(&early.0, &early.1).unwrap();
    assert!(plain.decide.is_none() && !plain.render().contains("decide"));
    assert!(!plain.measurements(0).contains("decide_"));
    let _ = std::fs::remove_dir_all(&dir);
}
