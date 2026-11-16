//! `DECIDE` (owner's decision, 2026-11-10): the post-pass of `conf-join
//! --decide`, which classifies each uncovered candidate summary as a violation
//! or a false alarm (`PLDI/tex/problem.tex`, Proposition `prop:decide`).
//!
//! A summary's order `O` is read from its count vector (`SUMMARY-FORMAT.md`):
//! `pred[(t, i)][u]` is the number of visible events of thread `u` before the
//! event `(t, i)`, and `pred[(t, i)][t] = i`. Containment of orders is the
//! pointwise `≤` of the count vectors. The candidate `O` is a violation iff some
//! linear extension of `O` extends none of the group's orders `O_1 .. O_k`
//! (equivalently: one pair of each `O_i \ O` can be reversed in `O` at once,
//! acyclically); that extension, labelled, is the witness. Otherwise it is a
//! false alarm.
//!
//! The search (after `consult38-opus/exact.py`): a depth-first search over the
//! ideals (prefixes) of `O`, carrying the set of group orders the prefix still
//! respects; a state whose ideal was already explored with a subset of its
//! live set is pruned (the subset dominates). An exhausted state budget gives
//! `Unresolved`, never a guess.

use std::collections::HashMap;

/// The default state budget per candidate (`--decide-budget`).
pub const DEFAULT_DECIDE_BUDGET: u64 = 10_000_000;

/// A position: the thread's index in sorted-name order, the event's index in
/// the thread's word.
pub(crate) type Pos = (usize, usize);

/// The classification of one uncovered candidate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Outcome {
    /// A witness: every visible position once, a linear extension of the
    /// candidate's order that extends none of the group's orders.
    Violation(Vec<Pos>),
    FalseAlarm,
    /// The state budget ran out.
    Unresolved,
}

impl Outcome {
    pub(crate) fn word(&self) -> &'static str {
        match self {
            Outcome::Violation(_) => "violation",
            Outcome::FalseAlarm => "false-alarm",
            Outcome::Unresolved => "unresolved",
        }
    }
}

/// One decision with its counters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Decision {
    pub(crate) outcome: Outcome,
    /// `k`: the group's orders as given.
    pub(crate) group: usize,
    /// The orders left after dropping those incompatible with the candidate
    /// and the non-minimal ones.
    pub(crate) effective: usize,
    /// Search states visited (0 for the shortcuts).
    pub(crate) states: u64,
}

/// The positions' layout of one signature.
struct Layout {
    lens: Vec<usize>,
    off: Vec<usize>,
    t: usize,
    n: usize,
}

impl Layout {
    fn new(lens: &[usize]) -> Self {
        let mut off = Vec::with_capacity(lens.len());
        let mut n = 0;
        for l in lens {
            off.push(n);
            n += l;
        }
        Layout {
            lens: lens.to_vec(),
            off,
            t: lens.len(),
            n,
        }
    }

    /// The `pred` table (event-major, `t` entries per event) of a count vector.
    fn pred(&self, counts: &[u16]) -> Vec<u16> {
        assert_eq!(
            counts.len(),
            self.n * self.t.saturating_sub(1),
            "conformance: decide: a count vector of the wrong length"
        );
        let mut p = vec![0u16; self.n * self.t];
        let mut it = counts.iter();
        for t in 0..self.t {
            for i in 0..self.lens[t] {
                let e = self.off[t] + i;
                for u in 0..self.t {
                    p[e * self.t + u] = if u == t {
                        i as u16
                    } else {
                        *it.next().unwrap()
                    };
                }
            }
        }
        p
    }

    /// Whether `(t, c[t])` exists and may follow the ideal `c` under `p`.
    fn can_add(&self, p: &[u16], c: &[u16], t: usize) -> bool {
        if c[t] as usize >= self.lens[t] {
            return false;
        }
        let e = self.off[t] + c[t] as usize;
        let row = &p[e * self.t..(e + 1) * self.t];
        (0..self.t).all(|u| u == t || row[u] <= c[u])
    }

    /// Completes the prefix `(c, w)` to a linear extension of `p`, with the
    /// extra edge `before.0 < before.1` if given; `None` if the relation is
    /// cyclic.
    fn complete(
        &self,
        p: &[u16],
        mut c: Vec<u16>,
        mut w: Vec<Pos>,
        before: Option<(Pos, Pos)>,
    ) -> Option<Vec<Pos>> {
        while w.len() < self.n {
            let t = (0..self.t).find(|&t| {
                self.can_add(p, &c, t)
                    && match before {
                        Some((e, a)) if a == (t, c[t] as usize) => c[e.0] as usize > e.1,
                        _ => true,
                    }
            })?;
            w.push((t, c[t] as usize));
            c[t] += 1;
        }
        Some(w)
    }

    /// Whether `p ∪ q` is acyclic (some linear extension of both exists).
    fn compatible(&self, p: &[u16], q: &[u16]) -> bool {
        let mut c = vec![0u16; self.t];
        for _ in 0..self.n {
            match (0..self.t).find(|&t| self.can_add(p, &c, t) && self.can_add(q, &c, t)) {
                Some(t) => c[t] += 1,
                None => return false,
            }
        }
        true
    }
}

/// `ord(r) ⊆ ord(q)`: pointwise `≤` of the count vectors.
pub(crate) fn contained(r: &[u16], q: &[u16]) -> bool {
    r.len() == q.len() && r.iter().zip(q).all(|(a, b)| a <= b)
}

/// The k = 1 shortcut: a pair `(a, e)` of `O_1 \ O` reversed in `O`.
fn reverse_one(lay: &Layout, p: &[u16], cand: &[u16], r: &[u16]) -> Option<Vec<Pos>> {
    let mut j = 0;
    for t in 0..lay.t {
        for i in 0..lay.lens[t] {
            for u in 0..lay.t {
                if u == t {
                    continue;
                }
                if r[j] > cand[j] {
                    // `(u, r[j] - 1)` precedes `(t, i)` in `O_1`, not in `O`.
                    let a = (u, r[j] as usize - 1);
                    return lay.complete(p, vec![0; lay.t], Vec::new(), Some(((t, i), a)));
                }
                j += 1;
            }
        }
    }
    None
}

/// Decides one uncovered candidate: `lens` its words' lengths (sorted-name
/// order), `cand` its count vector, `group` the count vectors of the
/// specification's summaries of its signature, `budget` the state budget.
pub(crate) fn decide(lens: &[usize], cand: &[u16], group: &[Vec<u16>], budget: u64) -> Decision {
    let lay = Layout::new(lens);
    let p = lay.pred(cand);
    let k = group.len();
    let done = |outcome, effective, states| Decision {
        outcome,
        group: k,
        effective,
        states,
    };
    let linear = |lay: &Layout| {
        lay.complete(&p, vec![0; lay.t], Vec::new(), None)
            .expect("conformance: decide: a summary's order is acyclic")
    };
    if k == 0 {
        return done(Outcome::Violation(linear(&lay)), 0, 0);
    }
    if k == 1 && !contained(&group[0], cand) {
        let w = reverse_one(&lay, &p, cand, &group[0])
            .expect("conformance: decide: a reversed pair outside O is acyclic");
        return done(Outcome::Violation(w), 1, 0);
    }
    // Drop the orders no extension of `O` can respect, then the non-minimal
    // ones (breaking `r ⊆ q` breaks `q`); of equal orders the first stays.
    let preds: Vec<Vec<u16>> = group.iter().map(|q| lay.pred(q)).collect();
    let live: Vec<usize> = (0..k).filter(|&j| lay.compatible(&p, &preds[j])).collect();
    let minimal: Vec<usize> = live
        .iter()
        .copied()
        .filter(|&j| {
            !live.iter().any(|&i| {
                i != j
                    && contained(&group[i], &group[j])
                    && (!contained(&group[j], &group[i]) || i < j)
            })
        })
        .collect();
    let m = minimal.len();
    if m == 0 {
        return done(Outcome::Violation(linear(&lay)), 0, 0);
    }
    if m == 1 && !contained(&group[minimal[0]], cand) {
        let w = reverse_one(&lay, &p, cand, &group[minimal[0]])
            .expect("conformance: decide: a reversed pair outside O is acyclic");
        return done(Outcome::Violation(w), 1, 0);
    }
    let refs: Vec<&[u16]> = minimal.iter().map(|&j| preds[j].as_slice()).collect();
    let words = m.div_ceil(64);
    let mut full = vec![!0u64; words];
    if m % 64 != 0 {
        full[words - 1] = (1u64 << (m % 64)) - 1;
    }
    let mut seen: HashMap<Vec<u16>, Vec<Vec<u64>>> = HashMap::new();
    let mut stack: Vec<(Vec<u16>, Vec<u64>, Vec<Pos>)> = vec![(vec![0; lay.t], full, Vec::new())];
    let mut states = 0u64;
    while let Some((c, alive, w)) = stack.pop() {
        if alive.iter().all(|x| *x == 0) {
            let w = lay
                .complete(&p, c, w, None)
                .expect("conformance: decide: a prefix of O completes");
            return done(Outcome::Violation(w), m, states);
        }
        let explored = seen.entry(c.clone()).or_default();
        if explored
            .iter()
            .any(|b| b.iter().zip(&alive).all(|(b, a)| b & !a == 0))
        {
            continue;
        }
        explored.push(alive.clone());
        states += 1;
        if states > budget {
            return done(Outcome::Unresolved, m, states);
        }
        let mut next: Vec<(u32, Vec<u16>, Vec<u64>, Vec<Pos>)> = Vec::new();
        for t in 0..lay.t {
            if !lay.can_add(&p, &c, t) {
                continue;
            }
            let mut a2 = alive.clone();
            for (j, r) in refs.iter().enumerate() {
                if a2[j / 64] >> (j % 64) & 1 == 1 && !lay.can_add(r, &c, t) {
                    a2[j / 64] &= !(1u64 << (j % 64));
                }
            }
            let mut c2 = c.clone();
            c2[t] += 1;
            let mut w2 = w.clone();
            w2.push((t, c[t] as usize));
            let ones = a2.iter().map(|x| x.count_ones()).sum();
            next.push((ones, c2, a2, w2));
        }
        // The child with the fewest live orders is popped first.
        next.sort_by(|x, y| y.0.cmp(&x.0));
        stack.extend(next.into_iter().map(|(_, c2, a2, w2)| (c2, a2, w2)));
    }
    done(Outcome::FalseAlarm, m, states)
}

/// Whether `w` is a linear extension of the order of `counts` (tests and the
/// witness check).
pub(crate) fn extends(lens: &[usize], counts: &[u16], w: &[Pos]) -> bool {
    let lay = Layout::new(lens);
    if w.len() != lay.n {
        return false;
    }
    let p = lay.pred(counts);
    let mut c = vec![0u16; lay.t];
    for &(t, i) in w {
        if t >= lay.t || c[t] as usize != i || !lay.can_add(&p, &c, t) {
            return false;
        }
        c[t] += 1;
    }
    true
}
