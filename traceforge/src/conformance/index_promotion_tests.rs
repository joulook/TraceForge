use super::*;
use crate::conformance::morphism::Status;
use crate::conformance::obs::Obs;
use crate::conformance::sig::{with_test_key, SigBuckets};
use crate::Val;

thread_local! {
    static COMPARISONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[derive(Clone, Debug)]
struct Value(usize);
impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        COMPARISONS.with(|n| n.set(n.get() + 1));
        self.0 == other.0
    }
}

fn summary(i: usize) -> CompactSummary {
    let sig = Sig::from_words(
        [("a".into(), Status::Done)].into(),
        [("a".into(), vec![Obs::Send(Val::new(Value(i)))])].into(),
    );
    CompactSummary {
        hash: sig.hash128(),
        sig,
        ord: OrdCounts::U8(vec![]),
        sig_est: 48,
    }
}

fn chain(chain: &SlotChain, n: usize) {
    assert_eq!(
        chain.iter().copied().collect::<Vec<_>>(),
        (0..n).collect::<Vec<_>>()
    );
    assert_eq!(matches!(chain, SlotChain::One(0)), n == 1);
}

#[test]
fn promotion_preserves_slots_order_answers_and_comparisons() {
    with_test_key(
        |_| 0,
        || {
            let mut compact = CompactIndex::new(false);
            let mut set = SetIndex::new();
            let mut worker = WorkerTable::new();
            let mut buckets = SigBuckets::new();
            for i in 0..3 {
                let s = summary(i);
                let before = compact.stats().sig_tests;
                assert_eq!(compact.insert(&s), (i as u32, Inserted::Stored(i as u64)));
                assert_eq!(compact.stats().sig_tests - before, i);
                let before = set.stats().sig_tests;
                assert_eq!(set.insert(&s), (i as u32, Inserted::Stored(i as u64)));
                assert_eq!(set.stats().sig_tests - before, i);
                let before = worker.sig_tests;
                let expected = if i == 0 {
                    SigLookup::NoBucket
                } else {
                    SigLookup::NoSig
                };
                assert_eq!(worker.resolve(s.hash, &s.sig), expected);
                assert_eq!(worker.sig_tests - before, i);
                worker.add(s.hash, i as u32, s.sig.clone());
                COMPARISONS.with(|n| n.set(0));
                assert_eq!(*buckets.entry(s.sig.clone(), || i), i);
                assert_eq!(COMPARISONS.with(|n| n.get()), i);
                assert_eq!(buckets.len(), i + 1);
                let frozen = set.clone().freeze().0;
                chain(&compact.buckets[&s.hash].chains[&0], i + 1);
                chain(&set.buckets[&s.hash].chains[&0], i + 1);
                chain(&worker.chains[&s.hash][&0], i + 1);
                chain(&frozen.chains[&s.hash][&0], i + 1);
                for j in 0..=i + 1 {
                    let q = summary(j);
                    let present = j <= i;
                    let cost = if present { j + 1 } else { i + 1 };
                    let answer = if present {
                        (Some(j as u32), Covers::Found(j as u64))
                    } else {
                        (None, Covers::NoSig)
                    };
                    let before = compact.stats().sig_tests;
                    assert_eq!(compact.covers(&q), answer);
                    assert_eq!(compact.stats().sig_tests - before, cost);
                    let before = set.stats().sig_tests;
                    assert_eq!(set.covers(&q), answer);
                    assert_eq!(set.stats().sig_tests - before, cost);
                    let lookup = if present {
                        SigLookup::Found(j as u32)
                    } else {
                        SigLookup::NoSig
                    };
                    let mut tests = 0;
                    assert_eq!(frozen.resolve(q.hash, &q.sig, &mut tests), lookup);
                    assert_eq!(tests, cost);
                    let before = worker.sig_tests;
                    assert_eq!(worker.resolve(q.hash, &q.sig), lookup);
                    assert_eq!(worker.sig_tests - before, cost);
                    COMPARISONS.with(|n| n.set(0));
                    assert_eq!(buckets.get(&q.sig).copied(), present.then_some(j));
                    assert_eq!(COMPARISONS.with(|n| n.get()), cost);
                }
            }
        },
    );
}
