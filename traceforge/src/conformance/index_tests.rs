//! ENG-INDEX: slot costs and semantics, without graph exploration.
use super::*;
use crate::conformance::morphism::Status;
use crate::conformance::obs::Obs;
use crate::conformance::sig::{with_test_key, SigBuckets};
use crate::Val;
use std::io::Write;

fn summary(value: Val) -> CompactSummary {
    let sig = Sig::from_words(
        [("a".into(), Status::Done)].into(),
        [("a".into(), vec![Obs::Send(value)])].into(),
    );
    CompactSummary {
        hash: sig.hash128(),
        sig,
        ord: OrdCounts::U8(vec![]),
        sig_est: 48,
    }
}

fn integer_key(sig: &Sig) -> u64 {
    let Obs::Send(value) = &sig.word("a")[0] else {
        panic!("conformance: send")
    };
    *value.as_any_ref().downcast_ref::<u64>().unwrap()
}

fn corpus() {
    const N: u64 = 100_000;
    let mut compact = CompactIndex::new(false);
    let mut set = SetIndex::new();
    let shared = SharedCache::new(Capacity::Unbounded);
    let mut writer = WorkerTable::new();
    let mut reader = WorkerTable::new();
    let mut chains = HashMap::<u64, usize>::new();
    let mut comparisons = 0;
    let mut operations = 0;
    for i in 0..N {
        let s = summary(Val::new(i));
        assert_eq!(s.hash, summary(Val::new(0u64)).hash);
        let length = *chains.get(&s.sig.value_key()).unwrap_or(&0);
        let before = compact.stats().sig_tests;
        assert_eq!(compact.insert(&s), (i as u32, Inserted::Stored(i)));
        assert_eq!(
            compact.stats().sig_tests - before,
            length,
            "conformance: compact insert {i}"
        );
        let before = set.stats().sig_tests;
        assert_eq!(set.insert(&s), (i as u32, Inserted::Stored(i)));
        assert_eq!(
            set.stats().sig_tests - before,
            length,
            "conformance: set insert {i}"
        );
        let before = writer.sig_tests;
        assert_eq!(
            shared.admit(&mut writer, &s, &s, || false),
            Admission::Admitted
        );
        assert_eq!(
            writer.sig_tests - before,
            2 * length,
            "conformance: worker insert {i}"
        );
        *chains.entry(s.sig.value_key()).or_default() += 1;
        assert!(
            chains[&s.sig.value_key()] <= 4,
            "conformance: chain bound at {i}"
        );
        comparisons += 4 * length;
        operations += 4;
    }
    let (frozen, _) = set.clone().freeze();
    for i in 0..N {
        let s = summary(Val::new(i));
        // The independent domain key makes every selected chain a singleton.
        let length = chains[&s.sig.value_key()];
        let before = compact.stats().sig_tests;
        assert_eq!(compact.covers(&s), (Some(i as u32), Covers::Found(i)));
        let cost = compact.stats().sig_tests - before;
        assert!(cost >= 1 && cost <= length);
        let before = set.stats().sig_tests;
        assert_eq!(set.covers(&s), (Some(i as u32), Covers::Found(i)));
        assert_eq!(set.stats().sig_tests - before, cost);
        let mut tests = 0;
        assert_eq!(
            frozen.resolve(s.hash, &s.sig, &mut tests),
            SigLookup::Found(i as u32)
        );
        assert_eq!(tests, cost);
        let before = reader.sig_tests;
        assert_eq!(shared.probe(&mut reader, &s).0, CacheProbe::Hit);
        assert_eq!(reader.sig_tests - before, cost);
        let before = compact.stats().sig_tests;
        assert_eq!(compact.insert(&s), (i as u32, Inserted::Duplicate));
        assert_eq!(compact.stats().sig_tests - before, cost);
        let before = set.stats().sig_tests;
        assert_eq!(set.insert(&s), (i as u32, Inserted::Duplicate));
        assert_eq!(set.stats().sig_tests - before, cost);
        let before = writer.sig_tests;
        assert_eq!(
            shared.admit(&mut writer, &s, &s, || false),
            Admission::Redundant
        );
        assert_eq!(writer.sig_tests - before, cost);
        comparisons += 7 * cost;
        operations += 7;
        let absent = summary(Val::new(N + i));
        let length = *chains.get(&absent.sig.value_key()).unwrap_or(&0);
        let before = compact.stats().sig_tests;
        assert_eq!(compact.covers(&absent), (None, Covers::NoSig));
        assert_eq!(compact.stats().sig_tests - before, length);
        let before = set.stats().sig_tests;
        assert_eq!(set.covers(&absent), (None, Covers::NoSig));
        assert_eq!(set.stats().sig_tests - before, length);
        let mut tests = 0;
        assert_eq!(
            frozen.resolve(absent.hash, &absent.sig, &mut tests),
            SigLookup::NoSig
        );
        assert_eq!(tests, length);
        let before = reader.sig_tests;
        assert_eq!(shared.probe(&mut reader, &absent).0, CacheProbe::Miss);
        assert_eq!(reader.sig_tests - before, length);
        comparisons += 4 * length;
        operations += 4;
    }
    let longest = chains.values().copied().max().unwrap();
    let mean = comparisons as f64 / operations as f64;
    let _ = writeln!(
        std::io::stderr(),
        "ENG-INDEX n={N} longest={longest} comparisons={comparisons} \
               operations={operations} mean={mean:.6}"
    );
    assert!(longest <= 4 && mean <= 1.1);
    assert_eq!(shared.absent_slots_for_test(), 0);
}

#[test]
fn ei_injective_100k() {
    with_test_key(integer_key, corpus);
}

#[test]
fn ei_production_100k() {
    corpus();
}

// Equality deliberately ignores the rendering noise.
#[derive(Clone, Debug)]
struct Opaque(u64, u64);
impl PartialEq for Opaque {
    fn eq(&self, other: &Self) -> bool {
        EQUALS.with(|n| n.set(n.get() + 1));
        self.0 == other.0
    }
}
thread_local! {
    static EQUALS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

fn linear_fixture(values: Vec<Val>) {
    let mut oracle: Vec<Sig> = Vec::new();
    let mut compact = CompactIndex::new(false);
    let mut set = SetIndex::new();
    let mut buckets = SigBuckets::new();
    let mut worker = WorkerTable::new();
    for value in values {
        let s = summary(value);
        let position = oracle.iter().position(|held| held == &s.sig);
        let cost = position.map_or(oracle.len(), |i| i + 1);
        let id = position.unwrap_or(oracle.len()) as u32;
        let before = compact.stats().sig_tests;
        let got = compact.insert(&s);
        assert_eq!(got.0, id);
        assert_eq!(compact.stats().sig_tests - before, cost);
        let before = set.stats().sig_tests;
        assert_eq!(set.insert(&s), got);
        assert_eq!(set.stats().sig_tests - before, cost);
        let mut tests = 0;
        let frozen = set.clone().freeze().0;
        assert_eq!(
            frozen.resolve(s.hash, &s.sig, &mut tests),
            SigLookup::Found(id)
        );
        assert_eq!(tests, id as usize + 1);
        if position.is_none() {
            oracle.push(s.sig.clone());
            worker.add(s.hash, id, s.sig.clone());
        }
        let before = worker.sig_tests;
        assert_eq!(worker.resolve(s.hash, &s.sig), SigLookup::Found(id));
        assert_eq!(worker.sig_tests - before, id as usize + 1);
        assert_eq!(*buckets.entry(s.sig.clone(), || id), id);
        assert_eq!(buckets.get(&s.sig), Some(&id));
        assert_eq!(buckets.len(), oracle.len());
    }
    assert_eq!(compact.stats().sig_aliases, 0);
    assert_eq!(set.stats().sig_aliases, 0);
}

#[test]
fn ei_collisions_keep_equality_and_creation_order() {
    with_test_key(
        |_| 0,
        || {
            linear_fixture([1u64, 2, 3, 2, 1, 4].map(Val::new).into());
        },
    );
}

#[test]
fn ei_opaque_and_decval_keep_the_scan() {
    linear_fixture(vec![
        Val::new(Opaque(1, 0)),
        Val::new(Opaque(2, 0)),
        Val::new(Opaque(1, 99)),
        Val::new(Opaque(3, 0)),
    ]);
    use crate::conformance::interchange::DecVal;
    linear_fixture(
        ["1", "2", "1", "3"]
            .map(|s| Val::new(DecVal(s.into())))
            .into(),
    );
}

#[test]
fn ei_sig_buckets_selects_only_its_chain() {
    fn key(sig: &Sig) -> u64 {
        let Obs::Send(v) = &sig.word("a")[0] else {
            panic!("conformance: send")
        };
        v.as_any_ref().downcast_ref::<Opaque>().unwrap().0
    }
    with_test_key(key, || {
        let mut buckets = SigBuckets::new();
        for i in 0..100 {
            let s = summary(Val::new(Opaque(i, 0)));
            EQUALS.with(|n| n.set(0));
            assert_eq!(*buckets.entry(s.sig.clone(), || i), i);
            assert_eq!(EQUALS.with(|n| n.get()), 0);
            assert_eq!(buckets.get(&s.sig), Some(&i));
            assert_eq!(EQUALS.with(|n| n.get()), 1);
        }
    });
}

#[test]
fn ei_sequential_caches_and_owned_insertions() {
    let mut compact = CompactCache::new(Capacity::Unbounded, false, false);
    let mut set = SetCache::new(Capacity::Unbounded);
    let mut owned = SetIndex::new();
    for i in 0..100u64 {
        let s = summary(Val::new(i));
        assert!(compact.admit(&s, &s));
        assert!(set.admit(&s, &s));
        assert_eq!(compact.stats().sig_tests, 0);
        assert_eq!(set.stats().sig_tests, 0);
        assert_eq!(
            owned.slot_for_owned(s.hash, s.sig.clone(), s.sig_est),
            i as usize
        );
        assert_eq!(owned.stats().sig_tests, 0);
    }
    for i in 0..100u64 {
        let s = summary(Val::new(i));
        let before = compact.stats().sig_tests;
        assert_eq!(compact.probe(&s).1, Some(i as u32));
        assert_eq!(compact.stats().sig_tests - before, 1);
        let before = set.stats().sig_tests;
        assert_eq!(set.probe(&s).1, Some(i as u32));
        assert_eq!(set.stats().sig_tests - before, 1);
    }
}
