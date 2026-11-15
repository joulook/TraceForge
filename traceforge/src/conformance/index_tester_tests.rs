//! `ENG-INDEX`'s tests, the tester's (`criteria/ENG-INDEX.md` EI-0.3, EI-1.1; the derivation
//! `log/dev/ENG-INDEX.derived.md` §3). A child of `compact_tests`, for its fixtures.
//!
//! **What doesn't change, field by field.** The base's resolution is the creation-order scan
//! of a bucket's slots; a constant value key makes each bucket one chain in creation order,
//! which is that scan. So the base's history is the fix's history under `with_test_key(|_| 0)`.
//! On the size-2 cells, every answer, id, iteration order and counter but `sig_tests` must be
//! equal between the constant key and the production key, and `sig_tests` no larger.

use super::*;
use crate::conformance::compact::SigLookup;
use crate::conformance::sig::{with_test_key, SigBuckets};

fn constant(_: &Sig) -> u64 {
    0
}

/// Everything a history shows: the answers, the iteration orders, the stats but
/// `sig_tests` (returned apart), on the set, compact and frozen indices and `SigBuckets`.
fn history(spec: &[CompactSummary], imp: &[CompactSummary]) -> (Vec<String>, [usize; 4]) {
    let mut out = Vec::new();
    let mut set = SetIndex::new();
    let mut compact = CompactIndex::new(false);
    for s in spec {
        out.push(format!("set insert {:?}", set.insert(s)));
        out.push(format!("compact insert {:?}", compact.insert(s)));
    }
    for q in imp.iter().chain(spec) {
        out.push(format!("set covers {:?}", set.covers(q)));
        out.push(format!("compact covers {:?}", compact.covers(q)));
    }
    let mut st = set.stats().clone();
    let set_tests = st.sig_tests;
    st.sig_tests = 0;
    out.push(format!("set stats {st:?}"));
    let mut ct = compact.stats().clone();
    let compact_tests = ct.sig_tests;
    ct.sig_tests = 0;
    out.push(format!("compact stats {ct:?}"));
    for e in set.entries() {
        out.push(format!("set entry {e:?}"));
    }
    let (table, store) = set.freeze();
    let mut frozen_tests = 0;
    for q in imp.iter().chain(spec) {
        let r = table.resolve(q.hash, &q.sig, &mut frozen_tests);
        out.push(format!("frozen {r:?}"));
        if let SigLookup::Found(id) = r {
            out.push(format!("store {:?}", store.covers(id, &q.ord).0));
        }
    }
    for e in table.entries() {
        out.push(format!("table entry {e:?}"));
    }
    let mut buckets: SigBuckets<usize> = SigBuckets::new();
    let mut n = 0;
    for s in spec {
        let slot = buckets.entry(s.sig.clone(), || {
            n += 1;
            n
        });
        out.push(format!("sigbuckets {slot}"));
    }
    for q in imp {
        out.push(format!("sigbuckets get {:?}", buckets.get(&q.sig)));
    }
    (out, [set_tests, compact_tests, frozen_tests, n])
}

#[test]
fn eit1_the_constant_key_is_the_base_and_nothing_but_sig_tests_moves() {
    let mut bad = Vec::new();
    for name in SIZE2_CELLS {
        let (spec, imp) = kept_summaries(&fx(name));
        let mut base = None;
        with_test_key(constant, || base = Some(history(&spec, &imp)));
        let (b, bt) = base.unwrap();
        let (f, ft) = history(&spec, &imp);
        if b != f {
            let at = b.iter().zip(&f).position(|(x, y)| x != y);
            bad.push(format!("{name}: first difference at {at:?} of {}", b.len()));
        }
        for k in 0..3 {
            if ft[k] > bt[k] {
                bad.push(format!(
                    "{name}: sig_tests {k} rose: {} against {}",
                    ft[k], bt[k]
                ));
            }
        }
        let _ = std::io::Write::write_fmt(
            &mut std::io::stderr(),
            format_args!(
                "EIT1 {name}: {} answers, sig_tests base {bt:?} fix {ft:?}\n",
                b.len()
            ),
        );
    }
    assert!(bad.is_empty(), "conformance: ENG-INDEX: {bad:#?}");
}

/// One visible thread sending one value: one shape for every value of a type.
fn one(v: crate::Val) -> CompactSummary {
    use crate::conformance::morphism::Status;
    use crate::conformance::obs::Obs;
    let sig = Sig::from_words(
        [("a".into(), Status::Done)].into(),
        [("a".into(), vec![Obs::Send(v)])].into(),
    );
    CompactSummary {
        hash: sig.hash128(),
        sig,
        ord: OrdCounts::U8(vec![]),
        sig_est: 48,
    }
}

/// The same check where the key matters: 2 000 signatures of one shape, `u64` and `String`
/// values, each inserted, queried, re-inserted. Everything but `sig_tests` equal to the
/// constant key's; `sig_tests` far below it.
#[test]
fn eit2_one_shape_nothing_but_sig_tests_moves() {
    let spec: Vec<CompactSummary> = (0..1000u64)
        .map(|i| one(crate::Val::new(i)))
        .chain((0..1000u64).map(|i| one(crate::Val::new(format!("s{i}")))))
        .collect();
    let imp: Vec<CompactSummary> = (500..1500u64)
        .map(|i| one(crate::Val::new(i)))
        .chain(spec.iter().cloned())
        .collect();
    let mut base = None;
    with_test_key(constant, || base = Some(history(&spec, &imp)));
    let (b, bt) = base.unwrap();
    let (f, ft) = history(&spec, &imp);
    assert_eq!(
        b.len(),
        f.len(),
        "conformance: ENG-INDEX: the histories' lengths"
    );
    let at = b.iter().zip(&f).position(|(x, y)| x != y);
    assert_eq!(at, None, "conformance: ENG-INDEX: first difference");
    let _ = std::io::Write::write_fmt(
        &mut std::io::stderr(),
        format_args!("EIT2 sig_tests constant key {bt:?} production {ft:?}\n"),
    );
    for k in 0..3 {
        assert!(
            ft[k] * 100 < bt[k],
            "conformance: ENG-INDEX: {k}: {ft:?} against {bt:?}"
        );
    }
}
