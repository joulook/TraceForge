//! Replay of a witness graph: one guided execution of the program along the graph.
//!
//! The program runs forward from an empty graph in probe mode, which performs the forced events
//! (thread creation, begin and end, blocking) and parks every thread at its next choice point.
//! The replay then walks the graph in its order: at each step the thread with the smallest index
//! whose next recorded event has all its porf predecessors replayed. That thread's next event in
//! the program, forced or offered, is compared with the recorded one; the first difference stops
//! the replay. An offered event that agrees is taken: a send as offered, a receive from the send
//! the graph's reads-from names (⊥ for `null`), a choice with the graph's raw index. A choice with
//! one option, and the labels the graph format does not carry, are taken without consulting the
//! graph. A thread waiting at a receive or a join is judged only once no thread can go on, so a
//! thread blocked for good meets a recorded BLK. No value is decoded from the graph: sends are
//! compared by their encoding, and every received value is the one the program sent.
//!
//! A panic of the program during a probe ends the replay as a failed run, also when a thread
//! earlier in the order would have deviated first.

use std::collections::HashMap;
use std::sync::Arc;

use serde_json::Value;

use crate::event::Event;
use crate::event_label::{BlockType, LabelEnum};
use crate::exec_graph::ExecutionGraph;
use crate::Config;

use super::execution_witness::emitted;
use super::interchange::{encode_generic, normal_value, record_thread_names, ThreadName, ThreadNames};
use super::probe::{NondetValue, Offer};
use super::prober::{install_checked, install_nondet_checked, install_recv_checked, probe_from};
use super::witness_json::{Ev, Graph};

/// How a replay ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ReplayResult {
    Reproduced { events: usize, threads: usize },
    Deviation(Deviation),
}

/// The first difference between the program and the graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Deviation {
    pub(crate) at: (usize, usize),
    pub(crate) thread: Option<String>,
    /// One of `event`, `dest`, `value`, `options`, `child`, `unavailable`, `early-end`,
    /// `overrun`, `status`.
    pub(crate) kind: &'static str,
    /// The graph's event and the program's, in the text witness's form (`None`: nothing).
    pub(crate) expected: Option<String>,
    pub(crate) actual: Option<String>,
}

/// A replay's outcome and its warnings (an opaque value that was not compared).
#[derive(Clone, Debug)]
pub(crate) struct Replay {
    pub(crate) result: ReplayResult,
    pub(crate) warnings: Vec<String>,
}

/// The text witness's form of a recorded event.
fn text_of(ev: &Ev, names: &[Option<String>]) -> String {
    let name = |t: usize| names.get(t).cloned().flatten().unwrap_or_else(|| format!("#{t}"));
    match ev {
        Ev::Begin => "BEGIN".into(),
        Ev::End => "END".into(),
        Ev::Blk => "BLK".into(),
        Ev::Error(m) => format!("ERROR({m})"),
        Ev::TCreate(c) => format!("TCREATE({c}:{:?})", name(*c)),
        Ev::TJoin(c) => format!("TJOIN({c})"),
        Ev::Send { to, v } => format!("SEND({}, {})", name(*to), v.as_deref().unwrap_or("<opaque>")),
        Ev::Recv { rf: None, .. } => "RECV() [TIMEOUT]".into(),
        Ev::Recv { rf: Some((t, k)), .. } => format!("RECV() [({t}, {k}) {}]", name(*t)),
        Ev::Nondet { i, .. } => format!("NONDET {i}"),
    }
}

/// What the program does next on one thread.
enum Next<'a> {
    /// An event the probe already performed (forced), at its written position.
    Done(&'a LabelEnum),
    /// A choice point the probe parked the thread at.
    Offer(&'a Offer),
    /// Waiting at a receive or a join (the probe's `Block`), judged only when nothing can go on.
    Waiting(Ev),
    /// The thread has nothing more.
    Nothing,
}

/// The program's written events so far, per thread: the labels the graph format carries, with
/// main's end implicit only once the execution is over.
fn written(g: &ExecutionGraph, tids: &[crate::ThreadId]) -> Vec<Vec<(Event, LabelEnum)>> {
    tids.iter()
        .map(|&tid| {
            let mut out = Vec::new();
            let mut ended = false;
            for k in 0..g.thread_size(tid) {
                let e = Event::new(tid, k as u32);
                let l = g.label(e);
                if !emitted(l) || (ended && matches!(l, LabelEnum::End(_))) {
                    continue;
                }
                ended |= matches!(l, LabelEnum::End(_) | LabelEnum::Block(_));
                out.push((e, l.clone()));
            }
            out
        })
        .collect()
}

/// A performed (forced) event as a recorded event, for comparing.
fn forced(l: &LabelEnum, index: &HashMap<crate::ThreadId, usize>) -> Option<Ev> {
    Some(match l {
        LabelEnum::Begin(_) => Ev::Begin,
        LabelEnum::End(_) => Ev::End,
        LabelEnum::Block(_) => Ev::Blk,
        LabelEnum::TCreate(c) => Ev::TCreate(*index.get(&c.cid())?),
        LabelEnum::TJoin(j) => Ev::TJoin(*index.get(&j.cid())?),
        _ => return None,
    })
}

/// A sent value's P5 encoding in normal form, or `None` if the encoder refuses it.
fn encoded(v: &crate::msg::Val, names: &ThreadNames) -> Option<String> {
    encode_generic(v, names)
        .ok()
        .and_then(|x| serde_json::from_str::<Value>(&x).ok())
        .and_then(|x| normal_value(&x).ok())
}

/// The program's offered event in the text witness's form.
fn offer_text(
    o: &Offer, index: &HashMap<crate::ThreadId, usize>, names: &[Option<String>], tnames: &ThreadNames,
) -> String {
    match o.label() {
        LabelEnum::SendMsg(s) => {
            let to = s.loc().as_thread_id().and_then(|d| index.get(&d).copied());
            let to = to.and_then(|t| names.get(t).cloned().flatten()).unwrap_or_else(|| "?".to_owned());
            format!("SEND({to}, {})", encoded(s.val(), tnames).unwrap_or_else(|| format!("{:?}", s.val().val)))
        }
        LabelEnum::RecvMsg(r) if r.is_non_blocking() => "RECV() (non-blocking)".to_owned(),
        LabelEnum::RecvMsg(_) => "RECV()".to_owned(),
        LabelEnum::CToss(_) => "NONDET (a toss)".to_owned(),
        LabelEnum::Choice(c) => format!("NONDET (over {}..={})", c.range().start(), c.range().end()),
        _ => "an event the graph format does not carry".to_owned(),
    }
}

/// Whether the recorded event `(t, k)` is enabled: its porf predecessors are replayed (po is the
/// walk itself; the others: the send a receive reads, the joined thread's end, and for a thread's
/// first event the creating event).
fn ready(
    rec: &Graph, checked: &[usize], creator: &HashMap<usize, (usize, usize)>, t: usize, k: usize,
) -> bool {
    match rec.events.get(t).and_then(|w| w.get(k)) {
        Some(Ev::Recv { rf: Some((st, sk)), .. }) => checked.get(*st).is_some_and(|c| c > sk),
        Some(Ev::TJoin(c)) => rec.events.get(*c).is_some_and(|w| checked[*c] == w.len()),
        Some(_) if k == 0 => creator.get(&t).is_none_or(|&(ct, ck)| checked[ct] > ck),
        _ => true,
    }
}

fn same_kind(a: &Ev, b: &Ev) -> bool {
    std::mem::discriminant(a) == std::mem::discriminant(b)
}

/// Replays the checked graph `rec` with the program `f` under `config`.
pub(crate) fn replay(config: Config, f: Arc<dyn Fn() + Send + Sync>, rec: &Graph) -> Result<Replay, String> {
    let names = &rec.names;
    let mut warnings = Vec::new();
    let total: usize = rec.events.iter().map(Vec::len).sum();
    let dev = |at: (usize, usize), kind, expected: Option<String>, actual: Option<String>| {
        ReplayResult::Deviation(Deviation { at, thread: names.get(at.0).cloned().flatten(), kind, expected, actual })
    };
    let exp_text = |t: usize, k: usize| rec.events.get(t).and_then(|w| w.get(k)).map(|e| text_of(e, names));
    // Events replayed per thread (the graph's positions).
    let mut checked: Vec<usize> = vec![0; rec.events.len()];
    // The recorded creating event of each thread.
    let creator: HashMap<usize, (usize, usize)> = rec
        .events
        .iter()
        .enumerate()
        .flat_map(|(t, w)| w.iter().enumerate().filter_map(move |(k, e)| match e {
            Ev::TCreate(c) => Some((*c, (t, k))),
            _ => None,
        }))
        .collect();
    let mut graph = ExecutionGraph::default();
    // One-option choices install without a recorded event; they are bounded separately.
    let mut singles = 0usize;
    loop {
        if singles > 1_000_000 {
            return Err("the program took more than a million one-option choices".to_owned());
        }
        let probed = {
            let f = Arc::clone(&f);
            probe_from(config.clone(), graph.clone(), move || f())
        };
        if let Some(t) = &probed.threshold {
            return Err(format!("the replay stopped at a threshold: {t:?}"));
        }
        let pg = probed.graph();
        let offers = probed.offers();
        // A one-option choice is taken at once, without a recorded event.
        if let Some(o) =
            offers.iter().find(|o| matches!(o.label(), LabelEnum::Choice(c) if c.range().start() == c.range().end()))
        {
            let LabelEnum::Choice(c) = o.label() else { unreachable!() };
            graph = install_nondet_checked(config.clone(), pg.clone(), o, NondetValue::Choice(*c.range().start()))
                .map_err(|e| format!("{e:?}"))?;
            singles += 1;
            continue;
        }
        let tids: Vec<crate::ThreadId> = pg.thread_ids().into_iter().collect();
        let index: HashMap<crate::ThreadId, usize> = tids.iter().enumerate().map(|(t, &tid)| (tid, t)).collect();
        let done = written(pg, &tids);
        let by_thread: HashMap<usize, &Offer> =
            offers.iter().filter_map(|o| index.get(&o.pos().thread).map(|&t| (t, o))).collect();
        let mut tnames = ThreadNames::new();
        record_thread_names(pg, &mut tnames);
        for &tid in &tids {
            if let Some(n) = pg.thread_name(tid) {
                tnames.insert(tid.to_number(), ThreadName::Named(n.to_owned()));
            }
        }
        let next_of = |t: usize, k: usize| -> Next<'_> {
            match done.get(t).and_then(|d| d.get(k)) {
                Some((_, LabelEnum::Block(b))) if k + 1 == done[t].len() => match b.btype() {
                    BlockType::Value(..) => Next::Waiting(Ev::Recv { try_: false, rf: None }),
                    BlockType::Join(c) => {
                        Next::Waiting(Ev::TJoin(tids.iter().position(|x| x == c).unwrap_or(usize::MAX)))
                    }
                    _ => Next::Done(&done[t][k].1),
                },
                Some((_, l)) => Next::Done(l),
                None => match by_thread.get(&t) {
                    Some(o) => Next::Offer(o),
                    None => Next::Nothing,
                },
            }
        };
        // Walk the graph's order on this probe's state until an offer is taken (then probe
        // again), a deviation is found, or nothing can go on.
        let installed = 'walk: loop {
            for t in 0..tids.len() {
                if t >= rec.events.len() {
                    return Ok(Replay {
                        result: dev((t, 0), "child", None, Some("a thread the graph does not have".into())),
                        warnings,
                    });
                }
                let k = checked[t];
                let exp = rec.events[t].get(k);
                if !ready(rec, &checked, &creator, t, k) {
                    continue;
                }
                // A thread's identity is judged with its first event, once its creation is replayed.
                if k == 0 && pg.thread_name(tids[t]).map(str::to_owned) != rec.names[t] {
                    return Ok(Replay {
                        result: dev((t, 0), "child", rec.names[t].clone(), pg.thread_name(tids[t]).map(str::to_owned)),
                        warnings,
                    });
                }
                match next_of(t, k) {
                    Next::Nothing => continue,
                    // A waiting receive or join is compared at once. Deferred are the waits the
                    // record agrees with (the same kind, the same joined thread) and a recorded end
                    // (END, BLK, ERROR): only the end of the run tells whether the thread resumes
                    // (then it overruns) or stays blocked (then its status differs or matches).
                    Next::Waiting(w) => {
                        let actual = match &w {
                            Ev::Recv { .. } => "RECV() (waiting)".to_owned(),
                            other => text_of(other, names),
                        };
                        let kind = match (exp, &w) {
                            (Some(Ev::Recv { .. }), Ev::Recv { .. }) | (Some(Ev::End | Ev::Blk | Ev::Error(_)), _) => continue,
                            (Some(Ev::TJoin(a)), Ev::TJoin(b)) if a == b => continue,
                            (Some(Ev::TJoin(_)), Ev::TJoin(_)) => "child",
                            (None, _) => "overrun",
                            _ => "event",
                        };
                        return Ok(Replay { result: dev((t, k), kind, exp.map(|e| text_of(e, names)), Some(actual)), warnings });
                    }
                    Next::Done(l) => {
                        let Some(have) = forced(l, &index) else {
                            return Err(format!("the program's event at ({t}, {k}) has no form in the graph format"));
                        };
                        let Some(exp) = exp else {
                            return Ok(Replay { result: dev((t, k), "overrun", None, Some(text_of(&have, names))), warnings });
                        };
                        let differs = match (exp, &have) {
                            (Ev::TCreate(a), Ev::TCreate(b)) | (Ev::TJoin(a), Ev::TJoin(b)) => (a != b).then_some("child"),
                            (Ev::End | Ev::Blk | Ev::Error(_), Ev::End | Ev::Blk) => {
                                (!same_kind(exp, &have)).then_some("status")
                            }
                            (Ev::End | Ev::Blk | Ev::Error(_), _) => Some("overrun"),
                            (_, Ev::End | Ev::Blk) => Some("early-end"),
                            _ => (!same_kind(exp, &have)).then_some("event"),
                        };
                        if let Some(kind) = differs {
                            return Ok(Replay {
                                result: dev((t, k), kind, Some(text_of(exp, names)), Some(text_of(&have, names))),
                                warnings,
                            });
                        }
                        checked[t] += 1;
                        continue 'walk;
                    }
                    Next::Offer(o) => {
                        let offered = offer_text(o, &index, names, &tnames);
                        let Some(exp) = exp else {
                            return Ok(Replay { result: dev((t, k), "overrun", None, Some(offered)), warnings });
                        };
                        let mismatch = |kind| dev((t, k), kind, Some(text_of(exp, names)), Some(offered.clone()));
                        let pgc = pg.clone();
                        let next = match (o.label(), exp) {
                            (_, Ev::End | Ev::Blk | Ev::Error(_)) => {
                                return Ok(Replay { result: mismatch("overrun"), warnings })
                            }
                            (LabelEnum::SendMsg(s), Ev::Send { to, v }) => {
                                let dest = s.loc().as_thread_id().and_then(|d| index.get(&d).copied());
                                if dest != Some(*to) {
                                    return Ok(Replay { result: mismatch("dest"), warnings });
                                }
                                match v {
                                    None => warnings.push(format!("opaque-not-compared at ({t}, {k})")),
                                    Some(v) => {
                                        if encoded(s.val(), &tnames).as_ref() != Some(v) {
                                            return Ok(Replay { result: mismatch("value"), warnings });
                                        }
                                    }
                                }
                                install_checked(config.clone(), pgc, o).map_err(|e| format!("{e:?}"))?
                            }
                            (LabelEnum::RecvMsg(r), Ev::Recv { try_, rf }) => {
                                if r.is_non_blocking() != *try_ {
                                    return Ok(Replay { result: mismatch("event"), warnings });
                                }
                                let source = match rf {
                                    None if o.may_read_nothing() => None,
                                    None => return Ok(Replay { result: mismatch("unavailable"), warnings }),
                                    Some((st, sk)) => match done.get(*st).and_then(|d| d.get(*sk)) {
                                        Some((e, _)) if o.sources().contains(e) => Some(*e),
                                        _ => return Ok(Replay { result: mismatch("unavailable"), warnings }),
                                    },
                                };
                                install_recv_checked(config.clone(), pgc, o, source).map_err(|e| format!("{e:?}"))?
                            }
                            (LabelEnum::CToss(_), Ev::Nondet { n: 2, i, lo: None }) => {
                                install_nondet_checked(config.clone(), pgc, o, NondetValue::Toss(*i == 1))
                                    .map_err(|e| format!("{e:?}"))?
                            }
                            (LabelEnum::Choice(c), Ev::Nondet { n, i, lo: Some(lo) }) => {
                                let (a, b) = (*c.range().start() as u128, *c.range().end() as u128);
                                if a != u128::from(*lo) || b - a + 1 != *n || *i > b - a {
                                    return Ok(Replay { result: mismatch("options"), warnings });
                                }
                                install_nondet_checked(config.clone(), pgc, o, NondetValue::Choice((a + i) as usize))
                                    .map_err(|e| format!("{e:?}"))?
                            }
                            (LabelEnum::CToss(_) | LabelEnum::Choice(_), Ev::Nondet { .. }) => {
                                return Ok(Replay { result: mismatch("options"), warnings });
                            }
                            _ => return Ok(Replay { result: mismatch("event"), warnings }),
                        };
                        checked[t] += 1;
                        break 'walk Some(next);
                    }
                }
            }
            break 'walk None;
        };
        if let Some(next) = installed {
            graph = next;
            continue;
        }
        // Nothing can go on: the remaining record is judged in the same order, each event only
        // once its recorded predecessors are judged.
        'judge: loop {
            for t in 0..rec.events.len() {
                let k = checked[t];
                let want = &rec.events[t];
                if t < tids.len() && k >= want.len() {
                    // The record is over; the program must have nothing more on this thread.
                    match next_of(t, k) {
                        Next::Nothing => continue,
                        Next::Waiting(w) => {
                            return Ok(Replay { result: dev((t, k), "overrun", None, Some(text_of(&w, names))), warnings });
                        }
                        Next::Offer(o) => {
                            let got = offer_text(o, &index, names, &tnames);
                            return Ok(Replay { result: dev((t, k), "overrun", None, Some(got)), warnings });
                        }
                        Next::Done(l) => {
                            let got = forced(l, &index).map(|e| text_of(&e, names));
                            return Ok(Replay { result: dev((t, k), "overrun", None, got), warnings });
                        }
                    }
                }
                if k >= want.len() || !ready(rec, &checked, &creator, t, k) {
                    continue;
                }
                if t >= tids.len() {
                    // A recorded thread the program never created.
                    return Ok(Replay { result: dev((t, 0), "child", exp_text(t, 0), None), warnings });
                }
                match next_of(t, k) {
                    Next::Waiting(w) => match want.get(k) {
                        // Blocked for good where the graph has BLK as the thread's last event.
                        Some(Ev::Blk) if k + 1 == want.len() => {
                            checked[t] += 1;
                            continue 'judge;
                        }
                        Some(exp) if same_kind(exp, &w) => {
                            return Ok(Replay {
                                result: dev((t, k), "early-end", Some(text_of(exp, names)), Some("BLK".into())),
                                warnings,
                            });
                        }
                        Some(exp) => {
                            let kind = if matches!(exp, Ev::End | Ev::Blk | Ev::Error(_)) { "status" } else { "event" };
                            // A waiting receive is not a receive that read ⊥.
                            let actual = match &w {
                                Ev::Recv { .. } => "RECV() (waiting)".to_owned(),
                                other => text_of(other, names),
                            };
                            return Ok(Replay { result: dev((t, k), kind, Some(text_of(exp, names)), Some(actual)), warnings });
                        }
                        None => unreachable!("conformance: replay: a judged thread has a recorded event left"),
                    },
                    // Enabled, offered or performed, and still not taken by the walk: the event
                    // it needs cannot be delivered.
                    Next::Offer(_) | Next::Done(_) => {
                        return Ok(Replay { result: dev((t, k), "unavailable", exp_text(t, k), None), warnings });
                    }
                    Next::Nothing => {
                        // Main's end is implicit: it finished, so its next event is END.
                        match want.get(k) {
                            Some(Ev::End) if t == 0 && k + 1 == want.len() => {
                                checked[t] += 1;
                                continue 'judge;
                            }
                            Some(exp @ (Ev::Blk | Ev::Error(_))) if t == 0 => {
                                return Ok(Replay {
                                    result: dev((t, k), "status", Some(text_of(exp, names)), Some("END".into())),
                                    warnings,
                                });
                            }
                            Some(exp) if t == 0 => {
                                return Ok(Replay {
                                    result: dev((t, k), "early-end", Some(text_of(exp, names)), Some("END".into())),
                                    warnings,
                                });
                            }
                            _ => return Ok(Replay { result: dev((t, k), "early-end", exp_text(t, k), None), warnings }),
                        }
                    }
                }
            }
            break 'judge;
        }
        // Events left that are never enabled: the first such thread's next event cannot happen.
        if let Some(t) = (0..rec.events.len()).find(|&t| checked[t] < rec.events[t].len()) {
            let k = checked[t];
            let kind = if t >= tids.len() { "child" } else { "unavailable" };
            return Ok(Replay { result: dev((t, k), kind, exp_text(t, k), None), warnings });
        }
        if checked.iter().zip(&rec.events).all(|(c, w)| *c == w.len()) {
            return Ok(Replay { result: ReplayResult::Reproduced { events: total, threads: rec.events.len() }, warnings });
        }
        return Err("the replay stopped with events left and nothing to judge".to_owned());
    }
}
