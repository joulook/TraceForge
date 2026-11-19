//! Unit tests of the witness-graph walk on hand-built execution graphs: labels the public API
//! cannot produce in an export (samples, inboxes), value refusals, and choice encodings.

use crate::channel::Thread;
use crate::conformance::witness_graph::threads_json;
use crate::event::Event;
use crate::event_label::{
    Begin, CToss, Choice, End, Inbox, LabelEnum, MonitorSends, RecvMsg, Sample, SendMsg, TCreate,
};
use crate::exec_graph::ExecutionGraph;
use crate::loc::{CommunicationModel, Loc, RecvLoc, SendLoc};
use crate::msg::Val;
use crate::runtime::task::TaskId;
use crate::thread::{construct_thread_id, main_thread_id};

/// main = t0 creates `v` = t1. Returns the graph after both BEGINs and the TCREATE.
fn two_threads() -> ExecutionGraph {
    let mut g = ExecutionGraph::new();
    let (t0, t1) = (main_thread_id(), construct_thread_id(1));
    let tc = TCreate::new(Event::new(t0, 1), t1, Some("v".to_owned()), false, None, vec![], vec![]);
    g.add_label(LabelEnum::TCreate(tc.clone()));
    g.add_new_thread(tc, TaskId(1));
    g.add_label(LabelEnum::Begin(Begin::new(Event::new(t1, 0), Some(Event::new(t0, 1)), None)));
    g
}

fn send(at: Event, to: Loc, v: Val) -> LabelEnum {
    LabelEnum::SendMsg(SendMsg::new(at, SendLoc::new(&to, at.thread, None), CommunicationModel::default(),
        v, MonitorSends::new(), false))
}

fn thread_loc(n: u32) -> Loc {
    Loc::new(Thread(construct_thread_id(n)))
}

fn recv(at: Event, rf: Option<Event>, non_blocking: bool) -> LabelEnum {
    let me = thread_loc(at.thread.to_number());
    LabelEnum::RecvMsg(RecvMsg::new(at, RecvLoc::new(vec![&me], None), CommunicationModel::default(),
        rf, non_blocking))
}

fn vis(names: &[&str]) -> Vec<String> {
    names.iter().map(|s| s.to_string()).collect()
}

#[test]
fn a_sample_anywhere_refuses_the_graph() {
    let mut g = ExecutionGraph::new();
    g.add_label(LabelEnum::Sample(Sample::new(Event::new(main_thread_id(), 1),
        serde_json::json!(3), vec![])));
    let r = threads_json(&g, &[]);
    assert!(matches!(&r, Err(e) if e.starts_with("unsupported event ") && e.contains("Sample")), "conformance: {r:?}");
}

#[test]
fn an_inbox_refuses_the_graph() {
    let mut g = ExecutionGraph::new();
    let me = thread_loc(0);
    g.add_label(LabelEnum::Inbox(Inbox::new(Event::new(main_thread_id(), 1),
        RecvLoc::new(vec![&me], None), CommunicationModel::default(), None, 0, None)));
    let r = threads_json(&g, &[]);
    assert!(matches!(&r, Err(e) if e.starts_with("unsupported event ") && e.contains("Inbox")), "conformance: {r:?}");
}

#[test]
fn a_send_to_a_channel_refuses_the_graph() {
    let mut g = ExecutionGraph::new();
    g.add_label(send(Event::new(main_thread_id(), 1), Loc::new(7u32), Val::new(1usize)));
    let r = threads_json(&g, &[]);
    assert!(matches!(&r, Err(e) if e.starts_with("unsupported event ")), "conformance: {r:?}");
}

#[test]
fn value_refusals_visible_and_invisible() {
    let (t0, t1) = (main_thread_id(), construct_thread_id(1));
    // main (invisible) sends a float that `v` reads, and a float nobody reads.
    let mut g = two_threads();
    g.add_label(send(Event::new(t0, 2), thread_loc(1), Val::new(0.5f64)));
    g.add_label(send(Event::new(t0, 3), thread_loc(0), Val::new(2.5f64)));
    g.add_label(recv(Event::new(t1, 1), Some(Event::new(t0, 2)), false));
    g.add_label(LabelEnum::End(End::new(Event::new(t1, 2), Val::new(()))));
    // Read by a visible thread: refused.
    assert!(threads_json(&g, &vis(&["v"])).is_err());
    // Nobody visible: both written opaque.
    let t = threads_json(&g, &[]).unwrap();
    let v: serde_json::Value = serde_json::from_str(&t).unwrap();
    assert!(v[0]["events"][2]["v"]["opaque"].is_string(), "conformance: {t}");
    assert!(v[0]["events"][3]["v"]["opaque"].is_string(), "conformance: {t}");
    assert_eq!(v[0]["events"][2]["v"].as_object().unwrap().len(), 1, "conformance: {t}");
    // Sent by a visible thread: refused, even though nobody reads it.
    let mut g = two_threads();
    g.add_label(send(Event::new(t1, 1), thread_loc(0), Val::new(0.5f64)));
    g.add_label(LabelEnum::End(End::new(Event::new(t1, 2), Val::new(()))));
    assert!(threads_json(&g, &vis(&["v"])).is_err());
    assert!(threads_json(&g, &[]).is_ok());
    // An encodable value of a visible thread is written in the interchange encoding.
    let mut g = two_threads();
    g.add_label(send(Event::new(t1, 1), thread_loc(0), Val::new(Some(3usize))));
    g.add_label(LabelEnum::End(End::new(Event::new(t1, 2), Val::new(()))));
    let t = threads_json(&g, &vis(&["v"])).unwrap();
    assert!(t.contains("{\"e\":\"SEND\",\"to\":0,\"v\":{\"t\":\"Some\",\"f\":[3]}}"), "conformance: {t}");
}

#[test]
fn choices_receives_and_positions() {
    let (t0, t1) = (main_thread_id(), construct_thread_id(1));
    let mut g = two_threads();
    let mut c = Choice::new(Event::new(t1, 1), &mut (4..=6));
    c.set_result(6);
    g.add_label(LabelEnum::Choice(c));
    // A one-option choice takes no position.
    g.add_label(LabelEnum::Choice(Choice::new(Event::new(t1, 2), &mut (9..=9))));
    g.add_label(LabelEnum::CToss(CToss::new(Event::new(t1, 3), true)));
    g.add_label(LabelEnum::CToss(CToss::new(Event::new(t1, 4), false)));
    g.add_label(send(Event::new(t0, 2), thread_loc(1), Val::new(5usize)));
    g.add_label(recv(Event::new(t1, 5), Some(Event::new(t0, 2)), true));
    g.add_label(recv(Event::new(t1, 6), None, true));
    g.add_label(LabelEnum::End(End::new(Event::new(t1, 7), Val::new(()))));
    let t = threads_json(&g, &vis(&["v"])).unwrap();
    assert_eq!(t, concat!(
        "[{\"name\":\"main\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},",
        "{\"e\":\"TCREATE\",\"child\":1},{\"e\":\"SEND\",\"to\":1,\"v\":5},{\"e\":\"END\"}]},",
        "{\"name\":\"v\",\"daemon\":false,\"events\":[{\"e\":\"BEGIN\"},",
        "{\"e\":\"NONDET\",\"n\":3,\"i\":2,\"lo\":4},{\"e\":\"NONDET\",\"n\":2,\"i\":1},",
        "{\"e\":\"NONDET\",\"n\":2,\"i\":0},{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":[0,2]},",
        "{\"e\":\"RECV\",\"mode\":\"try\",\"rf\":null},{\"e\":\"END\"}]}]"));
}

#[test]
fn a_choice_over_every_usize_has_two_to_the_64_options() {
    let t1 = construct_thread_id(1);
    let mut g = two_threads();
    let mut c = Choice::new(Event::new(t1, 1), &mut (0..=usize::MAX));
    c.set_result(5);
    g.add_label(LabelEnum::Choice(c));
    g.add_label(LabelEnum::End(End::new(Event::new(t1, 2), Val::new(()))));
    let t = threads_json(&g, &vis(&["v"])).unwrap();
    assert!(t.contains("{\"e\":\"NONDET\",\"n\":18446744073709551616,\"i\":5,\"lo\":0}"),
        "conformance: {t}");
    let mut g = two_threads();
    let mut c = Choice::new(Event::new(t1, 1), &mut (1..=usize::MAX));
    c.set_result(usize::MAX);
    g.add_label(LabelEnum::Choice(c));
    g.add_label(LabelEnum::End(End::new(Event::new(t1, 2), Val::new(()))));
    let t = threads_json(&g, &vis(&["v"])).unwrap();
    assert!(t.contains("{\"e\":\"NONDET\",\"n\":18446744073709551615,\"i\":18446744073709551614,\"lo\":1}"),
        "conformance: {t}");
}

#[test]
fn the_deprecated_cd_model_is_written_causal() {
    use crate::conformance::witness_graph::model_label;
    use crate::ConsType;
    #[allow(deprecated)]
    let cd = ConsType::CD;
    assert_eq!(model_label(cd), "causal");
    assert_eq!(model_label(ConsType::Causal), "causal");
    assert_eq!(model_label(ConsType::FIFO), "fifo");
    assert_eq!(model_label(ConsType::Bag), "bag");
}
