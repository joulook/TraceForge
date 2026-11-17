use super::*;
use crate::conformance::ctx::{ConfCtx, ConfMode};
use crate::conformance::report::SearchEnd;
use crate::parallel_verify::{verify_partitioned_rayon_with, PartitionHooks};
use std::sync::{Arc, Mutex};

fn config() -> Config {
    Config::builder().with_seed(0).with_cons_type(crate::ConsType::FIFO).build()
}

fn attach(must: &mut Must) {
    let ctx = ConfCtx::gate_disabled(
        must.config.clone(), Vec::new(), ConfMode::EnumeratePartitioned,
    );
    must.enable_conformance_partitioned(ctx);
}

// One binary choice: exactly two executions, independent of scheduler or worker order.
// Exercise the real warmup and continuation chunk loop, including cap == space.
#[test]
fn parallel_chunk_caps_preserve_the_uncapped_result() {
    let reference = Arc::new(Mutex::new(Vec::new()));
    let seen = Arc::clone(&reference);
    let baseline = crate::verify(config(), move || {
        let value = crate::nondet();
        seen.lock().unwrap().push(value);
    });
    let mut expected = reference.lock().unwrap().clone();
    expected.sort();
    assert_eq!(expected, [false, true]);
    assert_eq!((baseline.execs, baseline.block), (2, 0));

    for (warmup, interval, end) in [
        (2, 1, SearchEnd::StateSpaceExhausted),
        (1, 1, SearchEnd::MaxIterations(1)),
        (3, 3, SearchEnd::StateSpaceExhausted),
    ] {
        let mut conf = config();
        conf.partitioned_parallelization = true;
        conf.partitioned_num_threads = Some(1);
        conf.warmup = warmup;
        conf.iterations_until_split = interval;
        let ends = Arc::new(Mutex::new(Vec::new()));
        let recorded = Arc::clone(&ends);
        let hooks = PartitionHooks {
            on_must: Arc::new(attach),
            on_task_end: Arc::new(move |must| {
                recorded.lock().unwrap().push(must.conf_ctx().unwrap().end());
            }),
            ..PartitionHooks::default()
        };
        let values = Arc::new(Mutex::new(Vec::new()));
        let seen = Arc::clone(&values);
        let run = verify_partitioned_rayon_with(conf, move || {
            let value = crate::nondet();
            seen.lock().unwrap().push(value);
        }, hooks);
        let mut actual = values.lock().unwrap().clone();
        actual.sort();
        assert_eq!(actual, expected, "chunk cap lost or duplicated a choice");
        assert_eq!((run.stats.execs, run.stats.block), (baseline.execs, baseline.block));
        // ConfCtx keeps its first end: an early chunk's bound survives later chunks.
        assert_eq!(*ends.lock().unwrap(), [end]);
    }
    Must::set_current(None);
}

// White-box the saved-only boundary with a real, resumable nondet revisit. The repeated
// completion below isolates classification of a worker stack after its current queue drains.
#[test]
fn cap_peeks_at_saved_states_without_consuming_them() {
    let mut conf = config();
    conf.max_iterations = Some(1);
    let must = Rc::new(RefCell::new(Must::new(conf, false)));
    let f = Arc::new(|| { let _ = crate::nondet(); });
    crate::explore(&must, &f);
    {
        let mut m = must.borrow_mut();
        assert!(!m.current.rqueue.is_empty());
        let saved = m.current.clone();
        m.current.rqueue.clear();
        m.states.push(saved);
        m.config.partitioned_parallelization = true;
        attach(&mut m);
    }
    let before = serde_json::to_string(&must.borrow().states).unwrap();
    assert!(Must::complete_execution(&must));
    assert_eq!(must.borrow().conf_ctx().unwrap().end(), SearchEnd::MaxIterations(1));
    assert_eq!(serde_json::to_string(&must.borrow().states).unwrap(), before);
    assert!(must.borrow().current.rqueue.is_empty());
    // The caller, not the cap peek, must still be able to select the saved alternative.
    assert!(must.borrow_mut().try_revisit());
    Must::set_current(None);
}

// LTR runs sender 1, the reader, then senders 2 and 3: the receive does not block,
// and the later sends enqueue two backward revisits. After warmup 1, the root pops
// the newest revisit and saves the other. Interval 1 stops before that saved queue
// is consumed, so drain_saved_states/filter_nonempty_work_items produce a task.
// A reader spawned first would block until all senders finish, giving only forward
// revisits (no saved states). One Rayon worker suffices: spawning has no pool-size gate.
#[test]
fn parallel_task_chunks_preserve_all_receive_results() {
    fn run_program(values: &Mutex<Vec<i32>>) {
        let (tx, rx) = crate::channel::Builder::<i32>::new().build();
        let received = Arc::new(Mutex::new(None));
        let result = Arc::clone(&received);
        let first = tx.clone();
        crate::thread::spawn(move || first.send_msg(1));
        let reader = crate::thread::spawn(move || {
            let value = rx.recv_msg_block();
            *result.lock().unwrap() = Some(value);
        });
        for value in 2..=3 {
            let tx = tx.clone();
            crate::thread::spawn(move || tx.send_msg(value));
        }
        reader.join().unwrap();
        values.lock().unwrap().push(received.lock().unwrap().unwrap());
    }
    let reference = Arc::new(Mutex::new(Vec::new()));
    let seen = Arc::clone(&reference);
    let baseline = crate::verify(config(), move || run_program(&seen));
    let mut expected = reference.lock().unwrap().clone();
    expected.sort();
    assert_eq!(expected, [1, 2, 3]);
    assert_eq!((baseline.execs, baseline.block), (3, 0));
    for interval in [1, 2, 3] {
        let mut conf = config();
        conf.partitioned_parallelization = true;
        conf.partitioned_num_threads = Some(1);
        conf.warmup = 1;
        conf.iterations_until_split = interval;
        conf.state_batch_size = 1;
        let values = Arc::new(Mutex::new(Vec::new()));
        let seen = Arc::clone(&values);
        let run = verify_partitioned_rayon_with(
            conf, move || run_program(&seen), PartitionHooks::default(),
        );
        let mut actual = values.lock().unwrap().clone();
        actual.sort();
        assert_eq!(actual, expected, "task chunks lost or duplicated a receive");
        assert_eq!((run.stats.execs, run.stats.block), (baseline.execs, baseline.block));
        if interval == 1 {
            assert!(run.tasks_spawned > 0, "the fixture must exercise task chunks");
        }
    }
    Must::set_current(None);
}
