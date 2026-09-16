//! Test support: run a program once and keep the graph it produced.
//!
//! Criterion 8 asks for extraction driven by real graphs rather than only by
//! hand-built ones, and the reason is worth stating: a graph assembled by the
//! same person who wrote the extractor can encode the same misunderstanding as
//! the extractor, and then the test proves only that the author was
//! consistent. Everything here drives the real engine, so the graphs have
//! whatever shape TraceForge actually gives them.
//!
//! This is an in-crate harness, not an engine touch-point. `ExecutionObserver`
//! hands its `after` callback an `EndCondition` and a `CoverageInfo` rather
//! than the graph, so there is no existing hook that would do; adding one is
//! S4's work, and doing it here would be scope creep.

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use crate::exec_graph::ExecutionGraph;
use crate::must::Must;
use crate::runtime::execution::Execution;
use crate::runtime::thread::continuation::{ContinuationPool, CONTINUATION_POOL};
use crate::Config;

/// Clears the thread's current-`Must` pointer on the way out, including on a
/// panic — a test that runs a program which asserts false is an ordinary case
/// here, not an accident.
pub(crate) struct CurrentMustGuard;

impl Drop for CurrentMustGuard {
    fn drop(&mut self) {
        Must::set_current(None);
    }
}

/// Run `f` once under `config` and return the graph of that execution.
///
/// One execution, not an exploration: the scheduler takes whatever schedule
/// the policy gives it and the program runs to the end. That is all these
/// tests need, since they are about reading a finished graph rather than about
/// which graphs exist.
pub(crate) fn run_once<F>(config: Config, f: F) -> ExecutionGraph
where
    F: Fn() + Send + Sync + 'static,
{
    let must = Rc::new(RefCell::new(Must::new(config, false)));
    Must::set_current(Some(Rc::clone(&must)));
    let _guard = CurrentMustGuard;

    let f = Arc::new(f);
    CONTINUATION_POOL.set(&ContinuationPool::new(), || {
        let execution = Execution::new(Rc::clone(&must));
        Must::begin_execution(&must);
        let f = Arc::clone(&f);
        execution.run(move || f());
    });

    let graph = must.borrow_mut().take_graph();
    graph
}

/// The declared visible-thread list these tests use most often.
pub(crate) fn names(ns: &[&str]) -> Vec<String> {
    ns.iter().map(|s| (*s).to_string()).collect()
}
