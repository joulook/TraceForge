//! `B` (criteria `MEAS.md`): the measurement block every run of the shared
//! main and of `conf-join` prints after its own output — `--- measurements`,
//! then one `key: value` line per key, JMC's keys in JMC's order, then
//! TraceForge's extras (`brain-data/SCHEMA.md`: a number when measured, `0`
//! when the phase does not apply, empty when it applies but is not measured).
//!
//! This module gathers the values; `report.rs` renders them (S5 criterion 1);
//! the binaries write them. No engine file is involved: the offline rows (K1,
//! K6) echo numbers their outcomes already carry, and the printers with their
//! own code (K2 export, K3 `conf-join`, K4 online, K5 count) measure the rest.

use std::collections::HashMap;

use crate::conformance::compact::{CompactSummary, OrdCounts};
use crate::conformance::record::{GridEnd, GridEngine, GridRaw, Row};
use crate::conformance::sig::Sig;
use crate::conformance::{ConfError, ConfOutcome, ConfVerdict, Engine};
use crate::event::Event;
use crate::event_label::LabelEnum;
use crate::exec_graph::ExecutionGraph;

/// The block's keys, in order (MEAS-0.1). The three specification keys are
/// printed only by runs with a specification.
pub(crate) const KEYS: [&str; 37] = [
    "wall_ms",
    "explore_ms",
    "summarise_ms",
    "index_ms",
    "lookup_ms",
    "export_ms",
    "graphs_complete",
    "graphs_blocked",
    "summaries_distinct",
    "iterations",
    "stop_reason",
    "peak_rss_kb",
    "max_message_events",
    "max_porf_pairs",
    "first_miss_iteration",
    "first_miss_wall_ms",
    "uncovered_total",
    "max_graph_events",
    "mean_graph_events",
    "max_visible_events",
    "mean_visible_events",
    "max_summary_bytes",
    "max_porf_count",
    "join_ms",
    "spec_phase_ms",
    "impl_phase_ms",
    "explore_spec_ms",
    "explore_impl_ms",
    "spec_complete",
    "spec_blocked",
    "impl_complete",
    "impl_blocked",
    "spec_summaries",
    "impl_summaries",
    "precheck_ms",
    "merge_ms",
    "uncovered_distinct",
];

/// The specification keys (MEAS-0.1).
pub(crate) const SPEC_KEYS: [&str; 3] = [
    "first_miss_iteration",
    "first_miss_wall_ms",
    "uncovered_total",
];

/// One value of the block.
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Cell {
    /// A measured or counted integer, or `0` for "does not apply".
    N(u128),
    /// A mean, printed with three decimals.
    Mean(f64),
    /// Applies, not measured.
    Empty,
    /// `stop_reason`'s word.
    Word(&'static str),
}

/// `stop_reason` (`ISSUE-cluster.md` §7).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Stop {
    Exhausted,
    Budget,
    FirstMiss,
    Error,
}

impl Stop {
    pub(crate) fn word(self) -> &'static str {
        match self {
            Stop::Exhausted => "exhausted",
            Stop::Budget => "budget",
            Stop::FirstMiss => "first-miss",
            Stop::Error => "error",
        }
    }
}

/// The block's values (MEAS-0, MEAS-1).
#[derive(Clone, Debug, PartialEq)]
pub(crate) struct Measurements {
    /// Whether the specification keys are printed.
    pub(crate) with_spec: bool,
    cells: HashMap<&'static str, Cell>,
}

impl Measurements {
    /// Every key empty; `stop_reason` `error` until set.
    pub(crate) fn new(with_spec: bool) -> Self {
        let mut cells = HashMap::new();
        for k in KEYS.iter() {
            cells.insert(*k, Cell::Empty);
        }
        cells.insert("stop_reason", Cell::Word(Stop::Error.word()));
        Measurements { with_spec, cells }
    }

    /// Sets one key (a key outside [`KEYS`] is a programming error).
    pub(crate) fn set(&mut self, key: &'static str, value: Cell) {
        assert!(
            self.cells.contains_key(key),
            "conformance: measurement key `{key}` is not in the block"
        );
        self.cells.insert(key, value);
    }

    pub(crate) fn n(&mut self, key: &'static str, v: u128) {
        self.set(key, Cell::N(v));
    }

    pub(crate) fn zero(&mut self, keys: &[&'static str]) {
        for k in keys {
            self.set(k, Cell::N(0));
        }
    }

    pub(crate) fn stop(&mut self, s: Stop) {
        self.set("stop_reason", Cell::Word(s.word()));
    }

    pub(crate) fn get(&self, key: &str) -> &Cell {
        &self.cells[key]
    }

    /// The keys in print order, the specification keys only `with_spec`.
    pub(crate) fn ordered(&self) -> Vec<(&'static str, &Cell)> {
        KEYS.iter()
            .filter(|k| self.with_spec || !SPEC_KEYS.contains(k))
            .map(|k| (*k, &self.cells[k]))
            .collect()
    }
}

/// `VmHWM` of this process, in kB (`/proc/self/status`), `None` if unreadable.
pub(crate) fn peak_rss_kb() -> Option<u64> {
    let s = std::fs::read_to_string("/proc/self/status").ok()?;
    let line = s.lines().find(|l| l.starts_with("VmHWM:"))?;
    line.split_whitespace().nth(1)?.parse().ok()
}

/// A cell from an optional number: `Empty` for `None`.
pub(crate) fn opt(v: Option<u128>) -> Cell {
    v.map_or(Cell::Empty, Cell::N)
}

// ------------------------------------------------------- the shape counters --

/// The graph-shape counters over the graphs and summaries a printer sees
/// (SCHEMA's definitions): running maxima and sums.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Shape {
    graphs: u128,
    sum_graph_events: u128,
    max_graph_events: u128,
    max_message_events: u128,
    summaries: u128,
    sum_visible_events: u128,
    max_visible_events: u128,
    max_summary_bytes: u128,
    max_porf_count: u128,
    max_porf_pairs: u128,
}

impl Shape {
    /// One graph's events (every label of every thread, Must's count) and
    /// message events (sends and receives, inbox receives included, of all
    /// threads).
    pub(crate) fn graph_counts(g: &ExecutionGraph) -> (u128, u128) {
        let mut events = 0u128;
        let mut messages = 0u128;
        for t in g.thread_ids() {
            let n = g.thread_size(t);
            events += n as u128;
            for i in 0..n {
                if matches!(
                    g.label(Event::new(t, i as u32)),
                    LabelEnum::SendMsg(_) | LabelEnum::RecvMsg(_) | LabelEnum::Inbox(_)
                ) {
                    messages += 1;
                }
            }
        }
        (events, messages)
    }

    /// One summary's visible events (Σ of the words' lengths), its normal
    /// line's UTF-8 bytes (no `n`), its largest order-count entry and its
    /// number of non-zero entries.
    pub(crate) fn summary_counts(
        sig: &Sig,
        ord: &OrdCounts,
        names: &[String],
        line_bytes: usize,
    ) -> (u128, u128, u128, u128) {
        let visible: usize = names.iter().map(|n| sig.word(n).len()).sum();
        let (max, pairs) = match ord {
            OrdCounts::U8(c) => (
                c.iter().map(|&x| u128::from(x)).max().unwrap_or(0),
                c.iter().filter(|&&x| x != 0).count(),
            ),
            OrdCounts::U16(c) => (
                c.iter().map(|&x| u128::from(x)).max().unwrap_or(0),
                c.iter().filter(|&&x| x != 0).count(),
            ),
        };
        (visible as u128, line_bytes as u128, max, pairs as u128)
    }

    /// Folds one graph's counts in (arithmetic only: it cannot panic).
    pub(crate) fn add_graph_counts(&mut self, events: u128, messages: u128) {
        self.graphs += 1;
        self.sum_graph_events += events;
        self.max_graph_events = self.max_graph_events.max(events);
        self.max_message_events = self.max_message_events.max(messages);
    }

    /// Folds one summary's counts in (arithmetic only: it cannot panic).
    pub(crate) fn add_summary_counts(
        &mut self,
        visible: u128,
        bytes: u128,
        max: u128,
        pairs: u128,
    ) {
        self.summaries += 1;
        self.sum_visible_events += visible;
        self.max_visible_events = self.max_visible_events.max(visible);
        self.max_summary_bytes = self.max_summary_bytes.max(bytes);
        self.max_porf_count = self.max_porf_count.max(max);
        self.max_porf_pairs = self.max_porf_pairs.max(pairs);
    }

    pub(crate) fn add_graph(&mut self, g: &ExecutionGraph) {
        let (e, m) = Self::graph_counts(g);
        self.add_graph_counts(e, m);
    }

    pub(crate) fn add_summary(&mut self, cs: &CompactSummary, names: &[String], line_bytes: usize) {
        let (v, b, m, p) = Self::summary_counts(&cs.sig, &cs.ord, names, line_bytes);
        self.add_summary_counts(v, b, m, p);
    }

    /// Writes the graph counters (`graphs` true) and the summary counters
    /// (`summaries` true); a mean over nothing is 0.
    pub(crate) fn fill(&self, m: &mut Measurements, graphs: bool, summaries: bool) {
        let mean = |sum: u128, n: u128| if n == 0 { 0.0 } else { sum as f64 / n as f64 };
        if graphs {
            m.n("max_graph_events", self.max_graph_events);
            m.set(
                "mean_graph_events",
                Cell::Mean(mean(self.sum_graph_events, self.graphs)),
            );
            m.n("max_message_events", self.max_message_events);
        }
        if summaries {
            m.n("max_visible_events", self.max_visible_events);
            m.set(
                "mean_visible_events",
                Cell::Mean(mean(self.sum_visible_events, self.summaries)),
            );
            m.n("max_summary_bytes", self.max_summary_bytes);
            m.n("max_porf_count", self.max_porf_count);
            m.n("max_porf_pairs", self.max_porf_pairs);
        }
    }
}

// ------------------------------------------------------------------- K1 --

/// A record cell by name, `None` when absent or blank.
fn cell<'a>(row: &'a Row, key: &str) -> Option<&'a str> {
    row.iter()
        .find(|(k, _)| *k == key)
        .map(|(_, v)| v.as_str())
        .filter(|v| !v.is_empty())
}

/// A record cell as a number; `Empty` when blank, `None` or not a number. A
/// cell the record writes as an `Option`'s `Debug` (`vm_hwm_kb_after` reads
/// `Some(8632)`) is unwrapped (the tester's gate-3 finding).
fn num(row: &Row, key: &str) -> Cell {
    opt(cell(row, key).and_then(|v| {
        let v = v
            .strip_prefix("Some(")
            .and_then(|x| x.strip_suffix(')'))
            .unwrap_or(v);
        v.parse().ok()
    }))
}

/// K1 (`row`): the block from the record's cells and the raw result
/// (MEAS-1 K1). A `Verdict` route takes K6's table, keeping the record's
/// `wall_ms`, `peak_rss_kb` and `iterations`.
pub(crate) fn of_row(row: &Row, end: &GridEnd, engine: GridEngine, threads: usize) -> Measurements {
    let raw = match end {
        GridEnd::Ok(r) => Some(&r.raw),
        _ => None,
    };
    let panicked = !matches!(end, GridEnd::Ok(_));
    if let Some(GridRaw::Verdict(v)) = raw {
        let mut m = of_verdict(v);
        m.set("wall_ms", num(row, "wall_ms"));
        m.set("peak_rss_kb", num(row, "vm_hwm_kb_after"));
        m.set("iterations", num(row, "executions"));
        return m;
    }
    let baseline = matches!(engine, GridEngine::Explore | GridEngine::ExploreP);
    let mut m = Measurements::new(!baseline);
    m.set("wall_ms", num(row, "wall_ms"));
    m.set("iterations", num(row, "executions"));
    m.set("peak_rss_kb", num(row, "vm_hwm_kb_after"));
    m.zero(&["export_ms", "join_ms"]);
    m.set("first_miss_iteration", Cell::Empty);
    if baseline {
        let (spec_phase, impl_phase) = match engine {
            GridEngine::Explore => (Cell::N(0), num(row, "wall_ms")),
            _ => (num(row, "spec_wall_time_ms"), num(row, "impl_wall_time_ms")),
        };
        m.set("spec_phase_ms", spec_phase);
        m.set("impl_phase_ms", impl_phase);
        m.zero(&[
            "summarise_ms",
            "index_ms",
            "lookup_ms",
            "summaries_distinct",
            "impl_summaries",
            "spec_summaries",
            "max_visible_events",
            "max_summary_bytes",
            "max_porf_count",
            "max_porf_pairs",
            "precheck_ms",
            "merge_ms",
        ]);
        m.set("mean_visible_events", Cell::Mean(0.0));
        match raw {
            Some(GridRaw::Explore(s)) => {
                m.n("graphs_complete", s.execs as u128);
                m.n("graphs_blocked", s.block as u128);
                m.n("impl_complete", s.execs as u128);
                m.n("impl_blocked", s.block as u128);
                m.zero(&["spec_complete", "spec_blocked"]);
                m.n("max_graph_events", s.max_graph_events as u128);
            }
            Some(GridRaw::ExploreP(r)) => {
                for (k, c) in [
                    ("graphs_complete", "impl_complete"),
                    ("graphs_blocked", "impl_blocked"),
                    ("impl_complete", "impl_complete"),
                    ("impl_blocked", "impl_blocked"),
                    ("spec_complete", "spec_complete"),
                    ("spec_blocked", "spec_blocked"),
                ] {
                    m.set(k, num(row, c));
                }
                let max = r
                    .spec
                    .stats
                    .max_graph_events
                    .max(r.imp.stats.max_graph_events);
                m.n("max_graph_events", max as u128);
            }
            _ => {}
        }
        m.stop(if panicked {
            Stop::Error
        } else {
            Stop::Exhausted
        });
        return m;
    }

    // The conformance engines.
    let (spec_phase, impl_phase) = match engine {
        GridEngine::Stateful | GridEngine::SverifyP => {
            (num(row, "spec_wall_time_ms"), num(row, "impl_wall_time_ms"))
        }
        GridEngine::CompleteFirst => (
            num(row, "sweep_wall_time_ms"),
            num(row, "impl_phase_wall_ms"),
        ),
        GridEngine::CFirstP if threads <= 1 => (
            num(row, "sweep_wall_time_ms"),
            num(row, "impl_phase_wall_ms"),
        ),
        GridEngine::CFirstP => (Cell::Empty, Cell::Empty),
        GridEngine::Gated => (num(row, "sweep_wall_time_ms"), Cell::Empty),
        GridEngine::Enumerator => (Cell::Empty, num(row, "engine_wall_time_ms")),
        _ => (Cell::Empty, Cell::Empty),
    };
    m.set("spec_phase_ms", spec_phase);
    m.set("impl_phase_ms", impl_phase);
    if engine == GridEngine::Enumerator {
        m.zero(&["summarise_ms", "index_ms"]);
    }
    for k in [
        "spec_complete",
        "spec_blocked",
        "impl_complete",
        "impl_blocked",
    ] {
        m.set(k, num(row, k));
    }
    match (engine, raw) {
        (GridEngine::Enumerator, Some(GridRaw::Enumerator(o))) => {
            if let Some(s) = o.stats.as_ref() {
                m.n("graphs_complete", s.execs as u128);
                m.n("graphs_blocked", s.block as u128);
                m.n("max_graph_events", s.max_graph_events as u128);
            }
        }
        _ => {
            m.set("graphs_complete", num(row, "impl_complete"));
            m.set("graphs_blocked", num(row, "impl_blocked"));
        }
    }
    let distinct = num(row, "impl_distinct_summaries");
    m.set("summaries_distinct", distinct.clone());
    m.set("impl_summaries", distinct);
    if matches!(engine, GridEngine::Stateful | GridEngine::SverifyP) {
        m.set("spec_summaries", num(row, "orders_held"));
    }
    let counts_graphs = matches!(
        engine,
        GridEngine::Stateful
            | GridEngine::SverifyP
            | GridEngine::CompleteFirst
            | GridEngine::CFirstP
    );
    if counts_graphs {
        m.set(
            "first_miss_wall_ms",
            Cell::N(
                cell(row, "wall_ms_at_first_report")
                    .and_then(|v| v.parse().ok())
                    .unwrap_or(0),
            ),
        );
        m.set(
            "uncovered_total",
            match engine {
                GridEngine::SverifyP | GridEngine::CFirstP => num(row, "uncovered_multiplicity"),
                _ => num(row, "counter_reports"),
            },
        );
    }
    m.set(
        "precheck_ms",
        match engine {
            GridEngine::CompleteFirst | GridEngine::CFirstP | GridEngine::Gated => {
                num(row, "precheck_wall_time_ms")
            }
            _ => Cell::N(0),
        },
    );
    if !matches!(engine, GridEngine::SverifyP | GridEngine::CFirstP) {
        m.n("merge_ms", 0);
    }
    m.stop(row_stop(row, panicked));
    m
}

/// K1's `stop_reason` from the record (MEAS-1 K1, §7's precedence).
fn row_stop(row: &Row, panicked: bool) -> Stop {
    let errors = cell(row, "spec_errors")
        .and_then(|v| v.parse::<u64>().ok())
        .unwrap_or(0);
    // The enumerator's record names its one run's end `end`.
    let impl_end = cell(row, "impl_end")
        .or_else(|| cell(row, "end"))
        .unwrap_or("");
    if panicked
        || errors > 0
        || cell(row, "verdict") == Some("Err")
        || cell(row, "aborted") == Some("true")
        || impl_end == "SpecNotAssertionSafe"
        || impl_end == "Unknown"
    {
        Stop::Error
    } else if impl_end == "StoppedAtFirstReport" {
        Stop::FirstMiss
    } else if impl_end == "StateSpaceExhausted" {
        Stop::Exhausted
    } else if impl_end.starts_with("MaxIterations") {
        Stop::Budget
    } else {
        Stop::Error
    }
}

// ------------------------------------------------------------------- K6 --

/// K6 (`conf`), and K1's `Verdict` route: the block from the `ConfOutcome`
/// (MEAS-1 K6's table). `wall_ms` and `peak_rss_kb` are the caller's.
pub(crate) fn of_verdict(v: &Result<ConfVerdict, ConfError>) -> Measurements {
    let mut m = Measurements::new(true);
    m.zero(&["export_ms", "join_ms"]);
    let o: &ConfOutcome = match v {
        Err(_) => {
            m.stop(Stop::Error);
            return m;
        }
        Ok(v) => v.outcome(),
    };
    m.n("iterations", o.counters.executions as u128);
    m.stop(match o.end {
        crate::conformance::report::SearchEnd::StoppedAtFirstReport => Stop::FirstMiss,
        crate::conformance::report::SearchEnd::StateSpaceExhausted => Stop::Exhausted,
        crate::conformance::report::SearchEnd::MaxIterations(_) => Stop::Budget,
        _ => Stop::Error,
    });
    let first = |w: Option<u128>| Cell::N(w.unwrap_or(0));
    match o.engine {
        Engine::Stateful => {
            if let Some(c) = o.stateful_counters.as_ref() {
                m.n("spec_phase_ms", c.spec_wall_time_ms);
                m.n("impl_phase_ms", c.impl_wall_time_ms);
                let d = opt(c.impl_distinct_summaries.map(|x| x as u128));
                m.set("summaries_distinct", d.clone());
                m.set("impl_summaries", d);
                m.n("spec_summaries", c.orders_held as u128);
                m.set("first_miss_wall_ms", first(c.wall_ms_at_first_report));
            }
            m.n("uncovered_total", o.report_count as u128);
            m.zero(&["precheck_ms", "merge_ms"]);
        }
        Engine::SverifyP => {
            if let Some(c) = o.counters.sverify_p.as_ref() {
                m.n("spec_phase_ms", c.spec_wall_time_ms);
                m.n("impl_phase_ms", c.impl_wall_time_ms);
                m.n("graphs_complete", c.impl_complete as u128);
                m.n("graphs_blocked", c.impl_blocked as u128);
                m.n("impl_complete", c.impl_complete as u128);
                m.n("impl_blocked", c.impl_blocked as u128);
                m.n("spec_complete", c.spec_complete as u128);
                m.n("spec_blocked", c.spec_blocked as u128);
                let d = opt(c.impl_distinct_summaries.map(|x| x as u128));
                m.set("summaries_distinct", d.clone());
                m.set("impl_summaries", d);
                m.n("spec_summaries", c.orders_held as u128);
                m.set("first_miss_wall_ms", first(c.wall_ms_at_first_report));
            }
            m.n("uncovered_total", o.report_count as u128);
            m.n("precheck_ms", 0);
        }
        Engine::CompleteFirst => {
            if let Some(c) = o.cfirst_counters.as_ref() {
                m.n("spec_phase_ms", c.sweep_wall_time_ms);
                m.n(
                    "impl_phase_ms",
                    c.outer_wall_time_ms.saturating_sub(c.sweep_wall_time_ms),
                );
                m.set("first_miss_wall_ms", first(c.wall_ms_at_first_report));
                m.n("precheck_ms", c.precheck_wall_time_ms);
            }
            m.n("uncovered_total", o.report_count as u128);
            m.n("merge_ms", 0);
        }
        Engine::CFirstP => {
            if let Some(p) = o.counters.cfirst_p.as_ref() {
                let c = &p.base;
                if p.threads <= 1 {
                    m.n("spec_phase_ms", c.sweep_wall_time_ms);
                    m.n(
                        "impl_phase_ms",
                        c.outer_wall_time_ms.saturating_sub(c.sweep_wall_time_ms),
                    );
                }
                let d = opt(p.impl_distinct_summaries.map(|x| x as u128));
                m.set("summaries_distinct", d.clone());
                m.set("impl_summaries", d);
                m.n("uncovered_total", p.uncovered_multiplicity as u128);
                m.set("first_miss_wall_ms", first(c.wall_ms_at_first_report));
                m.n("precheck_ms", c.precheck_wall_time_ms);
            }
        }
        Engine::Gated => {
            if let Some(c) = o.gated_counters.as_ref() {
                m.n("spec_phase_ms", c.sweep_wall_time_ms);
                m.n("precheck_ms", c.precheck_wall_time_ms);
            }
            m.n("merge_ms", 0);
        }
        Engine::Enumerator => {
            m.n("impl_phase_ms", o.counters.wall_time_ms);
            m.zero(&["precheck_ms", "merge_ms"]);
        }
    }
    m
}

// ------------------------------------------------------------------- K4 --

/// K4 (`online`): every key from C's own run (MEAS-1 K4). `wall_ms` is the
/// caller's (the process from `main` to the block).
pub(crate) fn of_online(
    r: &crate::conformance::online::OnlineReport,
    wall_ms: u128,
) -> Measurements {
    use crate::conformance::online::End;
    let mut m = Measurements::new(true);
    m.n("wall_ms", wall_ms);
    m.n("explore_ms", r.explore_ms);
    m.n("explore_impl_ms", r.explore_ms);
    m.n("summarise_ms", r.summarise_ms);
    m.n("index_ms", r.index_ms);
    m.n("lookup_ms", r.lookup_ms);
    m.n("export_ms", r.export_ms);
    m.n("graphs_complete", r.graphs_complete as u128);
    m.n("graphs_blocked", r.graphs_blocked as u128);
    m.n("impl_complete", r.graphs_complete as u128);
    m.n("impl_blocked", r.graphs_blocked as u128);
    m.n("summaries_distinct", r.impl_lines as u128);
    m.n("impl_summaries", r.impl_lines as u128);
    m.n("spec_summaries", r.held as u128);
    m.n("iterations", r.iterations as u128);
    m.stop(match r.end {
        End::Failed => Stop::Error,
        End::FirstMiss => Stop::FirstMiss,
        End::Exhausted => Stop::Exhausted,
        End::Budget => Stop::Budget,
    });
    m.set("peak_rss_kb", opt(peak_rss_kb().map(u128::from)));
    let (iteration, wall) = r
        .first
        .as_ref()
        .map_or((0, 0), |f| (f.iteration as u128, u128::from(f.wall_ms)));
    m.n("first_miss_iteration", iteration);
    m.n("first_miss_wall_ms", wall);
    m.n("uncovered_total", r.uncovered_total as u128);
    r.shape.fill(&mut m, true, true);
    m.zero(&[
        "join_ms",
        "spec_phase_ms",
        "impl_phase_ms",
        "explore_spec_ms",
        "spec_complete",
        "spec_blocked",
        "precheck_ms",
        "merge_ms",
    ]);
    m
}

// ------------------------------------------------------------- K2, K3, K5 --

/// The side a K2 export or a K5 count explored.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Side {
    Spec,
    Impl,
}

/// K2 (`export`): from G1's export run (MEAS-1 K2); `Err` → `error` with only
/// `wall_ms` and `peak_rss_kb` measured.
pub(crate) fn of_export(
    r: &Result<
        crate::conformance::interchange::ExportStats,
        crate::conformance::interchange::ExportError,
    >,
    side: Side,
    wall_ms: u128,
) -> Measurements {
    let mut m = Measurements::new(false);
    m.n("wall_ms", wall_ms);
    m.set("peak_rss_kb", opt(peak_rss_kb().map(u128::from)));
    let s = match r {
        Err(_) => {
            m.stop(Stop::Error);
            return m;
        }
        Ok(s) => s,
    };
    m.n("explore_ms", s.explore_ms);
    m.n("summarise_ms", s.summarise_ms);
    m.n("export_ms", s.export_ms);
    m.zero(&[
        "index_ms",
        "lookup_ms",
        "join_ms",
        "spec_phase_ms",
        "impl_phase_ms",
    ]);
    m.zero(&["precheck_ms", "merge_ms"]);
    m.n("graphs_complete", s.graphs_complete as u128);
    m.n("graphs_blocked", s.graphs_blocked as u128);
    m.n("summaries_distinct", s.lines as u128);
    m.n("iterations", s.executions as u128);
    m.stop(Stop::Exhausted);
    s.shape.fill(&mut m, true, true);
    let (here, there) = match side {
        Side::Spec => (
            [
                "explore_spec_ms",
                "spec_complete",
                "spec_blocked",
                "spec_summaries",
            ],
            [
                "explore_impl_ms",
                "impl_complete",
                "impl_blocked",
                "impl_summaries",
            ],
        ),
        Side::Impl => (
            [
                "explore_impl_ms",
                "impl_complete",
                "impl_blocked",
                "impl_summaries",
            ],
            [
                "explore_spec_ms",
                "spec_complete",
                "spec_blocked",
                "spec_summaries",
            ],
        ),
    };
    m.n(here[0], s.explore_ms);
    m.n(here[1], s.graphs_complete as u128);
    m.n(here[2], s.graphs_blocked as u128);
    m.n(here[3], s.lines as u128);
    m.zero(&there);
    m.zero(&["uncovered_distinct"]);
    m
}

/// K3 (`conf-join`): from the join (MEAS-1 K3); `None` (a refused file) →
/// `error` with only `wall_ms` and `peak_rss_kb` measured.
pub(crate) fn of_join(
    r: Option<&crate::conformance::interchange::JoinReport>,
    wall_ms: u128,
) -> Measurements {
    let mut m = Measurements::new(true);
    m.n("wall_ms", wall_ms);
    m.set("peak_rss_kb", opt(peak_rss_kb().map(u128::from)));
    let Some(r) = r else {
        m.stop(Stop::Error);
        return m;
    };
    m.n("index_ms", r.index_ms);
    m.n("lookup_ms", r.lookup_ms);
    m.n("join_ms", r.join_ms);
    m.zero(&[
        "explore_ms",
        "explore_spec_ms",
        "explore_impl_ms",
        "spec_phase_ms",
        "impl_phase_ms",
        "summarise_ms",
        "export_ms",
        "graphs_complete",
        "graphs_blocked",
        "spec_complete",
        "spec_blocked",
        "impl_complete",
        "impl_blocked",
        "iterations",
        "precheck_ms",
        "merge_ms",
        "first_miss_iteration",
        "first_miss_wall_ms",
    ]);
    m.n("spec_summaries", r.spec_lines as u128);
    m.n("impl_summaries", r.impl_lines as u128);
    m.n("summaries_distinct", r.impl_lines as u128);
    m.n("uncovered_distinct", r.uncovered.len() as u128);
    m.stop(Stop::Exhausted);
    // The lines' counters; the graph counters and the mean stay empty (a file
    // has no graphs, and its lines carry no multiplicity).
    let mut lines = Measurements::new(true);
    r.shape.fill(&mut lines, false, true);
    for k in [
        "max_visible_events",
        "max_summary_bytes",
        "max_porf_count",
        "max_porf_pairs",
    ] {
        m.set(k, lines.get(k).clone());
    }
    m
}

/// K5 (`count`): plain Must on one side (MEAS-1 K5).
pub(crate) fn of_count(
    stats: &crate::Stats,
    side: Side,
    explore_ms: u128,
    wall_ms: u128,
) -> Measurements {
    let mut m = Measurements::new(false);
    m.n("wall_ms", wall_ms);
    m.set("peak_rss_kb", opt(peak_rss_kb().map(u128::from)));
    m.n("explore_ms", explore_ms);
    m.n("graphs_complete", stats.execs as u128);
    m.n("graphs_blocked", stats.block as u128);
    m.n("iterations", (stats.execs + stats.block) as u128);
    m.n("max_graph_events", stats.max_graph_events as u128);
    m.stop(Stop::Exhausted);
    m.zero(&[
        "summarise_ms",
        "index_ms",
        "lookup_ms",
        "export_ms",
        "join_ms",
        "spec_phase_ms",
        "impl_phase_ms",
        "precheck_ms",
        "merge_ms",
        "summaries_distinct",
        "spec_summaries",
        "impl_summaries",
        "max_visible_events",
        "max_summary_bytes",
        "max_porf_count",
        "max_porf_pairs",
        "uncovered_distinct",
    ]);
    m.set("mean_visible_events", Cell::Mean(0.0));
    let (here, there) = match side {
        Side::Spec => (
            ["explore_spec_ms", "spec_complete", "spec_blocked"],
            ["explore_impl_ms", "impl_complete", "impl_blocked"],
        ),
        Side::Impl => (
            ["explore_impl_ms", "impl_complete", "impl_blocked"],
            ["explore_spec_ms", "spec_complete", "spec_blocked"],
        ),
    };
    m.n(here[0], explore_ms);
    m.n(here[1], stats.execs as u128);
    m.n(here[2], stats.block as u128);
    m.zero(&there);
    m
}
