//! Optional, untimed check of the enumeration's distinctness assumption.
//!
//! Completion counts equal distinct canonical graphs because enumeration is optimal.
//! For Boolean tosses the cross-lineage argument is not proven. This diagnostic
//! checks observed runs; it is not a proof of optimality.
//!
//! CanonSet hashes CanonKey (positions, label shapes, types and reads-from) using
//! HashMap's 64-bit hash. It retains full canonical graphs and resolves every
//! collision by canonical equality, so there is no probabilistic collision loss.
//! Memory per distinct graph is proportional to events, reads-from, identity strings
//! and cloned payloads, plus a key per bucket and hash-table overhead; it is not fixed.
//! Workers share one run-local mutex/set, so cross-worker duplicates are compared too.
use std::sync::{Arc, Mutex};

use super::canon::{CanonSet, CanonicalGraph};
use crate::exec_graph::ExecutionGraph;

pub(crate) type OptionalAudit = Option<Arc<Mutex<GraphAudit>>>;

#[derive(Default)]
pub(crate) struct GraphAudit {
    completions: usize,
    graphs: CanonSet,
}

pub(crate) fn record(audit: &OptionalAudit, g: &ExecutionGraph, visible: &[String]) {
    if let Some(audit) = audit {
        let graph = CanonicalGraph::of(g, visible)
            .expect("conformance: summarised graph has canonical identities");
        let mut audit = audit.lock().expect("conformance: graph audit lock");
        audit.completions += 1;
        audit.graphs.insert(graph);
    }
}

pub(crate) fn append(audit: &OptionalAudit, block: &mut String) -> Option<String> {
    if let Some(audit) = audit {
        let audit = audit.lock().expect("conformance: graph audit lock");
        let completions = audit.completions;
        let distinct = audit.graphs.len();
        block.push_str(&format!(
            "audit_graph_completions: {completions}\naudit_graphs_distinct: {distinct}\n"
        ));
        if completions != distinct {
            return Some(format!(
                "conformance: engine distinctness defect: {completions} completions, \
                 {distinct} distinct canonical graphs"
            ));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn repeated_graph_is_not_distinct() {
        // Mutant: report completions as the distinct count.
        let audit = Some(Default::default());
        let g = ExecutionGraph::new();
        record(&audit, &g, &[]);
        record(&audit, &g, &[]);
        let mut block = String::new();
        let warning = append(&audit, &mut block);
        assert_eq!(warning.as_deref(), Some(
            "conformance: engine distinctness defect: 2 completions, 1 distinct canonical graphs"
        ), "conformance: mismatch warning names both counts");
        assert_eq!(block,
            "audit_graph_completions: 2\naudit_graphs_distinct: 1\n",
            "conformance: duplicate canonical graphs must be collapsed");
    }

    #[test]
    fn disabled_audit_preserves_output_bytes() {
        // Mutant: append diagnostic keys even when the audit is absent.
        let stdout = "conforms\n".to_owned();
        let mut block = super::super::measure::Measurements::new(true).render();
        let before = (stdout.clone(), block.clone(), 0u8);
        record(&None, &ExecutionGraph::new(), &[]);
        assert_eq!(append(&None, &mut block), None,
            "conformance: disabled audit has no stderr warning");
        assert_eq!((stdout, block, 0u8), before,
            "conformance: disabled audit preserves all output bytes and exit status");
    }

    #[test]
    fn workers_share_distinctness_set() {
        // Mutant: give each worker a separate set and sum its cardinality.
        let audit: OptionalAudit = Some(Default::default());
        let workers: Vec<_> = (0..2).map(|_| {
            let audit = audit.clone();
            std::thread::spawn(move || record(&audit, &ExecutionGraph::new(), &[]))
        }).collect();
        for worker in workers {
            worker.join().expect("conformance: audit worker completes");
        }
        let mut block = String::new();
        assert!(append(&audit, &mut block).is_some(),
            "conformance: duplicate across workers warns");
        assert_eq!(block, "audit_graph_completions: 2\naudit_graphs_distinct: 1\n",
            "conformance: workers share one exact set");
    }

}
