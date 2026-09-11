//! Conformance verification: does one program's visible behaviour refine
//! another's?
//!
//! The implementation and the specification are both ordinary TraceForge
//! programs. The implementation is explored by the stock Must engine; the
//! specification is consulted through [`probe`] executions, which report what
//! it could do next without committing to any of it. A search over
//! specification graphs then tries those options, looking for one that matches
//! what the implementation has done so far.
//!
//! This module is being built step by step; see
//! `plan/traceForge/conf-plan.md`. Present contents: probe mode.

// Probe mode is complete and tested, but nothing consumes it yet: the search
// that calls `probe_from`/`install` is the next step. Until it lands, most of
// this module is reachable only from its own tests, so the dead-code warnings
// are silenced *here*, bounded to this module — which keeps a genuinely new
// warning visible rather than buried in a dozen expected ones. Remove this
// when the search is wired in.
#![allow(dead_code)]

pub(crate) mod probe;
pub(crate) mod prober;
