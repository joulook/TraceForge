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
//! `plan/traceForge/conf-plan.md`. Present contents: probe mode (S1),
//! observations and the morphism (S2), and the inner search (S3). Still to
//! come: the gate that drives the search (S4) and reports (S5).

// The search now consumes the prober, but nothing yet consumes the search —
// that is S4's gate. So the module's public surface is still reachable only
// from its own tests, and the dead-code warnings are silenced *here*, bounded
// to this module, which keeps a genuinely new warning visible rather than
// buried among expected ones.
//
// **This should shrink, not stay.** Review round 6 noted the previous version
// of this comment still said the search had not landed. When S4 gives the
// module a caller, narrow this to the items that remain genuinely unused, or
// drop it — a blanket allow that outlives its reason is how the next real
// warning gets missed.
#![allow(dead_code)]

pub(crate) mod morphism;
pub(crate) mod obs;
pub(crate) mod probe;
pub(crate) mod prober;
pub(crate) mod search;

#[cfg(test)]
pub(crate) mod adversarial;
#[cfg(test)]
pub(crate) mod testing;
