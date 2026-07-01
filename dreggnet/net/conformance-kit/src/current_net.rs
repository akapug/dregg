//! [`CurrentNetAdapter`] — oracle backend #1 (the ONLY backend that exists today).
//!
//! A direct in-process call into today's `net/` Rust. This is a compiling STUB:
//! [`supports`](SutAdapter::supports) reflects the real seam table (42 §5 —
//! `CurrentNet` is `Supported` on all four primitives), but the four observation
//! bodies are `todo!()` because wiring them needs `net/httpe` internals
//! (`httparse` → `validate_h1_smuggling` → `ParsedRequest::from_httparse`, the
//! `h1_response_try_parse` feed loop, miri/loom lease instrumentation). Those
//! bodies are authored by units 2-4 against THESE signatures; keeping them
//! `todo!()` lets the kit skeleton build standalone (no net/httpe dependency).
//!
//! Provenance is [`AdapterProvenance::HandWritten`] — the deliberate non-emitted
//! control witness that makes an N-way agreement independent (CR-2 honesty clause;
//! 48 C-16).

use crate::adapter::{ObservedFields, Support, SutAdapter};
use crate::ids::{BackendId, Primitive, UnitId};
use crate::observation::{Event, Observation, ResourceOp, Schedule, Spec};
use crate::provenance::{AdapterProvenance, EmittedAdapterCert, ProvenancedAdapter};

/// Oracle backend #1. `realized` is the per-`(unit, primitive)` capability set the
/// adapter has actually wired (empty in the skeleton until units 2-4 land bodies).
pub struct CurrentNetAdapter {
    realized: Vec<(UnitId, Primitive)>,
}

impl CurrentNetAdapter {
    pub fn new() -> Self {
        CurrentNetAdapter {
            realized: Vec::new(),
        }
    }

    /// Declare a `(unit, primitive)` the in-process backend can observe (a unit-2/3/4
    /// adapter body calls this as it wires real surfaces).
    pub fn with_realized(mut self, unit: UnitId, prim: Primitive) -> Self {
        self.realized.push((unit, prim));
        self
    }

    /// The observed-field set per primitive (42 §5 `CurrentNet` row).
    fn observes(prim: Primitive) -> ObservedFields {
        match prim {
            // region: arena-view + error-class + consumed (+ status/headers/body if
            // the unit emits a response).
            Primitive::Region => {
                ObservedFields::ARENA_VIEW | ObservedFields::ERROR_CLASS | ObservedFields::CONSUMED
            }
            // machine: state-trace (from ProtocolState), body, error-class, consumed.
            Primitive::Machine => {
                ObservedFields::STATE_TRACE
                    | ObservedFields::BODY
                    | ObservedFields::ERROR_CLASS
                    | ObservedFields::CONSUMED
            }
            // linear: the X-4 trace (miri/loom).
            Primitive::Linear => ObservedFields::LINEAR_TRACE,
            // shared: linearization + invariant_held (loom/shuttle).
            Primitive::Shared => ObservedFields::LINEARIZATION,
        }
    }
}

impl Default for CurrentNetAdapter {
    fn default() -> Self {
        Self::new()
    }
}

impl SutAdapter for CurrentNetAdapter {
    fn backend(&self) -> BackendId {
        BackendId::CurrentNet
    }

    fn supports(&self, unit: UnitId, prim: Primitive) -> Support {
        if self.realized.contains(&(unit, prim)) {
            Support::Supported {
                observes: Self::observes(prim),
            }
        } else {
            Support::Absent {
                reason: crate::adapter::BackendAbsentReason::PrimitiveNotApplicable,
            }
        }
    }

    fn decode_region(&self, _unit: UnitId, _input: &[u8], _spec: &Spec) -> Observation {
        // httparse::Request → validate_h1_smuggling (parsed_request.rs:119) →
        // ParsedRequest::from_httparse (:1010) → project arena() + (name, off, len)
        // triples + sidecar → ArenaView; map SmuggleViolation → ErrorClass.
        todo!("CurrentNet region decode — unit 2 adapter body (parsed_request.rs)")
    }

    fn run_machine(&self, _unit: UnitId, _spec: &Spec, _events: &[Event]) -> Observation {
        // Drive h1_response_try_parse (response_parser.rs:58) / the per-protocol FSM
        // in a feed loop, recording each tri-state as a Step; project ProtocolState
        // → StateLabel.
        todo!("CurrentNet machine feed loop — unit 3 adapter body (response_parser.rs)")
    }

    fn run_linear(&self, _unit: UnitId, _ops: &[ResourceOp]) -> Observation {
        // Instrument acquire/use/drop on BufRingLease/PooledBuf (miri/loom) into a
        // LinearTrace.
        todo!("CurrentNet linear instrumentation — unit 4 adapter body (X-4)")
    }

    fn run_shared(&self, _unit: UnitId, _schedule: &Schedule) -> Observation {
        // loom/shuttle interleaving into a Linearization.
        todo!("CurrentNet shared interleaving — unit 4 adapter body (Iris ranks 5-7)")
    }
}

impl ProvenancedAdapter for CurrentNetAdapter {
    fn provenance(&self) -> AdapterProvenance {
        AdapterProvenance::HandWritten {
            crate_path: "net/httpe",
            reviewed_rev: "UNREVIEWED-skeleton",
        }
    }
    fn cert(&self) -> Option<&EmittedAdapterCert> {
        None // not a verified compiler output — trusted glue (named, CR-2)
    }
    fn realized(&self) -> &[(UnitId, Primitive)] {
        &self.realized
    }
}
