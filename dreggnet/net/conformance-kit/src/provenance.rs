//! Provenance & emission (48 §4 "the trait object the RUNNER actually holds";
//! 46).
//!
//! The runner holds [`ProvenancedAdapter`] (= [`SutAdapter`] + provenance), NOT a
//! bare `&dyn SutAdapter` (48 C-16): an all-emitted N-way agreement is a compiler
//! monoculture and must score zero, so the runner needs each backend's
//! [`AdapterProvenance`] to apply [`nway_has_independent_witness`]. This module
//! also pins the codegen hook ([`DslUnit`] + [`GeneratedAdapter`]) by which the
//! generated engine plugs in **for free**, and the [`FormalModelAdapter`] wrapper
//! that lifts a bare [`ModelBridgeFn`] into the uniform surface (48 C-17).

use core::marker::PhantomData;

use crate::adapter::{BackendAbsentReason, ObservedFields, Support, SutAdapter};
use crate::hash::ContentHash;
use crate::ids::{BackendId, Primitive, UnitId};
use crate::observation::{Event, Observation, Produced, ResourceOp, Schedule, Spec};
use crate::vector::Input;

/// Where a [`SutAdapter`] impl came from. Recorded per backend so an emitted
/// adapter and a hand-written one are NEVER conflated (CR-6: provenance is
/// evidence, not metadata — it drives the TCB ledger AND the non-vacuity gate).
pub enum AdapterProvenance {
    /// Emitted by the verified compiler from the SAME DSL description as the
    /// artifact under test. Covered by the faithful-projection clause.
    CompilerEmitted(EmittedAdapterCert),
    /// CakeML-extracted runnable model fn `obs_Φ ∘ step_Φ`. Also a compiler
    /// artifact (hence non-independent for the monoculture gate).
    ModelExtracted {
        theory: &'static str,
        extract_rev: ContentHash,
    },
    /// Hand-written for a backend the compiler does not emit (the `CurrentNet`
    /// baseline — the deliberate non-emitted control witness). Named-trusted.
    HandWritten {
        crate_path: &'static str,
        reviewed_rev: &'static str,
    },
    /// Out-of-process oracle wrapper (an external reference engine). CR-3: read via IPC, NEVER linked.
    OracleWrapper {
        transport: OracleTransport,
        observed: ObservationMode,
    },
}

impl AdapterProvenance {
    /// The compiler-monoculture half of the independence gate: emitted backends
    /// (`CompilerEmitted` / `ModelExtracted`) are NOT independent witnesses.
    pub fn is_emitted(&self) -> bool {
        matches!(
            self,
            AdapterProvenance::CompilerEmitted(_) | AdapterProvenance::ModelExtracted { .. }
        )
    }
}

pub enum OracleTransport {
    Subprocess { argv0: &'static str },
    UnixIpc { sock: &'static str },
}

/// Which slice of [`Observation`] a backend can furnish. A wire-only oracle ⇒
/// `WireOnly`; the gaps are reported `Absent`, never laundered. The emitted engine
/// adapter is `Full`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ObservationMode {
    Full,
    WireOnly,
}

/// Binds an emitted adapter to BOTH the artifact and the proof. `dsl_unit` is the
/// SAME content hash the `{code, model, proofs}` triple is keyed to
/// (`20-ARCHITECTURE.md:24`).
#[derive(Clone)]
pub struct EmittedAdapterCert {
    pub dsl_unit: DslUnitHash,
    pub artifact_hash: ArtifactHash,
    pub model_hash: ModelHash,
    pub compiler_rev: CompilerRev,
    pub projection: ProjectionTheoremRef,
}

/// Handle to the lemma stating the adapter is a faithful projection of the sans-IO
/// core: `observe(U,i) == lift(obs_Φ(step_Φ(U, decode(i))))`. `holds_modulo` names
/// any axioms the refinement leans on — an honest gap, surfaced, never hidden. A
/// `None` projection handle ⇒ NOT covered ⇒ treat as trusted glue.
#[derive(Clone)]
pub struct ProjectionTheoremRef {
    pub theory: &'static str,
    pub theorem: &'static str,
    pub unit: UnitId,
    pub holds_modulo: &'static [AxiomId],
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AxiomId(pub &'static str);

// content-addressed identities (newtypes over the kit's ContentHash)
#[derive(Clone, Copy)]
pub struct DslUnitHash(pub ContentHash);
#[derive(Clone, Copy)]
pub struct ArtifactHash(pub ContentHash);
#[derive(Clone, Copy)]
pub struct ModelHash(pub ContentHash);
#[derive(Clone, Copy)]
pub struct CompilerRev(pub &'static str);

/// Additive SUPERTRAIT over the FIXED [`SutAdapter`] spine — does NOT mutate it.
/// The runner requires this to read provenance, the cert, and the compile-time
/// realized set.
pub trait ProvenancedAdapter: SutAdapter {
    fn provenance(&self) -> AdapterProvenance;
    /// `Some` iff this adapter is a verified compiler output. `None` ⇒ trusted
    /// glue.
    fn cert(&self) -> Option<&EmittedAdapterCert>;
    /// Compile-time-known realized set, per-`(unit, primitive)` (48 C-14/C-15) —
    /// DERIVED FROM `D`, not a runtime guess. Drives `supports()`: `Supported` iff
    /// `(unit, prim) ∈ realized()`. CR-6-by-construction.
    fn realized(&self) -> &[(UnitId, Primitive)];
}

// ── the codegen hook: the generated engine plugs in for FREE (42 §7, 48 C-15) ───

/// The hook the verified compiler implements per unit. Each method is the
/// compiler-emitted sans-IO entry for one primitive of one unit.
pub trait DslUnit {
    const UNIT: UnitId;
    /// Per-primitive capability (48 C-15): `Some(fields)` iff this unit realizes
    /// `p`. Never blanket `all()` — an early engine realizing `region` but not
    /// `shared` must NOT falsely claim `LINEARIZATION`.
    fn realizes(p: Primitive) -> Option<ObservedFields>;
    fn region(input: &[u8], spec: &Spec) -> Produced;
    fn machine(spec: &Spec, events: &[Event]) -> Produced;
    fn linear(ops: &[ResourceOp]) -> Produced;
    fn shared(schedule: &Schedule) -> Produced;
}

/// The blanket adapter the compiler emits — a thin newtype over a [`DslUnit`].
/// `GeneratedAdapter<U>` IS the `Box<dyn ProvenancedAdapter>` shipped in the
/// `EmittedKitBundle`, with `provenance() = CompilerEmitted(cert)` (48 C-15).
pub struct GeneratedAdapter<U: DslUnit> {
    cert: EmittedAdapterCert,
    realized: Vec<(UnitId, Primitive)>,
    _u: PhantomData<U>,
}

impl<U: DslUnit> GeneratedAdapter<U> {
    /// Construct from the emitted cert. `realized` is computed from `U::realizes`
    /// over the four primitives (the compile-time-known capability set).
    pub fn new(cert: EmittedAdapterCert) -> Self {
        let realized = [
            Primitive::Region,
            Primitive::Machine,
            Primitive::Linear,
            Primitive::Shared,
        ]
        .into_iter()
        .filter(|p| U::realizes(*p).is_some())
        .map(|p| (U::UNIT, p))
        .collect();
        GeneratedAdapter {
            cert,
            realized,
            _u: PhantomData,
        }
    }
}

impl<U: DslUnit> SutAdapter for GeneratedAdapter<U> {
    fn backend(&self) -> BackendId {
        BackendId::GeneratedEngine
    }

    fn supports(&self, unit: UnitId, prim: Primitive) -> Support {
        if unit != U::UNIT {
            return Support::Absent {
                reason: BackendAbsentReason::EngineNotYetEmitted,
            };
        }
        match U::realizes(prim) {
            Some(observes) => Support::Supported { observes },
            None => Support::Absent {
                reason: BackendAbsentReason::PrimitiveNotApplicable,
            },
        }
    }

    fn decode_region(&self, unit: UnitId, input: &[u8], spec: &Spec) -> Observation {
        match self.supports(unit, Primitive::Region) {
            Support::Supported { .. } => Observation::Produced(U::region(input, spec)),
            Support::Absent { reason } => Observation::Absent { reason },
        }
    }

    fn run_machine(&self, unit: UnitId, spec: &Spec, events: &[Event]) -> Observation {
        match self.supports(unit, Primitive::Machine) {
            Support::Supported { .. } => Observation::Produced(U::machine(spec, events)),
            Support::Absent { reason } => Observation::Absent { reason },
        }
    }

    fn run_linear(&self, unit: UnitId, ops: &[ResourceOp]) -> Observation {
        match self.supports(unit, Primitive::Linear) {
            Support::Supported { .. } => Observation::Produced(U::linear(ops)),
            Support::Absent { reason } => Observation::Absent { reason },
        }
    }

    fn run_shared(&self, unit: UnitId, schedule: &Schedule) -> Observation {
        match self.supports(unit, Primitive::Shared) {
            Support::Supported { .. } => Observation::Produced(U::shared(schedule)),
            Support::Absent { reason } => Observation::Absent { reason },
        }
    }
}

impl<U: DslUnit> ProvenancedAdapter for GeneratedAdapter<U> {
    fn provenance(&self) -> AdapterProvenance {
        AdapterProvenance::CompilerEmitted(self.cert.clone())
    }
    fn cert(&self) -> Option<&EmittedAdapterCert> {
        Some(&self.cert)
    }
    fn realized(&self) -> &[(UnitId, Primitive)] {
        &self.realized
    }
}

/// The `FormalModel` backend's runnable step — the CakeML-extracted `obs_Φ ∘
/// step_Φ` the runner calls (`harness/executable-model-bridge`, `41:334`). Its
/// result IS an [`Observation`], so it is comparable field-for-field.
pub type ModelBridgeFn =
    fn(unit: UnitId, prim: Primitive, input: &Input, spec: &Spec) -> Observation;

/// Wraps a bare [`ModelBridgeFn`] into the uniform [`ProvenancedAdapter`] surface
/// (48 C-17): the runner sees `&dyn ProvenancedAdapter`; the bundle ships the bare
/// fn. The four methods dispatch the resolved typed args back into a stored
/// [`Input`] and call the bridge.
pub struct FormalModelAdapter {
    pub bridge: ModelBridgeFn,
    pub theory: &'static str,
    pub extract_rev: ContentHash,
    pub realized: Vec<(UnitId, Primitive)>,
}

impl SutAdapter for FormalModelAdapter {
    fn backend(&self) -> BackendId {
        BackendId::FormalModel
    }

    fn supports(&self, unit: UnitId, prim: Primitive) -> Support {
        // `shared` is honestly Absent for the model: Iris logical-atomicity is not
        // extraction-executable as a runtime schedule enumerator (42 tension #5).
        if prim == Primitive::Shared {
            return Support::Absent {
                reason: BackendAbsentReason::PrimitiveNotApplicable,
            };
        }
        if self.realized.contains(&(unit, prim)) {
            // region/machine/linear field sets are computed by the model-bridge
            // unit per the seam table (42 §5).
            todo!("FormalModel observed-field set per (unit, primitive) — model-bridge unit")
        } else {
            Support::Absent {
                reason: BackendAbsentReason::ProjectionClauseUndischarged { unit },
            }
        }
    }

    fn decode_region(&self, _unit: UnitId, _input: &[u8], _spec: &Spec) -> Observation {
        // The resolved `&[u8]` ↔ stored `Input::Bytes(InputHash)` reconciliation
        // is the model-bridge unit's job (CAS round-trip). Deferred seam.
        todo!("dispatch resolved region args into Input + call ModelBridgeFn (48 C-17)")
    }
    fn run_machine(&self, _unit: UnitId, _spec: &Spec, _events: &[Event]) -> Observation {
        todo!("dispatch resolved machine args into Input + call ModelBridgeFn (48 C-17)")
    }
    fn run_linear(&self, _unit: UnitId, _ops: &[ResourceOp]) -> Observation {
        todo!("dispatch resolved linear args into Input + call ModelBridgeFn (48 C-17)")
    }
    fn run_shared(&self, _unit: UnitId, _schedule: &Schedule) -> Observation {
        Observation::Absent {
            reason: BackendAbsentReason::PrimitiveNotApplicable,
        }
    }
}

impl ProvenancedAdapter for FormalModelAdapter {
    fn provenance(&self) -> AdapterProvenance {
        AdapterProvenance::ModelExtracted {
            theory: self.theory,
            extract_rev: self.extract_rev,
        }
    }
    fn cert(&self) -> Option<&EmittedAdapterCert> {
        None
    }
    fn realized(&self) -> &[(UnitId, Primitive)] {
        &self.realized
    }
}

/// The compiler's FOURTH output group for one DSL unit: shim + bridge + hooks, all
/// keyed to one `DslUnitHash`. `compile(D)` emits one per realized unit, ALONGSIDE
/// the status-quo `{machine_code, formal_model, proofs}`.
pub struct EmittedKitBundle {
    pub unit: UnitId,
    pub dsl_unit: DslUnitHash,
    /// (i) the generated-engine SUT shim ([`GeneratedAdapter`]).
    pub adapter: Box<dyn ProvenancedAdapter>,
    /// (ii) the extracted runnable model fn.
    pub model_bridge: ModelBridgeFn,
    /// (iii) the perf-instrumentation contract (48 C-13: the name is
    /// `ArtifactInstrumentation`, owned by `45`).
    pub perf_hooks: Box<dyn crate::perf::ArtifactInstrumentation>,
}

/// CR-6 INDEPENDENCE gate the runner MUST apply: an N-way agreement is a genuine
/// match ONLY if ≥1 agreeing backend is NOT compiler-emitted (a `HandWritten` or
/// `OracleWrapper`). All-emitted agreement ⇒ non-independent ⇒ uncounted. Guards
/// against compiler monoculture. REAL.
pub fn nway_has_independent_witness(agreeing: &[AdapterProvenance]) -> bool {
    agreeing.iter().any(|p| !p.is_emitted())
}

/// Build-time CR-3 firewall predicate (`harness/oracle-provenance-firewall`,
/// `41:332`): the engine link set must be disjoint from oracle symbols. `Err` =
/// the offending symbols; a non-empty `Err` FAILS THE BUILD.
pub fn engine_link_set_excludes_oracle(link_syms: &[&str]) -> Result<(), Vec<String>> {
    let offending: Vec<String> = link_syms
        .iter()
        .filter(|s| {
            s.contains("dhttp") || s.contains("external_http") || s.contains("oracle_dhttp")
        })
        .map(|s| s.to_string())
        .collect();
    if offending.is_empty() {
        Ok(())
    } else {
        Err(offending)
    }
}
