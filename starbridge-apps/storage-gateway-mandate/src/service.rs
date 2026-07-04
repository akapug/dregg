//! # storage-gateway-mandate — the gateway as a SERVICE CELL on the `invoke()` front door.
//!
//! The third axis of a modern starbridge-app (after the
//! [`FactoryDescriptor`](crate::sgm_factory_descriptor) + [`DeosApp`] surface):
//! the gateway re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen. A `service`
//! module on the existing crate publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the storage operations through the
//! [`dregg_app_framework::invoke`] front door — the userspace method-dispatch
//! layer that sits *slightly above* the effect-VM and desugars a method call to
//! the ordinary verified effects it names. There is **no `Effect::Invoke`**, no
//! kernel change, no new circuit rung: the kernel and the light client keep
//! seeing only the [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member
//! of the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME desugared turn bodies
//!
//! `put` desugars to the IDENTICAL [`put_effects`](crate::put_effects) the deos
//! `put` fire submits, and `get` to the IDENTICAL [`get_effects`](crate::get_effects).
//! The invoked method symbol is the action method, so the seeded
//! [`gateway_program_with_clearance`](crate::gateway_program_with_clearance)
//! re-enforces the SAME teeth: the `Always` invariants
//! (`FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)`, `Monotonic(VOLUME_SPENT)`,
//! `WriteOnce` anchor/ceiling/prefix/compartment) bite on every invoked turn, and
//! the `MethodIs("get")` [`clearance_dominates_constraint`](crate::clearance_dominates_constraint)
//! re-enforces GET clearance on the invoke()-desugared GET.
//!
//! ## The published interface (the gateway as typed methods)
//!
//! | method | semantics                 | auth        | args                  | desugars to |
//! |--------|---------------------------|-------------|-----------------------|-------------|
//! | `put`  | [`Semantics::Replayable`] | `Signature` | `(key, new_spent)`    | [`put_effects`](crate::put_effects) (metered write) |
//! | `get`  | [`Semantics::Replayable`] | `Signature` | `(key, clearance)`    | [`get_effects`](crate::get_effects) (clearance-gated read) |
//! | `list` | [`Semantics::Serviced`]   | `None`      | `()`                  | — (the named OFE read seam: enumerate a prefix, never desugared) |
//!
//! `put`/`get` are **replayable**: they desugar (via `invoke()`) to a verified
//! turn whose post-state the executor checks against the gateway
//! [`CellProgram`](dregg_cell::program::CellProgram). `list` is **serviced**: an
//! enumeration is a pure read (it rides the OFE cross-cell-read, never a replay),
//! so `invoke()` refuses to desugar it and names the seam honestly rather than
//! faking a write.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused, Turn,
    field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{get_effects, object_key_field, put_effects};

// =============================================================================
// Method names
// =============================================================================

/// The `put` method — a [`Semantics::Replayable`], `Signature`-gated mutator: a
/// metered write that advances the `VOLUME_SPENT` meter ([`put_effects`](crate::put_effects)).
pub const METHOD_PUT: &str = "put";
/// The `get` method — a [`Semantics::Replayable`], `Signature`-gated mutator: a
/// clearance-gated read that materializes the actor's clearance
/// ([`get_effects`](crate::get_effects)).
pub const METHOD_GET: &str = "get";
/// The `list` method — a [`Semantics::Serviced`] read (the named OFE seam):
/// enumerate a prefix. Never desugared.
pub const METHOD_LIST: &str = "list";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The gateway's first-class typed interface** — the three methods it
/// publishes, with their auth and replayable-vs-serviced semantics.
///
/// The richer-than-derived descriptor: `derive_replayable` would make every
/// method `Replayable`/`None`, but the gateway wants its two mutators
/// `Signature`-gated and `list` marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // put(key, new_spent): a metered write.
        mutator(METHOD_PUT, 2),
        // get(key, clearance): a clearance-gated read.
        mutator(METHOD_GET, 2),
        // list(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_LIST))
        },
    ])
}

/// Register the gateway's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the gateway's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed gateway cell** — bundles the gateway cell with its
/// published interface, and builds method invocations through the `invoke()`
/// front door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it
/// through an executor
/// ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct GatewayService {
    /// The gateway cell this handle drives.
    pub cell: CellId,
    /// The gateway's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl GatewayService {
    /// A handle to the gateway cell `cell`, carrying the gateway's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        GatewayService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `put(key, new_volume_spent)`** — a metered write: advance the
    /// `VOLUME_SPENT` meter to `new_volume_spent`, record the key + op, emit
    /// `storage-op`. Desugars to the SAME [`put_effects`](crate::put_effects) the
    /// deos `put` fire submits; the executor re-enforces
    /// `FieldLteField(VOLUME_SPENT <= VOLUME_CEILING)` + `Monotonic(VOLUME_SPENT)`,
    /// so an over-budget write is a REAL executor refusal on the desugared turn.
    pub fn put(
        &self,
        cipherclerk: &AppCipherclerk,
        key: &str,
        new_volume_spent: u64,
        blob_hash: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, GatewayServiceError> {
        let effects = put_effects(self.cell, key, new_volume_spent, blob_hash);
        self.invoke(
            cipherclerk,
            METHOD_PUT,
            vec![object_key_field(key), field_from_u64(new_volume_spent)],
            effects,
            authority,
        )
    }

    /// **Invoke `get(key, actor_clearance)`** — a clearance-gated read:
    /// materialize the acting reader's clearance into `ACTOR_CLEARANCE_SLOT`,
    /// record the key + op, emit `storage-op`. Desugars to the SAME
    /// [`get_effects`](crate::get_effects) the deos `get` fire submits; the
    /// executor's `MethodIs("get")` clearance tooth re-enforces that the presented
    /// clearance DOMINATES the frozen read compartment in the root-bound graph, so
    /// a guest's GET is a REAL executor refusal while a writer's is admitted.
    pub fn get(
        &self,
        cipherclerk: &AppCipherclerk,
        key: &str,
        actor_clearance: FieldElement,
        authority: InvokeAuthority,
    ) -> Result<Turn, GatewayServiceError> {
        let effects = get_effects(self.cell, key, actor_clearance);
        self.invoke(
            cipherclerk,
            METHOD_GET,
            vec![object_key_field(key), actor_clearance],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `list()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `list` is a [`Semantics::Serviced`] read
    /// (enumerate a prefix), answered by the OFE cross-cell-read, not a replay
    /// desugar. This method exists to make the seam legible (and testable): a
    /// serviced read is not a turn, and `invoke()` will not pretend otherwise.
    pub fn list(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, GatewayServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_LIST,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this gateway's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, GatewayServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(GatewayServiceError::Refused)
    }
}

/// Why a [`GatewayService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GatewayServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for GatewayServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GatewayServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for GatewayServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_three_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 3);
        assert!(iface.verify_id());

        for m in [METHOD_PUT, METHOD_GET] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let list = iface.method(&method_symbol(METHOD_LIST)).unwrap();
        assert_eq!(list.semantics, Semantics::Serviced);
        assert_eq!(list.auth_required, AuthRequired::None);
    }

    #[test]
    fn unauthorized_put_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = GatewayService::new(cclerk.cell_id());
        // `put` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.put(
                &cclerk,
                "uploads/doc.txt",
                5,
                FieldElement::default(),
                InvokeAuthority::None
            ),
            Err(GatewayServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn list_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = GatewayService::new(cclerk.cell_id());
        assert!(matches!(
            svc.list(&cclerk),
            Err(GatewayServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
