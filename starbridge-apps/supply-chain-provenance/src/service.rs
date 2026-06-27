//! # supply-chain-provenance — the custody lifecycle as a SERVICE CELL on the
//! `invoke()` front door.
//!
//! The custody lifecycle (mint → handoff → …) re-expressed as a
//! CELLS-AS-SERVICE-OBJECTS citizen (after the `starbridge-bounty-board`,
//! `starbridge-kvstore`, and `starbridge-escrow-market` exemplars). A new
//! `service` module on the existing crate: it publishes a first-class, typed
//! [`InterfaceDescriptor`] and drives the custody lifecycle through the
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
//! ## Non-degrading: the SAME canonical custody program
//!
//! The service face desugars to the IDENTICAL effects the
//! [`mint_effects_signed`](crate::mint_effects_signed) /
//! [`accept_custody_effects`](crate::accept_custody_effects) builders produce,
//! against a cell carrying the IDENTICAL canonical
//! [`item_program`](crate::item_program) the
//! [`FactoryDescriptor`](crate::item_factory_descriptor) bakes into every
//! factory-born item cell. So the custody teeth re-enforce on every
//! invoke()-desugared turn exactly as they do on a factory-born cell's turns:
//!
//! | Slot              | Caveat                          | Bites on |
//! |-------------------|---------------------------------|----------|
//! | `CUSTODIAN`       | `AnyOf[Immutable, SenderInSlot]`| every handoff (the baton accepts only the SIGNER) |
//! | `EPOCH`           | `StrictMonotonic`               | every turn (no replay — `mint` 0→1, handoffs 1→2→…) |
//! | `HEAD`            | `Monotonic`                     | every handoff (append-only chain) |
//! | `LINK_BASE + i`   | `WriteOnce`                     | each handoff (a committed link is frozen) |
//!
//! The `FactoryDescriptor` federation surface, the
//! [`DeosApp`](dregg_app_framework::DeosApp) composition skin
//! ([`item_app`](crate::item_app)), and the inspector are UNCHANGED — this
//! module is the service-object FACE of the same item primitive.
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method    | semantics                | auth        | args                       | desugars to |
//! |-----------|--------------------------|-------------|----------------------------|-------------|
//! | `mint`    | [`Semantics::Replayable`]| `Signature` | `()`                       | `SetField(CUSTODIAN=signer, EPOCH=1, link_0, HEAD=1, TIP)` |
//! | `handoff` | [`Semantics::Replayable`]| `Signature` | `(from, prev, epoch, i)`   | `SetField(CUSTODIAN=signer, EPOCH, link_i, HEAD, TIP)` |
//! | `view`    | [`Semantics::Serviced`]  | `None`      | `()`                       | — (the named OFE seam: a pure read, no turn) |
//!
//! `mint`/`handoff` are **replayable**: they desugar (via `invoke()`) to a
//! verified turn whose post-state the executor checks against the item
//! [`CellProgram`](dregg_cell::program::CellProgram). `view` is **serviced**:
//! the item's committed custody state IS the answer (it rides the OFE
//! cross-cell-read, not a replay), so `invoke()` refuses to desugar it and names
//! the seam honestly rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is
//! built — anti-ghost) and again by the executor (the desugared turn carries a
//! real signature the kernel verifies). The lifecycle is a rollback-proof one-way
//! ratchet at the verified commit path: `EPOCH` is `StrictMonotonic`, so a
//! replayed/stale handoff (and a second `mint`) is an EXECUTOR REFUSAL, not a
//! userspace check — and the actor-bound `AnyOf[Immutable, SenderInSlot]` baton
//! refuses any turn that flips `CUSTODIAN` to a party other than the signer.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    field_from_u64, invoke_with_descriptor,
};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_turn::Turn;
use dregg_types::CellId;

use crate::{accept_custody_effects, mint_effects_signed, signer_identity};

// =============================================================================
// Method names
// =============================================================================

/// The `mint` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// inaugurate the sole custodian (bind `CUSTODIAN = signer`, `EPOCH → 1`, append
/// the genesis custody link).
pub const METHOD_MINT: &str = "mint";
/// The `handoff` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// the incoming holder accepts custody (advance the actor-bound baton to the
/// signer, strictly advance `EPOCH`, append the `WriteOnce` link, advance `HEAD`).
pub const METHOD_HANDOFF: &str = "handoff";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read
/// the item's committed custody state + provenance chain. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The item's first-class typed interface** — the three methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make
/// every method `Replayable`/`None`, but the item wants its two mutators
/// `Signature`-gated and `view` marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam
/// shape, not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // mint(): inaugurate the sole custodian (the signer takes the baton).
        mutator(METHOD_MINT, 0),
        // handoff(from, prev, epoch, i): the incoming holder accepts custody.
        mutator(METHOD_HANDOFF, 4),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the item's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults
/// before falling back to derive-from-program. After this, the explorer resolves
/// the item's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed item cell** — bundles the item cell with its
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
pub struct ProvenanceService {
    /// The item cell this handle drives.
    pub cell: CellId,
    /// The item's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl ProvenanceService {
    /// A handle to the item cell `cell`, carrying the item's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        ProvenanceService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `mint()`** — inaugurate the sole custodian: bind `CUSTODIAN` to
    /// the signer's own identity (so the actor-bound `SenderInSlot` admits the
    /// inception), advance `EPOCH` 0 → 1 (`StrictMonotonic`, admitted from zero on
    /// this first turn), append the genesis custody link, advance `HEAD`, point
    /// `TIP`. Routes through the verified DFA, cap-gates on `Signature`, and
    /// desugars to the [`mint_effects_signed`](crate::mint_effects_signed) effects
    /// targeting the `mint` method symbol. A second `mint` is a no-advance
    /// `EPOCH 1 → 1` the executor's `StrictMonotonic(EPOCH)` refuses.
    pub fn mint(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, ProvenanceServiceError> {
        let effects = mint_effects_signed(cipherclerk, self.cell);
        self.invoke(
            cipherclerk,
            METHOD_MINT,
            vec![signer_identity(cipherclerk)],
            effects,
            authority,
        )
    }

    /// **Invoke `handoff(from, prev, epoch, i)`** — the incoming holder accepts
    /// custody: advance the actor-bound baton to the signer's own identity (so
    /// `SenderInSlot` admits), strictly advance `EPOCH` (no-replay), append the
    /// `WriteOnce` custody-receipt link at index `i`, advance `HEAD`, point `TIP`.
    ///
    /// `from` is the outgoing custodian's identity scalar (the current register
    /// value), `prev` is the chain tip the new link folds, `new_epoch` is the
    /// strictly-greater epoch, and `i` is the link index (the current `HEAD`).
    /// A stale `new_epoch`, a non-signer baton flip, or a re-used link index is a
    /// real executor refusal on the desugared turn.
    pub fn handoff(
        &self,
        cipherclerk: &AppCipherclerk,
        from: &FieldElement,
        prev: &FieldElement,
        new_epoch: u64,
        i: usize,
        authority: InvokeAuthority,
    ) -> Result<Turn, ProvenanceServiceError> {
        let to = signer_identity(cipherclerk); // the incoming holder IS the signer
        let effects = accept_custody_effects(cipherclerk, self.cell, from, prev, new_epoch, i);
        self.invoke(
            cipherclerk,
            METHOD_HANDOFF,
            vec![
                *from,
                to,
                field_from_u64(new_epoch),
                field_from_u64(i as u64),
            ],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the item's committed custody state +
    /// provenance chain), not a replay desugar. This method exists to make the
    /// seam legible (and testable): a serviced read is not a turn, and `invoke()`
    /// will not pretend otherwise. To actually READ the item, read the committed
    /// state at the item's slots ([`CUSTODIAN_SLOT`](crate::CUSTODIAN_SLOT),
    /// [`EPOCH_SLOT`](crate::EPOCH_SLOT), [`TIP_SLOT`](crate::TIP_SLOT), the link
    /// slots) and re-derive the chain with [`verify_chain`](crate::verify_chain).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, ProvenanceServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door
    /// against this item's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, ProvenanceServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(ProvenanceServiceError::Refused)
    }
}

/// Why a [`ProvenanceService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProvenanceServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority,
    /// or a serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for ProvenanceServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ProvenanceServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for ProvenanceServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_three_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 3);
        assert!(iface.verify_id());

        for m in [METHOD_MINT, METHOD_HANDOFF] {
            let sig = iface.method(&method_symbol(m)).unwrap();
            assert_eq!(sig.semantics, Semantics::Replayable, "{m} is replayable");
            assert_eq!(
                sig.auth_required,
                AuthRequired::Signature,
                "{m} is sig-gated"
            );
        }
        let view = iface.method(&method_symbol(METHOD_VIEW)).unwrap();
        assert_eq!(view.semantics, Semantics::Serviced);
        assert_eq!(view.auth_required, AuthRequired::None);
    }

    #[test]
    fn the_interface_names_the_lifecycle_vocabulary() {
        let iface = interface_descriptor();
        for m in [METHOD_MINT, METHOD_HANDOFF, METHOD_VIEW] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn unauthorized_mint_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = ProvenanceService::new(cclerk.cell_id());
        // `mint` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.mint(&cclerk, InvokeAuthority::None),
            Err(ProvenanceServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = ProvenanceService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(ProvenanceServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
