//! # sealed-auction — the lifecycle as a SERVICE CELL on the `invoke()` front door.
//!
//! The commit-reveal auction re-expressed as a CELLS-AS-SERVICE-OBJECTS citizen
//! (after the `starbridge-kvstore`, `starbridge-nameservice`, and
//! `starbridge-bounty-board` exemplars). A new `service` module on the existing
//! crate: it publishes a first-class, typed [`InterfaceDescriptor`] and drives the
//! auction lifecycle through the [`dregg_app_framework::invoke`] front door — the
//! userspace method-dispatch layer that sits *slightly above* the effect-VM and
//! desugars a method call to the ordinary verified effects it names. There is
//! **no `Effect::Invoke`**, no kernel change, no new circuit rung: the kernel and
//! the light client keep seeing only the
//! [`SetField`](dregg_app_framework::Effect::SetField) /
//! [`EmitEvent`](dregg_app_framework::Effect::EmitEvent) effects they already
//! enforce and witness. The one extra fact — that an invoked method is a member of
//! the cell's interface — is decided by the SAME verified DFA router
//! ([`InterfaceDescriptor::route_method`]) the protocol already uses.
//!
//! ## Non-degrading: the SAME canonical lifecycle program
//!
//! The service face drives a cell carrying the IDENTICAL canonical
//! [`auction_cell_program`](crate::auction_cell_program) the
//! [`auction_factory_descriptor`](crate::auction_factory_descriptor) bakes into
//! every factory-born auction cell. So the lifecycle teeth re-enforce on every
//! invoke()-desugared turn exactly as they do on a factory-born cell's turns:
//!
//! | Slot            | Caveat                  | Bites on |
//! |-----------------|-------------------------|----------|
//! | `COMMIT_BASE+i` | `WriteOnce`             | `commit_bid` (a committed bid is frozen — anti-front-running) |
//! | `PHASE`         | `StrictMonotonic`       | `close_commit` / `resolve` (one-way advance, no re-fire) |
//! | `SELLER`        | `WriteOnce`             | bound at seed |
//! | `WINNER`/`HIGH_BID` | `WriteOnce`         | `resolve` (the result freezes once announced) |
//!
//! The [`FactoryDescriptor`](dregg_app_framework::FactoryDescriptor) federation
//! surface, the [`DeosApp`](dregg_app_framework::DeosApp) composition skin
//! ([`auction_app`](crate::auction_app)), and the inspector are UNCHANGED — this
//! module is the service-object FACE of the same auction primitive.
//!
//! ## The published interface (the lifecycle as typed methods)
//!
//! | method         | semantics                | auth        | args                | desugars to |
//! |----------------|--------------------------|-------------|---------------------|-------------|
//! | `commit_bid`   | [`Semantics::Replayable`]| `Signature` | `(seal)`            | `SetField(COMMIT_BASE+i)` + `EmitEvent` |
//! | `close_commit` | [`Semantics::Replayable`]| `Signature` | `()`                | `SetField(PHASE=REVEAL)` + `EmitEvent` |
//! | `reveal_bid`   | [`Semantics::Replayable`]| `Signature` | `(bidder, value)`   | `EmitEvent(reveal)` |
//! | `resolve`      | [`Semantics::Replayable`]| `Signature` | `(winner, high_bid)`| `SetField(WINNER, HIGH_BID, PHASE=RESOLVED)` + `EmitEvent` |
//! | `view`         | [`Semantics::Serviced`]  | `None`      | `()`                | — (the named OFE seam: a pure read, no turn) |
//!
//! `commit_bid`/`close_commit`/`reveal_bid`/`resolve` are **replayable**: they
//! desugar (via `invoke()`) to a verified turn whose post-state the executor checks
//! against the auction [`CellProgram`](dregg_cell::program::CellProgram). `view` is
//! **serviced**: the auction's committed lifecycle state IS the answer (it rides the
//! OFE cross-cell-read, not a replay), so `invoke()` refuses to desugar it and names
//! the seam honestly rather than faking a write.
//!
//! ## The verified guarantee (the program bites)
//!
//! The cap-gate (`Signature` on every mutator) is enforced twice over: at the
//! `invoke()` front door (an unauthorized caller is refused before any turn is built
//! — anti-ghost) and again by the executor (the desugared turn carries a real
//! signature the kernel verifies). The lifecycle is a rollback-proof one-way ratchet
//! at the verified commit path: `PHASE` is `StrictMonotonic` (on the phase-advancing
//! methods), so a replayed/reordered/no-advance step is an EXECUTOR REFUSAL — and a
//! committed sealed bid is frozen (`WriteOnce(COMMIT_BASE+i)`, anti-front-running) as
//! a real refusal on the invoke()-desugared turn.

use dregg_app_framework::{
    AppCipherclerk, Effect, FieldElement, InterfaceRegistry, InvokeAuthority, InvokeRefused,
    field_from_u64, invoke_with_descriptor,
};
use dregg_app_framework::{CellId, Turn};
use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;

use crate::{Seal, close_commit_effects, commit_bid_effects, resolve_effects, reveal_bid_effects};

// =============================================================================
// Method names
// =============================================================================

/// The `commit_bid` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// write a sealed commitment into a fresh `WriteOnce` commit slot (anti-front-running).
pub const METHOD_COMMIT_BID: &str = "commit_bid";
/// The `close_commit` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// seal the commit phase, advancing `PHASE → REVEAL` (`StrictMonotonic`).
pub const METHOD_CLOSE_COMMIT: &str = "close_commit";
/// The `reveal_bid` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// record an opened bid's `(bidder, value)` (the phase is not advanced).
pub const METHOD_REVEAL_BID: &str = "reveal_bid";
/// The `resolve` method — a [`Semantics::Replayable`], `Signature`-gated mutator:
/// announce the winner — write `WINNER` / `HIGH_BID` (`WriteOnce`) and advance
/// `PHASE → RESOLVED` (`StrictMonotonic`, terminal).
pub const METHOD_RESOLVE: &str = "resolve";
/// The `view` method — a [`Semantics::Serviced`] read (the named OFE seam): read the
/// auction's committed lifecycle state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The auction's first-class typed interface** — the five methods it publishes,
/// with their auth and replayable-vs-serviced semantics.
///
/// This is the richer-than-derived descriptor: `derive_replayable` would make every
/// method `Replayable`/`None`, but the auction wants its four mutators
/// `Signature`-gated and `view` marked `Serviced`. An app registers THIS in an
/// [`InterfaceRegistry`] so the Service Explorer resolves the real auth + seam shape,
/// not the permissive derived default.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // commit_bid(seal): seal a bid into a fresh WriteOnce commit slot.
        mutator(METHOD_COMMIT_BID, 1),
        // close_commit(): seal the commit phase (COMMIT → REVEAL).
        mutator(METHOD_CLOSE_COMMIT, 0),
        // reveal_bid(bidder, value): open a committed bid.
        mutator(METHOD_REVEAL_BID, 2),
        // resolve(winner, high_bid): announce the winner (REVEAL → RESOLVED).
        mutator(METHOD_RESOLVE, 2),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the auction's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`] — the resolution path the Service Explorer consults before
/// falling back to derive-from-program. After this, the explorer resolves the
/// auction's real `Signature`/`Serviced` shape.
pub fn register_interface(registry: &mut InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — building invocations through invoke()
// =============================================================================

/// **A handle to a deployed auction cell** — bundles the auction cell with its
/// published interface, and builds method invocations through the `invoke()` front
/// door.
///
/// Each builder returns a fully-signed [`Turn`] (the build half); submit it through
/// an executor ([`dregg_app_framework::EmbeddedExecutor::submit_turn`], a node
/// `/turns/submit`, …) to actually commit. A refusal at the front door (unknown
/// method, insufficient authority, a serviced seam) is surfaced as an
/// [`InvokeRefused`] before any turn is built — fail-closed.
#[derive(Clone, Debug)]
pub struct AuctionService {
    /// The auction cell this handle drives.
    pub cell: CellId,
    /// The auction's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl AuctionService {
    /// A handle to the auction cell `cell`, carrying the auction's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        AuctionService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `commit_bid(seal)`** — seal a bid into the commit slot `slot` (a fresh
    /// `WriteOnce` slot, admitted from zero on this turn). Routes through the verified
    /// DFA, cap-gates on `Signature`, and desugars to the underlying commit effects
    /// targeting the `commit_bid` method symbol. Overwriting a committed slot is a real
    /// executor refusal (`WriteOnce` — the anti-front-running tooth).
    pub fn commit_bid(
        &self,
        cipherclerk: &AppCipherclerk,
        slot: usize,
        seal: Seal,
        authority: InvokeAuthority,
    ) -> Result<Turn, AuctionServiceError> {
        let effects = commit_bid_effects(self.cell, slot, &seal);
        self.invoke(
            cipherclerk,
            METHOD_COMMIT_BID,
            vec![seal],
            effects,
            authority,
        )
    }

    /// **Invoke `close_commit()`** — the auctioneer seals the commit phase: advance
    /// `PHASE → REVEAL`. A rewind or no-advance is an executor refusal
    /// (`StrictMonotonic(PHASE)`).
    pub fn close_commit(
        &self,
        cipherclerk: &AppCipherclerk,
        authority: InvokeAuthority,
    ) -> Result<Turn, AuctionServiceError> {
        let effects = close_commit_effects(self.cell);
        self.invoke(cipherclerk, METHOD_CLOSE_COMMIT, vec![], effects, authority)
    }

    /// **Invoke `reveal_bid(bidder, value)`** — a bidder opens its committed bid,
    /// recording `(bidder, value)` (the phase is not advanced).
    pub fn reveal_bid(
        &self,
        cipherclerk: &AppCipherclerk,
        bidder: FieldElement,
        value: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, AuctionServiceError> {
        let effects = reveal_bid_effects(self.cell, bidder, value);
        self.invoke(
            cipherclerk,
            METHOD_REVEAL_BID,
            vec![bidder, field_from_u64(value)],
            effects,
            authority,
        )
    }

    /// **Invoke `resolve(winner, high_bid)`** — the auctioneer announces the winner:
    /// write `WINNER` / `HIGH_BID` (`WriteOnce`) and advance `PHASE → RESOLVED`
    /// (`StrictMonotonic`, terminal). A re-resolve is a no-advance the executor refuses.
    pub fn resolve(
        &self,
        cipherclerk: &AppCipherclerk,
        winner: FieldElement,
        high_bid: u64,
        authority: InvokeAuthority,
    ) -> Result<Turn, AuctionServiceError> {
        let effects = resolve_effects(self.cell, winner, high_bid);
        self.invoke(
            cipherclerk,
            METHOD_RESOLVE,
            vec![winner, field_from_u64(high_bid)],
            effects,
            authority,
        )
    }

    /// **Attempt to invoke `view()`** — which ALWAYS refuses with
    /// [`InvokeRefused::ServicedSeam`]: `view` is a [`Semantics::Serviced`] read,
    /// answered by the OFE cross-cell-read (the auction's committed lifecycle state),
    /// not a replay desugar. This method exists to make the seam legible (and
    /// testable): a serviced read is not a turn, and `invoke()` will not pretend
    /// otherwise. To actually READ the auction, read the committed state at the
    /// auction's slots ([`PHASE_SLOT`](crate::PHASE_SLOT), …).
    pub fn view(&self, cipherclerk: &AppCipherclerk) -> Result<Turn, AuctionServiceError> {
        self.invoke(
            cipherclerk,
            METHOD_VIEW,
            vec![],
            vec![],
            InvokeAuthority::None,
        )
    }

    /// Route → cap-gate → desugar → sign, through the `invoke()` front door against
    /// this auction's published descriptor.
    fn invoke(
        &self,
        cipherclerk: &AppCipherclerk,
        method: &str,
        args: Vec<FieldElement>,
        effects: Vec<Effect>,
        authority: InvokeAuthority,
    ) -> Result<Turn, AuctionServiceError> {
        invoke_with_descriptor(
            cipherclerk,
            self.cell,
            &self.descriptor,
            method,
            args,
            effects,
            authority,
        )
        .map_err(AuctionServiceError::Refused)
    }
}

/// Why an [`AuctionService`] invocation could not be built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuctionServiceError {
    /// The `invoke()` front door refused (unknown method, insufficient authority, or a
    /// serviced seam) — fail-closed, no turn built.
    Refused(InvokeRefused),
}

impl std::fmt::Display for AuctionServiceError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AuctionServiceError::Refused(r) => write!(f, "invoke refused: {r}"),
        }
    }
}

impl std::error::Error for AuctionServiceError {}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::AgentCipherclerk;

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [
            METHOD_COMMIT_BID,
            METHOD_CLOSE_COMMIT,
            METHOD_REVEAL_BID,
            METHOD_RESOLVE,
        ] {
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
    fn the_published_interface_names_the_lifecycle_vocabulary() {
        let iface = interface_descriptor();
        for m in [
            METHOD_COMMIT_BID,
            METHOD_CLOSE_COMMIT,
            METHOD_REVEAL_BID,
            METHOD_RESOLVE,
            METHOD_VIEW,
        ] {
            assert!(iface.method(&method_symbol(m)).is_some(), "{m} published");
        }
    }

    #[test]
    fn unauthorized_commit_refused_at_the_front_door() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = AuctionService::new(cclerk.cell_id());
        // `commit_bid` needs `Signature`; a `None` holder is refused before any turn.
        assert!(matches!(
            svc.commit_bid(
                &cclerk,
                crate::commit_slot(0),
                [7u8; 32],
                InvokeAuthority::None
            ),
            Err(AuctionServiceError::Refused(
                InvokeRefused::Unauthorized { .. }
            ))
        ));
    }

    #[test]
    fn view_is_a_serviced_seam_never_desugared() {
        let cclerk = AppCipherclerk::new(AgentCipherclerk::new(), [0x11; 32]);
        let svc = AuctionService::new(cclerk.cell_id());
        assert!(matches!(
            svc.view(&cclerk),
            Err(AuctionServiceError::Refused(
                InvokeRefused::ServicedSeam { .. }
            ))
        ));
    }
}
