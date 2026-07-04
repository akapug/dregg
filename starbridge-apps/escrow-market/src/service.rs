//! # escrow-market — the sealed escrow as a SERVICE CELL on the `invoke()` front
//! door (the cells-as-service-objects face).
//!
//! The sealed atomic-swap marketplace re-expressed as a CELLS-AS-SERVICE-OBJECTS
//! citizen (after the `starbridge-kvstore` and `starbridge-nameservice`
//! exemplars). A `service` module on the existing crate: it publishes a
//! first-class, typed [`InterfaceDescriptor`] for the escrow lifecycle and drives
//! it through the PROVEN [`SealedEscrow`](dregg_cell::escrow_sealed) capacity.
//!
//! ## The published interface (the swap lifecycle as typed methods)
//!
//! | method    | semantics                 | auth        | drives |
//! |-----------|---------------------------|-------------|--------|
//! | `open`    | [`Semantics::Replayable`] | `Signature` | [`SealedEscrowMarket::open`] — seal the swap terms |
//! | `deposit` | [`Semantics::Replayable`] | `Signature` | [`SealedEscrowMarket::deposit`] — lock a conforming leg |
//! | `settle`  | [`Semantics::Replayable`] | `Signature` | [`SealedEscrowMarket::settle`] — complete the atomic swap |
//! | `reclaim` | [`Semantics::Replayable`] | `Signature` | [`SealedEscrowMarket::reclaim`] — pull a leg back (half-open defence) |
//! | `view`    | [`Semantics::Serviced`]   | `None`      | [`SealedEscrowMarket::state`] — the OFE seam: a pure read, no turn |
//!
//! `open`/`deposit`/`settle`/`reclaim` mutate the escrow's committed heap through
//! the capacity's forge-rejecting verification core
//! ([`EscrowState::check_claim`](dregg_cell::escrow_sealed::EscrowState) /
//! `settlement`); `view` is **serviced** — the escrow's committed state IS the
//! answer (it rides the OFE cross-cell-read), so it is never desugared to a turn.
//!
//! ## A note on the verified-turn path
//!
//! The escrow's state lives in the cell's committed HEAP, mutated by the
//! capacity's executor-level functions; there is no `SetField` desugar for it.
//! The in-circuit `SettleEscrow` effect — so a light client (not just a
//! re-executing validator) witnesses settlement-atomicity from a batch — is the
//! capacity's named next slice (see `dregg_cell::escrow_sealed`, and
//! `docs/deos/SEALED-ESCROW.md`). Until then this service is the typed discovery
//! face + the direct drive of the proven capacity; the `Signature` auth tier each
//! mutator publishes is the contract a host enforces.

use dregg_cell::interface::{ArgsSchema, InterfaceDescriptor, MethodSig, Semantics, method_symbol};
use dregg_cell::permissions::AuthRequired;
use dregg_types::CellId;

use crate::{EscrowError, EscrowState, Leg, MarketError, SealedEscrowMarket, Side};

// =============================================================================
// Method names
// =============================================================================

/// `open` — a [`Semantics::Replayable`], `Signature`-gated mutator: seal the swap
/// terms into a fresh escrow ([`SealedEscrowMarket::open`]).
pub const METHOD_OPEN: &str = "open";
/// `deposit` — a [`Semantics::Replayable`], `Signature`-gated mutator: a party
/// locks its conforming leg ([`SealedEscrowMarket::deposit`]).
pub const METHOD_DEPOSIT: &str = "deposit";
/// `settle` — a [`Semantics::Replayable`], `Signature`-gated mutator: complete the
/// 2-of-2 atomic swap ([`SealedEscrowMarket::settle`]).
pub const METHOD_SETTLE: &str = "settle";
/// `reclaim` — a [`Semantics::Replayable`], `Signature`-gated mutator: pull one's
/// own leg back before settlement ([`SealedEscrowMarket::reclaim`]).
pub const METHOD_RECLAIM: &str = "reclaim";
/// `view` — a [`Semantics::Serviced`] read (the named OFE seam): read the escrow's
/// committed leg state. Never desugared.
pub const METHOD_VIEW: &str = "view";

// =============================================================================
// The published, typed interface
// =============================================================================

/// **The escrow's first-class typed interface** — the five methods it publishes,
/// with their auth and replayable-vs-serviced semantics. Richer than
/// `derive_replayable` (which would make every method `Replayable`/`None`): the
/// four mutators are `Signature`-gated and `view` is `Serviced`.
pub fn interface_descriptor() -> InterfaceDescriptor {
    let mutator = |name: &str, args: u8| MethodSig {
        args_schema: ArgsSchema::Fixed(args),
        auth_required: AuthRequired::Signature,
        ..MethodSig::replayable(method_symbol(name))
    };
    InterfaceDescriptor::new(vec![
        // open(): seal the swap terms.
        mutator(METHOD_OPEN, 0),
        // deposit(side, amount): a party locks its conforming leg.
        mutator(METHOD_DEPOSIT, 2),
        // settle(): complete the atomic swap.
        mutator(METHOD_SETTLE, 0),
        // reclaim(side): pull one's own leg back.
        mutator(METHOD_RECLAIM, 1),
        // view(): a pure read — the named OFE seam, never desugared.
        MethodSig {
            args_schema: ArgsSchema::Fixed(0),
            auth_required: AuthRequired::None,
            semantics: Semantics::Serviced,
            ..MethodSig::replayable(method_symbol(METHOD_VIEW))
        },
    ])
}

/// Register the escrow's [`interface_descriptor`] for `cell` in a userspace
/// [`InterfaceRegistry`](dregg_cell::interface) — the resolution path the Service
/// Explorer consults before falling back to derive-from-program.
pub fn register_interface(registry: &mut dregg_app_framework::InterfaceRegistry, cell: CellId) {
    registry.register(cell, interface_descriptor());
}

// =============================================================================
// The service handle — driving the proven capacity through the typed interface
// =============================================================================

/// **A handle to a deployed sealed-escrow cell** — bundles the escrow cell id with
/// its published interface, and drives the swap lifecycle through the PROVEN
/// [`SealedEscrowMarket`] capacity. The mutators return the capacity's own
/// `Result`, so a non-conforming deposit, an over-claim, a one-shot replay, or a
/// half-open settle is the protocol's forge-rejection — not a userspace check.
#[derive(Clone, Debug)]
pub struct EscrowService {
    /// The escrow host cell this handle drives.
    pub cell: CellId,
    /// The escrow's published typed interface (the richer-than-derived one).
    pub descriptor: InterfaceDescriptor,
}

impl EscrowService {
    /// A handle to the escrow cell `cell`, carrying the escrow's published
    /// [`interface_descriptor`].
    pub fn new(cell: CellId) -> Self {
        EscrowService {
            cell,
            descriptor: interface_descriptor(),
        }
    }

    /// **Invoke `deposit(side, leg)`** — a party locks its conforming leg into the
    /// escrow `market`; the capacity refuses a non-conforming leg before any value
    /// moves. The depositing wallet `from` is debited the leg amount into custody.
    pub fn deposit(
        &self,
        market: &mut SealedEscrowMarket,
        side: Side,
        leg: &Leg,
        from: &mut dregg_cell::Cell,
    ) -> Result<(), MarketError> {
        market.deposit(side, leg, from)
    }

    /// **Invoke `settle()`** — complete the 2-of-2 atomic swap on `market`,
    /// crossing each leg to its counterparty. Refused (nothing moves) unless both
    /// legs are present, conforming, and unconsumed.
    pub fn settle(
        &self,
        market: &mut SealedEscrowMarket,
        a_receiving: &mut dregg_cell::Cell,
        b_receiving: &mut dregg_cell::Cell,
    ) -> Result<(i64, i64), MarketError> {
        market.settle(a_receiving, b_receiving)
    }

    /// **Invoke `reclaim(side)`** — pull one's own leg back before settlement (the
    /// half-open defence), making the depositor whole. Permitted only to the leg's
    /// depositor, only while the leg is still live.
    pub fn reclaim(
        &self,
        market: &mut SealedEscrowMarket,
        side: Side,
        by: CellId,
        to: &mut dregg_cell::Cell,
    ) -> Result<i64, MarketError> {
        market.reclaim(side, by, to)
    }

    /// **`view()`** — the named [`Semantics::Serviced`] seam: the escrow's
    /// committed leg state IS the answer (the OFE cross-cell-read), returned
    /// directly rather than desugared to a turn.
    pub fn view(&self, market: &SealedEscrowMarket) -> Result<EscrowState, EscrowError> {
        market.state()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interface_publishes_five_typed_methods() {
        let iface = interface_descriptor();
        assert_eq!(iface.methods.len(), 5);
        assert!(iface.verify_id());

        for m in [METHOD_OPEN, METHOD_DEPOSIT, METHOD_SETTLE, METHOD_RECLAIM] {
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
}
