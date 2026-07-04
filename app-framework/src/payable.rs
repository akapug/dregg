//! # `Payable` — the dregg standard interface for cross-app VALUE FLOW.
//!
//! The interop census (`docs/deos/APPS-INTEROP-CENSUS.md`) found that across all
//! starbridge-apps NO value flowed between apps: every app modelled money as
//! scalar `SetField`s on its own cell, never as a movable conserved asset crossing
//! an app boundary. `Payable` is the SHARED VALUE MEDIUM + SHARED INTERFACE that
//! closes that gap.
//!
//! ## The DSI lives in `dregg-payable`; the signed-turn `pay` wrapper lives here
//!
//! The `Payable` DSI itself — the canonical [`payable_descriptor`], the method
//! sigs, [`pay_effects`], and the [`Payable`] trait whose `pay` desugars to the
//! ONE conserving kernel [`dregg_turn::action::Effect::Transfer`] (per-asset Σδ=0)
//! — lives in the lower `dregg-payable` crate, so BOTH this app-facing surface and
//! the SDK's metered tool-gateway charge go through the SAME verified `pay` route
//! table ([`dregg_payable::resolve_pay`]). Those items are re-exported here so
//! existing `dregg_app_framework::payable::*` consumers are unchanged.
//!
//! What stays HERE is the cipherclerk-bound glue: the [`ActionSigner`] impl for
//! [`AppCipherclerk`] (so the trait's `pay` can sign a turn) and the free [`pay`]
//! convenience function that signs through the framework cipherclerk.
//!
//! ## Two apps implement it, so they pay each other through ONE interface
//!
//! `starbridge-bounty-board`'s reward treasury and `starbridge-escrow-market`'s
//! escrow holding cell each implement [`Payable`]. A bounty payout is
//! `bounty.pay(cipherclerk, reward, escrow_cell, authority)` — bounty-board paying
//! escrow-market THROUGH the shared interface, not bespoke wiring — and the escrow
//! settles onward with `escrow.pay(...)`. See
//! `starbridge-apps/escrow-market/tests/cross_app_value_flow.rs` for the proven
//! end-to-end flow (mint → cross-boundary transfer → settle → Σδ=0 across the
//! World).

use dregg_turn::Turn;
use dregg_turn::action::Action;
use dregg_types::CellId;

use crate::cipherclerk::AppCipherclerk;
use crate::invoke::{InvokeAuthority, InvokeRefused};

// The DSI core lives in `dregg-payable` (low enough for the SDK to reuse it).
// Re-exported here unchanged so existing app consumers are unaffected.
pub use dregg_payable::payable::{
    ActionSigner, AssetId, BALANCE_METHOD, PAY_METHOD, Payable, balance_method_sig, pay_args,
    pay_effects, pay_method_sig, payable_descriptor, resolve_pay,
};

/// The framework cipherclerk IS the [`Payable`] turn signer: it already exposes
/// `sign_action` / `make_turn` with exactly the shapes the trait needs, so this
/// one-line forwarding impl lets `cell.pay(cipherclerk, amount, to, authority)`
/// keep working while the DSI trait lives down in `dregg-payable`.
impl ActionSigner for AppCipherclerk {
    fn sign_action(&self, action: Action) -> Action {
        AppCipherclerk::sign_action(self, action)
    }
    fn make_turn(&self, action: Action) -> Turn {
        AppCipherclerk::make_turn(self, action)
    }
}

/// **Pay `amount` of `asset` from `payer_cell` to `to`, THROUGH the `Payable`
/// interface** — the cipherclerk-bound convenience function.
///
/// Routes the `pay` method against the shared [`payable_descriptor`]
/// ([`resolve_pay`]: verified DFA router → cap-gate on `Signature` → desugar),
/// then signs + wraps the desugared [`dregg_turn::action::Effect::Transfer`] in a
/// [`Turn`] ready for the executor. The returned turn carries ONLY the kernel
/// `Transfer` the conservation check already understands — there is no
/// `Effect::Invoke`, no new commitment field.
///
/// `asset` should be `payer_cell`'s `token_id` (a cell holds value only in its
/// own asset); it is bound into the invocation args as the payment's asset tag.
pub fn pay(
    cipherclerk: &AppCipherclerk,
    payer_cell: CellId,
    asset: AssetId,
    amount: u64,
    to: CellId,
    authority: InvokeAuthority,
) -> Result<Turn, InvokeRefused> {
    let (action, _sig) = resolve_pay(payer_cell, asset, amount, to, authority)?;
    let signed = cipherclerk.sign_action(action);
    Ok(cipherclerk.make_turn(signed))
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::interface::{Semantics, method_symbol};
    use dregg_turn::action::Effect;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    #[test]
    fn descriptor_is_canonical_and_routes_pay() {
        let d = payable_descriptor();
        assert!(d.verify_id(), "payable interface_id must be canonical");
        assert!(d.route_method(&method_symbol(PAY_METHOD)).is_some());
        assert!(d.route_method(&method_symbol(BALANCE_METHOD)).is_some());
        assert_eq!(d.interface_id, payable_descriptor().interface_id);
    }

    #[test]
    fn pay_desugars_to_a_single_conserving_transfer() {
        // The re-exported verified desugar still routes `pay` to exactly ONE
        // conserving Transfer (the SAME `resolve_pay` the SDK gateway charge uses).
        let from = cid(1);
        let to = cid(2);
        let (action, sig) = resolve_pay(from, [7u8; 32], 500, to, InvokeAuthority::Signature)
            .expect("pay must resolve through the Payable interface");

        assert_eq!(action.method, method_symbol(PAY_METHOD));
        assert_eq!(action.effects.len(), 1);
        match action.effects[0] {
            Effect::Transfer {
                from: f,
                to: t,
                amount,
            } => {
                assert_eq!(f, from);
                assert_eq!(t, to);
                assert_eq!(amount, 500);
            }
            ref other => panic!("pay must desugar to Transfer, got {other:?}"),
        }
        assert_eq!(sig.semantics, Semantics::Replayable);
    }

    #[test]
    fn pay_is_signature_gated() {
        let from = cid(1);
        let to = cid(2);
        let refused = resolve_pay(from, [7u8; 32], 500, to, InvokeAuthority::None)
            .expect_err("an unauthorized pay must be refused");
        assert!(matches!(refused, InvokeRefused::Unauthorized { .. }));
    }
}
