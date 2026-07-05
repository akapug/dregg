//! `conserve` — the conserving-move primitive the settlement rail upholds,
//! pointed at the REAL substrate proven signed-balance discipline instead of a
//! hand-rolled twin.
//!
//! ## What this dissolves
//!
//! The settlement's conserving move — debit the payer by `amount`, credit the
//! beneficiary by the same `amount`, so the per-asset Σδ = 0 — used to be
//! hand-rolled `i64` arithmetic inside [`ConservingLedger`](crate::ConservingLedger),
//! asserted *only* by three local unit tests. That made it a **soundness twin**
//! (`docs/SOUNDNESS-TWINS-CENSUS.md` #1) of a guarantee the substrate already
//! **proves**:
//!
//! - Lean: `metatheory/Dregg2/Exec/RecordKernel.lean` `recTransfer_balanceSum_conserve`
//!   — a transfer between two distinct accounts preserves the total `balance`
//!   field (debit and credit cancel), and the apex
//!   `metatheory/Dregg2/AssuranceCase.lean` `conservation_guarantee`.
//! - Rust home of that `recTransfer` debit/credit: `dregg_cell::CellState`'s
//!   signed-balance epoch — [`CellState::debit_balance`] (refuse-below-zero, the
//!   proven `InsufficientFunds` floor) + [`CellState::credit_balance`]
//!   (overflow-checked). `turn/src/action.rs` classifies `Effect::Transfer` as
//!   `LinearityClass::Conservative` (paired-delta), the executor-level shadow of
//!   the same theorem.
//!
//! [`apply_conserving_transfer`] is the single seam the ledger drives. In the
//! **`dregg-conserve`** lane it computes the post-balances by running the move
//! through the substrate's proven `CellState` signed-balance primitive — so the
//! cloud's "this settlement conserves" is **decided by the proven theorem's
//! deployed Rust home**, not by DreggNet arithmetic. With the lane off (the
//! default offline build, Apache-pure, no `dregg-circuit` closure) it computes
//! the *same* kernel paired-delta inline — a labelled mirror cross-checked
//! against the substrate primitive by running the *same pinned-value* settle
//! gauntlet (this module's tests + `settle`'s) under both backends: every
//! expected balance is fixed, so the substrate `CellState` move must produce the
//! identical integers the mirror asserts. It is a mirror, not an independent
//! reimplementation.
//!
//! ## The honest seam (why a lane, not an unconditional dependency)
//!
//! Unlike the account-recovery weld — whose proven primitive (`CellId::derive_raw`)
//! lives in the **light** `dregg-types` (serde + blake3, no heavy closure) — the
//! conservation primitive (`CellState` / `Effect::Transfer`) is welded to
//! `dregg-circuit` in **every** substrate carrier (`dregg-cell`, `dregg-turn`,
//! `dregg-payable`, `dregg-userspace-verify` all pull it). Depending on it
//! unconditionally would pull plonky3 into the *entire* cloud's default offline
//! build (every crate that depends on `dreggnet-durable`). So, exactly like the
//! `pg-dregg` verified-store lane and the bridge's `dregg-verify` lane, the real
//! substrate conservation is the **off-by-default `dregg-conserve` lane**. The
//! deeper seam — the settlement becoming a real **on-chain** `Payable`
//! (`Effect::Transfer`) whose receipt a light client witnesses in-circuit — is
//! the swarm's S3 flip (see [`crate::verified::S3_GATED_SEAM`]).
//!
//! [`CellState::debit_balance`]: https://docs.rs/dregg-cell
//! [`CellState::credit_balance`]: https://docs.rs/dregg-cell

use crate::settle::SettleError;

/// The post-balances of one conserving payer → beneficiary move. The invariant
/// `new_payer + new_beneficiary == payer_balance + beneficiary_balance` (per
/// asset, Σδ = 0) holds by construction of the kernel transfer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ConservedMove {
    /// The payer's balance after the debit.
    pub new_payer: i64,
    /// The beneficiary's balance after the credit.
    pub new_beneficiary: i64,
}

/// Apply a conserving transfer of `amount` of `asset` from a payer holding
/// `payer_balance` to a beneficiary holding `beneficiary_balance`, returning the
/// post-balances.
///
/// This is the conserving move the settlement rail performs, expressed as the
/// kernel `Effect::Transfer` paired-delta law (`recTransfer_balanceSum_conserve`):
/// the payer is debited *exactly* what the beneficiary is credited, so the
/// per-asset Σδ = 0. A debit that would take the payer below zero is **refused**
/// ([`SettleError::InsufficientFunds`]) — the proven `CellState::debit_balance`
/// floor (a funded lease reserves its budget, so within budget this never fires;
/// it guards against settling work the lease did not prove it paid for).
///
/// `amount` must be positive (the caller enforces [`SettleError::NonPositiveAmount`]
/// first); a non-positive or out-of-`u64`-range amount is rejected here too.
///
/// In the **`dregg-conserve`** lane the post-balances come from the substrate's
/// proven `dregg_cell::CellState` signed-balance primitive; with the lane off the
/// same paired-delta is computed inline (the labelled offline mirror).
pub fn apply_conserving_transfer(
    asset: &str,
    payer: &str,
    payer_balance: i64,
    beneficiary_balance: i64,
    amount: i64,
) -> Result<ConservedMove, SettleError> {
    if amount <= 0 {
        return Err(SettleError::NonPositiveAmount(amount));
    }

    #[cfg(feature = "dregg-conserve")]
    {
        // The REAL substrate conserving move: run the debit/credit through the
        // proven `CellState` signed-balance epoch — the deployed Rust home of
        // `recTransfer_balanceSum_conserve`. The Σδ = 0 (and the refuse-below-zero
        // `InsufficientFunds` floor) is the substrate's discipline, not ours.
        use dregg_cell::CellState;

        // `amount > 0` already, so this conversion is the in-range path; an
        // out-of-`u64` amount is a malformed charge, refused.
        let amt = u64::try_from(amount).map_err(|_| SettleError::NonPositiveAmount(amount))?;

        let mut payer_cell = CellState::new(payer_balance);
        // `debit_balance` refuses to go below zero — the proven floor. A `false`
        // return is exactly "the payer does not hold enough" (`InsufficientFunds`).
        if !payer_cell.debit_balance(amt) {
            return Err(SettleError::InsufficientFunds {
                payer: payer.to_string(),
                asset: asset.to_string(),
                balance: payer_balance,
                needed: amount,
            });
        }
        let mut beneficiary_cell = CellState::new(beneficiary_balance);
        // `credit_balance` is overflow-checked; a `false` return is an `i64`
        // overflow of the beneficiary's holdings (not a conservation fault) — the
        // backend refuses rather than wrap. Practically unreachable for metered
        // settlement, but the substrate primitive's honest failure mode.
        if !beneficiary_cell.credit_balance(amt) {
            return Err(SettleError::Backend(format!(
                "beneficiary `{}` balance would overflow crediting {amount} of `{asset}`",
                payer
            )));
        }
        return Ok(ConservedMove {
            new_payer: payer_cell.balance(),
            new_beneficiary: beneficiary_cell.balance(),
        });
    }

    #[cfg(not(feature = "dregg-conserve"))]
    {
        // The offline floor (Apache-pure, no `dregg-circuit` closure): the SAME
        // kernel paired-delta the substrate `CellState` computes, mirrored inline.
        // The `dregg-conserve` test gauntlet cross-checks this is byte-identical to
        // the substrate primitive; it is a labelled mirror, not a separate scheme.
        let _ = (asset, payer);
        // Refuse-below-zero: the proven `debit_balance` floor.
        if payer_balance < amount {
            return Err(SettleError::InsufficientFunds {
                payer: payer.to_string(),
                asset: asset.to_string(),
                balance: payer_balance,
                needed: amount,
            });
        }
        let new_payer = payer_balance - amount;
        let new_beneficiary = beneficiary_balance.checked_add(amount).ok_or_else(|| {
            SettleError::Backend(format!(
                "beneficiary balance would overflow crediting {amount} of `{asset}`"
            ))
        })?;
        Ok(ConservedMove {
            new_payer,
            new_beneficiary,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn move_conserves_sum() {
        // Σδ = 0: what leaves the payer arrives at the beneficiary, exactly.
        let before = 100 + 5;
        let m = apply_conserving_transfer("USD", "lessee", 100, 5, 7).expect("move");
        assert_eq!(m.new_payer, 93);
        assert_eq!(m.new_beneficiary, 12);
        assert_eq!(m.new_payer + m.new_beneficiary, before, "Σδ = 0");
    }

    #[test]
    fn refuses_below_zero_payer() {
        // The proven `debit_balance` floor: a debit beyond the reserve is refused,
        // nothing moves.
        assert!(matches!(
            apply_conserving_transfer("USD", "lessee", 2, 0, 5),
            Err(SettleError::InsufficientFunds {
                balance: 2,
                needed: 5,
                ..
            })
        ));
    }

    #[test]
    fn refuses_non_positive() {
        assert!(matches!(
            apply_conserving_transfer("USD", "lessee", 100, 0, 0),
            Err(SettleError::NonPositiveAmount(0))
        ));
        assert!(matches!(
            apply_conserving_transfer("USD", "lessee", 100, 0, -3),
            Err(SettleError::NonPositiveAmount(-3))
        ));
    }

    /// The conservation property holds across a sweep of moves regardless of which
    /// backend (substrate `CellState` in the lane, the inline mirror otherwise)
    /// computes it — the post-sum always equals the pre-sum.
    #[test]
    fn conserves_across_a_sweep() {
        let mut payer = 1_000i64;
        let mut benef = 0i64;
        for amount in [1, 7, 13, 100, 250, 3] {
            let pre = payer + benef;
            let m = apply_conserving_transfer("USD", "lessee", payer, benef, amount)
                .expect("in-budget move");
            payer = m.new_payer;
            benef = m.new_beneficiary;
            assert_eq!(payer + benef, pre, "every move conserves Σδ = 0");
        }
        assert_eq!(payer, 1_000 - (1 + 7 + 13 + 100 + 250 + 3));
        assert_eq!(benef, 1 + 7 + 13 + 100 + 250 + 3);
    }
}
