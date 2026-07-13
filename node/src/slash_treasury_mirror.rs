//! dregg-pay running-total view of the slash remainder — the treasury cell's
//! audit mirror of the ONE on-ledger remainder Transfer.
//!
//! When a slash is realized, [`crate::relay_dispute::build_slash_turn`] emits
//! the remainder of the seizure as ONE conserving `Effect::Transfer` from the
//! relay cell to the configured remainder destination
//! ([`SlashPlan::remainder_dest`], [`default_slash_treasury`] by default). This
//! module keeps a dregg-pay running total of what that cell has received, so the
//! treasury cell's on-ledger balance and the operator's dregg-pay view agree.
//!
//! Remainders are the operator's staked bond, denominated in the native token —
//! this mirror books them there and only there. It is an audit VIEW of the one
//! on-ledger movement, not a second creation of value, and it is built so the
//! two ways such a mirror could lie are impossible, not merely documented:
//!
//! - **Idempotent.** Each realized slash is recorded at most once, keyed by the
//!   slash identity (relay cell, seized amount, the post-slash bond amount,
//!   parties, split). Every real slash advances the bond, so sequential slashes
//!   have distinct keys while a replay of the exact same slash dedups — the
//!   running total can never inflate past the sum of distinct on-ledger
//!   remainder Transfers.
//! - **Destination-scoped.** Only remainders destined for THIS mirror's cell are
//!   recorded; a remainder Transferred elsewhere (a lottery cell, a burn address)
//!   records nothing, so the view can never show income the cell never received.
//!
//! Note (ledger is the truth): the authoritative accounting is the treasury
//! cell's on-ledger balance under the verified kernel; this dregg-pay total is a
//! convenience view for the operator, kept honest by the guards above.

use std::collections::HashSet;
use std::sync::Mutex;

use dregg_app_framework::{Action, AppCipherclerk, CellId};
use dregg_pay::{Treasury, TreasuryStore};

use crate::relay_dispute::{SlashPlan, build_slash_turn, default_slash_treasury};

/// The outcome of accounting one realized slash in the treasury mirror.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RemainderDeposit {
    /// The amount recorded — always exactly the plan's `payout.remainder`,
    /// the same amount the on-ledger Transfer to the treasury cell carries.
    pub deposited: u64,
    /// The treasury's running native-token total after the deposit.
    pub new_total: u64,
}

/// The treasury-cell mirror: the [`CellId`] a deployment points slash remainders
/// at, and the dregg-pay [`Treasury`] that keeps the operator's running total for
/// that cell. Recording is idempotent and destination-scoped.
pub struct SlashTreasuryMirror<S: TreasuryStore> {
    treasury_cell: CellId,
    treasury: Treasury<S>,
    /// Slash-identity keys already recorded — the idempotency guard against
    /// double-counting the one on-ledger remainder Transfer.
    recorded: Mutex<HashSet<[u8; 32]>>,
}

impl<S: TreasuryStore> SlashTreasuryMirror<S> {
    /// A mirror for an explicitly configured remainder-destination cell.
    pub fn new(treasury_cell: CellId, treasury: Treasury<S>) -> Self {
        SlashTreasuryMirror {
            treasury_cell,
            treasury,
            recorded: Mutex::new(HashSet::new()),
        }
    }

    /// A mirror for the default remainder destination ([`default_slash_treasury`]).
    pub fn for_default_treasury(treasury: Treasury<S>) -> Self {
        Self::new(default_slash_treasury(), treasury)
    }

    /// The remainder-destination cell this mirror accounts for.
    pub fn treasury_cell(&self) -> CellId {
        self.treasury_cell
    }

    /// Borrow the underlying dregg-pay treasury (e.g. to read the running total).
    pub fn treasury(&self) -> &Treasury<S> {
        &self.treasury
    }

    /// The stable idempotency key for a slash: its on-ledger identity. Two real
    /// slashes differ (the bond advances, so `new_bond_amount` differs); a replay
    /// of the same slash produces the same key.
    fn slash_key(plan: &SlashPlan) -> [u8; 32] {
        let mut h = blake3::Hasher::new();
        h.update(b"dregg-slash-mirror-key-v1");
        h.update(plan.relay_cell.as_bytes());
        h.update(&plan.seized_amount.to_le_bytes());
        h.update(&plan.new_bond_amount.to_le_bytes());
        h.update(plan.wronged_party.as_bytes());
        h.update(plan.remainder_dest.as_bytes());
        h.update(&plan.payout.restitution.to_le_bytes());
        h.update(&plan.payout.remainder.to_le_bytes());
        *h.finalize().as_bytes()
    }

    /// Account one realized slash: if `plan`'s remainder leg is non-zero, destined
    /// for THIS mirror's cell, and NOT already recorded, book the amount and return
    /// the deposit. Otherwise (zero remainder, foreign destination, or a replay of
    /// an already-recorded slash) record nothing and return `None`.
    pub fn record_remainder(&self, plan: &SlashPlan) -> Option<RemainderDeposit> {
        if plan.remainder_dest != self.treasury_cell || plan.payout.remainder == 0 {
            return None;
        }
        let key = Self::slash_key(plan);
        {
            let mut recorded = self.recorded.lock().expect("treasury mirror lock");
            if !recorded.insert(key) {
                return None; // already recorded this exact slash — do not double-count.
            }
        }
        let new_total = self.treasury.deposit_dregg(plan.payout.remainder);
        Some(RemainderDeposit {
            deposited: plan.payout.remainder,
            new_total,
        })
    }
}

/// Build the real slash ledger [`Action`] (via
/// [`crate::relay_dispute::build_slash_turn`]) AND record the remainder in the
/// treasury mirror, in one call — so the on-ledger Transfer and its audit deposit
/// cannot drift apart at the call site. Returns the action plus the deposit
/// (`None` when the plan's remainder is zero, destined elsewhere, or a replay).
pub fn build_slash_turn_accounted<S: TreasuryStore>(
    cclerk: &AppCipherclerk,
    plan: &SlashPlan,
    mirror: &SlashTreasuryMirror<S>,
) -> (Action, Option<RemainderDeposit>) {
    let action = build_slash_turn(cclerk, plan);
    let deposit = mirror.record_remainder(plan);
    (action, deposit)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::relay_dispute::plan_slash;
    use dregg_app_framework::{AgentCipherclerk, Effect};
    use dregg_pay::InMemoryTreasuryStore;

    fn test_cclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [42u8; 32])
    }

    fn mirror() -> SlashTreasuryMirror<InMemoryTreasuryStore> {
        SlashTreasuryMirror::for_default_treasury(Treasury::new(InMemoryTreasuryStore::new(), 6))
    }

    fn demo_plan(requested: u64, proven_fee: u64, bounty: u64) -> SlashPlan {
        plan_slash(
            true,
            10_000,
            1_000,
            0,
            requested,
            proven_fee,
            bounty,
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x03; 32]),
            [0xAB; 32],
        )
        .expect("a slash verdict yields a plan")
    }

    #[test]
    fn deposit_equals_the_remainder_transfer_leg() {
        let plan = demo_plan(500, 120, 30); // restitution 150, remainder 350
        assert_eq!(plan.payout.remainder, 350);
        let m = mirror();
        let (action, deposit) = build_slash_turn_accounted(&test_cclerk(), &plan, &m);
        let deposit = deposit.expect("non-zero remainder to the default treasury is recorded");
        assert_eq!(deposit.deposited, plan.payout.remainder);
        assert_eq!(m.treasury().dregg_balance(), 350);
        let to_treasury: Vec<u64> = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { to, amount, .. } if *to == default_slash_treasury() => {
                    Some(*amount)
                }
                _ => None,
            })
            .collect();
        assert_eq!(to_treasury, vec![350]);
        assert_eq!(
            to_treasury[0], deposit.deposited,
            "deposit mirrors the wire"
        );
    }

    #[test]
    fn re_recording_the_same_slash_is_a_no_op_no_double_count() {
        let plan = demo_plan(500, 120, 30);
        let m = mirror();
        assert!(m.record_remainder(&plan).is_some(), "first record books it");
        assert!(m.record_remainder(&plan).is_none(), "replay dedups");
        let (_, again) = build_slash_turn_accounted(&test_cclerk(), &plan, &m);
        assert!(
            again.is_none(),
            "the accounted builder also dedups the same slash"
        );
        assert_eq!(m.treasury().dregg_balance(), 350, "exactly one deposit");
    }

    #[test]
    fn distinct_sequential_slashes_each_record() {
        let m = mirror();
        let a = plan_slash(
            true,
            10_000,
            1_000,
            0,
            500,
            0,
            0,
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x03; 32]),
            [0xAB; 32],
        )
        .unwrap();
        let b = plan_slash(
            true,
            9_500,
            1_000,
            1,
            400,
            0,
            0,
            CellId::from_bytes([0x11; 32]),
            CellId::from_bytes([0x03; 32]),
            [0xAB; 32],
        )
        .unwrap();
        assert_ne!(
            SlashTreasuryMirror::<InMemoryTreasuryStore>::slash_key(&a),
            SlashTreasuryMirror::<InMemoryTreasuryStore>::slash_key(&b)
        );
        assert_eq!(m.record_remainder(&a).unwrap().deposited, 500);
        assert_eq!(m.record_remainder(&b).unwrap().deposited, 400);
        assert_eq!(m.treasury().dregg_balance(), 900);
    }

    #[test]
    fn foreign_destination_records_nothing() {
        let mut plan = demo_plan(500, 120, 30);
        plan.remainder_dest = CellId::from_bytes([0x77; 32]);
        let m = mirror();
        let (_, deposit) = build_slash_turn_accounted(&test_cclerk(), &plan, &m);
        assert!(deposit.is_none(), "remainder went to a foreign cell");
        assert_eq!(m.treasury().dregg_balance(), 0, "view unchanged");
    }

    #[test]
    fn zero_remainder_records_nothing() {
        let plan = demo_plan(500, 500, 100);
        assert_eq!(plan.payout.remainder, 0);
        assert!(mirror().record_remainder(&plan).is_none());
    }
}
