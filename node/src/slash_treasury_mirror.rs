//! dregg-pay deposit accounting for the slash remainder — the treasury cell's
//! audit MIRROR.
//!
//! When a slash is realized, [`crate::relay_dispute::build_slash_turn`] emits
//! the remainder of the seizure as ONE conserving `Effect::Transfer` from the
//! relay cell to the configured remainder destination
//! ([`SlashPlan::remainder_dest`], [`default_slash_treasury`] by default). The
//! operator behind that treasury cell also keeps a dregg-pay [`Treasury`]
//! running total. This module is the weld between the two views: on a realized
//! slash, the SAME remainder amount is recorded in the `Treasury` via
//! [`Treasury::deposit_dregg`], so the treasury cell's on-ledger balance and
//! the dregg-pay running total agree.
//!
//! **A mirror, NOT a second creation of value.** The remainder is ONE amount:
//! it moves once, on-ledger, as the conserving Transfer; the deposit here is
//! the operator-side bookkeeping of that same amount. Conservation is the
//! ledger's (`restitution + remainder == seized`, tested in `relay_dispute`);
//! the mirror records exactly the Transfer's amount, and ONLY when the plan's
//! destination is THIS mirror's cell — a deployment that points remainders
//! somewhere else (a lottery cell, a burn address) records nothing here, so
//! the audit view can never show income the cell never received.
//!
//! Units: the [`Treasury`]'s `$DREGG` pile is a plain `u64`; the mirror
//! carries the remainder 1:1 in the same computron units the ledger Transfer
//! names.
//!
//! Honest scope: [`SlashTreasuryMirror::record_remainder`] and
//! [`build_slash_turn_accounted`] are the tested weld at the plan level. The
//! legacy `POST /relay/dispute` route and the cell-program intake do not hold
//! a `Treasury` yet; giving the operator's service a mirror and calling the
//! accounted builder there is the same promotion seam `relay_dispute`'s module
//! docs already name for the ledger turn itself.

use dregg_app_framework::{Action, AppCipherclerk, CellId};
use dregg_pay::{Treasury, TreasuryStore};

use crate::relay_dispute::{SlashPlan, build_slash_turn, default_slash_treasury};

/// The outcome of accounting one realized slash in the treasury mirror.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RemainderDeposit {
    /// The amount recorded — always exactly the plan's `payout.remainder`,
    /// the same amount the on-ledger Transfer to the treasury cell carries.
    pub deposited: u64,
    /// The treasury's running `$DREGG` total after the deposit.
    pub new_total: u64,
}

/// The treasury-cell mirror: pairs the [`CellId`] a deployment points slash
/// remainders at with the dregg-pay [`Treasury`] that keeps the operator's
/// running total for that cell.
pub struct SlashTreasuryMirror<S: TreasuryStore> {
    /// The remainder-destination cell this mirror accounts for. Configurable:
    /// a deployment that overrides `SlashPlan::remainder_dest` points the
    /// mirror at that same cell.
    treasury_cell: CellId,
    treasury: Treasury<S>,
}

impl<S: TreasuryStore> SlashTreasuryMirror<S> {
    /// A mirror for an explicitly configured remainder-destination cell.
    pub fn new(treasury_cell: CellId, treasury: Treasury<S>) -> Self {
        SlashTreasuryMirror {
            treasury_cell,
            treasury,
        }
    }

    /// A mirror for the default remainder destination
    /// ([`default_slash_treasury`]) — what [`crate::relay_dispute::plan_slash`]
    /// plans point at unless overridden.
    pub fn for_default_treasury(treasury: Treasury<S>) -> Self {
        Self::new(default_slash_treasury(), treasury)
    }

    /// The remainder-destination cell this mirror accounts for.
    pub fn treasury_cell(&self) -> CellId {
        self.treasury_cell
    }

    /// Borrow the underlying dregg-pay treasury (e.g. to read the running
    /// total via `dregg_balance`).
    pub fn treasury(&self) -> &Treasury<S> {
        &self.treasury
    }

    /// Account one realized slash: if `plan`'s remainder leg is non-zero AND
    /// destined for THIS mirror's treasury cell, record the same amount via
    /// [`Treasury::deposit_dregg`] and return the deposit. Otherwise record
    /// nothing and return `None` — a remainder Transferred to some other cell
    /// must never appear in this cell's audit view (fail-closed against
    /// phantom income), and a zero remainder has no Transfer leg to mirror.
    pub fn record_remainder(&self, plan: &SlashPlan) -> Option<RemainderDeposit> {
        if plan.remainder_dest != self.treasury_cell || plan.payout.remainder == 0 {
            return None;
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
/// treasury mirror, in one call — so the on-ledger Transfer and its audit
/// deposit cannot drift apart at the call site. Returns the action plus the
/// deposit (which is `None` when the plan's remainder is zero or destined for
/// a cell other than the mirror's).
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

    fn default_mirror() -> SlashTreasuryMirror<InMemoryTreasuryStore> {
        SlashTreasuryMirror::for_default_treasury(Treasury::new(InMemoryTreasuryStore::new(), 6))
    }

    /// A realized plan via the real planner: bond 10_000, floor 1_000, so the
    /// requested seizure lands in full; the split follows proven_fee + bounty.
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
    fn deposit_recorded_equals_the_remainder_transfer_leg() {
        // Seize 500; proven loss 120 + bounty 30 => restitution 150, remainder 350.
        let plan = demo_plan(500, 120, 30);
        assert_eq!(plan.payout.remainder, 350);
        let mirror = default_mirror();

        let (action, deposit) = build_slash_turn_accounted(&test_cclerk(), &plan, &mirror);
        let deposit = deposit.expect("a non-zero remainder to the default treasury is recorded");
        assert_eq!(deposit.deposited, plan.payout.remainder);
        assert_eq!(deposit.new_total, 350);
        assert_eq!(
            mirror.treasury().dregg_balance(),
            350,
            "running total agrees"
        );

        // The mirror records EXACTLY what the on-ledger Transfer to the
        // treasury cell carries — the same ONE amount, viewed twice.
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
        assert_eq!(
            to_treasury,
            vec![350],
            "one remainder Transfer, same amount"
        );
        assert_eq!(
            to_treasury[0], deposit.deposited,
            "deposit mirrors the wire"
        );
    }

    #[test]
    fn conservation_holds_across_the_weld() {
        // The whole seizure leaves the relay cell as Transfers; the mirror's
        // deposit re-states the remainder leg, it does not add to the flow:
        // restitution + deposited == seized, and the sum of Transfer amounts
        // out of the relay cell == seized (unchanged by accounting).
        let plan = demo_plan(500, 120, 30);
        let mirror = default_mirror();
        let (action, deposit) = build_slash_turn_accounted(&test_cclerk(), &plan, &mirror);
        let deposit = deposit.unwrap();

        let out_of_relay: u64 = action
            .effects
            .iter()
            .filter_map(|e| match e {
                Effect::Transfer { from, amount, .. } if *from == plan.relay_cell => Some(*amount),
                _ => None,
            })
            .sum();
        assert_eq!(
            out_of_relay, plan.seized_amount,
            "the ledger moves the seizure once"
        );
        assert_eq!(
            plan.payout.restitution + deposit.deposited,
            plan.seized_amount,
            "restitution + the recorded remainder account for the whole seizure"
        );

        // A second slash accumulates: the running total is the sum of the
        // remainders actually Transferred to the cell, nothing more.
        let plan2 = demo_plan(400, 0, 0); // remainder = whole seizure = 400
        let (_, deposit2) = build_slash_turn_accounted(&test_cclerk(), &plan2, &mirror);
        assert_eq!(deposit2.unwrap().deposited, 400);
        assert_eq!(
            mirror.treasury().dregg_balance(),
            350 + 400,
            "running total == sum of remainder Transfers to this cell"
        );
    }

    #[test]
    fn foreign_destination_records_nothing() {
        // A deployment that points the remainder at some OTHER cell (a lottery,
        // a burn address) must not grow THIS treasury's audit view: the value
        // went elsewhere on-ledger, so the mirror stays silent (fail-closed
        // against phantom income).
        let mut plan = demo_plan(500, 120, 30);
        plan.remainder_dest = CellId::from_bytes([0x77; 32]);
        let mirror = default_mirror();

        let (action, deposit) = build_slash_turn_accounted(&test_cclerk(), &plan, &mirror);
        assert!(deposit.is_none(), "remainder went to a foreign cell");
        assert_eq!(mirror.treasury().dregg_balance(), 0, "audit view unchanged");
        // The ledger turn still carries the remainder Transfer — to the
        // deployment's chosen destination; only the accounting home differs.
        assert!(action.effects.iter().any(|e| matches!(
            e,
            Effect::Transfer { to, amount, .. } if *to == plan.remainder_dest && *amount == 350
        )));
    }

    #[test]
    fn zero_remainder_records_nothing() {
        // Proven loss + bounty >= the seizure => the whole seizure is
        // restitution, there is no remainder Transfer, so nothing to mirror.
        let plan = demo_plan(500, 500, 100);
        assert_eq!(plan.payout.remainder, 0);
        let mirror = default_mirror();
        assert!(mirror.record_remainder(&plan).is_none());
        assert_eq!(mirror.treasury().dregg_balance(), 0);
    }
}
