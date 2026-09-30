//! Computron cost configuration for turn metering.

use serde::{Deserialize, Serialize};

/// Cost configuration for computron metering.
///
/// Each operation has a base cost in computrons. The total cost of a turn
/// is the sum of all operation costs. If the agent's fee doesn't cover the
/// total, the turn is rejected.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ComputronCosts {
    /// Base cost per action in the forest.
    pub action_base: u64,
    /// Base cost per effect applied.
    pub effect_base: u64,
    /// Cost per computron transfer.
    pub transfer: u64,
    /// Cost for creating a new cell.
    pub create_cell: u64,
    /// Cost for verifying a ZK proof.
    pub proof_verify: u64,
    /// Cost for verifying a signature.
    pub signature_verify: u64,
    /// Cost per byte of data processed.
    pub per_byte: u64,
    /// Waive the CHARGE for COORDINATION turns
    /// ([`Turn::is_coordination`](crate::turn::Turn::is_coordination): every
    /// action has at least one effect, every effect is an `EmitEvent` on the
    /// turn's own agent cell, no `balance_change`). "Leash, not ledger": the
    /// computron is an oversight budget, and coordination turns are the
    /// oversight traffic itself. Default `false`. When enabled, a `fee = 0`
    /// coordination turn admits and commits as long as its metered cost stays
    /// within [`Self::coordination_exempt_ceiling`]; metering stays honest
    /// (receipts report the true `computrons_used`), and economic turns
    /// (Transfer/Burn/NoteSpend/CreateCell/SetField/…) charge exactly as before.
    #[serde(default)]
    pub coordination_exempt: bool,
    /// The most computrons an exempt coordination turn may meter without
    /// paying for them. A coordination turn is admitted when its metered cost
    /// is at most `max(turn.fee, coordination_exempt_ceiling)`: under the
    /// ceiling it rides free, over it the turn must pay its cost like any
    /// other turn, and a `fee = 0` turn over it is refused `BudgetExceeded`.
    /// Default [`COORDINATION_EXEMPT_CEILING`].
    #[serde(default = "default_coordination_exempt_ceiling")]
    pub coordination_exempt_ceiling: u64,
}

/// The default [`ComputronCosts::coordination_exempt_ceiling`]: 10,000 computrons.
///
/// No per-turn computron cap exists for ordinary turns; an ordinary turn is
/// capped by its own `fee`, which its balance must cover. The largest fee an
/// unfunded devnet participant can cover in one turn is one faucet grant, and
/// `POST /api/faucet` refuses any request above 10,000 computrons
/// (`node/src/api.rs`, `req.amount > 10_000`). The exempt class gets the same
/// per-turn cap an ordinary participant funded by one grant has: about eight
/// times the measured 1,254-computron `dregg-client-sign` chat turn.
pub const COORDINATION_EXEMPT_CEILING: u64 = 10_000;

fn default_coordination_exempt_ceiling() -> u64 {
    COORDINATION_EXEMPT_CEILING
}

impl ComputronCosts {
    /// Default cost configuration (reasonable for testing).
    pub fn default_costs() -> Self {
        ComputronCosts {
            action_base: 100,
            effect_base: 50,
            transfer: 75,
            create_cell: 500,
            proof_verify: 1000,
            signature_verify: 200,
            per_byte: 1,
            coordination_exempt: false,
            coordination_exempt_ceiling: COORDINATION_EXEMPT_CEILING,
        }
    }

    /// Zero costs (for testing without metering).
    pub fn zero() -> Self {
        ComputronCosts {
            action_base: 0,
            effect_base: 0,
            transfer: 0,
            create_cell: 0,
            proof_verify: 0,
            signature_verify: 0,
            per_byte: 0,
            coordination_exempt: false,
            coordination_exempt_ceiling: COORDINATION_EXEMPT_CEILING,
        }
    }
}

impl Default for ComputronCosts {
    fn default() -> Self {
        Self::default_costs()
    }
}
