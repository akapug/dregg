//! # Protocol-native run budget (Track C, rung 2a) — a conserved cell balance, no custody.
//!
//! This module is the **protocol-native settlement path** the crate's top-level
//! docs name as the endgame: a run's budget is a conserved balance in an
//! *internal* asset, and spending a run is one conserving `Effect::Transfer`
//! authorized by the **user's own** cell — not an off-chain sqlite number an
//! operator credits, and not a custodial HD deposit an operator sweeps.
//! (See `docs/deos/PROTOCOL-NATIVE-ECONOMY.md` §4 rung 2a.)
//!
//! ## What "protocol-native" means here, concretely
//!
//! The user holds a run-budget balance in their own `Payable` cell. A run debits
//! it via [`dregg_payable::resolve_pay`] — the one verified desugar to a single
//! conserving [`Effect::Transfer`] (per-asset Σδ=0, kernel-checked at
//! `turn/src/action.rs`), `Signature`-gated by the user's key. The run-budget
//! "ledger" here is a **read-model of conserved balances**: its only mutation is
//! applying a conserving transfer. There is no mint primitive, no
//! set-balance-from-payment authority, and — critically — **no custody key and no
//! sweeper reachable from this path**. The custodial modules (`hd`, `sweeper`)
//! are never imported here; the falsifier for rung 2a is exactly "grep this accept
//! path for the custody types and find nothing" and this module is written to
//! make that grep green (`tests/protocol_native_rung2a.rs`).
//!
//! ## Why an internal, dedicated run-credit asset (not bridged `$DREGG`, not computrons)
//!
//! Rung 2a ships the *mechanism* on an asset that carries **no bridged value**, so
//! it does not depend on the three open bridge value-path suspects
//! (`docs/deos/PROTOCOL-NATIVE-ECONOMY.md` §5). Two internal choices exist:
//! computrons (the node's `computron_transfers` metering ledger) or a dedicated
//! `Payable` asset. This module takes the **dedicated `Payable` asset**:
//!
//! * It keeps the run budget a *first-class `Payable` holding* spendable directly
//!   through `resolve_pay` — the exact rail rung 2b swaps to bridged `$DREGG` with
//!   a one-line asset-id change, because `resolve_pay` is asset-generic.
//! * It avoids pulling the node's computron-refill ledger (and its crate) onto the
//!   pay crate's accept path, keeping this module marshal-only / pure data
//!   construction (`resolve_pay` builds an `Action`; it never runs the executor).
//!
//! In the dregg value model an asset *is* its issuer cell, so the internal
//! run-credit asset id is a well-known, domain-separated 32-byte constant
//! ([`run_credit_asset`]) — the id of the internal issuer that denominates run
//! budgets. Rung 2b replaces this constant with the bridged-`$DREGG` vault-mint
//! asset id (gated on the bridge suspects closing); nothing else in this path
//! changes.
//!
//! ## Additive, config-selected
//!
//! This is a *new* rail selected by config ([`RunSettlementMode`]); the custodial
//! rail (`ledger`, `hd`, `sweeper`, `watcher`) keeps compiling and running
//! unchanged. An operator picks [`RunSettlementMode::ProtocolNative`] to settle
//! runs as conserving transfers with no custody, or leaves the custodial bridge in
//! place for users who arrive with raw SPL tokens and no cell (the on-ramp).

use std::collections::HashMap;

use dregg_payable::{AssetId, InvokeAuthority, InvokeRefused, resolve_pay};
use dregg_turn::action::{Action, Effect};
use dregg_types::CellId;

/// The domain string for the internal run-credit asset id. Domain-separated so it
/// can never collide with any other 32-byte asset id in the value model.
pub const RUN_CREDIT_ASSET_DOMAIN: &str = "dregg-pay/protocol-native-run-credit/v1";

/// The default run price: **one** run-credit per run. A run debits exactly this
/// many credits as a conserving transfer.
pub const DEFAULT_RUN_PRICE_CREDITS: u64 = 1;

/// The internal, dedicated run-credit [`AssetId`] — a domain-separated constant.
///
/// In the dregg value model an asset *is* its issuer cell; this is the id of the
/// internal issuer that denominates protocol-native run budgets. It carries no
/// bridged value (rung 2a). Rung 2b swaps this for the bridged-`$DREGG` vault mint.
pub fn run_credit_asset() -> AssetId {
    *blake3::hash(RUN_CREDIT_ASSET_DOMAIN.as_bytes()).as_bytes()
}

/// Which rail settles a run's budget. Selected by operator config; additive over
/// the existing custodial rail.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RunSettlementMode {
    /// The legacy "B" custodial HD-deposit rail (`hd` + `sweeper` + `ledger`):
    /// an operator holds a custody key and sweeps deposits; run credits are an
    /// off-chain sqlite number. The pragmatic on-ramp bridge.
    Custodial,
    /// The protocol-native rail (this module): run budget is a conserved cell
    /// balance in the internal run-credit asset; a run is one conserving
    /// `Effect::Transfer` from the user's cell. No custody key, no sweeper.
    ProtocolNative,
}

/// Why a protocol-native run charge was refused. Every variant is fail-closed:
/// on any error **no balance moves** (the check precedes every mutation).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChargeError {
    /// The `resolve_pay` front door refused the payment — e.g. the caller did not
    /// present the user's `Signature` authority (an operator cannot authorize a
    /// debit of the user's cell), or the method did not route.
    Refused(InvokeRefused),
    /// The user's run-budget balance is below the run price. Fail-closed: an empty
    /// (or insufficient) budget refuses the run and moves nothing.
    InsufficientBudget {
        /// The user's current run-credit balance.
        have: u64,
        /// The run price that could not be covered.
        need: u64,
    },
    /// Crediting the operator would overflow `u64`. Fail-closed; nothing moves.
    BalanceOverflow,
    /// `resolve_pay` did not desugar to exactly one `Effect::Transfer` from the
    /// user cell. Structurally impossible for the canonical `Payable` descriptor;
    /// surfaced fail-closed rather than trusted.
    Malformed,
}

impl std::fmt::Display for ChargeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Refused(r) => write!(f, "run charge refused at the pay front door: {r}"),
            Self::InsufficientBudget { have, need } => write!(
                f,
                "insufficient run budget: have {have} credit(s), run costs {need}"
            ),
            Self::BalanceOverflow => write!(f, "crediting the operator would overflow the balance"),
            Self::Malformed => write!(
                f,
                "pay did not desugar to exactly one conserving Transfer from the user cell"
            ),
        }
    }
}

impl std::error::Error for ChargeError {}

/// The receipt of a settled protocol-native run: the conserving [`Action`] the
/// user authorized (carrying the single [`Effect::Transfer`]) and the user's
/// remaining run-credit balance after the debit.
#[derive(Clone, Debug)]
pub struct RunReceipt {
    /// The unsigned, resolved pay action — its single effect is the conserving
    /// `Transfer` from the user cell to the operator cell. Downstream the executor
    /// binds the `Signature` to the `from` (user) cell's key and re-checks per-asset
    /// conservation; this receipt is the auditable record of what was paid.
    pub action: Action,
    /// The amount debited (the run price, in run-credits).
    pub debited: u64,
    /// The user's run-credit balance remaining after the run.
    pub remaining: u64,
}

impl RunReceipt {
    /// The single conserving transfer this run desugared to `(from, to, amount)`.
    /// Returns `None` if the action does not carry exactly one `Transfer`.
    pub fn transfer(&self) -> Option<(CellId, CellId, u64)> {
        single_transfer(&self.action)
    }
}

/// Extract the single `Effect::Transfer` from a resolved pay action, if the action
/// carries exactly one and it is a `Transfer`.
fn single_transfer(action: &Action) -> Option<(CellId, CellId, u64)> {
    match action.effects.as_slice() {
        [Effect::Transfer { from, to, amount }] => Some((*from, *to, *amount)),
        _ => None,
    }
}

/// **The protocol-native run-budget ledger — a read-model of conserved balances.**
///
/// Holds per-cell balances in ONE internal asset ([`run_credit_asset`]). Its only
/// mutation is [`RunBudgetLedger::charge_run`], which applies a single conserving
/// transfer produced by [`resolve_pay`]. There is no mint and no set-balance
/// authority: balances are established from a snapshot of the conserved on-chain
/// state ([`RunBudgetLedger::from_balances`]) and thereafter only move by
/// conserving transfers. The kernel is the authority on conservation
/// (`turn/src/action.rs`); this book applies the same kernel-shaped `Transfer` and
/// stays balanced by construction (it credits exactly what it debits).
#[derive(Clone, Debug)]
pub struct RunBudgetLedger {
    asset: AssetId,
    balances: HashMap<CellId, u64>,
}

impl RunBudgetLedger {
    /// A ledger in the internal run-credit asset with the given snapshot of
    /// conserved balances. The snapshot is a read of already-conserved on-chain
    /// state, not a mint — this constructor is the only way balances enter, and
    /// thereafter they only move by conserving transfer.
    pub fn from_balances(asset: AssetId, balances: HashMap<CellId, u64>) -> Self {
        Self { asset, balances }
    }

    /// A ledger denominated in the canonical internal run-credit asset
    /// ([`run_credit_asset`]) with the given balance snapshot.
    pub fn run_credits(balances: HashMap<CellId, u64>) -> Self {
        Self::from_balances(run_credit_asset(), balances)
    }

    /// The asset this ledger denominates run budgets in.
    pub fn asset(&self) -> AssetId {
        self.asset
    }

    /// A cell's current run-credit balance (0 if unknown).
    pub fn balance(&self, cell: &CellId) -> u64 {
        self.balances.get(cell).copied().unwrap_or(0)
    }

    /// The total run-credits across all cells — the per-asset conserved quantity.
    /// A correct charge leaves this **unchanged** (Σδ = 0); the adversarial tests
    /// assert exactly that.
    pub fn total(&self) -> u128 {
        self.balances.values().map(|&b| b as u128).sum()
    }

    /// **Settle a run: debit the user's budget by `price` as one conserving
    /// transfer to the operator cell.**
    ///
    /// The accept path, end to end:
    /// 1. [`resolve_pay`] routes the user's `pay(run_credit_asset, price,
    ///    operator)` through the canonical `Payable` descriptor, `Signature`-gated
    ///    by the user's `authority`, desugaring to exactly one conserving
    ///    [`Effect::Transfer`] from the **user** cell. An operator, holding no user
    ///    signature, cannot authorize it.
    /// 2. The transfer is applied to this read-model — **fail-closed** if the
    ///    user's budget is below `price` (checked before any mutation, so an empty
    ///    budget moves nothing) or if the operator credit would overflow.
    ///
    /// No custody key and no sweeper are reachable from this function — the run
    /// budget is spent entirely by a transfer the user authorized. On any error,
    /// no balance changes.
    pub fn charge_run(
        &mut self,
        user: CellId,
        operator: CellId,
        price: u64,
        authority: InvokeAuthority,
    ) -> Result<RunReceipt, ChargeError> {
        // (1) Resolve the pay to its single conserving Transfer, Signature-gated.
        let (action, _sig) = resolve_pay(user, self.asset, price, operator, authority)
            .map_err(ChargeError::Refused)?;

        // (2) The desugar must be exactly one Transfer from the user cell.
        let (from, to, amount) = single_transfer(&action).ok_or(ChargeError::Malformed)?;
        if from != user || to != operator || amount != price {
            return Err(ChargeError::Malformed);
        }

        // (3) Apply the conserving transfer, fail-closed, atomically (every new
        //     balance is computed before any is written). A self-transfer
        //     (`from == to`) is net-zero and must leave the balance unchanged —
        //     handled explicitly so the read-model can never inflate on it.
        let have = self.balance(&from);
        let new_from = have
            .checked_sub(amount)
            .ok_or(ChargeError::InsufficientBudget { have, need: amount })?;
        let remaining = if from == to {
            // net-zero: funds validated present, balance stays `have`.
            have
        } else {
            let new_to = self
                .balance(&to)
                .checked_add(amount)
                .ok_or(ChargeError::BalanceOverflow)?;
            self.balances.insert(from, new_from);
            self.balances.insert(to, new_to);
            new_from
        };

        Ok(RunReceipt {
            action,
            debited: amount,
            remaining,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    fn ledger(user_balance: u64) -> (RunBudgetLedger, CellId, CellId) {
        let user = cid(1);
        let operator = cid(2);
        let mut map = HashMap::new();
        map.insert(user, user_balance);
        (RunBudgetLedger::run_credits(map), user, operator)
    }

    /// A run debits exactly one credit as a conserving transfer: the per-asset
    /// total is unchanged, the user loses exactly the price, and the operator
    /// gains exactly the price. Non-vacuous: a charge that forgot to credit the
    /// operator (or credited a different amount) would move `total()`.
    #[test]
    fn run_debits_exactly_one_credit_conserving() {
        let (mut l, user, operator) = ledger(5);
        let total_before = l.total();

        let receipt = l
            .charge_run(
                user,
                operator,
                DEFAULT_RUN_PRICE_CREDITS,
                InvokeAuthority::Signature,
            )
            .expect("a funded budget settles one run as a conserving transfer");

        assert_eq!(
            l.total(),
            total_before,
            "per-asset Σδ must be 0 across the run"
        );
        assert_eq!(l.balance(&user), 4, "user debited exactly one credit");
        assert_eq!(
            l.balance(&operator),
            1,
            "operator credited exactly one credit"
        );
        assert_eq!(receipt.debited, 1);
        assert_eq!(receipt.remaining, 4);
        assert_eq!(
            receipt.transfer(),
            Some((user, operator, 1)),
            "the run desugared to one conserving Transfer from the user cell"
        );
    }

    /// An empty budget refuses the run (fail-closed) and moves nothing.
    #[test]
    fn empty_budget_refuses_and_moves_nothing() {
        let (mut l, user, operator) = ledger(0);
        let total_before = l.total();

        let err = l
            .charge_run(
                user,
                operator,
                DEFAULT_RUN_PRICE_CREDITS,
                InvokeAuthority::Signature,
            )
            .expect_err("an empty budget must refuse the run");

        assert!(
            matches!(err, ChargeError::InsufficientBudget { have: 0, need: 1 }),
            "fail-closed on empty budget, got {err:?}"
        );
        assert_eq!(l.total(), total_before, "a refused run moves nothing");
        assert_eq!(l.balance(&user), 0, "user balance untouched");
        assert_eq!(l.balance(&operator), 0, "operator credited nothing");
    }

    /// The debit is the USER's cap: an operator, holding no user signature, cannot
    /// authorize it. `resolve_pay` refuses `InvokeAuthority::None`, and nothing moves.
    #[test]
    fn operator_cannot_authorize_user_debit() {
        let (mut l, user, operator) = ledger(5);
        let total_before = l.total();

        let err = l
            .charge_run(
                user,
                operator,
                DEFAULT_RUN_PRICE_CREDITS,
                InvokeAuthority::None,
            )
            .expect_err("a debit without the user's Signature cap must be refused");

        assert!(
            matches!(
                err,
                ChargeError::Refused(InvokeRefused::Unauthorized { .. })
            ),
            "only the user's Signature cap admits the debit, got {err:?}"
        );
        assert_eq!(l.total(), total_before, "a refused run moves nothing");
        assert_eq!(l.balance(&user), 5, "user balance untouched");
    }

    /// The settled transfer's `from` is the user cell — so the executor binds the
    /// signature to the user's key, never the operator's.
    #[test]
    fn debit_is_from_the_user_cell() {
        let (mut l, user, operator) = ledger(3);
        let receipt = l
            .charge_run(user, operator, 2, InvokeAuthority::Signature)
            .expect("funded budget settles");
        let (from, to, amount) = receipt.transfer().expect("one transfer");
        assert_eq!(from, user);
        assert_eq!(to, operator);
        assert_eq!(amount, 2);
        assert_eq!(l.balance(&user), 1);
        assert_eq!(l.balance(&operator), 2);
    }

    /// A self-transfer (`user == operator`) is net-zero: the balance is unchanged
    /// and the per-asset total is conserved. Non-vacuous: the earlier double-write
    /// apply would have inflated the balance to `have + amount` here.
    #[test]
    fn self_transfer_is_net_zero_and_conserving() {
        let user = cid(1);
        let mut map = HashMap::new();
        map.insert(user, 5);
        let mut l = RunBudgetLedger::run_credits(map);
        let total_before = l.total();

        let receipt = l
            .charge_run(user, user, 2, InvokeAuthority::Signature)
            .expect("a self-transfer with sufficient funds is a valid net-zero move");

        assert_eq!(
            l.balance(&user),
            5,
            "self-transfer must not change the balance"
        );
        assert_eq!(l.total(), total_before, "self-transfer conserves the total");
        assert_eq!(receipt.remaining, 5);
    }

    /// The internal run-credit asset is a stable, domain-separated constant.
    #[test]
    fn run_credit_asset_is_stable_and_domain_separated() {
        assert_eq!(run_credit_asset(), run_credit_asset());
        assert_ne!(run_credit_asset(), [0u8; 32]);
    }
}
