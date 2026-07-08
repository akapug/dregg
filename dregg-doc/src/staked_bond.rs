//! STAKED-BOND FORFEITURE — the real, conserving, one-shot slash behind
//! [`crate::ci_assurance::CiAssurance::Staked`].
//!
//! ## The seam this closes
//!
//! [`CiAssurance::Staked`](crate::ci_assurance::CiAssurance::Staked) surfaces a
//! [`Conviction`] naming a `bond_ref` when its inner policy catches a lie — but a
//! `Conviction` alone moves no value: it is a label. The economic security the
//! rung PROMISES ("a caught lie has a cost") only exists once the bonded value
//! actually LEAVES the lying host. This module is that transfer: given a real
//! inner conviction, it moves the bonded amount OUT of the host's stake to a
//! slash beneficiary, conservingly and at-most-once.
//!
//! ## What is reused (NOT reinvented)
//!
//! - **The conserving transfer** is the `dregg_cell` signed-`i64` balance ledger
//!   ([`Cell`]'s [`dregg_cell::CellState::debit_balance`] /
//!   [`dregg_cell::CellState::credit_balance`]) — the SAME value primitive the
//!   `Payable` `Effect::Transfer` desugar and [`dregg_cell::escrow_sealed`] settle
//!   over. A slash debits the bond-holding cell by exactly `amount` and credits
//!   the beneficiary by exactly `amount`, so per-asset `Σδ = 0`: no value is
//!   created or destroyed, only moved.
//! - **The one-shot guard** mirrors [`dregg_cell::escrow_sealed`]'s committed-heap
//!   `Consumed` discipline exactly: the bond's status lives in the cell's
//!   committed heap (folded into the state commitment, so a light client sees the
//!   forfeiture), and slashing or releasing flips it to the terminal `Consumed`
//!   state. Any second slash/release of a `Consumed` bond is refused — a slashed
//!   bond is a spent nullifier. The `i64` heap encoding is
//!   [`dregg_cell::escrow_sealed::encode_i64`] / `decode_i64`, reused directly.
//!
//! ## Conviction-gating
//!
//! A [`SlashOutcome`] can ONLY be built from a real [`Conviction`]
//! ([`SlashOutcome::from_conviction`]); mere non-satisfaction ([`AssuranceOutcome::Unmet`])
//! produces no slash. A satisfied inner policy leaves the bond untouched and
//! RELEASABLE to the host ([`release_bond`]). See [`bond_disposition`].
//!
//! ## The remaining seam (named)
//!
//! The forfeiture-on-conviction here is real, conserving, and one-shot. What is
//! still out-of-crate is the host POSTING the bond at CI-job start (the deposit
//! that funds [`post_bond`]) and a cross-node stake registry that maps a
//! `bond_ref` to its holding cell — the deployment wires those. This module owns
//! the slash itself; it does not own where the stake came from.

use dregg_cell::escrow_sealed::{decode_i64, encode_i64};
use dregg_cell::{Cell, CellId, FieldElement};

use crate::ci_assurance::{AssuranceOutcome, BondRef, Conviction, ConvictionEvidence};

/// Reserved heap collection id for the staked-bond ledger. Lives inside the
/// bond-holding cell's committed heap (so the bond's amount + one-shot status are
/// folded into the canonical state commitment), chosen high to avoid colliding
/// with any application heap collection — the same discipline as
/// [`dregg_cell::escrow_sealed::ESCROW_COLL`].
pub const BOND_COLL: u32 = 0x0057_0A6E_u32; // a fixed reserved id ("STAKE")

/// Heap key: the bonded amount (canonical little-endian `i64`).
pub const KEY_BOND_AMOUNT: u32 = 0;
/// Heap key: the bond status flag — `0` = none, `1` = posted (live), `2` =
/// consumed (slashed OR released). The one-shot terminal is `2`.
pub const KEY_BOND_STATUS: u32 = 1;

/// A staked bond's lifecycle status, stored as one felt in the committed heap —
/// the [`dregg_cell::escrow_sealed::LegStatus`] discipline for a single stake.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BondStatus {
    /// No bond posted on this cell.
    None,
    /// A stake is posted and live — slashable (on conviction) or releasable (on
    /// satisfaction).
    Posted,
    /// The bond has been consumed — slashed to a beneficiary OR released to the
    /// host. The one-shot terminal: any further slash/release is refused.
    Consumed,
}

impl BondStatus {
    fn to_felt(self) -> FieldElement {
        encode_i64(match self {
            BondStatus::None => 0,
            BondStatus::Posted => 1,
            BondStatus::Consumed => 2,
        })
    }
    fn from_felt(f: &FieldElement) -> BondStatus {
        match decode_i64(f) {
            1 => BondStatus::Posted,
            2 => BondStatus::Consumed,
            _ => BondStatus::None,
        }
    }
}

/// WHERE a forfeit bond goes — a policy field on the [`StakedBond`]. Default is
/// [`SlashBeneficiary::Burn`] (value removed from the host with no recipient to
/// enrich, the neutral deterrent).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum SlashBeneficiary {
    /// Burn: the forfeit value moves to a deployment-configured burn cell
    /// (removed from the host's circulation). The burn-cell identity is the named
    /// deployment seam — [`slash_bond`] credits whatever burn cell the caller
    /// supplies and does not pin a fixed address here.
    #[default]
    Burn,
    /// A slashing pool that accrues forfeited bonds (the identified pool cell).
    Pool(CellId),
    /// The challenger who PROVED the lie (the divergent re-execution signer / the
    /// upheld-challenge author): the forfeit funds the party that caught the lie.
    Challenger(CellId),
}

impl SlashBeneficiary {
    /// The beneficiary cell this policy names, or `None` for [`SlashBeneficiary::Burn`]
    /// (whose burn cell the deployment supplies — the named seam). [`slash_bond`]
    /// enforces `beneficiary_cell.id() == Some(id)` when this is `Some`.
    pub fn cell(&self) -> Option<CellId> {
        match self {
            SlashBeneficiary::Burn => None,
            SlashBeneficiary::Pool(id) | SlashBeneficiary::Challenger(id) => Some(*id),
        }
    }
}

/// A STAKED BOND: the host's deposit backing a [`CiAssurance::Staked`] check. The
/// on-cell ledger ([`BOND_COLL`]) binds the `amount` + one-shot status; this
/// descriptor carries the policy (who posted, in what asset, where a slash goes)
/// the deployment holds keyed by `bond_ref`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StakedBond {
    /// The bond identifier (matches [`Conviction::bond_ref`] on a slash).
    pub bond_ref: BondRef,
    /// The bonded amount (`> 0`).
    pub amount: i64,
    /// The host that posted the deposit (the cell the bond returns to on release).
    pub poster: CellId,
    /// The asset the bond is denominated in.
    pub asset: CellId,
    /// Where a forfeit bond goes (policy; default [`SlashBeneficiary::Burn`]).
    pub beneficiary_on_slash: SlashBeneficiary,
}

impl StakedBond {
    /// A bond of `amount` posted by `poster` in `asset`, burned on slash (the
    /// default policy).
    pub fn burned(bond_ref: BondRef, amount: i64, poster: CellId, asset: CellId) -> Self {
        StakedBond {
            bond_ref,
            amount,
            poster,
            asset,
            beneficiary_on_slash: SlashBeneficiary::Burn,
        }
    }

    /// Set the slash beneficiary policy.
    pub fn to_beneficiary(mut self, beneficiary: SlashBeneficiary) -> Self {
        self.beneficiary_on_slash = beneficiary;
        self
    }
}

/// Why a bond operation was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BondError {
    /// The cell carries no bond ledger (nothing posted).
    NotABond,
    /// The bond is not in the live `Posted` state (never posted, or already
    /// consumed — see [`BondError::AlreadyConsumed`]).
    NotPosted,
    /// THE ONE-SHOT REJECTION: the bond is already `Consumed` (slashed or
    /// released); it cannot be slashed/released again.
    AlreadyConsumed,
    /// The committed bonded amount does not match the descriptor's `amount` — the
    /// wrong bond was presented for this cell.
    AmountMismatch {
        /// What the cell's ledger committed.
        committed: i64,
        /// What the [`StakedBond`] descriptor asserts.
        expected: i64,
    },
    /// A non-positive bond amount (a bond must lock real value).
    NonPositiveAmount(i64),
    /// The [`SlashOutcome`]'s `bond_ref` does not match this bond.
    BondRefMismatch,
    /// The supplied beneficiary cell is not the one the slash outcome names.
    WrongBeneficiary,
    /// The supplied host cell is not this bond's `poster` (release only returns to
    /// the poster).
    WrongPoster,
    /// The balance move underflowed (the holding cell held less than `amount`) or
    /// overflowed (the recipient could not hold it). A posted bond should never
    /// underflow; this guards the arithmetic.
    TransferFailed,
}

impl std::fmt::Display for BondError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BondError::NotABond => write!(f, "cell carries no staked-bond ledger"),
            BondError::NotPosted => write!(f, "bond is not in the live posted state"),
            BondError::AlreadyConsumed => write!(
                f,
                "bond already consumed (one-shot): cannot be slashed/released again"
            ),
            BondError::AmountMismatch {
                committed,
                expected,
            } => write!(
                f,
                "bond amount mismatch: cell commits {committed} but descriptor asserts {expected}"
            ),
            BondError::NonPositiveAmount(a) => write!(f, "bond amount must be positive, got {a}"),
            BondError::BondRefMismatch => write!(f, "slash outcome names a different bond"),
            BondError::WrongBeneficiary => {
                write!(f, "supplied beneficiary cell is not the one named")
            }
            BondError::WrongPoster => write!(f, "release only returns the bond to its poster"),
            BondError::TransferFailed => write!(f, "conserving balance move under/overflowed"),
        }
    }
}

impl std::error::Error for BondError {}

/// A read-only view of the bond ledger recovered from a cell's committed heap.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BondState {
    /// The committed bonded amount.
    pub amount: i64,
    /// The bond status.
    pub status: BondStatus,
}

impl BondState {
    /// Recover the bond ledger committed on `cell`, or [`BondError::NotABond`] if
    /// none was ever posted.
    pub fn read(cell: &Cell) -> Result<BondState, BondError> {
        let status = cell
            .state
            .get_heap(BOND_COLL, KEY_BOND_STATUS)
            .map(|f| BondStatus::from_felt(&f))
            .ok_or(BondError::NotABond)?;
        let amount = cell
            .state
            .get_heap(BOND_COLL, KEY_BOND_AMOUNT)
            .map(|f| decode_i64(&f))
            .unwrap_or(0);
        Ok(BondState { amount, status })
    }
}

/// **POST** a bond: lock `bond.amount` of value out of the host cell and into the
/// bond-holding cell, and write the live `Posted` ledger into the holding cell's
/// committed heap. This is the deposit the host makes when it takes the CI job —
/// a conserving transfer `host -> bond_cell` (per-asset `Σδ = 0`).
///
/// Refuses a non-positive amount, a re-post over a live/consumed bond, or a host
/// balance that cannot cover the stake.
pub fn post_bond(
    host: &mut Cell,
    bond_cell: &mut Cell,
    bond: &StakedBond,
) -> Result<(), BondError> {
    if bond.amount <= 0 {
        return Err(BondError::NonPositiveAmount(bond.amount));
    }
    // One-shot from empty: cannot re-post over a live or consumed bond.
    match BondState::read(bond_cell) {
        Err(BondError::NotABond) => {}
        Ok(BondState {
            status: BondStatus::None,
            ..
        }) => {}
        Ok(BondState {
            status: BondStatus::Posted,
            ..
        }) => return Err(BondError::NotPosted),
        Ok(BondState {
            status: BondStatus::Consumed,
            ..
        }) => return Err(BondError::AlreadyConsumed),
        Err(e) => return Err(e),
    }
    let amount =
        u64::try_from(bond.amount).map_err(|_| BondError::NonPositiveAmount(bond.amount))?;
    // The conserving transfer: debit the host, credit the holding cell.
    if !host.state.debit_balance(amount) {
        return Err(BondError::TransferFailed);
    }
    if !bond_cell.state.credit_balance(amount) {
        // Roll back the host debit so no value is destroyed on failure.
        let _ = host.state.credit_balance(amount);
        return Err(BondError::TransferFailed);
    }
    bond_cell
        .state
        .set_heap(BOND_COLL, KEY_BOND_AMOUNT, encode_i64(bond.amount));
    bond_cell
        .state
        .set_heap(BOND_COLL, KEY_BOND_STATUS, BondStatus::Posted.to_felt());
    Ok(())
}

/// THE FORFEITURE ACTION produced on a real inner [`Conviction`]: it names the
/// bond, the amount to move, where it goes, and the evidence that convicted. Its
/// ONLY public constructor is [`SlashOutcome::from_conviction`], so a slash cannot
/// be conjured without a genuine conviction (conviction-gating by construction).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SlashOutcome {
    /// The bond forfeit by this slash.
    pub bond_ref: BondRef,
    /// The amount to move out of the host's stake.
    pub amount: i64,
    /// Where the forfeit value goes.
    pub beneficiary: SlashBeneficiary,
    /// The evidence that proved the lie (from the conviction).
    pub evidence: ConvictionEvidence,
}

impl SlashOutcome {
    /// Build the forfeiture for `bond` from a real [`Conviction`], or `None` if
    /// the conviction names a different bond (or names no bond at all). This is
    /// the ONLY way to construct a [`SlashOutcome`] — a slash requires a
    /// conviction.
    pub fn from_conviction(bond: &StakedBond, conviction: &Conviction) -> Option<SlashOutcome> {
        match conviction.bond_ref {
            Some(bref) if bref == bond.bond_ref => Some(SlashOutcome {
                bond_ref: bond.bond_ref,
                amount: bond.amount,
                beneficiary: bond.beneficiary_on_slash,
                evidence: conviction.evidence.clone(),
            }),
            _ => None,
        }
    }
}

/// A bond RELEASE produced when the inner policy is satisfied: the untouched bond
/// is returnable to its poster.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BondRelease {
    /// The bond to release.
    pub bond_ref: BondRef,
    /// The amount to return.
    pub amount: i64,
    /// The host the bond returns to.
    pub poster: CellId,
}

/// The disposition of a staked bond given an inner-policy [`AssuranceOutcome`]:
/// SLASH on a conviction, RELEASE on satisfaction, HOLD otherwise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BondDisposition {
    /// The inner policy caught a lie — fire this forfeiture ([`slash_bond`]).
    Slash(SlashOutcome),
    /// The inner policy is satisfied — the bond is returnable ([`release_bond`]).
    Release(BondRelease),
    /// The inner policy is merely unmet (no lie proven) or the conviction names a
    /// different bond — the bond does NOT move.
    Hold,
}

/// Translate an inner-policy [`AssuranceOutcome`] + a bond descriptor into the
/// bond disposition. This is the conviction-gate: only [`AssuranceOutcome::Convicted`]
/// (with a matching `bond_ref`) yields a [`BondDisposition::Slash`]; a mere
/// [`AssuranceOutcome::Unmet`] holds, and [`AssuranceOutcome::Satisfied`] releases.
pub fn bond_disposition(outcome: &AssuranceOutcome, bond: &StakedBond) -> BondDisposition {
    match outcome {
        AssuranceOutcome::Convicted(c) => match SlashOutcome::from_conviction(bond, c) {
            Some(s) => BondDisposition::Slash(s),
            None => BondDisposition::Hold,
        },
        AssuranceOutcome::Satisfied => BondDisposition::Release(BondRelease {
            bond_ref: bond.bond_ref,
            amount: bond.amount,
            poster: bond.poster,
        }),
        AssuranceOutcome::Unmet(_) => BondDisposition::Hold,
    }
}

/// **SLASH** a bond: the real, conserving, one-shot forfeiture. Given a
/// [`SlashOutcome`] (which only a genuine [`Conviction`] can produce), it consumes
/// the bond ONE-SHOT and moves exactly `amount` from the holding cell to the
/// beneficiary cell — a conserving transfer (`Σδ = 0` across the two cells).
///
/// Refuses:
/// - [`BondError::BondRefMismatch`] — the outcome is for a different bond,
/// - [`BondError::NotABond`] / [`BondError::NotPosted`] — nothing live to slash,
/// - [`BondError::AlreadyConsumed`] — the ONE-SHOT bite: a second slash (or a
///   slash after release) is refused,
/// - [`BondError::AmountMismatch`] — the committed amount is not what the
///   descriptor asserts,
/// - [`BondError::WrongBeneficiary`] — the supplied cell is not the named
///   beneficiary (for a [`SlashBeneficiary::Pool`] / `Challenger`).
///
/// Returns the amount moved.
pub fn slash_bond(
    bond_cell: &mut Cell,
    beneficiary_cell: &mut Cell,
    bond: &StakedBond,
    outcome: &SlashOutcome,
) -> Result<i64, BondError> {
    if outcome.bond_ref != bond.bond_ref {
        return Err(BondError::BondRefMismatch);
    }
    if let Some(named) = outcome.beneficiary.cell() {
        if beneficiary_cell.id() != named {
            return Err(BondError::WrongBeneficiary);
        }
    }
    let amount = consume_posted_bond(bond_cell, bond)?;
    move_value(bond_cell, beneficiary_cell, amount)?;
    Ok(amount)
}

/// **RELEASE** a bond back to its poster when the inner policy is satisfied: the
/// same one-shot consume as a slash, but the value returns to the host, and only
/// the poster may receive it. A released bond can never then be slashed (and
/// vice-versa) — the one-shot `Consumed` flag is shared across both paths.
///
/// Returns the amount returned.
pub fn release_bond(
    bond_cell: &mut Cell,
    host_cell: &mut Cell,
    bond: &StakedBond,
) -> Result<i64, BondError> {
    if host_cell.id() != bond.poster {
        return Err(BondError::WrongPoster);
    }
    let amount = consume_posted_bond(bond_cell, bond)?;
    move_value(bond_cell, host_cell, amount)?;
    Ok(amount)
}

/// Verify the bond is live+posted at the descriptor's amount and flip it ONE-SHOT
/// to `Consumed`, returning the amount. Shared by [`slash_bond`] and
/// [`release_bond`] so the one-shot bite is identical on both paths.
fn consume_posted_bond(bond_cell: &mut Cell, bond: &StakedBond) -> Result<i64, BondError> {
    let state = BondState::read(bond_cell)?;
    match state.status {
        BondStatus::Posted => {}
        BondStatus::None => return Err(BondError::NotPosted),
        BondStatus::Consumed => return Err(BondError::AlreadyConsumed),
    }
    if state.amount != bond.amount {
        return Err(BondError::AmountMismatch {
            committed: state.amount,
            expected: bond.amount,
        });
    }
    bond_cell
        .state
        .set_heap(BOND_COLL, KEY_BOND_STATUS, BondStatus::Consumed.to_felt());
    Ok(state.amount)
}

/// The conserving value move: debit `from` by `amount`, credit `to` by `amount`.
/// If either half fails (under/overflow), the whole move is rolled back so no
/// value is created or destroyed.
fn move_value(from: &mut Cell, to: &mut Cell, amount: i64) -> Result<(), BondError> {
    let amt = u64::try_from(amount).map_err(|_| BondError::NonPositiveAmount(amount))?;
    if !from.state.debit_balance(amt) {
        return Err(BondError::TransferFailed);
    }
    if !to.state.credit_balance(amt) {
        let _ = from.state.credit_balance(amt);
        return Err(BondError::TransferFailed);
    }
    Ok(())
}
