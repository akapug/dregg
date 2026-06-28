//! `dregg-bridge::solana_trustless`: the **trustless** inbound proof-of-lock for
//! the Solana `$DREGG` mirror — the honest upgrade from the trusted-oracle
//! attestation in [`crate::solana_mirror`].
//!
//! See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md` for the full design (Option A vs B,
//! the recommendation, the migration). The short of it:
//!
//! Today [`crate::solana_mirror::MirrorState::mint_against_lock`] trusts a
//! threshold [`crate::midnight::FederationAttestation`] that the Solana lock
//! happened. This module replaces that trusted *word* with a verifiable
//! *proof-of-lock* — a [`SolanaLockProof`] carrying Solana consensus evidence +
//! an account-inclusion proof — verified by [`verify_lock_proof`] and routed
//! through the SAME conservation accounting
//! ([`crate::solana_mirror::MirrorState::credit_lock`]) as the trusted path.
//!
//! # What is real vs. what is the named-hard STUB
//!
//! - **Real:** the typed lock-proof shape, its structural well-formedness, and
//!   the *binding* checks — the inclusion proof's claimed fields must match the
//!   bound claim (amount/recipient/lock_id) and the mirror config (spl_mint,
//!   amount bounds). A malformed or mis-bound proof is refused.
//! - **Named-hard STUB:** [`verify_consensus`] does NOT yet verify Solana's
//!   consensus — no Tower-BFT stake-weighted vote-set verification, no PoH
//!   linkage, no real accounts-hash inclusion against Solana's live state. It
//!   currently checks only that the evidence is *structurally present and
//!   self-consistent*. Until that is replaced, a verified proof carries
//!   [`LockProofTrust::StructureOnly`], NOT [`LockProofTrust::ConsensusVerified`].
//!   The caller is told exactly which it got, so the structural check can never
//!   be mistaken for the (not-yet-built) consensus check.
//!
//! This is deliberately honest: the consensus verification IS the trustless
//! bridge, and it is large (the whole Option-B circuit). We structure it, name
//! it, and refuse to fake it as done.

use dregg_types::CellId;
use serde::{Deserialize, Serialize};

use crate::solana_mirror::{MirrorError, MirrorMint, MirrorState};

/// Solana Tower-BFT consensus evidence for one slot: the voted bank hash, the
/// stake that voted it, and the (succinct) vote-set proof.
///
/// In a finished bridge `vote_proof` is the succinct proof that ≥ `voted_stake`
/// of `total_stake` (the epoch's active stake) voted `bank_hash` at `slot` with
/// consistent lockouts, plus the PoH linkage. **Today its contents are not
/// verified** (see [`verify_consensus`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConsensusEvidence {
    /// The Solana slot the lock was finalized in.
    pub slot: u64,
    /// The bank hash the super-majority voted (the state commitment for `slot`).
    pub bank_hash: [u8; 32],
    /// Active stake (this epoch) that voted `bank_hash`. For real finality this
    /// must be ≥ 2/3 of `total_stake`.
    pub voted_stake: u128,
    /// Total active stake for the epoch (the denominator of the 2/3 threshold).
    pub total_stake: u128,
    /// The succinct proof of the stake-weighted vote set + PoH linkage.
    ///
    /// STUB: its bytes are not yet checked — only its presence. In Option B this
    /// is the relayer's light-client SNARK/STARK over the vote transactions and
    /// the epoch stake table.
    pub vote_proof: Vec<u8>,
}

/// Inclusion proof that the Solana vault account, in the proven bank state,
/// records the lock of `recorded_amount` bound to `recorded_recipient`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AccountInclusionProof {
    /// The Solana vault account pubkey that custodies locked `$DREGG`.
    pub vault_account: [u8; 32],
    /// The amount recorded as locked by this account state.
    pub recorded_amount: u64,
    /// The dregg recipient the lock record binds the mint to.
    pub recorded_recipient: CellId,
    /// The lock id recorded (the replay nonce; matches the bound claim).
    pub recorded_lock_id: [u8; 32],
    /// The accounts hash the bank hash commits to (the root the path proves into).
    pub accounts_hash: [u8; 32],
    /// The inclusion path of `vault_account` into `accounts_hash`.
    ///
    /// STUB: the path is required to be non-empty but is NOT yet verified against
    /// `accounts_hash` (the real accounts-hash format is version-coupled to the
    /// Solana release — see the design doc, Option A row "Accounts inclusion").
    pub merkle_path: Vec<[u8; 32]>,
}

/// A verifiable proof that `amount` of `spl_mint` was locked on a finalized
/// Solana slot, bound for `dregg_recipient` inside dregg. The trustless
/// counterpart of [`crate::solana_mirror::SolanaLockAttestation`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SolanaLockProof {
    /// Unique id of the Solana lock event (replay nonce).
    pub lock_id: [u8; 32],
    /// The SPL mint pubkey of the locked token (`$DREGG` on Solana).
    pub spl_mint: [u8; 32],
    /// Amount locked, in the token's atomic units.
    pub amount: u64,
    /// The dregg cell that should receive the mirrored asset.
    pub dregg_recipient: CellId,
    /// Solana Tower-BFT consensus evidence for the lock's slot.
    pub consensus: ConsensusEvidence,
    /// Inclusion of the vault account (with the lock record) into the bank state.
    pub inclusion: AccountInclusionProof,
}

/// The trust level a [`verify_lock_proof`] call actually achieved.
///
/// This is the honesty dial: it tells the caller whether the consensus
/// verification — the part that makes the bridge trustless — actually ran.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum LockProofTrust {
    /// Only the proof's STRUCTURE and BINDING were checked (well-formedness +
    /// the claim fields match). The Solana consensus verification is STUBBED
    /// (see [`verify_consensus`]); this is NOT yet a trustless guarantee.
    StructureOnly,
    /// Solana consensus was genuinely verified (Tower-BFT stake-weighted votes,
    /// PoH, accounts-hash inclusion). **Not reachable yet** — reserved for when
    /// [`verify_consensus`] is built. A real trustless mint.
    ConsensusVerified,
}

/// Why a [`SolanaLockProof`] was refused.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LockProofError {
    /// The proof is for a different SPL mint than this mirror.
    WrongMint,
    /// Amount is below the configured dust floor.
    BelowMin,
    /// Amount exceeds the configured per-lock maximum.
    AboveMax,
    /// The inclusion proof's recorded fields do not match the bound claim
    /// (amount / recipient / lock_id mismatch — the proof binds to a different
    /// lock than it claims).
    ClaimMismatch,
    /// The proof is structurally empty/ill-formed (missing vote proof, empty
    /// inclusion path, or a zero stake denominator).
    Malformed,
    /// The consensus evidence is internally inconsistent (voted stake does not
    /// meet the ≥ 2/3 threshold of total stake). This is a structural sanity
    /// check, NOT the real consensus verification.
    StakeBelowThreshold { voted: u128, total: u128 },
}

impl std::fmt::Display for LockProofError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::WrongMint => write!(f, "lock proof is for a different SPL mint"),
            Self::BelowMin => write!(f, "amount below the mirror minimum"),
            Self::AboveMax => write!(f, "amount above the per-lock maximum"),
            Self::ClaimMismatch => write!(f, "inclusion proof fields do not match the bound claim"),
            Self::Malformed => write!(f, "lock proof is structurally ill-formed"),
            Self::StakeBelowThreshold { voted, total } => write!(
                f,
                "voted stake {voted} does not meet the 2/3 threshold of total stake {total}"
            ),
        }
    }
}

impl std::error::Error for LockProofError {}

/// Error from [`MirrorState::mint_against_lock_proof`]: either the proof failed
/// to verify, or the (verified) mint broke the mirror's accounting.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ProofMintError {
    /// The lock proof did not verify.
    Proof(LockProofError),
    /// The proof verified, but crediting the lock broke mirror accounting
    /// (replay / conservation / overflow).
    Mint(MirrorError),
}

impl std::fmt::Display for ProofMintError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Proof(e) => write!(f, "lock proof verification failed: {e}"),
            Self::Mint(e) => write!(f, "mint accounting failed: {e}"),
        }
    }
}

impl std::error::Error for ProofMintError {}

/// Verify a Solana lock proof against the mirror config.
///
/// Checks (all REAL):
/// 1. The proof's `spl_mint` matches the mirror and `amount` is within bounds.
/// 2. The inclusion proof's recorded fields bind to THIS claim (amount,
///    recipient, lock_id) — a proof cannot claim one lock and include another.
/// 3. Structural well-formedness (non-empty vote proof + inclusion path, nonzero
///    total stake) and a stake-threshold sanity check.
///
/// Then delegates to [`verify_consensus`] for the **named-hard STUBBED** Solana
/// consensus verification, and returns the [`LockProofTrust`] level achieved.
///
/// Returns [`LockProofTrust::StructureOnly`] today: the structure and binding
/// are verified, but the consensus check is a stub, so this is NOT yet a
/// trustless guarantee. See `docs/deos/TRUSTLESS-SOLANA-BRIDGE.md`.
pub fn verify_lock_proof(
    proof: &SolanaLockProof,
    spl_mint: &[u8; 32],
    min_amount: u64,
    max_amount: u64,
) -> Result<LockProofTrust, LockProofError> {
    // (1) config binding.
    if proof.spl_mint != *spl_mint {
        return Err(LockProofError::WrongMint);
    }
    if proof.amount < min_amount {
        return Err(LockProofError::BelowMin);
    }
    if proof.amount > max_amount {
        return Err(LockProofError::AboveMax);
    }

    // (2) the inclusion proof must bind to exactly the claimed lock. A proof that
    // includes a different amount/recipient/lock_id than it claims is a forgery
    // attempt and is refused regardless of the (stubbed) consensus check.
    let inc = &proof.inclusion;
    if inc.recorded_amount != proof.amount
        || inc.recorded_recipient != proof.dregg_recipient
        || inc.recorded_lock_id != proof.lock_id
    {
        return Err(LockProofError::ClaimMismatch);
    }

    // (3) structural well-formedness.
    if proof.consensus.vote_proof.is_empty() || inc.merkle_path.is_empty() {
        return Err(LockProofError::Malformed);
    }
    if proof.consensus.total_stake == 0 {
        return Err(LockProofError::Malformed);
    }

    // The Solana consensus verification (the trustless core) — STUBBED.
    verify_consensus(&proof.consensus, inc)
}

/// **NAMED-HARD STUB — the trustless core.**
///
/// In a finished bridge this verifies, against Solana's own consensus:
/// - **Tower-BFT stake-weighted votes:** that ≥ 2/3 of the epoch's active stake
///   voted `consensus.bank_hash` at `consensus.slot`, with consistent lockouts —
///   tracking the per-epoch stake table (the hard part; the sync-committee
///   analogue, but over the full ~1–2k vote accounts and rotated per epoch);
/// - **PoH linkage:** that the slot's blockhash is the genuine tail of the PoH
///   tick chain;
/// - **Accounts inclusion:** that `inclusion.merkle_path` genuinely proves
///   `inclusion.vault_account` (carrying the lock record) into the
///   `inclusion.accounts_hash` that the voted `bank_hash` commits to.
///
/// **Today it does NONE of that.** It performs only a structural sanity check:
/// the voted stake meets the ≥ 2/3 ratio of total stake. The `vote_proof` bytes,
/// the PoH chain, and the `merkle_path` against `accounts_hash` are NOT verified.
/// It therefore returns [`LockProofTrust::StructureOnly`] — never
/// [`LockProofTrust::ConsensusVerified`]. Replacing this function (and flipping
/// the returned trust level) is the whole Option-B circuit; see the design doc.
fn verify_consensus(
    consensus: &ConsensusEvidence,
    _inclusion: &AccountInclusionProof,
) -> Result<LockProofTrust, LockProofError> {
    // Structural sanity only: voted stake must clear the 2/3 threshold. This is
    // NOT a verification that the votes are real — that requires the stake table
    // and the vote-set proof, which are not checked here.
    //   voted/total >= 2/3   ⟺   3*voted >= 2*total   (overflow-safe in u128)
    if consensus.voted_stake.saturating_mul(3) < consensus.total_stake.saturating_mul(2) {
        return Err(LockProofError::StakeBelowThreshold {
            voted: consensus.voted_stake,
            total: consensus.total_stake,
        });
    }

    // STUB: the real Tower-BFT vote-set / PoH / accounts-inclusion verification
    // goes here. Until it exists, this is structure-only — NOT trustless.
    Ok(LockProofTrust::StructureOnly)
}

impl MirrorState {
    /// **Mirror-mint against a trustless [`SolanaLockProof`]** — the honest
    /// upgrade from [`MirrorState::mint_against_lock`].
    ///
    /// Verifies the lock proof via [`verify_lock_proof`], then routes through the
    /// SAME conservation accounting ([`MirrorState::credit_lock`]) the trusted
    /// path uses. The conservation invariant (`live_supply ≤ currently_locked`),
    /// replay dedup, and the emitted [`Effect::Mint`](dregg_turn::action::Effect::Mint)
    /// are identical — only the lock *evidence* (proof vs signature) differs.
    ///
    /// Returns the [`LockProofTrust`] level alongside the mint, so the caller
    /// knows whether the consensus check actually ran. **Today that is always
    /// [`LockProofTrust::StructureOnly`]** — the consensus verification is
    /// stubbed (see [`verify_consensus`]). The trusted
    /// [`MirrorState::mint_against_lock`] remains the production fallback until
    /// the consensus core is built.
    ///
    /// On any error the state is left unchanged.
    pub fn mint_against_lock_proof(
        &mut self,
        proof: &SolanaLockProof,
    ) -> Result<(MirrorMint, LockProofTrust), ProofMintError> {
        let trust = verify_lock_proof(
            proof,
            &self.config.spl_mint,
            self.config.min_amount,
            self.config.max_amount,
        )
        .map_err(ProofMintError::Proof)?;

        let mint = self
            .credit_lock(proof.lock_id, proof.amount, proof.dregg_recipient)
            .map_err(ProofMintError::Mint)?;

        Ok((mint, trust))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::midnight::EpochKey;
    use crate::solana_mirror::MirrorConfig;
    use dregg_turn::action::Effect;
    use ed25519_dalek::SigningKey;

    fn cid(b: u8) -> CellId {
        CellId::from_bytes([b; 32])
    }

    const SPL_MINT: [u8; 32] = [0xABu8; 32];
    const MIRROR_ASSET: [u8; 32] = [0xCDu8; 32];

    fn config() -> MirrorConfig {
        let o = SigningKey::from_bytes(&[7u8; 32]);
        MirrorConfig {
            spl_mint: SPL_MINT,
            asset: MIRROR_ASSET,
            oracle_keys: vec![EpochKey {
                from_epoch: 0,
                to_epoch: None,
                pubkey: o.verifying_key().to_bytes(),
            }],
            min_amount: 1,
            max_amount: 1_000_000,
        }
    }

    /// A well-formed proof that locks `amount` for `recipient` (binding fields
    /// consistent, stake over threshold, non-empty stub evidence).
    fn well_formed(amount: u64, recipient: CellId, lock_id: u8) -> SolanaLockProof {
        SolanaLockProof {
            lock_id: [lock_id; 32],
            spl_mint: SPL_MINT,
            amount,
            dregg_recipient: recipient,
            consensus: ConsensusEvidence {
                slot: 12_345,
                bank_hash: [0x01; 32],
                voted_stake: 700,
                total_stake: 1000,
                vote_proof: vec![0xEE; 8], // non-empty stub
            },
            inclusion: AccountInclusionProof {
                vault_account: [0x22; 32],
                recorded_amount: amount,
                recorded_recipient: recipient,
                recorded_lock_id: [lock_id; 32],
                accounts_hash: [0x33; 32],
                merkle_path: vec![[0x44; 32]], // non-empty stub
            },
        }
    }

    #[test]
    fn well_formed_proof_accepted_as_structure_only() {
        let cfg = config();
        let proof = well_formed(500, cid(1), 1);
        let trust =
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).expect("ok");
        // HONEST: structure verified, consensus is stubbed — NOT trustless yet.
        assert_eq!(trust, LockProofTrust::StructureOnly);
    }

    #[test]
    fn mint_against_proof_credits_through_same_accounting() {
        let mut mirror = MirrorState::new(config());
        let recipient = cid(1);
        let (mint, trust) = mirror
            .mint_against_lock_proof(&well_formed(500, recipient, 1))
            .expect("a well-formed proof mirror-mints");

        assert_eq!(trust, LockProofTrust::StructureOnly);
        assert_eq!(mint.amount, 500);
        match mint.effect {
            Effect::Mint { target, amount, .. } => {
                assert_eq!(target, recipient);
                assert_eq!(amount, 500);
            }
            ref other => panic!("expected Effect::Mint, got {other:?}"),
        }
        // Same conservation accounting as the trusted path.
        assert_eq!(mirror.live_supply, 500);
        assert_eq!(mirror.currently_locked, 500);
        assert!(mirror.invariant_holds());
    }

    #[test]
    fn double_mint_via_proof_is_rejected() {
        let mut mirror = MirrorState::new(config());
        let proof = well_formed(500, cid(1), 1);
        mirror.mint_against_lock_proof(&proof).expect("first ok");
        assert_eq!(
            mirror.mint_against_lock_proof(&proof).unwrap_err(),
            ProofMintError::Mint(MirrorError::DuplicateLock)
        );
        assert_eq!(mirror.live_supply, 500);
    }

    #[test]
    fn malformed_proof_refused_empty_vote_proof() {
        let cfg = config();
        let mut proof = well_formed(500, cid(1), 1);
        proof.consensus.vote_proof.clear();
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::Malformed
        );
    }

    #[test]
    fn malformed_proof_refused_empty_inclusion_path() {
        let cfg = config();
        let mut proof = well_formed(500, cid(1), 1);
        proof.inclusion.merkle_path.clear();
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::Malformed
        );
    }

    #[test]
    fn claim_mismatch_refused() {
        let cfg = config();
        // Inclusion records a DIFFERENT recipient than the claim binds.
        let mut proof = well_formed(500, cid(1), 1);
        proof.inclusion.recorded_recipient = cid(9);
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::ClaimMismatch
        );

        // Inclusion records a different amount than the claim.
        let mut proof2 = well_formed(500, cid(1), 2);
        proof2.inclusion.recorded_amount = 501;
        assert_eq!(
            verify_lock_proof(&proof2, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::ClaimMismatch
        );
    }

    #[test]
    fn wrong_mint_refused() {
        let cfg = config();
        let mut proof = well_formed(500, cid(1), 1);
        proof.spl_mint = [0xFF; 32];
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::WrongMint
        );
    }

    #[test]
    fn amount_bounds_enforced() {
        let cfg = config();
        let below = well_formed(0, cid(1), 1);
        assert_eq!(
            verify_lock_proof(&below, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::BelowMin
        );
        let above = well_formed(2_000_000, cid(1), 2);
        assert_eq!(
            verify_lock_proof(&above, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::AboveMax
        );
    }

    #[test]
    fn stake_below_threshold_refused() {
        let cfg = config();
        // 600/1000 < 2/3 — even the structural sanity check refuses this.
        let mut proof = well_formed(500, cid(1), 1);
        proof.consensus.voted_stake = 600;
        proof.consensus.total_stake = 1000;
        assert_eq!(
            verify_lock_proof(&proof, &cfg.spl_mint, cfg.min_amount, cfg.max_amount).unwrap_err(),
            LockProofError::StakeBelowThreshold {
                voted: 600,
                total: 1000
            }
        );
    }
}
