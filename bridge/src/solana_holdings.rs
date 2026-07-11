//! Non-custodial **proof-of-holdings** — the dreggic alternative to lock-and-mirror.
//!
//! `solana_mirror` / `solana-lock` implement the *lock* path: a holder moves their
//! `$DREGG` into a vault and dregg mirrors it in. That is legitimate for *importing
//! spendable value* or posting a *slashable bond* — the cases where an escrow
//! genuinely prevents double-spend — but it is the WRONG mechanism for
//! participation. To *vote* or to have *weight*, no one should have to surrender
//! custody. As ember put it: "why should you need to move your DREGG into a special
//! wrap bridge wallet that isn't even your own custody, just to be able to vote with
//! it? there is no reason for this except bad system design."
//!
//! So this module does the full-client thing instead. dregg is already a Solana
//! light client (`solana_consensus`: stake-weighted ≥2/3 Ed25519 supermajority on a
//! bank hash + accounts-Merkle inclusion). That verifier reads ANY finalized account
//! — so we point it at the holder's OWN SPL token account (never a vault), decode the
//! balance, and PROVE "wallet W holds `amount` of mint M at finalized slot S". The
//! holder keeps custody; the tokens never move; dregg grants governance weight /
//! eligibility by proof.
//!
//! This is the "proof-of-holding → eligibility/weight" primitive named as the missing
//! spine in `docs/FINDING-chain-participation-census.md` §5.
//!
//! # Trust
//!
//! A [`ProvenHolding`] carries its [`LockProofTrust`]: only
//! [`LockProofTrust::ConsensusVerified`] (a real supermajority over a finalized bank
//! hash) is trustless. A [`LockProofTrust::StructureOnly`] holding (a plain-RPC read)
//! is NOT proof — the weight-binding layer must refuse to grant weight from it, the
//! same fail-closed rule the mint gate uses.

use crate::solana_trustless::LockProofTrust;

/// The SPL Token `Account` on-chain layout offsets (spl-token `state::Account`,
/// 165 bytes): `mint(32) ‖ owner(32) ‖ amount_le(8) ‖ …`. We read only the three
/// fields proof-of-holdings needs; the account's inclusion under a consensus-verified
/// bank hash is what makes those three bytes trustworthy.
pub const SPL_ACCOUNT_LEN: usize = 165;
/// `mint` pubkey occupies bytes `[0, 32)`.
pub const SPL_MINT_OFFSET: usize = 0;
/// `owner` pubkey (the wallet that controls the account) occupies bytes `[32, 64)`.
pub const SPL_OWNER_OFFSET: usize = 32;
/// `amount` (u64 little-endian) occupies bytes `[64, 72)`.
pub const SPL_AMOUNT_OFFSET: usize = 64;

/// Decode the three proof-of-holdings fields from a finalized SPL token account's
/// `data`: `(mint, owner, amount)`. Returns `None` unless the data is at least a full
/// SPL `Account` (165 bytes) — a shorter blob is not a token account and is refused
/// (fail closed). The account's authenticity comes from the caller having verified its
/// inclusion under a consensus-verified bank hash; this function only reads the layout.
pub fn decode_spl_token_account(data: &[u8]) -> Option<([u8; 32], [u8; 32], u64)> {
    if data.len() < SPL_ACCOUNT_LEN {
        return None;
    }
    let mut mint = [0u8; 32];
    mint.copy_from_slice(&data[SPL_MINT_OFFSET..SPL_MINT_OFFSET + 32]);
    let mut owner = [0u8; 32];
    owner.copy_from_slice(&data[SPL_OWNER_OFFSET..SPL_OWNER_OFFSET + 32]);
    let mut amt = [0u8; 8];
    amt.copy_from_slice(&data[SPL_AMOUNT_OFFSET..SPL_AMOUNT_OFFSET + 8]);
    Some((mint, owner, u64::from_le_bytes(amt)))
}

/// A proven, NON-CUSTODIAL holding: at finalized `slot`, the SPL token account
/// `token_account` (controlled by `owner`) held `amount` of `mint`. The holder never
/// moved anything — this is a snapshot proven over their own account.
///
/// Produced by the consensus-verified observe path (the verifier body is
/// `prove_holding_consensus`, built alongside this type). Consumed by the
/// weight-binding layer, which grants governance weight / eligibility ONLY when
/// `trust` is [`LockProofTrust::ConsensusVerified`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProvenHolding {
    /// The holder's SPL token account pubkey (their own custody, not a vault).
    pub token_account: [u8; 32],
    /// The wallet that controls the account (SPL `Account.owner`).
    pub owner: [u8; 32],
    /// The SPL mint proven held (`$DREGG` on Solana).
    pub mint: [u8; 32],
    /// The balance proven at `slot`, in atomic units.
    pub amount: u64,
    /// The finalized Solana slot the holding was proven at (the snapshot point).
    pub slot: u64,
    /// How trusted the observation is. Weight is granted ONLY for
    /// [`LockProofTrust::ConsensusVerified`]; [`LockProofTrust::StructureOnly`] is a
    /// plain-RPC read and MUST NOT grant weight (fail closed).
    pub trust: LockProofTrust,
}

impl ProvenHolding {
    /// True iff this holding is backed by a real stake-weighted supermajority over a
    /// finalized bank hash — the only state from which governance weight may be
    /// granted. A `StructureOnly` (RPC-echo) holding returns `false`.
    pub fn is_consensus_proven(&self) -> bool {
        matches!(self.trust, LockProofTrust::ConsensusVerified)
    }
}
