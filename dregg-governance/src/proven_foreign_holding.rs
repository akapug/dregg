//! # The chain-agnostic proven-holding fact — ONE weight binding for ANY chain
//!
//! [`holding_weight`](crate::holding_weight) grew up Solana-first: it consumed the
//! bridge's [`ProvenHolding`] directly. But the governance spine named in
//! `docs/FINDING-chain-participation-census.md` §5.1 is *chain-agnostic*: "prove an
//! account I control held ≥ W $DREGG at snapshot S **on chain C**". This module is the
//! minimal unification point — the smallest fact every light-client lane already
//! produces:
//!
//! - Solana ([`dregg_bridge::solana_holdings::ProvenHolding`]): `{token_account, owner,
//!   mint, amount, slot, trust}` — converted here via `From` (the bridge IS a dep).
//! - EVM (`eth-lightclient`'s `ProvenErc20Holding`): `{holder, token, balance,
//!   state_root, block_number}` — its edge constructs [`ProvenForeignHolding`] directly
//!   (that crate is standalone; the per-crate conversion lives there, as a follow-up).
//! - Cosmos (`cosmos-lightclient`'s `ProvenCosmosFact`): `{chain_id, height, store_key,
//!   key, value}` — likewise constructed at its edge (a bank-balance fact decodes to
//!   holder/asset/amount there).
//!
//! Deliberately NOT here: proof material (Merkle branches, sync-committee signatures,
//! vote sets). By the time a [`ProvenForeignHolding`] exists, the per-chain light client
//! has already rendered its verdict — this type carries only the VERDICT
//! ([`consensus_proven`](ProvenForeignHolding::consensus_proven)) and the proven fields.
//! The weight layer stays fail-closed on that verdict: a `consensus_proven: false` fact
//! (a plain-RPC echo, the `StructureOnly` rung) grants ZERO, exactly the Nomad-law rule
//! the Solana path already enforces.

use dregg_bridge::solana_holdings::ProvenHolding;

/// Which chain a holding was proven on. Scopes the per-poll nullifier
/// ([`ProvenForeignHolding::nullifier_key`]) so the same holder key on two different
/// chains is two DISTINCT facts — a holder who genuinely holds on both chains counts
/// both, and a proof from chain A can never occupy chain B's slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChainId {
    /// Solana (the bridge's stake-weighted ≥2/3 supermajority light client).
    Solana,
    /// An EVM chain (the eth-lightclient sync-committee → `state_root` → MPT path).
    Evm,
    /// A Cosmos-SDK chain (the cosmos-lightclient Tendermint → IAVL/ICS-23 path).
    Cosmos,
}

impl ChainId {
    /// The stable one-byte tag folded into the nullifier key. Never reuse a value.
    pub fn tag(self) -> u8 {
        match self {
            ChainId::Solana => 0,
            ChainId::Evm => 1,
            ChainId::Cosmos => 2,
        }
    }
}

/// The chain-agnostic minimal proven-holding fact: on `chain`, at finalized snapshot
/// height `snapshot`, `holder` held `amount` atomic units of `asset` — and
/// `consensus_proven` records whether a REAL light-client consensus proof backs it.
///
/// Non-custodial by construction: this is a read proof over the holder's own account on
/// the foreign chain. Nothing moved, locked, escrowed, or wrapped.
///
/// Field conventions per chain:
///
/// | field      | Solana              | EVM                          | Cosmos                     |
/// |------------|---------------------|------------------------------|----------------------------|
/// | `holder`   | owner wallet pubkey | 20-byte address, left-padded | 32-byte account id/hash    |
/// | `asset`    | SPL mint pubkey     | 20-byte token addr, padded   | denom commitment (hash)    |
/// | `snapshot` | slot                | block number                 | height                     |
///
/// `holder` doubles as the key the owner→voter [`OwnerBinding`](crate::holding_weight::OwnerBinding)
/// signature is verified against, so for weight-granting it must be (or embed) an
/// Ed25519 public key the holder controls. (A native secp256k1 EVM-address binding is a
/// named follow-up; until then an EVM holder registers an Ed25519 binding key as their
/// 32-byte `holder` identity at the eth edge.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProvenForeignHolding {
    /// The chain the holding was proven on (scopes the nullifier).
    pub chain: ChainId,
    /// The holding account's controlling identity (see the per-chain table above).
    pub holder: [u8; 32],
    /// The asset proven held, as a 32-byte chain-scoped identifier.
    pub asset: [u8; 32],
    /// The proven balance in atomic units. `u128` because an ERC-20 `balanceOf` is a
    /// `U256` in the wild but real supplies fit far below; an EVM edge must refuse
    /// (fail closed) rather than truncate a balance above `u128`.
    pub amount: u128,
    /// The finalized snapshot height (slot / block number / height) the balance was
    /// proven at. Polls pin one snapshot PER CHAIN; a holding proven at any other
    /// height is refused.
    pub snapshot: u64,
    /// `true` iff a real light-client consensus proof (supermajority / sync committee /
    /// Tendermint commit) backs this fact. A structure-only RPC echo is `false` and
    /// grants ZERO weight — fail closed, always.
    pub consensus_proven: bool,
}

impl ProvenForeignHolding {
    /// True iff this fact is backed by a real consensus proof — the only state from
    /// which governance weight may be granted (mirrors
    /// [`ProvenHolding::is_consensus_proven`]).
    pub fn is_consensus_proven(&self) -> bool {
        self.consensus_proven
    }

    /// The per-poll consume-once nullifier key for this holding:
    /// `blake3("dregg-foreign-holding-nullifier-v1", chain_tag ‖ holder ‖ asset)`.
    ///
    /// Scoped by **chain + holder + asset** so:
    /// - the same holder+asset re-presented into one poll is [`AlreadyCounted`](crate::holding_weight::GrantError::AlreadyCounted);
    /// - the same holder on two DIFFERENT chains is two distinct nullifiers (a holder
    ///   legitimately holding on both chains counts both);
    /// - two different assets held by one holder are likewise distinct.
    ///
    /// Deliberately NOT keyed on `amount` or `snapshot`: re-proving the same account at
    /// the same pinned snapshot with a different claimed amount must not mint a fresh
    /// nullifier.
    pub fn nullifier_key(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-foreign-holding-nullifier-v1");
        h.update(&[self.chain.tag()]);
        h.update(&self.holder);
        h.update(&self.asset);
        *h.finalize().as_bytes()
    }
}

/// The Solana edge lights up for free: the bridge's [`ProvenHolding`] IS already the
/// per-chain fact, so the conversion is a field mapping. `holder` is the SPL
/// `Account.owner` wallet (the Ed25519 key the [`OwnerBinding`](crate::holding_weight::OwnerBinding)
/// verifies against), `asset` the mint, `snapshot` the proven slot, and
/// `consensus_proven` is the bridge's own [`ProvenHolding::is_consensus_proven`] verdict
/// — a `StructureOnly` holding converts to a `consensus_proven: false` fact and still
/// grants ZERO through the generic path.
impl From<&ProvenHolding> for ProvenForeignHolding {
    fn from(h: &ProvenHolding) -> Self {
        ProvenForeignHolding {
            chain: ChainId::Solana,
            holder: h.owner,
            asset: h.mint,
            amount: h.amount as u128,
            snapshot: h.slot,
            consensus_proven: h.is_consensus_proven(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_bridge::solana_trustless::LockProofTrust;

    fn solana_holding(trust: LockProofTrust) -> ProvenHolding {
        ProvenHolding {
            token_account: [1u8; 32],
            owner: [2u8; 32],
            mint: [3u8; 32],
            amount: 4242,
            slot: 777,
            trust,
        }
    }

    #[test]
    fn from_solana_maps_every_field_and_the_trust_verdict() {
        let f = ProvenForeignHolding::from(&solana_holding(LockProofTrust::ConsensusVerified));
        assert_eq!(f.chain, ChainId::Solana);
        assert_eq!(
            f.holder, [2u8; 32],
            "holder is the OWNER wallet, not the token account"
        );
        assert_eq!(f.asset, [3u8; 32]);
        assert_eq!(f.amount, 4242u128);
        assert_eq!(f.snapshot, 777);
        assert!(f.consensus_proven);

        // REJECT polarity: a StructureOnly (RPC-echo) holding converts to an UNPROVEN
        // fact — the fail-closed verdict survives the conversion.
        let weak = ProvenForeignHolding::from(&solana_holding(LockProofTrust::StructureOnly));
        assert!(!weak.consensus_proven);
        assert!(!weak.is_consensus_proven());
    }

    #[test]
    fn nullifier_is_distinct_per_chain_holder_and_asset() {
        let base = ProvenForeignHolding {
            chain: ChainId::Solana,
            holder: [9u8; 32],
            asset: [7u8; 32],
            amount: 100,
            snapshot: 5,
            consensus_proven: true,
        };
        // Same fact → same nullifier (deterministic).
        assert_eq!(base.nullifier_key(), base.nullifier_key());
        // Different CHAIN, same holder+asset → distinct (a holder on two chains is two facts).
        let on_evm = ProvenForeignHolding {
            chain: ChainId::Evm,
            ..base
        };
        let on_cosmos = ProvenForeignHolding {
            chain: ChainId::Cosmos,
            ..base
        };
        assert_ne!(base.nullifier_key(), on_evm.nullifier_key());
        assert_ne!(base.nullifier_key(), on_cosmos.nullifier_key());
        assert_ne!(on_evm.nullifier_key(), on_cosmos.nullifier_key());
        // Different holder or asset → distinct.
        let other_holder = ProvenForeignHolding {
            holder: [10u8; 32],
            ..base
        };
        let other_asset = ProvenForeignHolding {
            asset: [8u8; 32],
            ..base
        };
        assert_ne!(base.nullifier_key(), other_holder.nullifier_key());
        assert_ne!(base.nullifier_key(), other_asset.nullifier_key());
        // NOT keyed on amount/snapshot: re-proving with a different claimed amount at
        // the pinned snapshot must not mint a fresh nullifier.
        let other_amount = ProvenForeignHolding {
            amount: 999,
            ..base
        };
        let other_snapshot = ProvenForeignHolding {
            snapshot: 6,
            ..base
        };
        assert_eq!(base.nullifier_key(), other_amount.nullifier_key());
        assert_eq!(base.nullifier_key(), other_snapshot.nullifier_key());
    }

    #[test]
    fn chain_tags_are_distinct() {
        // The nullifier's domain separation rests on distinct tags.
        assert_ne!(ChainId::Solana.tag(), ChainId::Evm.tag());
        assert_ne!(ChainId::Solana.tag(), ChainId::Cosmos.tag());
        assert_ne!(ChainId::Evm.tag(), ChainId::Cosmos.tag());
    }
}
