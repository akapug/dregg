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
///
/// MULTI-NETWORK: there is more than one EVM chain (Ethereum mainnet, Base, …) and more
/// than one Cosmos-SDK chain (cosmoshub-4, osmosis-1, …), and they are DIFFERENT
/// consensus domains — a holding proven on Base and one on Ethereum are two distinct
/// facts (both legitimately count), and a proof from one must never occupy the other's
/// nullifier slot. So the EVM and Cosmos variants carry a per-network discriminator:
///
/// - [`Evm`](ChainId::Evm) carries the EIP-155 chain id (Ethereum mainnet = 1,
///   Base = 8453, …) — the same integer every EVM wallet/replay-protection layer keys on.
/// - [`Cosmos`](ChainId::Cosmos) carries a 32-byte commitment to the network's canonical
///   chain-id string (build it with [`ChainId::cosmos`], e.g. `cosmos("cosmoshub-4")`) —
///   Cosmos chain ids are variable-length strings, so a fixed-width hash keeps the
///   nullifier wire fixed-width per tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChainId {
    /// Solana (the bridge's stake-weighted ≥2/3 supermajority light client).
    Solana,
    /// An EVM chain (the eth-lightclient sync-committee → `state_root` → MPT path),
    /// discriminated by its EIP-155 chain id — `Evm(1)` = Ethereum mainnet,
    /// `Evm(8453)` = Base. Two different chain ids are two distinct consensus domains.
    /// `u64`, not `u32`: some real EIP-155 ids exceed 2³² (e.g. Palm = 11297108109), so
    /// a `u32` would make them unrepresentable.
    Evm(u64),
    /// A Cosmos-SDK chain (the cosmos-lightclient Tendermint → IAVL/ICS-23 path),
    /// discriminated by a 32-byte commitment to its canonical chain-id string —
    /// construct via [`ChainId::cosmos`].
    Cosmos([u8; 32]),
}

impl ChainId {
    /// Ethereum mainnet (EIP-155 chain id 1).
    pub const ETHEREUM: ChainId = ChainId::Evm(1);
    /// Base (EIP-155 chain id 8453).
    pub const BASE: ChainId = ChainId::Evm(8453);

    /// A Cosmos-SDK network from its canonical chain-id string (e.g. `"cosmoshub-4"`,
    /// `"osmosis-1"`): the discriminator is
    /// `blake3(derive_key = "dregg-cosmos-chain-id-v1", chain_id_utf8)`, so two
    /// different chain-id strings are two distinct [`ChainId`]s.
    pub fn cosmos(chain_id: &str) -> ChainId {
        let mut h = blake3::Hasher::new_derive_key("dregg-cosmos-chain-id-v1");
        h.update(chain_id.as_bytes());
        ChainId::Cosmos(*h.finalize().as_bytes())
    }

    /// The stable one-byte LEAD tag of the nullifier wire — the chain FAMILY. Never
    /// reuse a value. The per-network discriminator follows it in [`wire_bytes`](Self::wire_bytes);
    /// the tag alone does NOT identify a network for Evm/Cosmos.
    pub fn tag(self) -> u8 {
        match self {
            ChainId::Solana => 0,
            ChainId::Evm(_) => 1,
            ChainId::Cosmos(_) => 2,
        }
    }

    /// The full chain-identity wire folded into the nullifier key:
    ///
    /// | variant      | bytes                                   | length |
    /// |--------------|-----------------------------------------|--------|
    /// | `Solana`     | `[0]`                                   | 1      |
    /// | `Evm(id)`    | `[1] ‖ id as u64 big-endian`            | 9      |
    /// | `Cosmos(h)`  | `[2] ‖ h`                               | 33     |
    ///
    /// The lead tag byte uniquely determines the payload length, so the concatenation
    /// `wire_bytes ‖ holder ‖ asset` inside [`ProvenForeignHolding::nullifier_key`] is
    /// prefix-unambiguous: no two distinct (chain, holder, asset) triples serialize to
    /// the same byte string.
    pub fn wire_bytes(self) -> Vec<u8> {
        match self {
            ChainId::Solana => vec![0],
            ChainId::Evm(id) => {
                let mut w = Vec::with_capacity(9);
                w.push(1);
                w.extend_from_slice(&id.to_be_bytes());
                w
            }
            ChainId::Cosmos(h) => {
                let mut w = Vec::with_capacity(33);
                w.push(2);
                w.extend_from_slice(&h);
                w
            }
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
    /// `blake3(derive_key = "dregg-foreign-holding-nullifier-v2",
    ///         chain.wire_bytes() ‖ holder ‖ asset)`.
    ///
    /// Scoped by **network + holder + asset** — where "network" is the FULL
    /// [`ChainId::wire_bytes`] (lead family tag + per-network discriminator), not just
    /// the family tag — so:
    /// - the same holder+asset re-presented into one poll is [`AlreadyCounted`](crate::holding_weight::GrantError::AlreadyCounted);
    /// - the same holder on two DIFFERENT networks is two distinct nullifiers, even
    ///   within one family: a holding on Base (`Evm(8453)`) and one on Ethereum
    ///   (`Evm(1)`) both count — a holder legitimately holding on both networks counts
    ///   both, and a proof from one network can never occupy another's slot;
    /// - two different assets held by one holder are likewise distinct.
    ///
    /// Wire (v2 — v1 hashed only the one-byte family tag, which conflated all EVM
    /// networks into one nullifier slot; v2 folds the whole network identity):
    /// `wire_bytes(1|5|33 bytes, length determined by the lead tag) ‖ holder(32) ‖
    /// asset(32)` — prefix-unambiguous, see [`ChainId::wire_bytes`].
    ///
    /// Deliberately NOT keyed on `amount` or `snapshot`: re-proving the same account at
    /// the same pinned snapshot with a different claimed amount must not mint a fresh
    /// nullifier.
    pub fn nullifier_key(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-foreign-holding-nullifier-v2");
        h.update(&self.chain.wire_bytes());
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
            chain: ChainId::ETHEREUM,
            ..base
        };
        let on_cosmos = ProvenForeignHolding {
            chain: ChainId::cosmos("cosmoshub-4"),
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
        // The nullifier's family-level domain separation rests on distinct lead tags.
        assert_ne!(ChainId::Solana.tag(), ChainId::ETHEREUM.tag());
        assert_ne!(ChainId::Solana.tag(), ChainId::cosmos("cosmoshub-4").tag());
        assert_ne!(
            ChainId::ETHEREUM.tag(),
            ChainId::cosmos("cosmoshub-4").tag()
        );
        // Within a family the LEAD tag is shared (stable wire) — the network
        // discriminator that follows it is what separates Base from Ethereum.
        assert_eq!(ChainId::ETHEREUM.tag(), ChainId::BASE.tag());
    }

    #[test]
    fn chain_wire_bytes_are_the_documented_encoding() {
        // The documented wire, byte for byte: tag ‖ per-network discriminator.
        assert_eq!(ChainId::Solana.wire_bytes(), vec![0u8]);
        // Evm id is u64 big-endian (9 bytes: tag ‖ 8) so ids > 2^32 (e.g. Palm) fit.
        assert_eq!(
            ChainId::ETHEREUM.wire_bytes(),
            vec![1u8, 0, 0, 0, 0, 0, 0, 0, 1]
        );
        assert_eq!(
            ChainId::BASE.wire_bytes(),
            vec![1u8, 0, 0, 0, 0, 0, 0, 33, 5] // 8453 = 0x2105
        );
        let hub = ChainId::cosmos("cosmoshub-4");
        let w = hub.wire_bytes();
        assert_eq!(w.len(), 33);
        assert_eq!(w[0], 2);
        let ChainId::Cosmos(h) = hub else {
            panic!("cosmos() builds a Cosmos variant")
        };
        assert_eq!(&w[1..], &h);
    }

    #[test]
    fn evm_id_above_2_32_is_representable() {
        // The reason Evm is u64, not u32: Palm's EIP-155 chain id (11297108109) exceeds
        // 2^32. A u32 would make it unrepresentable; u64 encodes it distinctly.
        let palm = ChainId::Evm(11_297_108_109);
        let w = palm.wire_bytes();
        assert_eq!(w.len(), 9, "u64 big-endian ‖ tag");
        assert_eq!(w[0], 1);
        assert_eq!(&w[1..], &11_297_108_109u64.to_be_bytes());
        // Distinct from Ethereum (a low id) — no collision at the wide end.
        assert_ne!(palm.wire_bytes(), ChainId::ETHEREUM.wire_bytes());
    }

    #[test]
    fn two_evm_networks_are_distinct_nullifiers_same_network_is_stable() {
        // MULTI-NETWORK: the same holder+asset proven on Base vs Ethereum is TWO
        // distinct facts — both count; neither occupies the other's slot.
        let base_chain = ProvenForeignHolding {
            chain: ChainId::BASE,
            holder: [9u8; 32],
            asset: [7u8; 32],
            amount: 100,
            snapshot: 5,
            consensus_proven: true,
        };
        let eth_chain = ProvenForeignHolding {
            chain: ChainId::ETHEREUM,
            ..base_chain
        };
        assert_ne!(
            base_chain.nullifier_key(),
            eth_chain.nullifier_key(),
            "Base and Ethereum are different consensus domains — distinct nullifiers"
        );
        // REJECT-side invariant: the SAME network+holder+asset is the SAME nullifier
        // (that is what makes the second presentation AlreadyCounted downstream).
        let eth_again = ProvenForeignHolding {
            amount: 999_999,
            snapshot: 6,
            ..eth_chain
        };
        assert_eq!(eth_chain.nullifier_key(), eth_again.nullifier_key());
    }

    #[test]
    fn two_cosmos_networks_are_distinct_nullifiers() {
        let on = |chain: ChainId| ProvenForeignHolding {
            chain,
            holder: [9u8; 32],
            asset: [7u8; 32],
            amount: 100,
            snapshot: 5,
            consensus_proven: true,
        };
        let hub = on(ChainId::cosmos("cosmoshub-4"));
        let osmo = on(ChainId::cosmos("osmosis-1"));
        assert_ne!(ChainId::cosmos("cosmoshub-4"), ChainId::cosmos("osmosis-1"));
        assert_ne!(
            hub.nullifier_key(),
            osmo.nullifier_key(),
            "two Cosmos networks are distinct nullifier domains"
        );
        // Deterministic: the same chain-id string always names the same network.
        assert_eq!(ChainId::cosmos("osmosis-1"), ChainId::cosmos("osmosis-1"));
        assert_eq!(
            osmo.nullifier_key(),
            on(ChainId::cosmos("osmosis-1")).nullifier_key()
        );
    }
}
