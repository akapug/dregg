//! # dregg-interchain-gov — the COMPILED join for cross-chain non-custodial governance
//!
//! Three proof lanes already exist, and each one is real on its own:
//!
//! - **Solana**: `dregg-bridge`'s [`ProvenHolding`] (stake-weighted ≥ 2/3 supermajority
//!   over a finalized bank hash, anchored stake provenance) — `dregg-governance`
//!   consumes it directly (`From<&ProvenHolding> for ProvenForeignHolding`).
//! - **EVM**: `eth-lightclient`'s [`ProvenErc20Holding`] (sync-committee finality →
//!   `state_root` → EIP-1186 MPT account+storage proofs) →
//!   [`to_foreign_fields`](ProvenErc20Holding::to_foreign_fields).
//! - **Cosmos**: `cosmos-lightclient`'s [`ProvenCosmosFact`] (Tendermint ≥ 2/3 commit →
//!   `app_hash` → ICS-23 membership) → [`foreign_holding_fields`].
//!
//! But `eth-lightclient` and `cosmos-lightclient` are STANDALONE workspaces (excluded
//! from the breadstuffs root for dependency-isolation reasons), so they cannot depend
//! on `dregg-governance` — and before this crate, NOTHING compiled both sides together:
//! the edges emit `ForeignHoldingFields { chain_tag: u8, … }` and governance's
//! [`ProvenForeignHolding::from_foreign_fields`] consumes them, with the tag agreement
//! (`Solana = 0`, `EVM = 1`, `Cosmos = 2`) held only by mirrored constants and mirrored
//! tests — a doc contract. `from_foreign_fields` had zero non-test callers.
//!
//! This crate IS the relayer seam, compiled: it path-depends on the light clients AND
//! on governance, and the functions below are the one place an edge's fields become a
//! governance fact. The compile-time pins ([`_EVM_TAG_PINNED`]/[`_COSMOS_TAG_PINNED`])
//! plus the cross-crate tests make a tag drift a BUILD/TEST FAILURE here, not a silent
//! mis-attribution into the wrong chain's nullifier space.
//!
//! Non-custodial throughout: every lane is a READ PROOF over the holder's own account
//! on the foreign chain. Nothing is moved, locked, escrowed, or wrapped; the holder's
//! wallet key then signs an owner→voter binding (Ed25519 on Solana, secp256k1
//! EIP-191 on EVM, secp256k1 over the dregg Cosmos sign-doc), and the weight flows
//! through the fail-closed grant path into one [`CollectiveChoice`] tally.
//!
//! [`CollectiveChoice`]: dregg_governance::CollectiveChoice
//! [`foreign_holding_fields`]: cosmos_lightclient::foreign_holding_fields

use cosmos_lightclient::{BankBalanceError, ProvenCosmosFact};
use dregg_bridge::solana_holdings::ProvenHolding;
use dregg_governance::proven_foreign_holding::{ChainId, ForeignFieldsError, ProvenForeignHolding};
use eth_lightclient::evm::ProvenErc20Holding;

/// COMPILE-TIME pin of the cross-crate EVM family tag: `eth-lightclient` hard-codes
/// `CHAIN_TAG_EVM` (it cannot depend on governance), and governance's
/// `ChainId::Evm(_).tag()` must equal it. `tag()` is not a `const fn`, so the const
/// side pins the edge byte here and `tests` in this file pin the governance side —
/// together with the compiled [`evm_fields_to_holding`] path (which REFUSES on any
/// mismatch at runtime), the agreement is build-enforced, not a doc contract.
const _EVM_TAG_PINNED: () = assert!(eth_lightclient::evm::CHAIN_TAG_EVM == 1);

/// COMPILE-TIME pin of the cross-crate Cosmos family tag (see [`_EVM_TAG_PINNED`]).
const _COSMOS_TAG_PINNED: () = assert!(cosmos_lightclient::COSMOS_CHAIN_TAG == 2);

/// Why the join refused to turn an edge's output into a governance fact. Every
/// variant is fail-closed: no [`ProvenForeignHolding`] is minted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JoinError {
    /// The caller paired EVM edge fields with a non-EVM [`ChainId`] (or vice versa a
    /// network whose family cannot have produced these fields). Refused here, before
    /// governance even sees the tag — the relayer named the wrong network family.
    WrongNetworkFamily {
        /// The family tag the light-client edge stamped on its fields.
        edge_tag: u8,
        /// The family tag of the [`ChainId`] the caller supplied.
        network_family: u8,
    },
    /// Governance's own defensive tooth fired
    /// ([`ProvenForeignHolding::from_foreign_fields`] tag mismatch).
    ChainTag(ForeignFieldsError),
    /// The EVM edge refused to emit fields (a `U256` balance above `u128::MAX` is
    /// never truncated).
    EvmFields(eth_lightclient::evm::ForeignFieldsError),
    /// The Cosmos edge refused to decode the proven fact into bank-balance fields
    /// (wrong chain id pin, non-bank store, malformed key/value, over-`u128` amount).
    CosmosFields(BankBalanceError),
}

impl core::fmt::Display for JoinError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            JoinError::WrongNetworkFamily {
                edge_tag,
                network_family,
            } => write!(
                f,
                "edge fields carry family tag {edge_tag} but the supplied network is family \
                 {network_family} — refused (wrong-network pairing)"
            ),
            JoinError::ChainTag(e) => write!(f, "governance refused the chain tag: {e:?}"),
            JoinError::EvmFields(e) => write!(f, "EVM edge refused: {e}"),
            JoinError::CosmosFields(e) => write!(f, "Cosmos edge refused: {e}"),
        }
    }
}

impl std::error::Error for JoinError {}

/// Join EVM edge fields to a governance fact. `network` names WHICH EVM chain the
/// light client verified (`ChainId::Evm(1)` = Ethereum mainnet, `Evm(8453)` = Base…) —
/// the edge's one-byte family tag alone cannot say, which is exactly why the relayer
/// supplies it and why the pairing is checked twice (here, and inside
/// [`ProvenForeignHolding::from_foreign_fields`]).
pub fn evm_fields_to_holding(
    fields: &eth_lightclient::evm::ForeignHoldingFields,
    network: ChainId,
) -> Result<ProvenForeignHolding, JoinError> {
    if !matches!(network, ChainId::Evm(_)) {
        return Err(JoinError::WrongNetworkFamily {
            edge_tag: fields.chain_tag,
            network_family: network.tag(),
        });
    }
    ProvenForeignHolding::from_foreign_fields(
        network,
        fields.chain_tag,
        fields.holder,
        fields.asset,
        fields.amount,
        fields.snapshot,
        fields.consensus_proven,
    )
    .map_err(JoinError::ChainTag)
}

/// The whole EVM lane in one call: a light-client-proven ERC-20 holding →
/// edge fields (fail-closed on `U256 → u128` overflow) → governance fact on the
/// EIP-155 network `eip155_chain_id` (1 = Ethereum, 8453 = Base, …).
///
/// The `consensus_proven` verdict is carried, never asserted: only a holding minted
/// by `verify_erc20_holding_finalized` (the full sync-committee finality path)
/// arrives `true`; a structure-only holding arrives `false` and grants ZERO weight
/// downstream.
pub fn evm_holding_to_governance(
    holding: &ProvenErc20Holding,
    eip155_chain_id: u64,
) -> Result<ProvenForeignHolding, JoinError> {
    let fields = holding.to_foreign_fields().map_err(JoinError::EvmFields)?;
    evm_fields_to_holding(&fields, ChainId::Evm(eip155_chain_id))
}

/// Join Cosmos edge fields to a governance fact on the network named by its
/// canonical chain-id string (`"cosmoshub-4"`, `"osmosis-1"`, …). The governance
/// [`ChainId::cosmos`] commitment is derived from the SAME string the caller pins,
/// so a fact decoded under one chain-id can never occupy another's nullifier space.
pub fn cosmos_fields_to_holding(
    fields: &cosmos_lightclient::ForeignHoldingFields,
    chain_id: &str,
) -> Result<ProvenForeignHolding, JoinError> {
    let network = ChainId::cosmos(chain_id);
    if !matches!(network, ChainId::Cosmos(_)) {
        unreachable!("ChainId::cosmos always builds the Cosmos variant");
    }
    ProvenForeignHolding::from_foreign_fields(
        network,
        fields.chain_tag,
        fields.holder,
        fields.asset,
        fields.amount,
        fields.snapshot,
        fields.consensus_proven,
    )
    .map_err(JoinError::ChainTag)
}

/// The whole Cosmos lane in one call: a header-verified [`ProvenCosmosFact`] →
/// bank-balance fields (the edge REFUSES a fact from any chain other than
/// `expected_chain_id`, a non-bank store, a malformed key/value, an over-`u128`
/// amount) → governance fact on `ChainId::cosmos(expected_chain_id)`.
///
/// `consensus_proven` is `true` by construction here — a [`ProvenCosmosFact`] can
/// only be minted by `prove_cosmos_fact` (≥ 2/3-signed verified header + ICS-23
/// membership); there is no structure-only rung in the Cosmos edge.
pub fn cosmos_fact_to_governance(
    fact: &ProvenCosmosFact,
    expected_chain_id: &str,
) -> Result<ProvenForeignHolding, JoinError> {
    let fields = cosmos_lightclient::foreign_holding_fields(fact, expected_chain_id)
        .map_err(JoinError::CosmosFields)?;
    cosmos_fields_to_holding(&fields, expected_chain_id)
}

/// The Solana lane, for symmetry (governance already Froms the bridge type; this
/// crate names all three lanes in one place). Carries the bridge's consensus
/// verdict: a `StructureOnly` RPC echo converts to `consensus_proven: false` and
/// grants ZERO weight downstream.
pub fn solana_holding_to_governance(holding: &ProvenHolding) -> ProvenForeignHolding {
    ProvenForeignHolding::from(holding)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The cross-crate tag agreement, asserted with BOTH sides linked in one test —
    /// the assertion the mirrored per-crate tests could only state as a doc contract.
    #[test]
    fn chain_family_tags_agree_across_the_three_crates() {
        assert_eq!(ChainId::Solana.tag(), 0);
        assert_eq!(
            ChainId::Evm(1).tag(),
            eth_lightclient::evm::CHAIN_TAG_EVM,
            "governance ChainId::Evm family tag must equal eth-lightclient CHAIN_TAG_EVM"
        );
        assert_eq!(
            ChainId::Evm(8453).tag(),
            eth_lightclient::evm::CHAIN_TAG_EVM,
            "every EVM network shares the family tag"
        );
        assert_eq!(
            ChainId::cosmos("cosmoshub-4").tag(),
            cosmos_lightclient::COSMOS_CHAIN_TAG,
            "governance ChainId::Cosmos family tag must equal cosmos-lightclient COSMOS_CHAIN_TAG"
        );
    }

    /// The 20 → 32 byte holder/asset padding conventions agree: the EVM edge's
    /// `pad_address_32` produces exactly the layout governance's EVM binding
    /// extractor (`evm_address_of_holder`) accepts and inverts.
    #[test]
    fn evm_padding_conventions_agree_across_the_join() {
        let addr = [0xABu8; 20];
        let padded = eth_lightclient::evm::pad_address_32(&addr);
        assert_eq!(
            dregg_governance::holding_weight::evm_address_of_holder(&padded),
            Some(addr),
            "governance must invert the edge's padding exactly"
        );
    }

    /// REJECT: Cosmos edge fields (family 2) paired with an EVM network — refused at
    /// the join's own gate, before governance's tooth.
    #[test]
    fn cosmos_fields_paired_with_an_evm_network_are_refused() {
        let fields = cosmos_lightclient::ForeignHoldingFields {
            chain_tag: cosmos_lightclient::COSMOS_CHAIN_TAG,
            holder: [1u8; 32],
            asset: [2u8; 32],
            amount: 5,
            snapshot: 9,
            consensus_proven: true,
        };
        // Force them down the EVM join: the family gate refuses.
        let evm_shaped = eth_lightclient::evm::ForeignHoldingFields {
            chain_tag: fields.chain_tag, // 2 — a Cosmos edge byte
            holder: fields.holder,
            asset: fields.asset,
            amount: fields.amount,
            snapshot: fields.snapshot,
            consensus_proven: fields.consensus_proven,
        };
        // The join's own family gate passes (network IS Evm) but governance's
        // tag tooth fires: edge said 2, network family is 1.
        assert_eq!(
            evm_fields_to_holding(&evm_shaped, ChainId::Evm(8453)),
            Err(JoinError::ChainTag(ForeignFieldsError::ChainTagMismatch {
                edge_tag: 2,
                chain_family: 1
            })),
        );
    }

    /// REJECT: EVM edge fields paired with a non-EVM network refuse at the join's
    /// family gate (the relayer named the wrong network family outright).
    #[test]
    fn evm_fields_paired_with_a_non_evm_network_are_refused() {
        let fields = eth_lightclient::evm::ForeignHoldingFields {
            chain_tag: eth_lightclient::evm::CHAIN_TAG_EVM,
            holder: [1u8; 32],
            asset: [2u8; 32],
            amount: 5,
            snapshot: 9,
            consensus_proven: true,
        };
        assert_eq!(
            evm_fields_to_holding(&fields, ChainId::cosmos("cosmoshub-4")),
            Err(JoinError::WrongNetworkFamily {
                edge_tag: 1,
                network_family: 2
            }),
        );
        assert_eq!(
            evm_fields_to_holding(&fields, ChainId::Solana),
            Err(JoinError::WrongNetworkFamily {
                edge_tag: 1,
                network_family: 0
            }),
        );
    }

    /// ACCEPT: matching pairings build, carrying every field (including the
    /// fail-closed consensus verdict) through unchanged.
    #[test]
    fn matching_pairings_join_and_carry_all_fields() {
        let evm = eth_lightclient::evm::ForeignHoldingFields {
            chain_tag: eth_lightclient::evm::CHAIN_TAG_EVM,
            holder: [3u8; 32],
            asset: [4u8; 32],
            amount: 1_000,
            snapshot: 21_000_000,
            consensus_proven: true,
        };
        let h = evm_fields_to_holding(&evm, ChainId::Evm(8453)).expect("EVM joins");
        assert_eq!(h.chain, ChainId::Evm(8453));
        assert_eq!(h.holder, [3u8; 32]);
        assert_eq!(h.asset, [4u8; 32]);
        assert_eq!(h.amount, 1_000);
        assert_eq!(h.snapshot, 21_000_000);
        assert!(h.consensus_proven);

        let cosmos = cosmos_lightclient::ForeignHoldingFields {
            chain_tag: cosmos_lightclient::COSMOS_CHAIN_TAG,
            holder: [5u8; 32],
            asset: [6u8; 32],
            amount: 500,
            snapshot: 31_992_690,
            consensus_proven: false, // the verdict is CARRIED, never asserted
        };
        let h = cosmos_fields_to_holding(&cosmos, "cosmoshub-4").expect("Cosmos joins");
        assert_eq!(h.chain, ChainId::cosmos("cosmoshub-4"));
        assert!(!h.consensus_proven, "the edge's verdict survives the join");
    }
}
