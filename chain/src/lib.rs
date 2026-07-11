//! # dregg-chain: the EVM settlement layer
//!
//! Solidity contracts + host-side bridge flows for settling dregg proofs and
//! value on EVM chains (Base, Ethereum, or any chain with the EIP-196/197
//! pairing precompiles):
//!
//! - `contracts/DreggVault.sol` — shielded vault: ERC-20/ETH deposits create
//!   note commitments the federation mirrors into dregg's private note tree;
//!   withdrawals require a wrapped proof of note ownership + spend validity,
//!   double-spends blocked by on-chain nullifiers.
//! - `contracts/DreggCredentialGate.sol` — on-chain anonymous-credential
//!   verification (ring membership + predicate), gating mints/votes with
//!   per-action nullifiers.
//! - `contracts/IDreggSettlement.sol` — whole-history proof settlement
//!   (`settle(a,b,c, genesisRoot, finalRoot, numTurns, chainDigest)`), the
//!   seam `bridge/src/ethereum.rs` encodes calldata for.
//! - This crate's Rust: the Base event listener (`listener`), the bridge
//!   runner (`bridge`), and withdrawal/credential proof-flow drivers.
//!
//! ## The wrap prover (pending)
//!
//! On-chain verification needs the dregg recursive batch-STARK wrapped into a
//! ~256-byte Groth16/BN254 proof. The wrap prover is the **native gnark
//! FRI-verifier circuit** — `chain/gnark/`, design and milestones in
//! `docs/deos/ETH-NATIVE-WRAP.md`, Lean refinement obligation `GnarkRefines`
//! (`metatheory/Dregg2/Circuit/FriVerifier.lean`). Until it is wired, proof
//! generation is fail-closed ([`ChainError::WrapProverMissing`]) unless the
//! `mock` feature explicitly opts into simulated proofs for integration tests.
//!
//! The predecessor SP1 RISC-V-zkVM wrap was deleted (2026-07): it verified the
//! pre-Plonky3 legacy proof format and paid a 1–2 order-of-magnitude
//! interpreter tax (`docs/deos/ETH-NATIVE-WRAP.md` §1).

pub mod bridge;
pub mod credential;
pub mod error;
pub mod listener;
pub mod prove;
pub mod verify;
pub mod withdraw;

#[cfg(feature = "mock")]
pub mod mock;

pub use error::ChainError;
pub use listener::{Address, NoteCreationRequest};
pub use prove::{EvmProof, wrap_for_evm};
pub use verify::verify_on_chain;
pub use withdraw::{WithdrawalProof, WithdrawalRequest, generate_withdrawal_proof};

/// Re-export canonical types used by callers when constructing proofs for settlement.
///
/// The typical flow is: attest a root via federation consensus (`AttestedRoot`),
/// generate a STARK proof of Merkle inclusion/exclusion (circuit crate), then wrap
/// that proof for EVM verification via this crate.
pub use dregg_types::AttestedRoot;

/// Placeholder verifying-key identifier used ONLY by mock-mode simulated proofs.
/// A real deployment's vkey comes from the gnark wrap circuit's setup
/// (`EthSettlementProof::verifying_key_hash` on the bridge seam).
pub const MOCK_PROGRAM_VKEY: &str = "PLACEHOLDER_VKEY_MOCK_ONLY";

/// Placeholder verifier-contract address used ONLY by mock-mode simulated proofs.
/// A real deployment sets the deployed verifier contract's address (the
/// gnark-generated `DreggSettlementVerifier` / vault / credential-gate verifier).
pub const MOCK_VERIFIER_ADDRESS: &str = "0x0000000000000000000000000000000000000000";
