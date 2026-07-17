//! Error types for the chain crate.

use thiserror::Error;

/// Errors that can occur during EVM proof wrapping and verification.
#[derive(Debug, Error)]
pub enum ChainError {
    /// The STARK proof bytes could not be deserialized.
    #[error("invalid STARK proof: {0}")]
    InvalidProof(String),

    /// Wrap proving failed.
    #[error("wrap proving failed: {0}")]
    ProvingFailed(String),

    /// No wrap prover is enabled: the native gnark wrap circuit
    /// (docs/deos/ETH-NATIVE-WRAP.md) is not yet wired. Build with
    /// `--features mock` for simulated proofs in tests.
    #[error(
        "no wrap prover enabled (native gnark wrap pending; use --features mock for simulated proofs)"
    )]
    WrapProverMissing,

    /// No verifier is enabled: the default build has neither the real
    /// on-chain verifier (`--features on-chain`) nor the opt-in simulated
    /// one (`--features mock`). Fail-closed, mirroring [`Self::WrapProverMissing`]:
    /// a build NEVER silently substitutes a simulated verification for a real one.
    #[error(
        "no on-chain verifier enabled (use --features on-chain for the real contract call, or --features mock for simulated verification in tests)"
    )]
    VerifierMissing,

    /// On-chain verification call failed.
    #[error("on-chain verification failed: {0}")]
    OnChainError(String),

    /// RPC connection error.
    #[error("RPC error: {0}")]
    RpcError(String),

    /// The proof was rejected by the on-chain verifier.
    #[error("proof rejected by on-chain verifier")]
    ProofRejected,

    /// Generic error.
    #[error(transparent)]
    Other(#[from] anyhow::Error),
}
