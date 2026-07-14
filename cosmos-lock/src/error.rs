use cosmwasm_std::StdError;
use thiserror::Error;

/// Escrow contract errors — the Cosmos twin of the `DreggVault` escrow reverts and
/// the `solana-lock` `LockError` escrow variants. Every rejection path is typed and
/// fails closed.
#[derive(Error, Debug, PartialEq)]
pub enum ContractError {
    #[error(transparent)]
    Std(#[from] StdError),

    /// The oracle set is malformed: empty, zero threshold, M > N, a non-32-byte key,
    /// a zero key, or a duplicate. NOMAD-LAW: fail closed.
    #[error("invalid oracle set (empty, zero/oversize threshold, bad or duplicate key)")]
    InvalidOracleSet,

    /// Exactly one native coin, non-zero, must be escrowed by a lock.
    #[error("a single non-zero native coin must be escrowed")]
    InvalidFunds,

    /// A lock carried a non-positive deadline (a zero deadline would make refund
    /// immediately available, defeating the timed lock).
    #[error("zero deadline")]
    ZeroDeadline,

    /// An escrow already exists for this id (an id reaches one terminal state, so it
    /// is never reused).
    #[error("escrow id already exists: {0}")]
    DuplicateEscrowId(String),

    /// No escrow exists for this id.
    #[error("no escrow with id: {0}")]
    UnknownEscrow(String),

    /// The escrow is not `Locked` (already Released/Refunded) — a terminal escrow
    /// cannot transition again. This is the exactly-once guard.
    #[error("escrow is not Locked (already released or refunded)")]
    EscrowNotLocked,

    /// The clearing root the release names is not proven by the settlement contract
    /// (the rung-8 accept-path answered false).
    #[error("clearing root not proven by the settlement contract: {0}")]
    ClearingRootNotProven(String),

    /// The release did not carry a threshold of valid signatures from DISTINCT
    /// configured oracle keys over the canonical release digest.
    #[error("release attestation below threshold: {got} distinct of {threshold}")]
    ThresholdNotMet { got: u32, threshold: u32 },

    /// A refund was attempted at or before the escrow's deadline (the timeout is the
    /// refund condition).
    #[error("refund before deadline (now {now} <= deadline {deadline})")]
    RefundBeforeDeadline { now: u64, deadline: u64 },

    /// A refund was attempted by an address other than the recorded depositor.
    #[error("only the depositor may refund")]
    NotDepositor,
}
