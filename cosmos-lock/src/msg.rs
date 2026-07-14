use cosmwasm_schema::{cw_serde, QueryResponses};
use cosmwasm_std::{Binary, Uint128};

use crate::state::EscrowStatus;

#[cw_serde]
pub struct InstantiateMsg {
    /// The `cosmos-settlement` contract address the release gate queries.
    pub settlement: String,
    /// M: the release attestation threshold (1 <= M <= number of oracle keys).
    pub oracle_threshold: u32,
    /// N ed25519 oracle public keys (32 bytes each).
    pub oracle_pubkeys: Vec<Binary>,
}

/// One oracle's ed25519 signature over the canonical release digest.
#[cw_serde]
pub struct OracleSignature {
    /// The 32-byte ed25519 public key (must be one of the configured oracle keys).
    pub pubkey: Binary,
    /// The 64-byte ed25519 signature over `release_digest`.
    pub signature: Binary,
}

#[cw_serde]
pub enum ExecuteMsg {
    /// LOCK the native coin(s) attached to this message into a timed escrow under
    /// `escrow_id`, reclaimable after `deadline` (unix seconds) if no DrEX fill
    /// clears it. Exactly one non-zero coin must be sent.
    EscrowLock { escrow_id: String, deadline: u64 },
    /// RELEASE a locked escrow to the ring-matched `recipient`, gated on BOTH
    ///   (i) the settlement contract proving `clearing_root`, AND
    ///   (ii) a threshold of DISTINCT oracle ed25519 signatures over the canonical
    ///        release digest binding (escrow_id, denom, amount, recipient, clearing_root).
    /// Terminal: the escrow moves to `Released`.
    EscrowRelease {
        escrow_id: String,
        recipient: String,
        clearing_root: String,
        signatures: Vec<OracleSignature>,
    },
    /// REFUND a locked escrow to its depositor once `block.time > deadline`. No
    /// attestation — the timeout IS the condition. Terminal: `Refunded`.
    EscrowRefund { escrow_id: String },
}

#[cw_serde]
#[derive(QueryResponses)]
pub enum QueryMsg {
    /// The escrow record for `escrow_id` (errors if unknown).
    #[returns(EscrowResponse)]
    Escrow { escrow_id: String },
    /// The immutable config.
    #[returns(ConfigResponse)]
    Config {},
}

#[cw_serde]
pub struct EscrowResponse {
    pub depositor: String,
    pub denom: String,
    pub amount: Uint128,
    pub deadline: u64,
    pub status: EscrowStatus,
}

#[cw_serde]
pub struct ConfigResponse {
    pub settlement: String,
    pub oracle_threshold: u32,
    pub oracle_pubkeys: Vec<Binary>,
}
