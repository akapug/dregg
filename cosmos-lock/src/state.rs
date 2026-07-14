use cosmwasm_schema::cw_serde;
use cosmwasm_std::{Addr, Binary, Uint128};
use cw_storage_plus::{Item, Map};

/// Immutable-after-instantiation config: the settlement contract the release gate
/// queries (`IsProvenRoot`), plus the M-of-N ed25519 oracle key-set that authorizes
/// a release (the recipient binding). The Cosmos analog of `DreggVault`'s
/// `settlement` immutable + the Solana lock's on-chain oracle set.
#[cw_serde]
pub struct Config {
    /// The `cosmos-settlement` contract (the rung-8 clearing accept-path). A release
    /// is gated on this contract answering `IsProvenRoot { clearing_root } == true`.
    pub settlement: Addr,
    /// Threshold M: the minimum number of DISTINCT configured oracle keys whose
    /// ed25519 signature over the canonical release digest must be present. 1 <= M <= N.
    pub oracle_threshold: u32,
    /// The oracle verifying key-set (N ed25519 public keys, 32 bytes each). Non-empty,
    /// no zero key, no duplicate (enforced at instantiate).
    pub oracle_pubkeys: Vec<Binary>,
}

/// The escrow state machine. `Locked` is the only non-terminal state; a release or
/// refund moves it to exactly one terminal value. An escrow id absent from the map is
/// `None` — never a live state.
#[cw_serde]
pub enum EscrowStatus {
    Locked,
    Released,
    Refunded,
}

/// A per-escrow record — the Cosmos twin of `DreggVault.Escrow` /
/// `EscrowRecord`.
#[cw_serde]
pub struct Escrow {
    /// Who locked; the only address allowed to refund, and the refund recipient.
    pub depositor: Addr,
    /// The native denom escrowed.
    pub denom: String,
    /// The exact escrowed amount — the only amount a release/refund moves.
    pub amount: Uint128,
    /// Unix seconds; refund becomes available once `env.block.time > deadline`.
    pub deadline: u64,
    pub status: EscrowStatus,
}

pub const CONFIG: Item<Config> = Item::new("config");

/// Escrows keyed by a caller-supplied unique id (the batch mirror commitment, hex).
pub const ESCROWS: Map<&str, Escrow> = Map::new("escrows");
