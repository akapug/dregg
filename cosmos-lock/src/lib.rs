//! # dregg custody escrow — the Cosmos side (CosmWasm)
//!
//! The TIMEOUT/REFUND ESCROW that makes locking a foreign asset into a DrEX trade
//! SAFE on Cosmos — the twin of the EVM `chain/contracts/DreggVault.sol` escrow
//! surface and the `solana-lock` escrow. A locked native deposit reaches EXACTLY
//! ONE terminal state:
//!
//!   * RELEASED to the ring-matched recipient — gated on BOTH the `cosmos-settlement`
//!     contract proving the DrEX clearing root (`IsProvenRoot`, the rung-8
//!     accept-path — the Cosmos analog of `DreggVault.settlement.isProvenRoot`) AND
//!     an M-of-N ed25519 oracle attestation binding the specific escrow to the
//!     recipient (the analog of the SP1 fill proof / the Solana oracle attestation),
//!     XOR
//!   * REFUNDED to the depositor — gated only on `block.time > deadline` (the timeout
//!     IS the condition; no proof).
//!
//! The two branches are mutually exclusive on `EscrowStatus`: release and refund each
//! require `Locked` and flip it to a terminal value before emitting the `BankMsg`, so
//! a released escrow can never be refunded and vice-versa, and — because refund is
//! always reachable after the deadline with no external dependency — a lock is never
//! stuck.
//!
//! ## Honest scope
//!
//! - The state machine + both release gates are real: a proofless (under-threshold)
//!   release and a release naming an unproven clearing root both fail closed.
//! - Custody is native bank funds held by the contract; release/refund pay out with
//!   `BankMsg::Send`.
//! - This is test/local-demonstrated (cw-multi-test), not deployed to a live chain.
//! - The residual it does NOT close — full cross-vault ATOMIC release across a
//!   permanently-unavailable chain — is the named RESEARCH rung
//!   (`docs/deos/DREX-ROUTING.md §4(a)`); the escrow guarantees per-leg
//!   reclaimability, not heterogeneous-vault atomicity.

pub mod error;
pub mod msg;
pub mod settlement;
pub mod state;

use cosmwasm_std::{
    entry_point, to_json_binary, Api, BankMsg, Binary, Coin, Deps, DepsMut, Env, MessageInfo,
    Response, StdResult, Uint128,
};
use sha3::{Digest, Keccak256};

use error::ContractError;
use msg::{ConfigResponse, EscrowResponse, ExecuteMsg, InstantiateMsg, OracleSignature, QueryMsg};
use settlement::{BoolResponse, SettlementQueryMsg};
use state::{Config, Escrow, EscrowStatus, CONFIG, ESCROWS};

/// Domain separator for the release-attestation digest (distinct from any other
/// dregg signing domain so a signature can never be replayed across surfaces).
pub const RELEASE_DOMAIN: &[u8] = b"dregg-cosmos-escrow-release-v1";

const ED25519_PUBKEY_LEN: usize = 32;

/// The canonical 32-byte digest the oracle set signs to authorize a release. Binds
/// every field with an explicit length prefix so no field boundary is ambiguous:
/// `keccak256(DOMAIN ‖ len(id)‖id ‖ len(denom)‖denom ‖ len(recip)‖recip ‖
/// len(root)‖root ‖ amount_be16)`.
pub fn release_digest(
    escrow_id: &str,
    denom: &str,
    amount: Uint128,
    recipient: &str,
    clearing_root: &str,
) -> [u8; 32] {
    let mut h = Keccak256::new();
    h.update(RELEASE_DOMAIN);
    for field in [
        escrow_id.as_bytes(),
        denom.as_bytes(),
        recipient.as_bytes(),
        clearing_root.as_bytes(),
    ] {
        h.update((field.len() as u64).to_be_bytes());
        h.update(field);
    }
    h.update(amount.to_be_bytes());
    h.finalize().into()
}

#[entry_point]
pub fn instantiate(
    deps: DepsMut,
    _env: Env,
    _info: MessageInfo,
    msg: InstantiateMsg,
) -> Result<Response, ContractError> {
    let settlement = deps.api.addr_validate(&msg.settlement)?;
    validate_oracle_set(msg.oracle_threshold, &msg.oracle_pubkeys)?;

    CONFIG.save(
        deps.storage,
        &Config {
            settlement,
            oracle_threshold: msg.oracle_threshold,
            oracle_pubkeys: msg.oracle_pubkeys,
        },
    )?;

    Ok(Response::new().add_attribute("action", "instantiate"))
}

/// Fail-closed oracle-set validation (NOMAD-LAW): `1 <= M <= N`, every key is a
/// 32-byte ed25519 key, no zero key, no duplicate.
fn validate_oracle_set(threshold: u32, keys: &[Binary]) -> Result<(), ContractError> {
    let n = keys.len() as u32;
    if n == 0 || threshold == 0 || threshold > n {
        return Err(ContractError::InvalidOracleSet);
    }
    for (i, k) in keys.iter().enumerate() {
        if k.len() != ED25519_PUBKEY_LEN || k.as_slice() == [0u8; ED25519_PUBKEY_LEN] {
            return Err(ContractError::InvalidOracleSet);
        }
        if keys[..i].iter().any(|p| p == k) {
            return Err(ContractError::InvalidOracleSet);
        }
    }
    Ok(())
}

#[entry_point]
pub fn execute(
    deps: DepsMut,
    env: Env,
    info: MessageInfo,
    msg: ExecuteMsg,
) -> Result<Response, ContractError> {
    match msg {
        ExecuteMsg::EscrowLock {
            escrow_id,
            deadline,
        } => escrow_lock(deps, info, escrow_id, deadline),
        ExecuteMsg::EscrowRelease {
            escrow_id,
            recipient,
            clearing_root,
            signatures,
        } => escrow_release(deps, escrow_id, recipient, clearing_root, signatures),
        ExecuteMsg::EscrowRefund { escrow_id } => escrow_refund(deps, env, info, escrow_id),
    }
}

/// LOCK — escrow the single native coin attached to this message under `escrow_id`.
fn escrow_lock(
    deps: DepsMut,
    info: MessageInfo,
    escrow_id: String,
    deadline: u64,
) -> Result<Response, ContractError> {
    if deadline == 0 {
        return Err(ContractError::ZeroDeadline);
    }
    // Exactly one non-zero coin (the foreign asset being locked).
    if info.funds.len() != 1 {
        return Err(ContractError::InvalidFunds);
    }
    let coin = &info.funds[0];
    if coin.amount.is_zero() {
        return Err(ContractError::InvalidFunds);
    }
    // Fresh id only — the exactly-once id guard (a terminal escrow keeps its record).
    if ESCROWS.has(deps.storage, &escrow_id) {
        return Err(ContractError::DuplicateEscrowId(escrow_id));
    }

    ESCROWS.save(
        deps.storage,
        &escrow_id,
        &Escrow {
            depositor: info.sender.clone(),
            denom: coin.denom.clone(),
            amount: coin.amount,
            deadline,
            status: EscrowStatus::Locked,
        },
    )?;

    Ok(Response::new()
        .add_attribute("action", "escrow_lock")
        .add_attribute("escrow_id", escrow_id)
        .add_attribute("denom", coin.denom.clone())
        .add_attribute("amount", coin.amount.to_string())
        .add_attribute("deadline", deadline.to_string()))
}

/// RELEASE — pay a locked escrow to the ring-matched recipient. Fails closed on a
/// non-Locked escrow, an under-threshold attestation, or an unproven clearing root.
fn escrow_release(
    deps: DepsMut,
    escrow_id: String,
    recipient: String,
    clearing_root: String,
    signatures: Vec<OracleSignature>,
) -> Result<Response, ContractError> {
    let mut e = ESCROWS
        .may_load(deps.storage, &escrow_id)?
        .ok_or_else(|| ContractError::UnknownEscrow(escrow_id.clone()))?;
    // EXACTLY-ONCE: only a Locked escrow can transition.
    if e.status != EscrowStatus::Locked {
        return Err(ContractError::EscrowNotLocked);
    }
    let recipient_addr = deps.api.addr_validate(&recipient)?;
    let config = CONFIG.load(deps.storage)?;

    // (i) The M-of-N oracle attestation binding this escrow to this recipient.
    let digest = release_digest(&escrow_id, &e.denom, e.amount, &recipient, &clearing_root);
    let distinct = count_oracle_sigs(deps.api, &digest, &signatures, &config)?;
    if distinct < config.oracle_threshold {
        return Err(ContractError::ThresholdNotMet {
            got: distinct,
            threshold: config.oracle_threshold,
        });
    }

    // (ii) The clearing root must be genuinely proven by the settlement contract
    //      (the rung-8 accept-path). A cross-contract smart query.
    let proven: BoolResponse = deps.querier.query_wasm_smart(
        config.settlement.clone(),
        &SettlementQueryMsg::IsProvenRoot {
            root: clearing_root.clone(),
        },
    )?;
    if !proven.value {
        return Err(ContractError::ClearingRootNotProven(clearing_root));
    }

    // Effects before the payout message: consume the lock (terminal Released).
    e.status = EscrowStatus::Released;
    let payout = Coin {
        denom: e.denom.clone(),
        amount: e.amount,
    };
    ESCROWS.save(deps.storage, &escrow_id, &e)?;

    Ok(Response::new()
        .add_message(BankMsg::Send {
            to_address: recipient_addr.to_string(),
            amount: vec![payout],
        })
        .add_attribute("action", "escrow_release")
        .add_attribute("escrow_id", escrow_id)
        .add_attribute("recipient", recipient)
        .add_attribute("clearing_root", clearing_root))
}

/// REFUND — reclaim a locked escrow to its depositor after the deadline.
fn escrow_refund(
    deps: DepsMut,
    env: Env,
    info: MessageInfo,
    escrow_id: String,
) -> Result<Response, ContractError> {
    let mut e = ESCROWS
        .may_load(deps.storage, &escrow_id)?
        .ok_or_else(|| ContractError::UnknownEscrow(escrow_id.clone()))?;
    if e.status != EscrowStatus::Locked {
        return Err(ContractError::EscrowNotLocked);
    }
    // The timeout IS the condition: the deadline must have STRICTLY passed.
    let now = env.block.time.seconds();
    if now <= e.deadline {
        return Err(ContractError::RefundBeforeDeadline {
            now,
            deadline: e.deadline,
        });
    }
    // Only the recorded depositor may refund (and funds only ever go to them).
    if info.sender != e.depositor {
        return Err(ContractError::NotDepositor);
    }

    e.status = EscrowStatus::Refunded;
    let payout = Coin {
        denom: e.denom.clone(),
        amount: e.amount,
    };
    let depositor = e.depositor.clone();
    ESCROWS.save(deps.storage, &escrow_id, &e)?;

    Ok(Response::new()
        .add_message(BankMsg::Send {
            to_address: depositor.to_string(),
            amount: vec![payout],
        })
        .add_attribute("action", "escrow_refund")
        .add_attribute("escrow_id", escrow_id))
}

/// Count DISTINCT configured oracle keys that ed25519-signed `digest`. Only signatures
/// whose pubkey is an active configured key AND that verify count; a key that signs
/// twice counts once. Anything else is silently not counted (fail-closed).
fn count_oracle_sigs(
    api: &dyn Api,
    digest: &[u8; 32],
    sigs: &[OracleSignature],
    config: &Config,
) -> Result<u32, ContractError> {
    let mut seen: Vec<Binary> = Vec::new();
    for s in sigs {
        if !config.oracle_pubkeys.iter().any(|k| k == &s.pubkey) {
            continue; // not a configured oracle key
        }
        if seen.iter().any(|k| k == &s.pubkey) {
            continue; // distinct signers only
        }
        // A signature over EXACTLY our digest, by this key, must verify.
        match api.ed25519_verify(digest, s.signature.as_slice(), s.pubkey.as_slice()) {
            Ok(true) => seen.push(s.pubkey.clone()),
            _ => continue,
        }
    }
    Ok(seen.len() as u32)
}

#[entry_point]
pub fn query(deps: Deps, _env: Env, msg: QueryMsg) -> StdResult<Binary> {
    match msg {
        QueryMsg::Escrow { escrow_id } => {
            let e = ESCROWS.load(deps.storage, &escrow_id)?;
            to_json_binary(&EscrowResponse {
                depositor: e.depositor.to_string(),
                denom: e.denom,
                amount: e.amount,
                deadline: e.deadline,
                status: e.status,
            })
        }
        QueryMsg::Config {} => {
            let c = CONFIG.load(deps.storage)?;
            to_json_binary(&ConfigResponse {
                settlement: c.settlement.to_string(),
                oracle_threshold: c.oracle_threshold,
                oracle_pubkeys: c.oracle_pubkeys,
            })
        }
    }
}
