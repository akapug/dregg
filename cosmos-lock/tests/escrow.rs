//! End-to-end test of the TIMEOUT/REFUND ESCROW — the Cosmos twin of the EVM
//! `DreggVault` / `solana-lock` two-branch escrow — routed through a full
//! `cw-multi-test` App (blocks, block-time, bank balances, cross-contract queries).
//!
//! It runs the escrow against a companion SETTLEMENT contract (a minimal
//! IsProvenRoot oracle, the same test boundary as the EVM `MockSettlement`), and
//! exercises the REAL exactly-once state machine, both polarities:
//!   * FILLED → RELEASE: a proven clearing root (settlement) + an M-of-N ed25519
//!     oracle attestation release to the ring-matched recipient; the escrow is then
//!     terminal and a refund is refused.
//!   * UNFILLED → REFUND: after the deadline the depositor reclaims; the escrow is
//!     then terminal and a release is refused.
//!
//! The exactly-once teeth: filled→release, unfilled→refund, early-refund reverts,
//! under-threshold ("proofless") release reverts, unproven-clearing-root release
//! reverts, wrong-recipient release reverts (the attestation binds the recipient),
//! double release / double refund revert, non-depositor refund reverts.

use cosmwasm_schema::cw_serde;
use cosmwasm_std::{
    coins, to_json_binary, Binary, Deps, DepsMut, Env, MessageInfo, Response, StdResult, Uint128,
};
use cw_multi_test::{App, ContractWrapper, Executor};
use cw_storage_plus::Map;
use ed25519_dalek::{Signer, SigningKey};

use cosmos_lock::error::ContractError;
use cosmos_lock::msg::{EscrowResponse, ExecuteMsg, InstantiateMsg, OracleSignature, QueryMsg};
use cosmos_lock::state::EscrowStatus;
use cosmos_lock::{execute, instantiate, query, release_digest};

const DENOM: &str = "uatom";
const LOCKED: u128 = 250_000;

// ─── The companion settlement contract (minimal IsProvenRoot oracle) ────────────

const MOCK_PROVEN: Map<&str, bool> = Map::new("mock_proven");

#[cw_serde]
struct MockInstantiate {}
#[cw_serde]
enum MockExec {
    SetProven { root: String },
}
#[cw_serde]
enum MockQuery {
    IsProvenRoot { root: String },
}
#[cw_serde]
struct MockBoolResponse {
    value: bool,
}

fn mock_instantiate(
    _d: DepsMut,
    _e: Env,
    _i: MessageInfo,
    _m: MockInstantiate,
) -> StdResult<Response> {
    Ok(Response::new())
}
fn mock_execute(deps: DepsMut, _e: Env, _i: MessageInfo, m: MockExec) -> StdResult<Response> {
    match m {
        MockExec::SetProven { root } => {
            MOCK_PROVEN.save(deps.storage, &root, &true)?;
            Ok(Response::new())
        }
    }
}
fn mock_query(deps: Deps, _e: Env, m: MockQuery) -> StdResult<Binary> {
    match m {
        MockQuery::IsProvenRoot { root } => {
            let value = if root.trim_start_matches('0').is_empty() {
                false
            } else {
                MOCK_PROVEN.may_load(deps.storage, &root)?.unwrap_or(false)
            };
            to_json_binary(&MockBoolResponse { value })
        }
    }
}

// ─── Harness ────────────────────────────────────────────────────────────────────

struct Env2 {
    app: App,
    escrow: cosmwasm_std::Addr,
    settlement: cosmwasm_std::Addr,
    depositor: cosmwasm_std::Addr,
    recipient: cosmwasm_std::Addr,
    oracles: Vec<SigningKey>, // 3 oracle signing keys (2-of-3)
}

/// The 3 deterministic oracle signing keys.
fn oracle_keys() -> Vec<SigningKey> {
    (1u8..=3)
        .map(|i| SigningKey::from_bytes(&[i; 32]))
        .collect()
}

fn setup(deadline_offset: i64) -> (Env2, String, u64) {
    let oracles = oracle_keys();
    let mut app = App::new(|router, api, storage| {
        let depositor = api.addr_make("depositor");
        router
            .bank
            .init_balance(storage, &depositor, coins(1_000_000, DENOM))
            .unwrap();
    });
    let depositor = app.api().addr_make("depositor");
    let recipient = app.api().addr_make("recipient");

    // Store + instantiate the companion settlement contract.
    let settlement_code = app.store_code(Box::new(ContractWrapper::new(
        mock_execute,
        mock_instantiate,
        mock_query,
    )));
    let settlement = app
        .instantiate_contract(
            settlement_code,
            app.api().addr_make("deployer"),
            &MockInstantiate {},
            &[],
            "mock-settlement",
            None,
        )
        .unwrap();

    // Store + instantiate the escrow with a 2-of-3 oracle set.
    let escrow_code = app.store_code(Box::new(ContractWrapper::new(execute, instantiate, query)));
    let oracle_pubkeys: Vec<Binary> = oracles
        .iter()
        .map(|k| Binary::new(k.verifying_key().to_bytes().to_vec()))
        .collect();
    let escrow = app
        .instantiate_contract(
            escrow_code,
            app.api().addr_make("deployer"),
            &InstantiateMsg {
                settlement: settlement.to_string(),
                oracle_threshold: 2,
                oracle_pubkeys,
            },
            &[],
            "dregg-escrow",
            None,
        )
        .unwrap();

    // Lock LOCKED uatom under a fresh escrow id with a deadline relative to now.
    let now = app.block_info().time.seconds();
    let deadline = (now as i64 + deadline_offset) as u64;
    let escrow_id = "e1".to_string();
    app.execute_contract(
        depositor.clone(),
        escrow.clone(),
        &ExecuteMsg::EscrowLock {
            escrow_id: escrow_id.clone(),
            deadline,
        },
        &coins(LOCKED, DENOM),
    )
    .expect("lock");

    (
        Env2 {
            app,
            escrow,
            settlement,
            depositor,
            recipient,
            oracles,
        },
        escrow_id,
        deadline,
    )
}

impl Env2 {
    /// Mark `root` proven on the settlement contract.
    fn set_proven(&mut self, root: &str) {
        let deployer = self.app.api().addr_make("deployer");
        self.app
            .execute_contract(
                deployer,
                self.settlement.clone(),
                &MockExec::SetProven {
                    root: root.to_string(),
                },
                &[],
            )
            .unwrap();
    }

    /// Build `n` oracle signatures (from the first `n` oracle keys) over the release
    /// digest for `(escrow_id, recipient, clearing_root)`.
    fn sigs(
        &self,
        oracle_indices: &[usize],
        escrow_id: &str,
        recipient: &str,
        clearing_root: &str,
    ) -> Vec<OracleSignature> {
        let digest = release_digest(
            escrow_id,
            DENOM,
            Uint128::new(LOCKED),
            recipient,
            clearing_root,
        );
        oracle_indices
            .iter()
            .map(|&i| {
                let sk = &self.oracles[i];
                OracleSignature {
                    pubkey: Binary::new(sk.verifying_key().to_bytes().to_vec()),
                    signature: Binary::new(sk.sign(&digest).to_bytes().to_vec()),
                }
            })
            .collect()
    }

    fn release(
        &mut self,
        escrow_id: &str,
        recipient: &cosmwasm_std::Addr,
        clearing_root: &str,
        oracle_indices: &[usize],
    ) -> Result<(), anyhow::Error> {
        let signatures = self.sigs(oracle_indices, escrow_id, recipient.as_str(), clearing_root);
        self.app
            .execute_contract(
                self.app.api().addr_make("anyone"),
                self.escrow.clone(),
                &ExecuteMsg::EscrowRelease {
                    escrow_id: escrow_id.to_string(),
                    recipient: recipient.to_string(),
                    clearing_root: clearing_root.to_string(),
                    signatures,
                },
                &[],
            )
            .map(|_| ())
    }

    fn refund(
        &mut self,
        escrow_id: &str,
        sender: &cosmwasm_std::Addr,
    ) -> Result<(), anyhow::Error> {
        self.app
            .execute_contract(
                sender.clone(),
                self.escrow.clone(),
                &ExecuteMsg::EscrowRefund {
                    escrow_id: escrow_id.to_string(),
                },
                &[],
            )
            .map(|_| ())
    }

    fn advance(&mut self, secs: u64) {
        self.app
            .update_block(|b| b.time = b.time.plus_seconds(secs));
    }

    fn balance(&self, who: &cosmwasm_std::Addr) -> u128 {
        self.app
            .wrap()
            .query_balance(who, DENOM)
            .unwrap()
            .amount
            .u128()
    }

    fn status(&self, escrow_id: &str) -> EscrowStatus {
        let r: EscrowResponse = self
            .app
            .wrap()
            .query_wasm_smart(
                &self.escrow,
                &QueryMsg::Escrow {
                    escrow_id: escrow_id.to_string(),
                },
            )
            .unwrap();
        r.status
    }
}

fn err(e: anyhow::Error) -> ContractError {
    e.downcast::<ContractError>()
        .expect("a cosmos-lock ContractError")
}

const ROOT: &str = "aabbccddeeff00112233445566778899aabbccddeeff00112233445566778899";

// ─── POLARITY 1: FILLED → RELEASE ───────────────────────────────────────────────

#[test]
fn filled_escrow_releases_to_recipient() {
    let (mut env, id, _dl) = setup(1000);
    env.set_proven(ROOT);
    let recipient = env.recipient.clone();

    env.release(&id, &recipient, ROOT, &[0, 1])
        .expect("release");
    assert_eq!(env.balance(&recipient), LOCKED);
    assert_eq!(env.status(&id), EscrowStatus::Released);
}

/// TOOTH: a Released escrow is terminal — a refund (block advanced past the deadline,
/// so the deadline guard is not what stops it) is refused. Released-and-also-refunded
/// is unreachable.
#[test]
fn released_escrow_cannot_be_refunded() {
    let (mut env, id, _dl) = setup(1000);
    env.set_proven(ROOT);
    let (recipient, depositor) = (env.recipient.clone(), env.depositor.clone());
    env.release(&id, &recipient, ROOT, &[0, 1])
        .expect("release");

    env.advance(2000); // now past the deadline
    let e = err(env.refund(&id, &depositor).unwrap_err());
    assert_eq!(e, ContractError::EscrowNotLocked);
    assert_eq!(env.balance(&recipient), LOCKED);
    assert_eq!(env.status(&id), EscrowStatus::Released);
}

// ─── POLARITY 2: UNFILLED → REFUND ──────────────────────────────────────────────

#[test]
fn unfilled_escrow_refunds_to_depositor_after_deadline() {
    let (mut env, id, _dl) = setup(1000);
    let depositor = env.depositor.clone();
    // Depositor started with 1_000_000, minus LOCKED escrowed.
    assert_eq!(env.balance(&depositor), 1_000_000 - LOCKED);

    env.advance(2000); // past the deadline
    env.refund(&id, &depositor).expect("refund");
    assert_eq!(env.balance(&depositor), 1_000_000); // full lock returned
    assert_eq!(env.status(&id), EscrowStatus::Refunded);
}

/// TOOTH: a Refunded escrow is terminal — a release with a fully valid attestation
/// over a proven root is refused. Refunded-and-also-released is unreachable.
#[test]
fn refunded_escrow_cannot_be_released() {
    let (mut env, id, _dl) = setup(1000);
    let (recipient, depositor) = (env.recipient.clone(), env.depositor.clone());
    env.advance(2000);
    env.refund(&id, &depositor).expect("refund");

    env.set_proven(ROOT);
    let e = err(env.release(&id, &recipient, ROOT, &[0, 1]).unwrap_err());
    assert_eq!(e, ContractError::EscrowNotLocked);
    assert_eq!(env.balance(&recipient), 0);
    assert_eq!(env.status(&id), EscrowStatus::Refunded);
}

// ─── EXACTLY-ONCE TEETH ─────────────────────────────────────────────────────────

/// A refund BEFORE the deadline reverts (the timeout IS the condition).
#[test]
fn refund_before_deadline_reverts() {
    let (mut env, id, dl) = setup(1000);
    let depositor = env.depositor.clone();
    let e = err(env.refund(&id, &depositor).unwrap_err());
    let now = env.app.block_info().time.seconds();
    assert_eq!(e, ContractError::RefundBeforeDeadline { now, deadline: dl });
    assert_eq!(env.status(&id), EscrowStatus::Locked);
}

/// A release WITHOUT a threshold of valid oracle signatures reverts (1 of 2) — the
/// "proofless release" tooth.
#[test]
fn release_with_insufficient_sigs_reverts() {
    let (mut env, id, _dl) = setup(1000);
    env.set_proven(ROOT);
    let recipient = env.recipient.clone();
    let e = err(env.release(&id, &recipient, ROOT, &[0]).unwrap_err()); // 1 sig
    assert_eq!(
        e,
        ContractError::ThresholdNotMet {
            got: 1,
            threshold: 2
        }
    );
    assert_eq!(env.balance(&recipient), 0);
    assert_eq!(env.status(&id), EscrowStatus::Locked);
}

/// A release whose clearing root is NOT proven by the settlement contract reverts,
/// even with a full valid attestation.
#[test]
fn release_with_unproven_root_reverts() {
    let (mut env, id, _dl) = setup(1000);
    // NOTE: set_proven NOT called — ROOT is unproven.
    let recipient = env.recipient.clone();
    let e = err(env.release(&id, &recipient, ROOT, &[0, 1]).unwrap_err());
    assert_eq!(e, ContractError::ClearingRootNotProven(ROOT.to_string()));
    assert_eq!(env.status(&id), EscrowStatus::Locked);
}

/// The attestation binds the RECIPIENT: signatures for the ring-matched recipient do
/// not authorize a release to a different address (the digest differs → 0 valid
/// sigs → under threshold).
#[test]
fn release_to_wrong_recipient_reverts() {
    let (mut env, id, _dl) = setup(1000);
    env.set_proven(ROOT);
    let attacker = env.app.api().addr_make("attacker");
    // Sign for the real recipient, but submit a release to the attacker.
    let recipient = env.recipient.clone();
    let signatures = env.sigs(&[0, 1], &id, recipient.as_str(), ROOT);
    let res = env.app.execute_contract(
        env.app.api().addr_make("anyone"),
        env.escrow.clone(),
        &ExecuteMsg::EscrowRelease {
            escrow_id: id.clone(),
            recipient: attacker.to_string(), // redirected
            clearing_root: ROOT.to_string(),
            signatures,
        },
        &[],
    );
    let e = err(res.unwrap_err());
    assert_eq!(
        e,
        ContractError::ThresholdNotMet {
            got: 0,
            threshold: 2
        }
    );
    assert_eq!(env.balance(&attacker), 0);
    assert_eq!(env.status(&id), EscrowStatus::Locked);
}

/// A double release reverts (the second sees a non-Locked status). The second tx uses
/// a different oracle pair so it is a distinct, independently-valid attestation.
#[test]
fn double_release_reverts() {
    let (mut env, id, _dl) = setup(1000);
    env.set_proven(ROOT);
    let recipient = env.recipient.clone();
    env.release(&id, &recipient, ROOT, &[0, 1])
        .expect("first release");
    let e = err(env.release(&id, &recipient, ROOT, &[0, 2]).unwrap_err());
    assert_eq!(e, ContractError::EscrowNotLocked);
    assert_eq!(env.balance(&recipient), LOCKED); // paid exactly once
}

/// A double refund reverts (the second sees a non-Locked status).
#[test]
fn double_refund_reverts() {
    let (mut env, id, _dl) = setup(1000);
    let depositor = env.depositor.clone();
    env.advance(2000);
    env.refund(&id, &depositor).expect("first refund");
    let e = err(env.refund(&id, &depositor).unwrap_err());
    assert_eq!(e, ContractError::EscrowNotLocked);
    assert_eq!(env.balance(&depositor), 1_000_000); // refunded exactly once
}

/// A refund by a non-depositor reverts.
#[test]
fn refund_by_non_depositor_reverts() {
    let (mut env, id, _dl) = setup(1000);
    env.advance(2000);
    let stranger = env.app.api().addr_make("stranger");
    let e = err(env.refund(&id, &stranger).unwrap_err());
    assert_eq!(e, ContractError::NotDepositor);
    assert_eq!(env.status(&id), EscrowStatus::Locked);
}

/// A fresh id cannot be locked twice.
#[test]
fn duplicate_escrow_id_reverts() {
    let (mut env, id, _dl) = setup(1000);
    let depositor = env.depositor.clone();
    let now = env.app.block_info().time.seconds();
    let res = env.app.execute_contract(
        depositor,
        env.escrow.clone(),
        &ExecuteMsg::EscrowLock {
            escrow_id: id.clone(),
            deadline: now + 1000,
        },
        &coins(1, DENOM),
    );
    assert_eq!(err(res.unwrap_err()), ContractError::DuplicateEscrowId(id));
}
