//! The live-relayer round-trip soundness proof.
//!
//! This proves the OFF-CHAIN relayer drives the full inbound bridge against a
//! (mock) Solana RPC — the watching service the library was missing:
//!
//! 1. a finalized lock into the bridge vault → the relayer observes it
//!    ([`SolanaRelayer::observe_vault_lock`]), verifying finality + the
//!    escrow-to-bridge-vault binding (BR-2-B) + structure/binding;
//! 2. the verified lock mints CONSERVING mirror credit through the SAME committed,
//!    multi-relayer-safe `bridge_mint_against_lock` the soundness work landed
//!    (Σδ=0, consume-once nullifier);
//! 3. a SECOND relayer racing the same lock is REFUSED by the committed nullifier
//!    (no double-mint), even though it observed the lock independently;
//! 4. an un-escrowed lock (attacker-owned account) is refused at observe;
//! 5. an un-finalized lock (visible only at confirmed) is refused at observe.
//!
//! The mock RPC models the real finalized/confirmed commitment split, so the
//! finality gate is genuinely exercised; the same `observe → BridgeMintRequest`
//! path runs against the live JSON-RPC client in production (the only swap is the
//! [`SolanaRpc`] impl). The in-circuit witness of the Solana consensus (so a dregg
//! LIGHT client, not a re-executing relayer, sees the backing) is the circuit
//! swarm's G1 VK-epoch (`dregg_circuit::bridge_action_air`) — out of scope here.

use dregg_bridge::solana_mirror::MirrorConfig;
use dregg_bridge::solana_relayer::{MockSolanaRpc, RelayerError, SolanaRelayer};
use dregg_bridge::solana_trustless::LockProofTrust;
use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, Ledger, Permissions};
use dregg_turn::{
    BridgeMintError, ComputronCosts, TurnExecutor, new_mirror_ledger_cell, read_supply,
};

const SPL_MINT: [u8; 32] = [0xABu8; 32];
const MIRROR_ASSET: [u8; 32] = [0x77u8; 32];
const VAULT: [u8; 32] = [0x22u8; 32];
const LOCK_PROGRAM: [u8; 32] = [0x07u8; 32];

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn pk(seed: u8) -> [u8; 32] {
    let mut p = [0u8; 32];
    p[0] = seed;
    p[31] = seed.wrapping_mul(37).wrapping_add(1);
    p
}

fn open_cell(seed: u8, token_id: [u8; 32], balance: i64) -> Cell {
    let mut cell = Cell::with_balance(pk(seed), token_id, balance);
    cell.permissions = open_permissions();
    cell
}

fn derived_well_id(token_id: &[u8; 32]) -> CellId {
    let well_pubkey = blake3::derive_key("dregg-issuer-well-key-v1", token_id);
    CellId::derive_raw(&well_pubkey, token_id)
}

/// `(ledger, recipient, issuer-holding-the-mint-cap, committed-ledger-cell)`.
fn scaffold(token: [u8; 32]) -> (Ledger, CellId, CellId, CellId) {
    let well_id = derived_well_id(&token);

    let recipient = open_cell(1, token, 0);
    let recipient_id = recipient.id();

    let mut issuer = open_cell(2, token, 0);
    issuer
        .capabilities
        .grant_faceted(well_id, AuthRequired::None, EFFECT_MINT)
        .expect("grant mint-cap to the bridge cell");
    let issuer_id = issuer.id();

    let ledger_cell = new_mirror_ledger_cell(pk(9), [0x44u8; 32]);
    let ledger_cell_id = ledger_cell.id();

    let mut ledger = Ledger::new();
    ledger.insert_cell(recipient).unwrap();
    ledger.insert_cell(issuer).unwrap();
    ledger.insert_cell(ledger_cell).unwrap();

    (ledger, recipient_id, issuer_id, ledger_cell_id)
}

fn config() -> MirrorConfig {
    MirrorConfig {
        spl_mint: SPL_MINT,
        asset: MIRROR_ASSET,
        oracle_keys: vec![],
        min_amount: 1,
        max_amount: 1_000_000,
        vault_account: VAULT,
        lock_program: LOCK_PROGRAM,
        pinned_anchor_epoch: None,
        pinned_anchor_root: None,
    }
}

#[test]
fn relayer_lock_to_finalized_to_conserving_mint() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    // A REAL finalized lock into the bridge vault, owned by the lock program.
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(
        VAULT,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount),
    );

    // ── (1) the relayer WATCHES + VERIFIES the finalized lock ───────────────
    let relayer = SolanaRelayer::new(config(), rpc);
    let observed = relayer
        .observe_vault_lock()
        .expect("the relayer observes the finalized vault lock");
    assert_eq!(observed.amount, amount);
    assert_eq!(observed.recipient, recipient);
    assert_eq!(observed.trust, LockProofTrust::StructureOnly);
    assert_eq!(observed.finalized_slot, 100);

    // ── (2) MINT through the committed, conserving, multi-relayer-safe path ─
    let req = observed.to_bridge_mint_request(issuer, ledger_cell);
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, &req)
        .expect("the verified lock mints conserving mirror credit");
    assert_eq!(receipt.amount, amount);
    assert_eq!(receipt.currently_locked, amount);
    assert_eq!(receipt.live_supply, amount);

    // Conservation: live_supply ≤ currently_locked; recipient credited once; the
    // issuer well carries the conserving −amount (Σδ=0).
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
    assert!(live <= locked);
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        amount as i64,
        "recipient credited exactly the locked amount"
    );

    // ── (3) a SECOND relayer racing the SAME lock is refused (no double-mint) ─
    let mut rpc2 = MockSolanaRpc::new(100, 105, 110);
    rpc2.insert_finalized(
        VAULT,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount),
    );
    let relayer2 = SolanaRelayer::new(config(), rpc2);
    let observed2 = relayer2
        .observe_vault_lock()
        .expect("a second relayer independently observes the same lock");
    assert_eq!(
        observed2.nullifier, observed.nullifier,
        "the same lock yields the same committed consume-once nullifier"
    );
    let req2 = observed2.to_bridge_mint_request(issuer, ledger_cell);
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req2)
            .unwrap_err(),
        BridgeMintError::DuplicateLock,
        "the committed nullifier refuses the second mint of the same lock"
    );
    // Supply unchanged after the refused double-mint.
    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
}

#[test]
fn relayer_refuses_unescrowed_lock_round_trip() {
    // A finalized account that exists on Solana but is owned by an ATTACKER
    // program (the self-asserted-blob attack, BR-2-B). It never reaches the mint.
    let recipient = CellId::from_bytes(pk(1));
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(
        VAULT,
        MockSolanaRpc::lock_account([0x99u8; 32], 1_000_000, 0, [0x33u8; 32], recipient, 500),
    );
    let relayer = SolanaRelayer::new(config(), rpc);
    assert_eq!(
        relayer.observe_vault_lock().unwrap_err(),
        RelayerError::NotBridgeVault,
        "an un-escrowed lock is refused before any mint"
    );
}

#[test]
fn relayer_refuses_unfinalized_lock_round_trip() {
    // The lock is visible at confirmed but NOT finalized — never minted against.
    let recipient = CellId::from_bytes(pk(1));
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_confirmed_only(
        VAULT,
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, [0x55u8; 32], recipient, 500),
    );
    let relayer = SolanaRelayer::new(config(), rpc);
    assert_eq!(
        relayer.observe_vault_lock().unwrap_err(),
        RelayerError::NotFinalized,
        "an un-finalized lock is refused before any mint"
    );
}
