//! The trustless-mint invariant: **only a real stake-weighted Solana
//! super-majority can mint the $DREGG mirror.**
//!
//! This drives the consensus-verified lock-observation path end to end over the
//! in-memory chain double and proves both polarities of the mint trust gate:
//!
//! 1. **`ConsensusVerified` ⟹ mintable.** A finalized lock record owned by the
//!    configured lock program, PLUS finality evidence (an epoch stake table + real
//!    Ed25519 vote txns clearing ≥ 2/3), verifies to
//!    [`LockProofTrust::ConsensusVerified`] via
//!    [`SolanaRelayer::observe_vault_lock_consensus`]. The resulting
//!    `BridgeMintRequest` carries `consensus_verified = true`, and the committed
//!    [`TurnExecutor::bridge_mint_against_lock`] mints conserving credit against
//!    the independently-recorded escrow.
//! 2. **RPC-only / `StructureOnly` ⟹ CANNOT mint** (the load-bearing reject). The
//!    SAME finalized account observed WITHOUT consensus evidence (the plain-RPC
//!    path a forged/MITM node can fabricate) reaches only
//!    [`LockProofTrust::StructureOnly`], so its request carries
//!    `consensus_verified = false` and the committed mint refuses it with
//!    [`BridgeMintError::TrustTooLow`]. No supply moves.
//! 3. **A sub-super-majority CANNOT reach consensus** (the invariant's teeth).
//!    Consensus evidence signed by a single validator holding < 2/3 of the epoch
//!    stake is refused at observe time with
//!    [`LockProofError::StakeBelowThreshold`] — it never becomes a mintable
//!    `ConsensusVerified` request. The stake threshold is what makes the mint
//!    trustless, so it is exercised against a REJECT, not merely a happy path.
//!
//! Every fixture is built from the REAL crate constructors (`EpochStakeTable`,
//! `ValidatorVote::sign`, `BankHashComponents`, `MockSolanaRpc`) — the same
//! finalized account bytes drive both the mintable and the refused observations,
//! so the ONLY difference between mint and no-mint is the presence of a genuine
//! stake-weighted super-majority. The one residual — a fully-trustless in-circuit
//! witness so a dregg LIGHT client (not this re-executing relayer) sees the
//! backing, and the operator's snapshot/geyser vote feed rather than a supplied
//! `ConsensusEvidence` bundle — is the circuit swarm's G1 VK-epoch, named in
//! `observe_vault_lock_consensus`'s own doc and out of scope here.

use dregg_bridge::solana_consensus::{BankHashComponents, EpochStakeTable, ValidatorVote};
use dregg_bridge::solana_mirror::MirrorConfig;
use dregg_bridge::solana_relayer::{MockSolanaRpc, RelayerError, RpcAccount, SolanaRelayer};
use dregg_bridge::solana_trustless::{ConsensusEvidence, LockProofError, LockProofTrust};
use dregg_bridge::solana_wire::{accounts_merkle_node, encode_lock_record, solana_account_hash};
use dregg_cell::{AuthRequired, Cell, CellId, EFFECT_MINT, Ledger, Permissions};
use dregg_turn::{
    BridgeMintError, ComputronCosts, TurnExecutor, new_mirror_ledger_cell, read_supply,
};
use ed25519_dalek::SigningKey;

const SPL_MINT: [u8; 32] = [0xABu8; 32];
const MIRROR_ASSET: [u8; 32] = [0x77u8; 32];
const VAULT: [u8; 32] = [0x22u8; 32];
const LOCK_PROGRAM: [u8; 32] = [0x07u8; 32];
/// The stake-table epoch the consensus fixtures vote under.
const EPOCH: u64 = 5;

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

fn vk(seed: u8) -> SigningKey {
    SigningKey::from_bytes(&[seed; 32])
}

/// Three validators, 400/400/200 stake (total 1000). Any two of the top pair
/// (800/1000 = 80%) clear 2/3; a single 400-stake validator (40%) does not.
fn stake_table() -> EpochStakeTable {
    EpochStakeTable::from_entries(
        EPOCH,
        [
            (vk(11).verifying_key().to_bytes(), 400),
            (vk(12).verifying_key().to_bytes(), 400),
            (vk(13).verifying_key().to_bytes(), 200),
        ],
    )
}

/// Build the accounts hash the relayer itself derives over the REAL finalized
/// vault account — the bundle's `bank_components.accounts_hash` must match it or
/// the consensus verify refuses with a bank-hash mismatch.
fn accounts_hash_for(
    account: &RpcAccount,
    lock_id: [u8; 32],
    recipient: CellId,
    amount: u64,
) -> [u8; 32] {
    let vault_data = encode_lock_record(&lock_id, &recipient, amount);
    let leaf = solana_account_hash(
        account.lamports,
        &account.owner,
        account.executable,
        account.rent_epoch,
        &vault_data,
        &VAULT,
    );
    accounts_merkle_node(&[leaf])
}

/// Finality evidence consistent with the relayer's single-leaf accounts hash over
/// the REAL finalized account, signed by the validators in `signers`. This is the
/// snapshot/geyser bundle a real operator supplies; the relayer cross-checks it
/// against the account it reads itself and recounts the stake from the votes.
fn consensus_signed_by(
    account: &RpcAccount,
    lock_id: [u8; 32],
    recipient: CellId,
    amount: u64,
    signers: &[SigningKey],
) -> ConsensusEvidence {
    let accounts_hash = accounts_hash_for(account, lock_id, recipient, amount);
    let slot = 12_345u64;
    let bank_components = BankHashComponents {
        parent_bank_hash: [0x01u8; 32],
        accounts_hash,
        signature_count: signers.len() as u64,
        last_blockhash: [0u8; 32],
    };
    let bank_hash = bank_components.compute();
    let votes = signers
        .iter()
        .map(|s| ValidatorVote::sign(s, slot, bank_hash))
        .collect();
    ConsensusEvidence {
        slot,
        bank_hash,
        epoch: EPOCH,
        // Claimed scalars — the consensus path recounts real stake from `votes`
        // against the tracked table, so these are not what the gate trusts.
        voted_stake: 0,
        total_stake: 1000,
        votes,
        bank_components,
        poh: None,
    }
}

/// The ≥ 2/3 super-majority bundle (validators 11 + 12 = 800/1000).
fn consensus_supermajority(
    account: &RpcAccount,
    lock_id: [u8; 32],
    recipient: CellId,
    amount: u64,
) -> ConsensusEvidence {
    consensus_signed_by(account, lock_id, recipient, amount, &[vk(11), vk(12)])
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) ConsensusVerified ⟹ a mintable request that mints conserving credit.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn consensus_verified_lock_yields_mintable_request() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    // A finalized lock record owned by the configured lock program (the 72-byte
    // lock_id ‖ recipient ‖ amount_le layout MockSolanaRpc::lock_account encodes).
    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    // Drive the consensus path with a genuine ≥ 2/3 stake-weighted vote set.
    let consensus = consensus_supermajority(&account, lock_id, recipient, amount);
    let observed = relayer
        .observe_vault_lock_consensus(consensus, &stake_table(), false)
        .expect("finalized lock + super-majority evidence verifies to consensus");
    assert_eq!(
        observed.trust,
        LockProofTrust::ConsensusVerified,
        "the stake-weighted super-majority is genuinely verified"
    );
    assert_eq!(observed.amount, amount);
    assert_eq!(observed.lock_id, lock_id);

    // The mintable result: consensus_verified = true.
    let req = observed.to_bridge_mint_request(issuer, ledger_cell);
    assert!(
        req.consensus_verified,
        "a ConsensusVerified observation produces a MINTABLE request"
    );

    // Record the independent escrow leg, then the committed mint DRAWS against it.
    exec.bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
        .expect("consensus-verified escrow recorded");
    let receipt = exec
        .bridge_mint_against_lock(&mut ledger, &req)
        .expect("the consensus-verified lock mints conserving mirror credit");
    assert_eq!(receipt.currently_locked, amount);
    assert_eq!(receipt.live_supply, amount);

    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (amount, amount));
    assert!(
        live <= locked,
        "live supply never exceeds the locked backing"
    );
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        amount as i64,
        "recipient credited exactly the locked amount"
    );
    assert_eq!(
        ledger
            .get(&derived_well_id(&MIRROR_ASSET))
            .unwrap()
            .state
            .balance(),
        -(amount as i64),
        "the issuer well carries the conserving −supply (Σδ = 0)"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) RPC-only / StructureOnly ⟹ CANNOT mint (the load-bearing reject).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn rpc_only_observation_of_the_same_lock_cannot_mint() {
    let (mut ledger, recipient, issuer, ledger_cell) = scaffold(MIRROR_ASSET);
    let exec = TurnExecutor::new(ComputronCosts::zero());
    let amount = 500u64;
    let lock_id = [0x11u8; 32];

    // The SAME finalized account that mints on the consensus path above — here it
    // is observed over a plain RPC (no vote set, no stake table), exactly what a
    // forged/MITM node can fabricate. It reaches only StructureOnly.
    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient, amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    let observed = relayer
        .observe_vault_lock()
        .expect("the plain-RPC observe still surfaces the finalized lock");
    assert_eq!(
        observed.trust,
        LockProofTrust::StructureOnly,
        "a plain-RPC observation is NOT consensus-verified"
    );

    // The request is NOT mintable.
    let req = observed.to_bridge_mint_request(issuer, ledger_cell);
    assert!(
        !req.consensus_verified,
        "a StructureOnly observation yields consensus_verified = false"
    );

    // Its escrow leg cannot even raise the backing…
    assert_eq!(
        exec.bridge_record_escrow(&mut ledger, &observed.to_escrow_record(ledger_cell))
            .unwrap_err(),
        BridgeMintError::TrustTooLow,
        "a StructureOnly observation cannot record escrow backing"
    );
    // …and the committed mint itself refuses it BEFORE touching any state.
    assert_eq!(
        exec.bridge_mint_against_lock(&mut ledger, &req)
            .unwrap_err(),
        BridgeMintError::TrustTooLow,
        "an RPC-only (StructureOnly) proof CANNOT mint — the trustless invariant"
    );

    let (locked, live) = read_supply(ledger.get(&ledger_cell).unwrap());
    assert_eq!((locked, live), (0, 0), "no unbacked supply was created");
    assert_eq!(
        ledger.get(&recipient).unwrap().state.balance(),
        0,
        "recipient uncredited by the refused RPC-only path"
    );
}

// ─────────────────────────────────────────────────────────────────────────────
// (3) A sub-super-majority CANNOT reach consensus — the invariant's teeth.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn sub_supermajority_evidence_cannot_reach_consensus() {
    let amount = 500u64;
    let lock_id = [0x11u8; 32];
    let account =
        MockSolanaRpc::lock_account(LOCK_PROGRAM, 1_000_000, 0, lock_id, recipient_id(), amount);
    let mut rpc = MockSolanaRpc::new(100, 105, 110);
    rpc.insert_finalized(VAULT, account.clone());
    let relayer = SolanaRelayer::new(config(), rpc);

    // Consensus evidence signed by ONLY validator 11 (400 of 1000 = 40% < 2/3).
    // The votes are individually valid Ed25519 signatures over the real bank hash,
    // and the accounts hash matches the finalized account — the ONLY defect is
    // insufficient stake. The relayer recounts real stake and refuses.
    let consensus = consensus_signed_by(&account, lock_id, recipient_id(), amount, &[vk(11)]);
    let err = relayer
        .observe_vault_lock_consensus(consensus, &stake_table(), false)
        .expect_err("a 40% vote set cannot reach consensus");
    match err {
        RelayerError::Proof(LockProofError::StakeBelowThreshold { voted, total }) => {
            assert!(
                voted.saturating_mul(3) < total.saturating_mul(2),
                "the refused tally is genuinely below the 2/3 super-majority: {voted}/{total}"
            );
            assert_eq!(voted, 400, "only validator 11's real stake was counted");
            assert_eq!(total, 1000, "against the full epoch stake");
        }
        other => panic!("expected StakeBelowThreshold, got {other:?}"),
    }
}

/// The recipient cell id used by test (3) (fixed, matches `scaffold`'s recipient
/// derivation is not needed here — the reject fires before any ledger touch).
fn recipient_id() -> CellId {
    CellId::from_bytes(pk(1))
}
