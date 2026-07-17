//! # The cross-chain non-custodial governance demo — run it: it drives the REAL code
//!
//! ```text
//! cargo run --example cross_chain_vote
//! ```
//!
//! Alice proves $DREGG holdings on THREE chains — Solana, Base (EVM), and
//! cosmoshub-4 (Cosmos) — non-custodially, binds each with the wallet key that
//! controls it, and casts one holding-weighted ballot; Bob votes the other way; the
//! tally derives the cross-chain weighted outcome. A forged proof is refused live.
//!
//! Every step below calls the production verifiers and the production grant path
//! (`dregg-bridge` anchored consensus verify, `eth-lightclient` EIP-1186 verify,
//! the `cosmos-lightclient` bank decoder, the three real signature schemes, the
//! Lean-proven weight verdict, the CollectiveChoice engine). What is fixture is
//! SAID to be fixture, inline, when it prints.

use dregg_bridge::solana_holdings::{
    fixtures as sol_fixtures, prove_holding_consensus_anchored, ProvenHolding,
};
use dregg_governance::holding_weight::{
    binding_message, cosmos_address_of_pubkey, cosmos_binding_prehash, eip191_message_hash,
    evm_address_of_pubkey, evm_binding_message, narrow_ballot_weight, CosmosOwnerBinding,
    EvmOwnerBinding, GrantError, HoldingWeightRegistry, OwnerBinding, VerifiedHoldingBallotBox,
    VoterBinding, WeightedBallotEngine,
};
use dregg_governance::proven_foreign_holding::ChainId;
use dregg_governance::{CastOutcome, DecisionRule, Electorate, OptionId, PollSpec, VoterId};
use dregg_interchain_gov::{
    cosmos_fields_to_holding, evm_holding_to_governance, solana_holding_to_governance,
};
use eth_lightclient::evm::{
    erc20_balance_slot_key, verify_erc20_holding_finalized, AccountClaim, Uint256,
};
use eth_lightclient::finality::FinalizedExecution;

use ed25519_dalek::{Signer, SigningKey as Ed25519Key};
use k256::ecdsa::signature::hazmat::PrehashSigner;
use k256::ecdsa::{Signature as Secp256k1Signature, SigningKey as Secp256k1Key};

const ALICE_VOTER: VoterId = [0xA1u8; 32];
const BOB_VOTER: VoterId = [0xB0u8; 32];
const DREGG_MINT: [u8; 32] = [0xD6u8; 32];
const SPL_TOKEN_PROGRAM: [u8; 32] = [0x06u8; 32];
const SOLANA_FIXTURE_SLOT: u64 = 7_000;
const BASE_BLOCK: u64 = 21_000_000;
const COSMOS_HEIGHT: u64 = 31_992_690;
const DREGG_TOKEN_ON_BASE: [u8; 20] = [0xD7u8; 20];
const BALANCES_SLOT: u64 = 3;

fn main() {
    println!("── dregg cross-chain non-custodial governance ─────────────────────────────");
    println!("   one holder · three chains · one weighted vote · custody never moves");
    println!();

    if !dregg_lean_ffi::holding_grant_weight_core_available() {
        eprintln!(
            "the Lean-proven weight-verdict core is not in the linked archive; \
             the grant path fail-closes by design. Rebuild dregg-lean-ffi and re-run."
        );
        std::process::exit(1);
    }

    // ───────────────────────── the poll ─────────────────────────
    let mut engine = VerifiedHoldingBallotBox::new([0u8; 32]);
    let poll = engine
        .open_weighted_poll(&PollSpec {
            question: "adopt the treasury proposal?".into(),
            options: vec!["no".into(), "yes".into()],
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum: 1 },
            enact_on_pass: false,
            nonce: 0,
        })
        .expect("the weighted holding poll opens on the verified executor");
    let mut reg = HoldingWeightRegistry::new();
    reg.open_chain_snapshot(poll, ChainId::Solana, SOLANA_FIXTURE_SLOT);
    reg.open_chain_snapshot(poll, ChainId::BASE, BASE_BLOCK);
    reg.open_chain_snapshot(poll, ChainId::cosmos("cosmoshub-4"), COSMOS_HEIGHT);
    println!("poll opened: \"adopt the treasury proposal?\"  options: no / yes");
    println!("snapshots pinned per chain: Solana slot {SOLANA_FIXTURE_SLOT} · Base block {BASE_BLOCK} · cosmoshub-4 height {COSMOS_HEIGHT}");
    println!();

    // ───────────────────────── Solana: 2000 $DREGG ─────────────────────────
    let alice_sol = Ed25519Key::from_bytes(&[0x51u8; 32]);
    let sol_holding =
        solana_proven_holding(alice_sol.verifying_key().to_bytes(), [0xAAu8; 32], 2_000);
    assert!(sol_holding.is_consensus_proven());
    let sol_fact = solana_holding_to_governance(&sol_holding);
    println!("[solana]  Alice proves 2000 $DREGG at slot {SOLANA_FIXTURE_SLOT}");
    println!("          via the REAL anchored consensus verifier: stake provenance from bank");
    println!("          state under the pinned anchor, >=2/3 signed TowerSync votes, bank-hash");
    println!("          binding, PoH chain  (cluster = a local 2-validator fixture; the");
    println!("          verifier is the production path)  -> ConsensusVerified");

    // ───────────────────────── Base (EVM): 1000 $DREGG ─────────────────────────
    let alice_evm = Secp256k1Key::from_slice(&[0x52u8; 32]).unwrap();
    let holder20 = evm_address_of_pubkey(alice_evm.verifying_key());
    let world = evm_world(holder20, 1_000);
    let base_holding = verify_erc20_holding_finalized(
        &FinalizedExecution::new_unchecked(
            0,
            [0u8; 32],
            BASE_BLOCK,
            [0u8; 32],
            world.state_root,
            0,
        ),
        &world.account_proof,
        &world.storage_proof,
        DREGG_TOKEN_ON_BASE,
        holder20,
        BALANCES_SLOT,
        &world.account,
        Uint256::from(1_000u64),
    )
    .expect("the genuine proof over the synthesized world verifies");
    let base_fact = evm_holding_to_governance(&base_holding, 8453).expect("the compiled EVM join");
    println!("[base]    Alice proves 1000 $DREGG at block {BASE_BLOCK} (EIP-155 chain 8453)");
    println!("          via the REAL EIP-1186 verifier: account trie -> storageHash -> balance");
    println!("          slot, Merkle-Patricia proofs checked by the pinned alloy-trie");
    println!("          (token state = a locally synthesized fixture trie; the finality root");
    println!("          is a stand-in for a live sync-committee update)  -> ConsensusProven");

    // ───────────────────────── cosmoshub-4: 500 $DREGG ─────────────────────────
    let alice_cosmos = Secp256k1Key::from_slice(&[0x53u8; 32]).unwrap();
    let cosmos_addr = cosmos_address_of_pubkey(alice_cosmos.verifying_key());
    let cosmos_fact = cosmos_fields_to_holding(&cosmos_fields_for(cosmos_addr, 500), "cosmoshub-4")
        .expect("the compiled Cosmos join");
    println!("[cosmos]  Alice holds 500 $DREGG (udregg) at height {COSMOS_HEIGHT} on cosmoshub-4");
    println!("          bank KV decoded by the edge crate's REAL decoder; consensus verdict is");
    println!("          a FIXTURE here (a bindable live fact needs a funded account on a live");
    println!("          chain — the genuine header+ICS-23 path runs in this crate's tests");
    println!("          against real cosmoshub-4 mainnet captures)");
    println!();

    // ───────────────────────── the bindings ─────────────────────────
    let sol_bind = VoterBinding::Ed25519(ed25519_bind(&alice_sol, ALICE_VOTER));
    let base_bind = VoterBinding::Evm(evm_bind(&alice_evm, ALICE_VOTER));
    let cosmos_bind_ = VoterBinding::Cosmos(cosmos_bind(&alice_cosmos, ALICE_VOTER));
    println!("Alice binds each holding to her ONE dregg voter id, signing with the wallet");
    println!("key that controls it — a signature, never a transfer:");
    println!("  solana : Ed25519 over the domain-separated binding message");
    println!("  base   : secp256k1 EIP-191 personal_sign (any stock EVM wallet)");
    println!("  cosmos : secp256k1 over the dregg Cosmos sign-doc, pubkey carried");
    println!();

    // ───────────────────────── grant + one weighted ballot ─────────────────────────
    let g_sol = reg
        .grant_foreign_into_poll(poll, &sol_fact, &sol_bind)
        .expect("solana grant");
    let g_base = reg
        .grant_foreign_into_poll(poll, &base_fact, &base_bind)
        .expect("base grant");
    let g_cos = reg
        .grant_foreign_into_poll(poll, &cosmos_fact, &cosmos_bind_)
        .expect("cosmos grant");
    let total = narrow_ballot_weight(g_sol.weight + g_base.weight + g_cos.weight).expect("fits");
    println!("each grant runs the fail-closed path: consensus verdict -> owner binding ->");
    println!("positive amount -> the LEAN-PROVEN weight verdict -> per-chain snapshot pin ->");
    println!("consume-once nullifier (chain+holder+asset):");
    println!("  solana grant : {} weight", g_sol.weight);
    println!("  base grant   : {} weight", g_base.weight);
    println!("  cosmos grant : {} weight", g_cos.weight);
    println!("Alice casts ONE ballot for \"yes\" carrying her cross-chain weight: {total}");
    assert_eq!(
        engine
            .cast_weighted_ballot(poll, ALICE_VOTER, OptionId(1), total)
            .expect("poll open"),
        CastOutcome::Accepted
    );

    // ───────────────────────── Bob votes no ─────────────────────────
    let bob_sol = Ed25519Key::from_bytes(&[0x61u8; 32]);
    let bob_holding =
        solana_proven_holding(bob_sol.verifying_key().to_bytes(), [0xBBu8; 32], 1_200);
    let bob_fact = solana_holding_to_governance(&bob_holding);
    let bob_bind = VoterBinding::Ed25519(ed25519_bind(&bob_sol, BOB_VOTER));
    let outcome = reg
        .foreign_grant_and_cast(&mut engine, poll, OptionId(0), &bob_fact, &bob_bind)
        .expect("bob grant-and-cast");
    assert_eq!(outcome, CastOutcome::Accepted);
    println!("Bob proves 1200 $DREGG on Solana (same real verifier) and votes \"no\"");
    println!();

    // ───────────────────────── the tally ─────────────────────────
    let tally = engine.tally(poll).expect("tally");
    let yes = tally.per_option.get(1).copied().unwrap_or(0);
    let no = tally.per_option.get(0).copied().unwrap_or(0);
    println!("── TALLY ──────────────────────────────────────────────────────────────────");
    println!("  yes : {yes}   (Alice — 2000 solana + 1000 base + 500 cosmoshub-4)");
    println!("  no  : {no}   (Bob — 1200 solana)");
    println!(
        "  total weight on the verified executor board: {}",
        tally.total
    );
    assert_eq!(yes, 3_500);
    assert_eq!(no, 1_200);
    println!("  => \"yes\" carries, 3500 to 1200 — a holding-weighted outcome spanning");
    println!("     three chains, and custody never left Alice's or Bob's wallets.");
    println!();

    // ───────────────────────── the forgery, refused live ─────────────────────────
    println!("── FORGERY, REFUSED ───────────────────────────────────────────────────────");
    // 1. Mallory tampers a storage-proof node to claim Alice's Base balance is hers.
    let mallory_evm = Secp256k1Key::from_slice(&[0x66u8; 32]).unwrap();
    let mallory20 = evm_address_of_pubkey(mallory_evm.verifying_key());
    let mut tampered = world.storage_proof.clone();
    let last = tampered.len() - 1;
    tampered[last][5] ^= 0x01;
    let forged = verify_erc20_holding_finalized(
        &FinalizedExecution::new_unchecked(
            0,
            [0u8; 32],
            BASE_BLOCK,
            [0u8; 32],
            world.state_root,
            0,
        ),
        &world.account_proof,
        &tampered,
        DREGG_TOKEN_ON_BASE,
        mallory20,
        BALANCES_SLOT,
        &world.account,
        Uint256::from(1_000u64),
    );
    println!(
        "  a tampered EIP-1186 storage proof     -> {:?}",
        forged.unwrap_err()
    );
    // 2. Alice's own Base holding, re-presented into the SAME poll with her OWN
    //    (valid) binding: the consume-once nullifier already fired, so no
    //    double-count — AlreadyCounted. (The binding must be genuine to reach the
    //    nullifier check; the grant path verifies the owner binding first.)
    assert_eq!(
        reg.grant_foreign_into_poll(poll, &base_fact, &base_bind),
        Err(GrantError::AlreadyCounted),
        "the same holding cannot be counted twice in one poll"
    );
    println!("  re-presenting Alice's counted holding -> AlreadyCounted (nullifier fired)");
    // 3. On a fresh poll, the stranger binding itself is refused.
    let poll2 = engine
        .open_weighted_poll(&PollSpec {
            question: "second poll".into(),
            options: vec!["no".into(), "yes".into()],
            electorate: Electorate::Open,
            rule: DecisionRule::Plurality { quorum: 1 },
            enact_on_pass: false,
            nonce: 1,
        })
        .expect("second weighted poll opens");
    reg.open_chain_snapshot(poll2, ChainId::BASE, BASE_BLOCK);
    assert_eq!(
        reg.grant_foreign_into_poll(poll2, &base_fact, &evm_bind(&mallory_evm, BOB_VOTER)),
        Err(GrantError::UnboundOwner)
    );
    println!("  a stranger's binding on Alice's holding -> UnboundOwner (wrong wallet key)");
    println!();
    println!("done: the whole flow above ran the production verifiers and grant path.");
}

// ── helpers (mirrors of the integration-test fixtures) ──────────────────────

fn solana_proven_holding(wallet: [u8; 32], token_account: [u8; 32], amount: u64) -> ProvenHolding {
    let (proof, anchor, policy) = sol_fixtures::anchored_holding_with_cluster(
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        token_account,
        wallet,
        amount,
        &[(11, 700), (12, 300)],
    );
    prove_holding_consensus_anchored(
        &proof,
        &DREGG_MINT,
        &SPL_TOKEN_PROGRAM,
        &anchor,
        true,
        Some(&policy),
    )
    .expect("a genuine holding under the pinned anchor verifies")
}

struct EvmWorld {
    state_root: [u8; 32],
    account_proof: Vec<Vec<u8>>,
    storage_proof: Vec<Vec<u8>>,
    account: AccountClaim,
}

/// Synthesize the token world with the same pinned alloy-trie the verifier uses
/// (fixture STATE; real VERIFICATION).
fn evm_world(holder: [u8; 20], balance: u128) -> EvmWorld {
    use alloy_primitives::{keccak256, Bytes, B256};
    use alloy_trie::{proof::ProofRetainer, HashBuilder, Nibbles, TrieAccount};

    fn build_trie(
        entries: &[(Vec<u8>, Vec<u8>)],
        targets: &[Vec<u8>],
    ) -> ([u8; 32], Vec<Vec<Vec<u8>>>) {
        let target_nibbles: Vec<Nibbles> = targets
            .iter()
            .map(|k| Nibbles::unpack(keccak256(k)))
            .collect();
        let retainer = ProofRetainer::new(target_nibbles.clone());
        let mut hb = HashBuilder::default().with_proof_retainer(retainer);
        let mut sorted: Vec<(Nibbles, &Vec<u8>)> = entries
            .iter()
            .map(|(k, v)| (Nibbles::unpack(keccak256(k)), v))
            .collect();
        sorted.sort_by(|a, b| a.0.cmp(&b.0));
        for (path, value) in sorted {
            hb.add_leaf(path, value);
        }
        let root: B256 = hb.root();
        let retained: Vec<(Nibbles, Bytes)> = hb.take_proof_nodes().into_nodes_sorted();
        let proofs = target_nibbles
            .iter()
            .map(|t| {
                retained
                    .iter()
                    .filter(|(p, _)| t.starts_with(p))
                    .map(|(_, n)| n.to_vec())
                    .collect::<Vec<_>>()
            })
            .collect();
        (root.0, proofs)
    }

    let slot_key = erc20_balance_slot_key(&holder, BALANCES_SLOT).to_vec();
    let other_key = erc20_balance_slot_key(&[0x99u8; 20], BALANCES_SLOT).to_vec();
    let (storage_root, storage_proofs) = build_trie(
        &[
            (slot_key.clone(), alloy_rlp::encode(Uint256::from(balance))),
            (other_key, alloy_rlp::encode(Uint256::from(7u8))),
        ],
        &[slot_key],
    );
    let account = AccountClaim {
        nonce: 1,
        balance: Uint256::ZERO,
        storage_hash: storage_root,
        code_hash: [0xCCu8; 32],
    };
    let account_rlp = alloy_rlp::encode(TrieAccount {
        nonce: account.nonce,
        balance: account.balance,
        storage_root: account.storage_hash.into(),
        code_hash: account.code_hash.into(),
    });
    let (state_root, account_proofs) = build_trie(
        &[(DREGG_TOKEN_ON_BASE.to_vec(), account_rlp)],
        &[DREGG_TOKEN_ON_BASE.to_vec()],
    );
    EvmWorld {
        state_root,
        account_proof: account_proofs[0].clone(),
        storage_proof: storage_proofs[0].clone(),
        account,
    }
}

/// Alice's Cosmos bank-balance fields: the KV synthesized for her address, decoded
/// by the edge crate's REAL decoder; `consensus_proven: true` is a fixture verdict
/// (see the inline narration when this prints).
fn cosmos_fields_for(addr: [u8; 20], amount: u128) -> cosmos_lightclient::ForeignHoldingFields {
    let mut key = vec![0x02u8, 20];
    key.extend_from_slice(&addr);
    key.extend_from_slice(b"udregg");
    let value = amount.to_string();
    let bal = cosmos_lightclient::decode_bank_balance_kv(b"bank", &key, value.as_bytes())
        .expect("a well-formed bank KV decodes");
    let mut holder = [0u8; 32];
    holder[12..].copy_from_slice(&addr);
    cosmos_lightclient::ForeignHoldingFields {
        chain_tag: cosmos_lightclient::COSMOS_CHAIN_TAG,
        holder,
        asset: cosmos_lightclient::cosmos_denom_asset_id(&bal.denom),
        amount: bal.amount,
        snapshot: COSMOS_HEIGHT,
        consensus_proven: true,
    }
}

fn ed25519_bind(owner: &Ed25519Key, voter: VoterId) -> OwnerBinding {
    let owner_pk = owner.verifying_key().to_bytes();
    let sig = owner.sign(&binding_message(&owner_pk, &voter)).to_bytes();
    OwnerBinding { voter, sig }
}

fn evm_bind(key: &Secp256k1Key, voter: VoterId) -> EvmOwnerBinding {
    let addr = evm_address_of_pubkey(key.verifying_key());
    let prehash = eip191_message_hash(&evm_binding_message(&addr, &voter));
    let (sig, recid) = key.sign_prehash_recoverable(&prehash).expect("signs");
    let mut bytes = [0u8; 65];
    bytes[..64].copy_from_slice(&sig.to_bytes());
    bytes[64] = recid.to_byte() + 27;
    EvmOwnerBinding { voter, sig: bytes }
}

fn cosmos_bind(key: &Secp256k1Key, voter: VoterId) -> CosmosOwnerBinding {
    let addr = cosmos_address_of_pubkey(key.verifying_key());
    let prehash = cosmos_binding_prehash(&addr, &voter);
    let sig: Secp256k1Signature = key.sign_prehash(&prehash).expect("signs");
    let mut sig_bytes = [0u8; 64];
    sig_bytes.copy_from_slice(&sig.to_bytes());
    let mut pubkey = [0u8; 33];
    pubkey.copy_from_slice(key.verifying_key().to_encoded_point(true).as_bytes());
    CosmosOwnerBinding {
        voter,
        pubkey,
        sig: sig_bytes,
    }
}
