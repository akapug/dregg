//! `solana_verify_bench`: wall-time of the trustless Solana lock-proof verify as
//! a function of the validator-vote count.
//!
//! The trustless consensus verify
//! ([`dregg_bridge::verify_lock_proof_consensus`] /
//! [`dregg_bridge::verify_lock_proof_consensus_anchored`]) is **O(votes)** in its
//! hot loop: one Ed25519 verify per counted vote, plus the (one) accounts-hash
//! Merkle fold and (optional) PoH tick chain. This bench measures that cost at
//! realistic validator counts (Solana mainnet is ~1500 active vote accounts) so
//! we can decide whether the direct in-process verify is fast enough for staging
//! or whether the Option-B succinct O(1) wrapper
//! (`docs/deos/SOLANA-SUCCINCT-WRAPPER.md`) is needed soon.
//!
//! Two vote authenticity paths are benched, both at 100 / 500 / 1500 votes:
//!
//! - **placeholder** — `ValidatorVote::sign` (a bare Ed25519 signature over the
//!   canonical vote message). This is the minimal per-vote cost: one
//!   `VerifyingKey::from_bytes` + one `verify`.
//! - **witness** — a real-wire vote *transaction* per vote (the path the
//!   anchored, mainnet-faithful verify actually runs): each vote re-parses and
//!   re-verifies a bincode Solana `Transaction`, the heavier real cost.
//!
//! The accounts-inclusion leg is the modeled sorted-pair path (one Merkle fold);
//! the anchored verify additionally pays a one-time O(stake+vote accounts)
//! provenance derivation, which is *not* in this O(votes) loop and is amortized
//! once per proof.

use criterion::{BenchmarkId, Criterion, black_box, criterion_group, criterion_main};
use dregg_bridge::solana_consensus::{
    BankHashComponents, EpochStakeTable, PohSegment, ValidatorVote, account_leaf, merkle_node,
};
use dregg_bridge::solana_trustless::{
    AccountInclusionProof, ConsensusEvidence, SolanaLockProof, verify_lock_proof_consensus,
};
use dregg_bridge::solana_wire::ingest_vote_transaction;
use dregg_types::CellId;
use ed25519_dalek::SigningKey;

const SPL_MINT: [u8; 32] = [0xABu8; 32];
const EPOCH: u64 = 7;
const SLOT: u64 = 222_333;
const AMOUNT: u64 = 500;

fn vk(seed: u64) -> SigningKey {
    let mut s = [0u8; 32];
    s[..8].copy_from_slice(&seed.to_le_bytes());
    s[31] = 1; // keep the scalar nonzero / well-formed across all seeds
    SigningKey::from_bytes(&s)
}

/// A real Solana vote `Transaction` (legacy wire layout) voting `(slot,
/// bank_hash)` for `vote_account`, signed by `authority`. Mirrors the wire shape
/// the bridge's `parse_verified_vote_tx` ingests. Built here (not harvested) so
/// the bench is self-contained; the local-validator e2e harness exercises the
/// harvested-artifact path.
fn build_vote_tx(
    authority: &SigningKey,
    vote_account: [u8; 32],
    slot: u64,
    bank_hash: [u8; 32],
) -> Vec<u8> {
    use ed25519_dalek::Signer;
    use solana_vote_interface::instruction::VoteInstruction;
    use solana_vote_interface::state::TowerSync;

    // Solana ShortU16 (little-endian 7-bits-per-byte varint).
    fn push_compact_u16(out: &mut Vec<u8>, mut v: u16) {
        loop {
            let mut byte = (v & 0x7f) as u8;
            v >>= 7;
            if v != 0 {
                byte |= 0x80;
            }
            out.push(byte);
            if v == 0 {
                break;
            }
        }
    }

    let auth_pk = authority.verifying_key().to_bytes();
    let vote_program = solana_vote_interface::program::id().to_bytes();

    // account_keys: [authority(signer), vote_account, vote_program]
    let account_keys: Vec<[u8; 32]> = vec![auth_pk, vote_account, vote_program];

    // TowerSync vote for (slot, bank_hash): meta layout (0: vote account, 1: authority).
    let mut tower = TowerSync::default();
    tower.hash = solana_hash::Hash::new_from_array(bank_hash);
    tower
        .lockouts
        .push_back(solana_vote_interface::state::Lockout::new(slot));
    let ix = VoteInstruction::TowerSync(tower);
    let ix_data = bincode::serialize(&ix).expect("serialize vote ix");

    // CompiledInstruction: program_id_index=2, accounts=[1(vote_acct), 0(authority)].
    // message: header(3) ‖ account_keys ‖ recent_blockhash ‖ instructions
    let mut message = Vec::new();
    message.push(1u8); // num_required_signatures
    message.push(0u8); // num_readonly_signed
    message.push(1u8); // num_readonly_unsigned (the vote program)
    push_compact_u16(&mut message, account_keys.len() as u16);
    for k in &account_keys {
        message.extend_from_slice(k);
    }
    message.extend_from_slice(&[0u8; 32]); // recent blockhash
    push_compact_u16(&mut message, 1); // one instruction
    message.push(2u8); // program_id_index
    push_compact_u16(&mut message, 2); // accounts len
    message.push(1u8); // vote account meta
    message.push(0u8); // authority meta
    push_compact_u16(&mut message, ix_data.len() as u16); // data len
    message.extend_from_slice(&ix_data);

    let sig = authority.sign(&message).to_bytes();

    let mut tx = Vec::new();
    push_compact_u16(&mut tx, 1); // signature count
    tx.extend_from_slice(&sig);
    tx.extend_from_slice(&message);
    tx
}

/// Build an `n`-vote consensus-grade lock proof: `n` validators each with stake 1
/// (so any 2/3 of them clears the threshold), all `n` voting the same bank hash.
/// `witness = true` carries a real-wire vote transaction per vote (the heavier
/// anchored-tally path); otherwise a bare signed placeholder.
fn build_proof(n: usize, witness: bool) -> (SolanaLockProof, EpochStakeTable) {
    let recipient = CellId::from_bytes([3u8; 32]);
    let lock_id = [9u8; 32];
    let vault = [0x22u8; 32];

    // Accounts hash: the lock-record leaf with one modeled sibling.
    let leaf = account_leaf(&vault, AMOUNT, &recipient, &lock_id);
    let sib = [0xEEu8; 32];
    let accounts_hash = merkle_node(&leaf, &sib);

    // A short real PoH tick chain ending at the slot's last blockhash.
    use sha2::{Digest, Sha256};
    let anchor = [0x55u8; 32];
    let mut tail = anchor;
    for _ in 0..64u64 {
        let mut h = Sha256::new();
        h.update(tail);
        tail = h.finalize().into();
    }
    let bank_components = BankHashComponents {
        parent_bank_hash: [0x01; 32],
        accounts_hash,
        signature_count: n as u64,
        last_blockhash: tail,
    };
    let bank_hash = bank_components.compute();

    let mut entries = Vec::with_capacity(n);
    let mut votes = Vec::with_capacity(n);
    for i in 0..n {
        let key = vk(i as u64 + 1);
        let pk = key.verifying_key().to_bytes();
        entries.push((pk, 1u64));
        if witness {
            let tx = build_vote_tx(&key, pk, SLOT, bank_hash);
            votes.push(ingest_vote_transaction(&tx).expect("ingest self-built vote tx"));
        } else {
            votes.push(ValidatorVote::sign(&key, SLOT, bank_hash));
        }
    }
    let stake_table = EpochStakeTable::from_entries(EPOCH, entries);

    let proof = SolanaLockProof {
        lock_id,
        spl_mint: SPL_MINT,
        amount: AMOUNT,
        dregg_recipient: recipient,
        consensus: ConsensusEvidence {
            slot: SLOT,
            bank_hash,
            epoch: EPOCH,
            voted_stake: n as u128,
            total_stake: n as u128,
            votes,
            bank_components,
            poh: Some(PohSegment {
                anchor_hash: anchor,
                num_hashes: 64,
                tail_hash: tail,
            }),
        },
        inclusion: AccountInclusionProof {
            vault_account: vault,
            recorded_amount: AMOUNT,
            recorded_recipient: recipient,
            recorded_lock_id: lock_id,
            accounts_hash,
            merkle_path: vec![sib],
            mainnet: None,
        },
        stake_provenance: None,
    };
    (proof, stake_table)
}

fn bench_verify_by_votes(c: &mut Criterion) {
    let counts = [100usize, 500, 1500];

    let mut g = c.benchmark_group("solana_consensus_verify_placeholder");
    for &n in &counts {
        let (proof, table) = build_proof(n, false);
        // sanity: the proof must verify before we time it.
        assert!(
            verify_lock_proof_consensus(&proof, &SPL_MINT, 1, 1_000_000, &table, true).is_ok(),
            "placeholder proof of {n} votes must verify"
        );
        g.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, _| {
            b.iter(|| {
                black_box(
                    verify_lock_proof_consensus(&proof, &SPL_MINT, 1, 1_000_000, &table, true)
                        .is_ok(),
                )
            });
        });
    }
    g.finish();

    let mut g = c.benchmark_group("solana_consensus_verify_witness");
    for &n in &counts {
        let (proof, table) = build_proof(n, true);
        assert!(
            verify_lock_proof_consensus(&proof, &SPL_MINT, 1, 1_000_000, &table, true).is_ok(),
            "witness proof of {n} votes must verify"
        );
        g.bench_with_input(BenchmarkId::from_parameter(n), &n, |b, _| {
            b.iter(|| {
                black_box(
                    verify_lock_proof_consensus(&proof, &SPL_MINT, 1, 1_000_000, &table, true)
                        .is_ok(),
                )
            });
        });
    }
    g.finish();
}

criterion_group!(benches, bench_verify_by_votes);
criterion_main!(benches);
