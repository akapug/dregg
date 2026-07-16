//! **Adversarial canaries for the three Solana-bridge value-path holes**
//! (HORIZONLOG P1, flagged 2026-07-15). Written RED-FIRST: each test states the
//! attack, fails against the pre-fix tree, and goes green only when the hole is
//! actually closed.
//!
//! - **HOLE 1 — optimistic ≠ finalized.** The anchored value-release verifier
//!   tallied an exact-slot ≥2/3 supermajority only (optimistic-confirmation
//!   grade). Nothing verified the slot was ROOTED. Fix: value release also
//!   requires a ≥2/3 authorized-voter-bound *rooted* attestation — vote
//!   transactions whose tower `root ≥ slot`.
//! - **HOLE 2 — membership without completeness.** `derive_stake_table` proved
//!   each supplied stake account IS in the accounts hash but never that the
//!   supplied set is COMPLETE, so omitting stake accounts shrinks the 2/3
//!   denominator. Fix: a total-effective-stake floor cross-checked against the
//!   proven StakeHistory sysvar.
//! - **HOLE 3 — rotation not authorized-voter-bound.** `rotate` tallied with
//!   plain `verify_supermajority`, so a rotation witness could be signed by ANY
//!   key naming itself the vote authority. Fix: rotation tallies with
//!   `tally_authorized`.

use dregg_bridge::solana_consensus::BankHashComponents;
use dregg_bridge::solana_provenance::{
    ProvenAccount, ProvenanceError, RotationStep, STAKE_HISTORY_SYSVAR_ID, STAKE_PROGRAM_ID,
    SYSVAR_OWNER_ID, VerifiedStakeTable, WeakSubjectivityAnchor, derive_stake_table,
    fixtures as prov, rotate, vote_program_id,
};
use dregg_bridge::solana_trustless::{
    LockProofError, LockProofTrust, fixtures, verify_lock_proof_consensus_anchored,
    verify_lock_proof_consensus_anchored_optimistic,
};
use dregg_bridge::solana_wire::solana_account_hash;
use dregg_types::CellId;
use ed25519_dalek::SigningKey;

const DREGG_MINT: [u8; 32] = [0xABu8; 32];
const LOCK_PROGRAM: [u8; 32] = [0x07u8; 32];
const VAULT: [u8; 32] = [0x22u8; 32];
/// 400/400/200 stake: any two of the three clear 2/3; no single one does.
const CLUSTER: [(u8, u64); 3] = [(11, 400), (12, 400), (13, 200)];

fn cid(b: u8) -> CellId {
    CellId::from_bytes([b; 32])
}

// ===========================================================================
// A two-validator bank state WITH a live StakeHistory (700 + 300 = 1000, and
// the proven sysvar SAYS the cluster's effective stake is 1000) — the shape
// where the HOLE-2 completeness attack is visible.
// ===========================================================================

struct BankState {
    accounts_hash: [u8; 32],
    stake_accounts: Vec<ProvenAccount>,
    vote_accounts: Vec<ProvenAccount>,
    stake_history: ProvenAccount,
}

const VA1: [u8; 32] = [0xA1u8; 32];
const VA2: [u8; 32] = [0xA2u8; 32];

fn a1() -> SigningKey {
    prov::sk(11)
}
fn a2() -> SigningKey {
    prov::sk(12)
}

/// Bank state at `epoch`: va1 delegated 700, va2 delegated 300 (both fully
/// warmed — activation epoch 0 predates the bounded history), authorized voters
/// a1/a2, and the StakeHistory sysvar recording the cluster's effective stake as
/// `history_effective` at `epoch`.
fn bank_state(epoch: u64, history_effective: u64) -> BankState {
    let vote_program = vote_program_id();
    let vd1 = prov::build_vote_account_data(&[0x01u8; 32], &a1().verifying_key().to_bytes(), epoch);
    let vd2 = prov::build_vote_account_data(&[0x02u8; 32], &a2().verifying_key().to_bytes(), epoch);
    let sd1 = prov::build_stake_account_data(&VA1, 700, 0, u64::MAX);
    let sd2 = prov::build_stake_account_data(&VA2, 300, 0, u64::MAX);
    let shd = prov::encode_stake_history_data(&[(epoch, history_effective, 0, 0)]);
    let sa1 = [0x51u8; 32];
    let sa2 = [0x52u8; 32];

    let leaves = [
        solana_account_hash(1_000_000, &vote_program, false, 0, &vd1, &VA1),
        solana_account_hash(1_000_000, &vote_program, false, 0, &vd2, &VA2),
        solana_account_hash(1_000_000, &STAKE_PROGRAM_ID, false, 0, &sd1, &sa1),
        solana_account_hash(1_000_000, &STAKE_PROGRAM_ID, false, 0, &sd2, &sa2),
        solana_account_hash(
            1_000_000,
            &SYSVAR_OWNER_ID,
            false,
            0,
            &shd,
            &STAKE_HISTORY_SYSVAR_ID,
        ),
    ];
    let (accounts_hash, proofs) = prov::single_chunk(&leaves);
    BankState {
        accounts_hash,
        vote_accounts: vec![
            prov::proven_account(VA1, vote_program, vd1, proofs[0].clone()),
            prov::proven_account(VA2, vote_program, vd2, proofs[1].clone()),
        ],
        stake_accounts: vec![
            prov::proven_account(sa1, STAKE_PROGRAM_ID, sd1, proofs[2].clone()),
            prov::proven_account(sa2, STAKE_PROGRAM_ID, sd2, proofs[3].clone()),
        ],
        stake_history: prov::proven_account(
            STAKE_HISTORY_SYSVAR_ID,
            SYSVAR_OWNER_ID,
            shd,
            proofs[4].clone(),
        ),
    }
}

/// The trusted table at the anchor epoch (full honest derivation).
fn anchored_current(epoch: u64) -> (VerifiedStakeTable, BankState) {
    let bs = bank_state(epoch, 1000);
    let derived = derive_stake_table(
        epoch,
        &bs.accounts_hash,
        &bs.stake_accounts,
        &bs.vote_accounts,
        &bs.stake_history,
        None,
    )
    .expect("full honest derivation clears the history floor");
    let anchor = WeakSubjectivityAnchor::from_table(&derived.table);
    let current = VerifiedStakeTable::from_anchor(
        &anchor,
        &bs.accounts_hash,
        &bs.stake_accounts,
        &bs.vote_accounts,
        &bs.stake_history,
        None,
    )
    .expect("anchor admits its own derivation");
    (current, bs)
}

/// A rotation step to `next` whose bank state is `bs` (epoch `next`), attested
/// by `votes`, but SUPPLYING only the given subset of stake accounts.
fn step_with(
    next: u64,
    bs: &BankState,
    stake_accounts: Vec<ProvenAccount>,
    votes: Vec<dregg_bridge::solana_consensus::ValidatorVote>,
    bank_components: BankHashComponents,
    bank_hash: [u8; 32],
    slot: u64,
) -> RotationStep {
    RotationStep {
        to_epoch: next,
        slot,
        bank_hash,
        bank_components,
        votes,
        accounts_hash: bs.accounts_hash,
        stake_accounts,
        vote_accounts: bs.vote_accounts.clone(),
        stake_history_account: bs.stake_history.clone(),
        new_rate_activation_epoch: None,
    }
}

fn components_for(bs: &BankState) -> (BankHashComponents, [u8; 32]) {
    let bank_components = BankHashComponents {
        parent_bank_hash: [0x01; 32],
        accounts_hash: bs.accounts_hash,
        signature_count: 1,
        last_blockhash: [0x02; 32],
    };
    let bank_hash = bank_components.compute();
    (bank_components, bank_hash)
}

// ===========================================================================
// HOLE 1 — value release on optimistic confirmation only
// ===========================================================================

/// ATTACK: a proof carrying ONLY the exact-slot ≥2/3 supermajority (optimistic
/// confirmation — what a validator set can produce for a slot that later gets
/// abandoned without any lockout violation reaching the tally) must NOT release
/// value. The value-release verifier must demand a rooted attestation.
#[test]
fn hole1_exact_slot_supermajority_alone_does_not_release_value() {
    let (mut proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        1,
        &CLUSTER,
    );
    // Strip every rooted attestation, keeping the full exact-slot supermajority
    // (pre-fix the fixture carries none, so this is the pre-fix proof verbatim).
    let slot = proof.consensus.slot;
    proof.consensus.votes.retain(|v| v.slot == slot);

    let res = verify_lock_proof_consensus_anchored(
        &proof,
        &DREGG_MINT,
        1,
        1_000_000,
        &anchor,
        true,
        Some(&policy),
    );
    assert!(
        matches!(res, Err(LockProofError::SlotNotRooted { .. })),
        "HOLE 1 OPEN: exact-slot supermajority (optimistic-confirmation grade) \
         released value with no rooted attestation — got {res:?}"
    );
}

/// Honest polarity: the same lock WITH a ≥2/3 authorized-voter-bound rooted
/// attestation (tower `root ≥ slot`) is CONSENSUS-VERIFIED.
#[test]
fn hole1_rooted_lock_verifies() {
    let (proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        2,
        &CLUSTER,
    );
    let trust = verify_lock_proof_consensus_anchored(
        &proof,
        &DREGG_MINT,
        1,
        1_000_000,
        &anchor,
        true,
        Some(&policy),
    )
    .expect("a rooted ≥2/3 lock proof verifies");
    assert_eq!(trust, LockProofTrust::ConsensusVerified);
}

/// A rooted attestation whose towers root BELOW the lock slot is not a rooted
/// attestation OF the lock slot.
#[test]
fn hole1_root_below_slot_refused() {
    let (mut proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        3,
        &CLUSTER,
    );
    let slot = proof.consensus.slot;
    // Replace the rooted attestation with towers rooting slot-1 (still signed by
    // the genuine authorized voters).
    proof.consensus.votes.retain(|v| v.slot == slot);
    for (seed, _) in CLUSTER {
        proof.consensus.votes.push(prov::tower_sync_tx_rooted(
            &prov::sk(seed),
            &[seed ^ 0xA5; 32],
            slot + 32,
            [0x66u8; 32],
            slot - 1,
        ));
    }
    let res = verify_lock_proof_consensus_anchored(
        &proof,
        &DREGG_MINT,
        1,
        1_000_000,
        &anchor,
        true,
        Some(&policy),
    );
    assert!(
        matches!(res, Err(LockProofError::SlotNotRooted { .. })),
        "towers rooting below the lock slot must not count as a rooted \
         attestation — got {res:?}"
    );
}

/// A rooted attestation signed by imposters (not the on-chain authorized
/// voters) contributes zero rooted stake.
#[test]
fn hole1_imposter_rooted_attestation_refused() {
    let (mut proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        4,
        &CLUSTER,
    );
    let slot = proof.consensus.slot;
    proof.consensus.votes.retain(|v| v.slot == slot);
    for (seed, _) in CLUSTER {
        // The imposter names ITSELF the vote authority for the victim's vote
        // account and signs genuinely — pass-2's forgery shape.
        proof.consensus.votes.push(prov::tower_sync_tx_rooted(
            &prov::sk(seed ^ 0x77),
            &[seed ^ 0xA5; 32],
            slot + 32,
            [0x66u8; 32],
            slot,
        ));
    }
    let res = verify_lock_proof_consensus_anchored(
        &proof,
        &DREGG_MINT,
        1,
        1_000_000,
        &anchor,
        true,
        Some(&policy),
    );
    assert!(
        matches!(res, Err(LockProofError::SlotNotRooted { .. })),
        "imposter-signed rooted attestations must contribute zero rooted stake \
         — got {res:?}"
    );
}

/// The exact-slot-only grade still exists — but only under its honest name.
#[test]
fn hole1_optimistic_path_is_explicitly_named() {
    let (mut proof, anchor, policy) = fixtures::anchored_lock_with_cluster(
        &DREGG_MINT,
        &LOCK_PROGRAM,
        VAULT,
        cid(1),
        500,
        5,
        &CLUSTER,
    );
    let slot = proof.consensus.slot;
    proof.consensus.votes.retain(|v| v.slot == slot);
    let trust = verify_lock_proof_consensus_anchored_optimistic(
        &proof,
        &DREGG_MINT,
        1,
        1_000_000,
        &anchor,
        true,
        Some(&policy),
    )
    .expect("the explicitly-optimistic path accepts an exact-slot supermajority");
    assert_eq!(trust, LockProofTrust::ConsensusVerified);
}

// ===========================================================================
// HOLE 2 — stake-set completeness (the shrunken denominator)
// ===========================================================================

/// ATTACK: a rotation step whose bank state genuinely commits 1000 effective
/// stake (the proven StakeHistory sysvar says so) but which SUPPLIES only the
/// 300-stake minority's stake account. Pre-fix the derived table's 2/3
/// denominator becomes 300, so the minority alone "clears" every later
/// supermajority.
#[test]
fn hole2_omitted_stake_accounts_cannot_shrink_the_denominator() {
    let (current, _bs42) = anchored_current(42);
    let bs43 = bank_state(43, 1000);
    let (bank_components, bank_hash) = components_for(&bs43);
    let slot = 5_000u64;
    // Honestly attested by the trusted epoch's ≥2/3 (both validators).
    let votes = vec![
        prov::tower_sync_tx(&a1(), &VA1, slot, bank_hash),
        prov::tower_sync_tx(&a2(), &VA2, slot, bank_hash),
    ];
    // ... but the step supplies ONLY the minority's stake account.
    let step = step_with(
        43,
        &bs43,
        vec![bs43.stake_accounts[1].clone()], // va2's 300 only
        votes,
        bank_components,
        bank_hash,
        slot,
    );
    let res = rotate(&current, &step);
    assert!(
        matches!(
            res,
            Err(ProvenanceError::StakeBelowHistoryFloor {
                supplied: 300,
                floor: 1000
            })
        ),
        "HOLE 2 OPEN: omitting stake accounts shrank the 2/3 denominator to the \
         supplied minority — got {res:?}"
    );
}

/// Honest polarity: the same rotation step with the COMPLETE stake set clears
/// the history floor and rotates.
#[test]
fn hole2_complete_stake_set_rotates() {
    let (current, _bs42) = anchored_current(42);
    let bs43 = bank_state(43, 1000);
    let (bank_components, bank_hash) = components_for(&bs43);
    let slot = 5_000u64;
    let votes = vec![
        prov::tower_sync_tx(&a1(), &VA1, slot, bank_hash),
        prov::tower_sync_tx(&a2(), &VA2, slot, bank_hash),
    ];
    let step = step_with(
        43,
        &bs43,
        bs43.stake_accounts.clone(),
        votes,
        bank_components,
        bank_hash,
        slot,
    );
    let rotated = rotate(&current, &step).expect("complete stake set clears the history floor");
    assert_eq!(rotated.epoch(), 43);
    assert_eq!(rotated.table().total_stake(), 1000);
}

/// The floor also guards the direct derivation (the anchor/feed path): a
/// supplied set summing below the proven cluster effective stake is refused.
#[test]
fn hole2_direct_derivation_below_floor_refused() {
    let bs = bank_state(42, 1000);
    let res = derive_stake_table(
        42,
        &bs.accounts_hash,
        &bs.stake_accounts[..1], // va1's 700 only, floor says 1000
        &bs.vote_accounts,
        &bs.stake_history,
        None,
    );
    assert!(
        matches!(
            res,
            Err(ProvenanceError::StakeBelowHistoryFloor {
                supplied: 700,
                floor: 1000
            })
        ),
        "HOLE 2 OPEN: direct derivation accepted an incomplete stake set — got {res:?}"
    );
}

// ===========================================================================
// HOLE 3 — rotation witness not bound to the authorized voter
// ===========================================================================

/// ATTACK: the rotation attestation votes are real, genuinely-signed vote
/// transactions — but signed by imposter keys that name THEMSELVES the vote
/// authority for the trusted validators' vote accounts. Pre-fix, the plain
/// `verify_supermajority` tally counted them at the vote accounts' full stake.
#[test]
fn hole3_rotation_witness_must_bind_the_authorized_voter() {
    let (current, _bs42) = anchored_current(42);
    let bs43 = bank_state(43, 1000);
    let (bank_components, bank_hash) = components_for(&bs43);
    let slot = 5_000u64;
    let imposter1 = prov::sk(91);
    let imposter2 = prov::sk(92);
    let votes = vec![
        prov::tower_sync_tx(&imposter1, &VA1, slot, bank_hash),
        prov::tower_sync_tx(&imposter2, &VA2, slot, bank_hash),
    ];
    let step = step_with(
        43,
        &bs43,
        bs43.stake_accounts.clone(),
        votes,
        bank_components,
        bank_hash,
        slot,
    );
    let res = rotate(&current, &step);
    assert!(
        matches!(res, Err(ProvenanceError::RotationNotAttested)),
        "HOLE 3 OPEN: rotation accepted witness votes not signed by the \
         on-chain authorized voters — got {res:?}"
    );
}

// (Honest polarity for HOLE 3 is `hole2_complete_stake_set_rotates` above:
// the same rotation attested by the genuine authorized voters is accepted.)
