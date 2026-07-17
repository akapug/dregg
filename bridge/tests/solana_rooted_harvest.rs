//! `solana_rooted_harvest`: the **rooted-attestation harvester** (Track A, rung 1)
//! drives the value-release entry to `ConsensusVerified` from a NON-fixture rooted
//! vote set — and, with the harvest withheld, the same proof fails closed at
//! `SlotNotRooted`, proving the finality leg is load-bearing.
//!
//! This is the in-process gate for the harvester seam
//! ([`dregg_bridge::solana_feed::VoteHarvester`] / [`LedgerVoteHarvester`]). It
//! needs no validator: the `SOLANA_LOCAL=1`-gated `solana_local_e2e` test exercises
//! the same seam over a real `solana-test-validator`. Here the exact-slot "which
//! bank hash" super-majority is the fixture cluster's, while the rooted-finality
//! votes come from the HARVESTER (not the fixture's baked-in rooted votes), so the
//! polarity tests bind exactly the leg rung 1 makes real:
//! [`verify_lock_proof_consensus_anchored`] demands `tally_authorized_rooted`, which
//! only the harvested `root >= slot` votes satisfy.

use dregg_bridge::solana_consensus::ValidatorVote;
use dregg_bridge::solana_feed::{HarvestableVoter, LedgerVoteHarvester, VoteHarvester};
use dregg_bridge::solana_provenance::fixtures as prov;
use dregg_bridge::solana_trustless::{
    LockProofError, LockProofTrust, SolanaLockProof, fixtures::anchored_lock_with_cluster,
    verify_lock_proof_consensus_anchored,
};
use dregg_types::CellId;

const MINT: [u8; 32] = [0xD6u8; 32];
const LOCK_PROGRAM: [u8; 32] = [0x71u8; 32];
const VAULT: [u8; 32] = [0x7Au8; 32];
const AMOUNT: u64 = 500_000;

/// The fixture cluster's per-validator identities: authority `prov::sk(seed)`,
/// vote account `[seed ^ 0xA5; 32]` (the derivation `anchored_lock_with_cluster`
/// uses). These are the keys the harvester signs with.
fn voter(seed: u8) -> HarvestableVoter {
    HarvestableVoter {
        vote_authority: prov::sk(seed),
        vote_account: [seed ^ 0xA5; 32],
    }
}

/// Rebuild the exact-slot ("which bank hash") votes for the cluster — the same
/// `root = None` votes the fixture builds — so a test can substitute its OWN
/// rooted-vote set (from the harvester) for the fixture's baked-in one.
fn exact_slot_votes(
    validators: &[(u8, u64)],
    slot: u64,
    bank_hash: [u8; 32],
) -> Vec<ValidatorVote> {
    validators
        .iter()
        .map(|(seed, _)| {
            prov::tower_sync_tx(&prov::sk(*seed), &[*seed ^ 0xA5; 32], slot, bank_hash)
        })
        .collect()
}

fn a_lock(
    validators: &[(u8, u64)],
) -> (
    SolanaLockProof,
    dregg_bridge::solana_provenance::WeakSubjectivityAnchor,
    dregg_bridge::solana_consensus::PohAnchorPolicy,
) {
    anchored_lock_with_cluster(
        &MINT,
        &LOCK_PROGRAM,
        VAULT,
        CellId::from_bytes([0x11u8; 32]),
        AMOUNT,
        0x42,
        validators,
    )
}

/// POSITIVE: a genuinely-rooted attestation set from the HARVESTER drives the
/// anchored value-release entry to `ConsensusVerified`. The rooted votes are the
/// harvester's, not the fixture's — proving the seam supplies real finality.
#[test]
fn harvested_rooted_votes_release_value() {
    let validators = [(1u8, 700u64), (2, 200), (3, 100)];
    let (mut proof, anchor, policy) = a_lock(&validators);
    let slot = proof.consensus.slot;
    let bank_hash = proof.consensus.bank_hash;

    // Exact-slot super-majority (fixture cluster) + rooted votes FROM THE HARVESTER.
    let harvester = LedgerVoteHarvester::new(validators.iter().map(|(s, _)| voter(*s)).collect());
    let mut votes = exact_slot_votes(&validators, slot, bank_hash);
    votes.extend(
        harvester
            .harvest_rooted(slot)
            .expect("harvest rooted votes"),
    );
    proof.consensus.votes = votes;

    let trust = verify_lock_proof_consensus_anchored(
        &proof,
        &MINT,
        1,
        u64::MAX,
        &anchor,
        true,
        Some(&policy),
    )
    .expect("harvested rooted evidence releases value");
    assert_eq!(trust, LockProofTrust::ConsensusVerified);
}

/// NEGATIVE (the leg is load-bearing): the SAME proof with the rooted votes
/// WITHHELD — only the exact-slot optimistic-confirmation votes — is refused with
/// `SlotNotRooted`. The exact-slot super-majority alone cannot release value.
#[test]
fn exact_slot_only_refuses_slot_not_rooted() {
    let validators = [(1u8, 700u64), (2, 200), (3, 100)];
    let (mut proof, anchor, policy) = a_lock(&validators);
    let slot = proof.consensus.slot;
    let bank_hash = proof.consensus.bank_hash;

    proof.consensus.votes = exact_slot_votes(&validators, slot, bank_hash);

    let err = verify_lock_proof_consensus_anchored(
        &proof,
        &MINT,
        1,
        u64::MAX,
        &anchor,
        true,
        Some(&policy),
    )
    .expect_err("an exact-slot-only (unrooted) vote set must be refused");
    assert!(
        matches!(err, LockProofError::SlotNotRooted { .. }),
        "want SlotNotRooted, got {err:?}"
    );
}

/// ADVERSARIAL: a rooted set below the 2/3 finality threshold is refused. The
/// exact-slot super-majority still clears (all validators vote the bank hash), but
/// only a <2/3 minority roots the slot.
#[test]
fn rooted_below_supermajority_refuses() {
    // Even stakes so no single validator is a super-majority: 1/3 each.
    let validators = [(1u8, 100u64), (2, 100), (3, 100)];
    let (mut proof, anchor, policy) = a_lock(&validators);
    let slot = proof.consensus.slot;
    let bank_hash = proof.consensus.bank_hash;

    // All three vote the bank hash (which-bank clears); only validator 1 (100/300
    // < 2/3) submits a rooted attestation.
    let mut votes = exact_slot_votes(&validators, slot, bank_hash);
    let partial = LedgerVoteHarvester::new(vec![voter(1)]);
    votes.extend(partial.harvest_rooted(slot).expect("harvest rooted votes"));
    proof.consensus.votes = votes;

    let err = verify_lock_proof_consensus_anchored(
        &proof,
        &MINT,
        1,
        u64::MAX,
        &anchor,
        true,
        Some(&policy),
    )
    .expect_err("a <2/3 rooted minority must be refused");
    match err {
        LockProofError::SlotNotRooted { rooted, total } => {
            assert_eq!(rooted, 100, "only validator 1's stake roots the slot");
            assert_eq!(total, 300, "the full cluster is the 2/3 denominator");
        }
        other => panic!("want SlotNotRooted, got {other:?}"),
    }
}

/// ADVERSARIAL: an IMPOSTER-signed rooted vote (signer is not the vote account's
/// on-chain authorized voter) contributes zero rooted stake — the slot is not
/// rooted, value is not released.
#[test]
fn imposter_rooted_vote_refuses() {
    let validators = [(1u8, 100u64), (2, 100), (3, 100)];
    let (mut proof, anchor, policy) = a_lock(&validators);
    let slot = proof.consensus.slot;
    let bank_hash = proof.consensus.bank_hash;

    // All three exact-slot votes clear the which-bank leg. The rooted vote is for
    // validator 1's vote ACCOUNT but signed by stranger key sk(9), which is NOT
    // that account's on-chain authorized voter — so the rooted tally ignores it.
    let mut votes = exact_slot_votes(&validators, slot, bank_hash);
    let imposter = HarvestableVoter {
        vote_authority: prov::sk(9),
        vote_account: [1u8 ^ 0xA5; 32],
    };
    votes.extend(
        LedgerVoteHarvester::new(vec![imposter])
            .harvest_rooted(slot)
            .expect("harvest rooted votes"),
    );
    proof.consensus.votes = votes;

    let err = verify_lock_proof_consensus_anchored(
        &proof,
        &MINT,
        1,
        u64::MAX,
        &anchor,
        true,
        Some(&policy),
    )
    .expect_err("an imposter-signed rooted vote must be refused");
    match err {
        LockProofError::SlotNotRooted { rooted, .. } => {
            assert_eq!(rooted, 0, "an imposter contributes no rooted stake");
        }
        other => panic!("want SlotNotRooted, got {other:?}"),
    }
}
