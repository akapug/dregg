//! The `HybridPq` quorum wired into the consensus path — STAGED, OFF BY
//! DEFAULT.
//!
//! Classical half = the EXISTING ed25519 `votes` quorum (unchanged);
//! post-quantum half = per-member FIPS 204 ML-DSA-65 signatures over the SAME
//! canonical vote message. These tests cover:
//!
//! * DEFAULT (flag off, no ML-DSA keys): the default committee finalizes on
//!   the untouched path, produces no hybrid artifacts, and the pre-existing
//!   wire discriminants are pinned byte-for-byte.
//! * HYBRID ENABLED: a committee with ML-DSA keys finalizes; the certificate
//!   verifies via `HybridQuorumCertificate::verify_with_keys` AND via the
//!   `QuorumScheme::HybridVotes` selector over opaque bytes; a missing or
//!   forged ML-DSA signature is rejected — at collection time and at
//!   certificate-verification time.
//! * FAIL-CLOSED: flag ON with an incomplete PQ key table refuses to
//!   finalize (never a silent classical downgrade).

use dregg_federation::frost::{MlDsaSigningKey, QuorumScheme, verify_pq_quorum_half};
use dregg_federation::{
    ConsensusConfig, ConsensusMessage, ConsensusState, HybridQuorumCertificate, MorpheusFederation,
    QuorumCertificate, RevocationBlock, Vote, generate_keypair, sign,
};

// =============================================================================
// DEFAULT PATH — flag off, byte-identical wire
// =============================================================================

#[test]
fn default_committee_finalizes_with_no_hybrid_artifacts() {
    let mut fed = MorpheusFederation::new(&["alpha", "beta", "gamma", "delta"]);
    assert!(!fed.config.hybrid_pq);
    assert!(!fed.config.hybrid_pq_active());
    assert!(fed.config.ml_dsa_members.is_empty());

    fed.submit_revocation(0, "token-default-1");
    let (block, qc) = fed.run_consensus_round().expect("default round finalizes");
    assert_eq!(block.height, 1);
    assert!(qc.votes.len() >= qc.threshold);

    // The default path produced NO hybrid state anywhere.
    assert!(fed.last_hybrid_qc.is_none());
    for state in &fed.consensus_states {
        assert!(state.ml_dsa_signing_key.is_none());
        assert!(state.collected_pq_sigs.is_empty());
    }
}

/// Pin the postcard wire encoding of the DEFAULT path: `Vote`'s byte length
/// (proves no field was added to the vote that crosses the TCP transport) and
/// the enum discriminants of every pre-existing `ConsensusMessage` variant
/// (proves the hybrid variants were APPENDED, not interleaved).
#[test]
fn default_wire_bytes_are_pinned() {
    let (sk, _pk) = generate_keypair();
    let vote_message = QuorumCertificate::vote_message(&[7u8; 32], 1, 1);
    let vote = Vote {
        block_hash: [7u8; 32],
        height: 1,
        view: 1,
        voter: 0,
        signature: sign(&sk, &vote_message),
    };

    // Vote: 32 (block_hash array) + 1 (height varint) + 1 (view varint)
    //     + 1 (voter varint) + 65 (Signature: len-prefixed 64-byte seq)
    //     = 100 bytes, exactly as before the hybrid landed. A new field
    //     would change this length.
    let vote_bytes = postcard::to_stdvec(&vote).unwrap();
    assert_eq!(vote_bytes.len(), 100, "Vote wire shape must be unchanged");

    // ConsensusMessage discriminants (postcard varint tags): the historical
    // variants keep their positions; the hybrid ones are strictly after.
    let vote_msg = postcard::to_stdvec(&ConsensusMessage::VoteMsg(vote.clone())).unwrap();
    assert_eq!(vote_msg[0], 1, "VoteMsg discriminant must stay 1");
    assert_eq!(
        &vote_msg[1..],
        &vote_bytes[..],
        "VoteMsg payload must be exactly the unchanged Vote bytes"
    );
    let get_root = postcard::to_stdvec(&ConsensusMessage::GetAttestedRoot).unwrap();
    assert_eq!(
        get_root,
        vec![4],
        "GetAttestedRoot discriminant must stay 4"
    );
    let view_change = postcard::to_stdvec(&ConsensusMessage::ViewChange(
        dregg_federation::ViewChangeMessage {
            new_view: 2,
            height: 1,
            voter: 0,
            signature: sign(&sk, b"vc"),
        },
    ))
    .unwrap();
    assert_eq!(view_change[0], 6, "ViewChange discriminant must stay 6");

    // The appended hybrid variants sit AFTER every historical one.
    let hybrid_vote = postcard::to_stdvec(&ConsensusMessage::HybridVoteMsg(
        dregg_federation::HybridVote {
            vote,
            pq_signature: vec![0u8; 4],
        },
    ))
    .unwrap();
    assert_eq!(hybrid_vote[0], 7, "HybridVoteMsg is appended at 7");
}

// =============================================================================
// HYBRID ENABLED — finalizes, verifies, rejects forgery
// =============================================================================

fn hybrid_federation() -> MorpheusFederation {
    MorpheusFederation::new_hybrid_pq(&["alpha", "beta", "gamma", "delta"])
        .expect("hybrid federation constructs")
}

#[test]
fn hybrid_committee_finalizes_and_qc_verifies_both_halves() {
    let mut fed = hybrid_federation();
    assert!(fed.config.hybrid_pq);
    assert!(fed.config.hybrid_pq_active());

    fed.submit_revocation(0, "token-hybrid-1");
    let (block, qc) = fed.run_consensus_round().expect("hybrid round finalizes");
    assert_eq!(block.height, 1);

    let hqc = fed.last_hybrid_qc.clone().expect("hybrid QC recorded");
    assert_eq!(hqc.qc.block_hash, qc.block_hash);
    assert_eq!(hqc.pq_sigs.len(), hqc.qc.votes.len());
    assert!(hqc.pq_sigs.len() >= fed.config.threshold);

    // Full hybrid verification: classical ∧ pq.
    assert!(hqc.verify_with_keys(&fed.config.members, &fed.config.ml_dsa_members));

    // The PQ half alone also verifies via the factored frost verifier.
    let message = QuorumCertificate::vote_message(&hqc.qc.block_hash, hqc.qc.height, hqc.qc.view);
    assert!(verify_pq_quorum_half(
        &fed.config.ml_dsa_members,
        &message,
        &hqc.pq_sigs,
        fed.config.threshold,
    ));

    // …and via the scheme selector over the opaque-bytes seam.
    let opaque = hqc.to_bytes();
    let scheme = QuorumScheme::HybridVotes {
        members: &fed.config.members,
        ml_dsa_pubkeys: &fed.config.ml_dsa_members,
    };
    assert!(scheme.verify_opaque_qc(&opaque, &message));
    assert!(!scheme.verify_opaque_qc(&opaque, b"some other message"));

    // Round trip through the opaque bytes.
    let hqc2 = HybridQuorumCertificate::from_bytes(&opaque).unwrap();
    assert!(hqc2.verify_with_keys(&fed.config.members, &fed.config.ml_dsa_members));

    // The classical projection is exactly today's QC and still verifies on
    // today's path.
    assert!(hqc.qc.verify_with_keys(&fed.config.members));

    // Attested roots were updated as on the default path.
    for node in &fed.nodes {
        assert!(node.get_attested_root().is_some());
    }
}

#[test]
fn hybrid_missing_or_forged_ml_dsa_sig_is_rejected_at_verification() {
    let mut fed = hybrid_federation();
    fed.submit_revocation(1, "token-hybrid-2");
    fed.run_consensus_round().expect("hybrid round finalizes");
    let hqc = fed.last_hybrid_qc.clone().unwrap();
    let members = &fed.config.members;
    let pq = &fed.config.ml_dsa_members;
    assert!(hqc.verify_with_keys(members, pq));

    // FORGED: one flipped byte in one ML-DSA signature.
    let mut forged = hqc.clone();
    forged.pq_sigs[1].1[100] ^= 0x01;
    assert!(!forged.verify_with_keys(members, pq));

    // MISSING: dropping one PQ signature breaks the voter↔signer binding
    // (and, below threshold, the count too).
    let mut missing = hqc.clone();
    missing.pq_sigs.pop();
    assert!(!missing.verify_with_keys(members, pq));

    // SUBSTITUTED: a signature moved to another member's slot.
    let mut swapped = hqc.clone();
    swapped.pq_sigs.swap(0, 1);
    let (i0, s0) = swapped.pq_sigs[0].clone();
    let (i1, s1) = swapped.pq_sigs[1].clone();
    swapped.pq_sigs[0] = (i0, s1);
    swapped.pq_sigs[1] = (i1, s0);
    assert!(!swapped.verify_with_keys(members, pq));

    // The selector rejects all of them too.
    let message = QuorumCertificate::vote_message(&hqc.qc.block_hash, hqc.qc.height, hqc.qc.view);
    let scheme = QuorumScheme::HybridVotes {
        members,
        ml_dsa_pubkeys: pq,
    };
    for bad in [&forged, &missing, &swapped] {
        assert!(!scheme.verify_opaque_qc(&bad.to_bytes(), &message));
    }
}

#[test]
fn hybrid_forged_vote_is_refused_at_collection() {
    // Drive the states directly: a voter whose ML-DSA signature is tampered
    // must not be counted toward the quorum.
    let n = 4usize;
    let keypairs: Vec<_> = (0..n).map(|_| generate_keypair()).collect();
    let members: Vec<_> = keypairs.iter().map(|(_, pk)| *pk).collect();
    let ml_dsa: Vec<(_, _)> = (0..n)
        .map(|i| {
            let mut seed = [0u8; 32];
            seed[0] = 0x42;
            seed[1] = i as u8;
            MlDsaSigningKey::from_seed(&seed)
        })
        .collect();
    let config =
        ConsensusConfig::genesis_hybrid(members, ml_dsa.iter().map(|(pk, _)| pk.clone()).collect())
            .unwrap();

    let mut states: Vec<ConsensusState> = (0..n)
        .map(|i| {
            ConsensusState::new(i, keypairs[i].0.clone(), config.clone())
                .with_ml_dsa_key(ml_dsa[i].1.clone())
        })
        .collect();

    // Leader for view 1 is node 1.
    let leader = config.leader_for_view(1);
    states[leader].submit_revocation(dregg_federation::RevocationEvent {
        token_id: "tok".into(),
        authority_id: leader,
        signature: sign(&keypairs[leader].0, b"revoke:tok"),
    });
    let proposal: RevocationBlock = states[leader].create_proposal().unwrap();

    // An honest hybrid vote from node 0 is collected…
    let honest = states[0].vote_on_proposal_hybrid(&proposal).unwrap();
    let leader_state = &mut states[leader];
    leader_state.current_proposal = Some(proposal.clone());
    assert!(leader_state.collect_hybrid_vote(honest).is_none()); // below threshold
    assert_eq!(leader_state.collected_votes.len(), 1);
    assert_eq!(leader_state.collected_pq_sigs.len(), 1);

    // …but node 2's vote with a FORGED PQ half is refused outright: neither
    // the ed25519 vote nor the PQ signature is counted.
    let mut forged = states[2].vote_on_proposal_hybrid(&proposal).unwrap();
    forged.pq_signature[64] ^= 0xff;
    let leader_state = &mut states[leader];
    assert!(leader_state.collect_hybrid_vote(forged).is_none());
    assert_eq!(leader_state.collected_votes.len(), 1);
    assert_eq!(leader_state.collected_pq_sigs.len(), 1);

    // A vote with NO valid PQ half cannot enter through the classical door
    // either — the hybrid collector is the only door this committee opens.
    let classical_only = states[3].vote_on_proposal(&proposal).unwrap();
    let leader_state = &mut states[leader];
    assert!(
        leader_state
            .collect_hybrid_vote(dregg_federation::HybridVote {
                vote: classical_only,
                pq_signature: vec![0u8; 16],
            })
            .is_none()
    );
    assert_eq!(leader_state.collected_votes.len(), 1);
}

// =============================================================================
// FAIL-CLOSED — flag on, keys missing
// =============================================================================

#[test]
fn hybrid_flag_with_incomplete_keys_fails_closed() {
    let mut fed = MorpheusFederation::new(&["alpha", "beta", "gamma", "delta"]);
    fed.submit_revocation(0, "token-failclosed");

    // Misconfiguration: the flag is ON but no PQ key table exists.
    fed.config.hybrid_pq = true;
    fed.orchestrator.config.hybrid_pq = true;
    for state in &mut fed.consensus_states {
        state.config.hybrid_pq = true;
    }

    // The consensus path refuses to finalize (no silent classical fallback).
    assert!(fed.run_consensus_round().is_none());
    assert!(fed.last_hybrid_qc.is_none());
    assert!(fed.finalized_history.is_empty());
}

#[test]
fn genesis_hybrid_refuses_misaligned_key_tables() {
    let members: Vec<_> = (0..3).map(|_| generate_keypair().1).collect();
    let (pq_pk, _) = MlDsaSigningKey::from_seed(&[9u8; 32]);
    // 3 members, 1 PQ key: not a hybrid committee.
    assert!(ConsensusConfig::genesis_hybrid(members.clone(), vec![pq_pk.clone()]).is_none());
    // Empty member set: refused.
    assert!(ConsensusConfig::genesis_hybrid(Vec::new(), Vec::new()).is_none());
    // Aligned: accepted, flag on, active.
    let aligned =
        ConsensusConfig::genesis_hybrid(members, vec![pq_pk.clone(), pq_pk.clone(), pq_pk])
            .unwrap();
    assert!(aligned.hybrid_pq);
    assert!(aligned.hybrid_pq_active());
}
