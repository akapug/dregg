//! LIVE-BYZANTINE Attack 5b forge — the served state attestation has no deployed
//! committee binding (order is BFT-certified; state is not yet).
//!
//! The deployed cross-node committee quorum (`node::finalization_votes`) agrees
//! on block ORDER. The per-node `StoredAttestedRoot` binds the state `merkle_root`
//! but, in full mode, carries only the PRODUCING node's single `quorum_signatures`
//! entry (`blocklace_sync.rs:4589`). `GET /api/federation/roots` (`api.rs:4901`)
//! surfaces that root as `{ merkle_root, signatures: quorum_signatures.len() }` —
//! a COUNT, with no committee verification.
//!
//! This forge shows a single Byzantine node can present TWO conflicting state
//! roots for the SAME finalized block, each passing the count-only gate the API
//! serves, so a light client trusting that surface cannot arbitrate them — there
//! is no committee certificate over the state in the served root.
//!
//! It ALSO pins the in-flight fix (N3 committee-restart / Fix B): the new
//! `finalization_quorum` field + `verify_finalization_quorum` (which binds the
//! committee's v2 finalization votes OVER `(block_id, merkle_root)`) is the
//! discriminator — but the deployed producer does NOT yet back-fill it, so
//! `has_finalization_quorum()` is false on a live root. When that weld lands, a
//! light client gains a real committee state cert and this gap closes.
//!
//! Uses only `dregg_persist` re-exported types (no signing, no manifest edit) so
//! it never touches the actively-edited `persist/src/tests.rs`.
//!
//! See `docs/audit/LIVE-BYZANTINE.md` Attack 5b (and Attack 3 — the same weld).

use dregg_persist::StoredAttestedRoot;
use dregg_persist::federation::{FederationId, PublicKey, Signature};

/// A full-mode attested root as the deployed commit path persists it: bound to a
/// blocklace block + height, carrying a single (producer-local) `quorum_signatures`
/// entry, threshold 3 (the N3 committee shape), and — crucially — an EMPTY
/// `finalization_quorum` (the deployed producer does not yet back-fill the
/// cross-node committee votes).
fn full_mode_root(
    block_id: [u8; 32],
    merkle_root: [u8; 32],
    producer: PublicKey,
) -> StoredAttestedRoot {
    StoredAttestedRoot {
        merkle_root,
        note_tree_root: None,
        nullifier_set_root: None,
        height: 1,
        timestamp: 1_700_000_000,
        blocklace_block_id: Some(block_id),
        finality_round: Some(1),
        // Full mode pushes ONLY the local signature (1 < threshold 3).
        quorum_signatures: vec![(producer, Signature([0x01; 64]))],
        threshold_qc: None,
        threshold: 3,
        federation_id: FederationId::PLACEHOLDER,
        receipt_stream_root: None,
        // The deployed producer does not yet assemble this (Fix B, in flight).
        finalization_quorum: Vec::new(),
    }
}

/// A single Byzantine node signs two CONFLICTING state roots for the SAME
/// finalized block (same `blocklace_block_id`, same height, different
/// `merkle_root`). Both pass the count-only gate the API serves, and neither
/// carries a committee finalization quorum — so nothing in the served artifact
/// lets a light client tell the honest root from the forged one.
#[test]
fn byzantine_conflicting_state_roots_both_pass_count_only_gate() {
    let byz = PublicKey([0xBB; 32]);
    let block_id = [0xCD; 32];

    let honest = full_mode_root(block_id, [0xAA; 32], byz);
    let forged = full_mode_root(block_id, [0x00; 32], byz);

    // Same finalized block, CONFLICTING state.
    assert_eq!(honest.blocklace_block_id, forged.blocklace_block_id);
    assert_eq!(honest.height, forged.height);
    assert_ne!(honest.merkle_root, forged.merkle_root);

    // (1) The count-only gate the API's `signatures:` field reflects: a single
    // self-signature meets `is_structurally_complete()` only when threshold <= 1.
    // At the N3 threshold (3) a full-mode root is NOT structurally complete — the
    // count is 1. So a count-trusting consumer sees `signatures: 1` for BOTH
    // conflicting roots and has no committee evidence either way.
    assert_eq!(honest.quorum_signatures.len(), 1);
    assert_eq!(forged.quorum_signatures.len(), 1);
    assert!(!honest.is_structurally_complete());
    assert!(!forged.is_structurally_complete());

    // A Byzantine node CAN also declare threshold 1 (a self-federation) to make
    // its forged root `is_structurally_complete()` — the count gate cannot stop it.
    let forged_solo = StoredAttestedRoot {
        threshold: 1,
        ..forged.clone()
    };
    assert!(
        forged_solo.is_structurally_complete(),
        "count-only completeness cannot distinguish a forged solo-threshold root"
    );

    // (2) THE DEPLOYED GAP: neither served root carries a committee finalization
    // quorum over its state, so the Fix-B discriminator is simply absent — a
    // light client has NO committee certificate binding `merkle_root`.
    assert!(!honest.has_finalization_quorum());
    assert!(!forged.has_finalization_quorum());

    let committee = vec![PublicKey([1; 32]), PublicKey([2; 32]), PublicKey([3; 32])];
    assert!(
        !honest.verify_finalization_quorum(&committee),
        "an empty finalization_quorum cannot certify state (nothing to verify) — \
         the deployed producer does not back-fill it yet"
    );
    assert!(!forged.verify_finalization_quorum(&committee));
}

/// Pin the Fix-B gate's SOUNDNESS: `verify_finalization_quorum` is crypto-bound,
/// not a count — a Byzantine node cannot forge a state quorum by stuffing
/// `finalization_quorum` with junk signatures or non-committee keys. This is the
/// property the served root must eventually carry to close Attack 5b/3.
#[test]
fn finalization_quorum_rejects_forged_and_noncommittee_signatures() {
    let committee = vec![PublicKey([1; 32]), PublicKey([2; 32]), PublicKey([3; 32])];

    // A root claiming a 3-of-3 committee quorum, but every signature is junk.
    let mut root = full_mode_root([0xCD; 32], [0xAA; 32], PublicKey([1; 32]));
    root.finalization_quorum = committee
        .iter()
        .map(|pk| (*pk, Signature([0x00; 64])))
        .collect();
    assert!(root.has_finalization_quorum());
    assert!(
        !root.verify_finalization_quorum(&committee),
        "junk signatures over the (block_id, merkle_root) preimage must NOT certify — \
         the gate verifies Ed25519, it does not count entries"
    );

    // A quorum of NON-committee keys (a Sybil minting fresh keypairs) is rejected
    // even if it were to carry valid signatures: the keys are not in the committee.
    let outsiders = vec![PublicKey([9; 32]), PublicKey([8; 32]), PublicKey([7; 32])];
    let mut sybil = full_mode_root([0xCD; 32], [0xAA; 32], PublicKey([9; 32]));
    sybil.finalization_quorum = outsiders
        .iter()
        .map(|pk| (*pk, Signature([0x00; 64])))
        .collect();
    assert!(
        !sybil.verify_finalization_quorum(&committee),
        "non-committee signers cannot form a finalization quorum (Sybil rejected)"
    );

    // A sub-threshold count (below `threshold`) is rejected regardless of validity.
    let mut short = full_mode_root([0xCD; 32], [0xAA; 32], PublicKey([1; 32]));
    short.finalization_quorum = vec![(PublicKey([1; 32]), Signature([0x00; 64]))];
    assert!(!short.verify_finalization_quorum(&committee));
}
