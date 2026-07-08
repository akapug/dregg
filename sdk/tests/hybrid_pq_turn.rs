//! HYBRID (ed25519 + ML-DSA-65) turn perimeter — the SDK signing side
//! (`dregg_turn::pq`). The client (cipherclerk) always signs BOTH halves over
//! the SAME canonical message; the verifier gates the PQ half (staged). These
//! integration tests pin that the cipherclerk PRODUCES verifiable hybrid
//! material end-to-end, and that a forged PQ half fails closed.

use dregg_sdk::{AgentCipherclerk, Signature, SignedTurn};
use dregg_turn::action::{Action, Authorization, CommitmentMode, DelegationMode};
use dregg_turn::executor::TurnExecutor;

fn empty_action(target: dregg_sdk::CellId, method: u8) -> Action {
    Action {
        target,
        method: [method; 32],
        args: vec![],
        authorization: Authorization::Unchecked,
        preconditions: Default::default(),
        effects: vec![],
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    }
}

#[test]
fn sign_action_produces_verifiable_hybrid() {
    let cclerk = AgentCipherclerk::new();
    let fed = [7u8; 32];
    let target = cclerk.cell_id("default");
    let signed = cclerk.sign_action_hybrid(empty_action(target, 1), &fed);

    let (ed25519, ml_dsa, ml_dsa_pk) = match &signed.authorization {
        Authorization::HybridSignature {
            ed25519,
            ml_dsa,
            ml_dsa_pk,
        } => (*ed25519, ml_dsa.clone(), ml_dsa_pk.clone()),
        other => panic!("sign_action must produce a HybridSignature, got {other:?}"),
    };

    // Both halves cover the SAME compute_signing_message.
    let unsigned = Action {
        authorization: Authorization::Unchecked,
        ..signed.clone()
    };
    let msg = TurnExecutor::compute_signing_message(&unsigned, &fed);
    // Classical half verifies against the clerk's ed25519 identity.
    assert!(cclerk.public_key().verify(&msg, &Signature(ed25519)));
    // Post-quantum half is present and verifies against the carried pk.
    assert!(!ml_dsa.is_empty(), "the client always signs the PQ half");
    assert_eq!(ml_dsa_pk.len(), dregg_turn::pq::ML_DSA_PK_LEN);
    assert!(dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &ml_dsa));
    // Forged PQ half fails closed.
    let mut forged = ml_dsa.clone();
    forged[0] ^= 0xff;
    assert!(!dregg_turn::pq::ml_dsa_verify(&ml_dsa_pk, &msg, &forged));
}

#[test]
fn sign_turn_carries_verifiable_pq_envelope() {
    let cclerk = AgentCipherclerk::new();
    let target = cclerk.cell_id("default");
    let turn = cclerk.make_turn(empty_action(target, 2));
    let signed = cclerk.sign_turn(&turn);
    let h = signed.turn.hash();

    // Classical half verifies.
    assert!(signed.signer.verify(&h, &signed.signature));
    // PQ half is present and verifies over the SAME turn hash both halves cover.
    assert!(!signed.pq_signature.is_empty());
    assert_eq!(signed.pq_signer.len(), dregg_turn::pq::ML_DSA_PK_LEN);
    assert!(dregg_turn::pq::ml_dsa_verify(
        &signed.pq_signer,
        &h,
        &signed.pq_signature
    ));
    // Present-but-forged PQ half fails closed.
    let mut forged = signed.pq_signature.clone();
    forged[0] ^= 0xff;
    assert!(!dregg_turn::pq::ml_dsa_verify(
        &signed.pq_signer,
        &h,
        &forged
    ));

    // The widened envelope round-trips through postcard (the wire flag-day).
    let bytes = postcard::to_stdvec(&signed).expect("encode");
    let back: SignedTurn = postcard::from_bytes(&bytes).expect("decode");
    assert_eq!(back.pq_signature, signed.pq_signature);
    assert_eq!(back.pq_signer, signed.pq_signer);
}

#[test]
fn derivation_is_deterministic_across_signings() {
    // The same cipherclerk derives the SAME ML-DSA key on every signing (the
    // deterministic-from-seed property that lets a node/genesis fixture built
    // from the same mnemonic agree without a separate ceremony).
    let cclerk = AgentCipherclerk::new();
    let target = cclerk.cell_id("default");
    let a = cclerk.sign_turn(&cclerk.make_turn(empty_action(target, 3)));
    let b = cclerk.sign_turn(&cclerk.make_turn(empty_action(target, 3)));
    assert_eq!(
        a.pq_signer, b.pq_signer,
        "same identity → same ML-DSA pubkey"
    );
    // Distinct identities derive distinct PQ keys.
    let other = AgentCipherclerk::new();
    let c = other.sign_turn(&other.make_turn(empty_action(other.cell_id("default"), 3)));
    assert_ne!(a.pq_signer, c.pq_signer);
}
