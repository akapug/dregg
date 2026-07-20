//! End-to-end game-service cutover: collective BFV public material, a real
//! HidingFri transition proof, collective Tier-1 same-opening, one staged
//! encrypted candidate, independent authenticated FHDAR decision, atomic
//! commit, and restart on both sides of the phase boundary.

#![cfg(feature = "dark-amm-game")]

use std::time::Duration;

use dregg_circuit_prove::dark_amm_private::{PrivateAmmWitness, prove_zk};
use dreggnet_market::dark_amm_collective::{
    CollectiveDarkAmmConfig, CollectiveDarkAmmError, CollectiveDarkAmmSession,
};
use dreggnet_market::dark_amm_game::{
    DarkAmmPublicSession, SameOpeningProvedEncryptedSwapRequest,
    produce_proved_encrypted_swap_seeded,
};
use ed25519_dalek::SigningKey;
use fhe::bfv::{PublicKey, RelinearizationKey};
use fhe_traits::{DeserializeParametrized, Serialize as FheSerialize};
use fhegg_fhe::amm_same_opening::{
    AmmPrivacyTier, AmmSameOpeningContext, ExactBfvAmountOpening, Tier1SameOpeningAuthority,
};
use fhegg_fhe::attestation::{
    AuthenticatedQuorumVerifier, ComputationIntegrityEvidence, ComputationIntegrityResidual,
};
use fhegg_fhe::dark_amm::{DarkPool, DarkPoolPublicHostMaterial};
use fhegg_fhe::dark_amm_attested::AttestedPrivateDecisionPolicy;
use fhegg_fhe::decision_attestation::{AttestedDecisionReceipt, ExpectedDecisionContext};
use fhegg_fhe::mpc_party::{DecisionTranscript, PartyMpcSession, simulate_decision_transcript};
use fhegg_fhe::threshold::relin::{RelinKeySession, generate_relinearization_key};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};
use rand::SeedableRng as SeedableRng08;
use rand::rngs::StdRng as StdRng08;

const N: usize = 3;
const VALUE_BITS: usize = 19;
const HOSTED_SESSION: [u8; 32] = [0x91; 32];

struct CollectiveFixture {
    params: BfvParams,
    keygen: KeygenSession,
    public_key_bytes: Vec<u8>,
    relin: RelinearizationKey,
}

impl CollectiveFixture {
    fn new() -> Self {
        let params = BfvParams::fold_set();
        let keygen = KeygenSession::from_seed(N, [0x92; 32]).unwrap();
        let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
        let mut parties = Vec::new();
        for party in 0..N {
            let (holder, contribution) = ThresholdParty::join(&keygen, party, &params).unwrap();
            coordinator.accept(contribution).unwrap();
            parties.push(holder);
        }
        let collective = coordinator.finish().unwrap();
        let public_key_bytes = collective.pk.to_bytes();
        let relin_session = RelinKeySession::from_public_entropy(
            &keygen,
            &collective,
            [0x93; 32],
            Duration::from_secs(30),
        )
        .unwrap();
        let relin =
            generate_relinearization_key(&relin_session, &params, &collective, &parties).unwrap();
        Self {
            params,
            keygen,
            public_key_bytes,
            relin,
        }
    }

    fn collective(&self) -> CollectivePublicKey {
        CollectivePublicKey {
            pk: PublicKey::from_bytes(&self.public_key_bytes, self.params.arc()).unwrap(),
        }
    }

    fn initial_material(&self) -> DarkPoolPublicHostMaterial {
        let collective = self.collective();
        let mut pool = DarkPool::init(
            self.params.arc(),
            &collective.pk,
            &self.relin,
            100,
            900,
            400,
            1_000,
            &mut rand_09::rng(),
        )
        .unwrap();
        pool.strip_lp_view();
        pool.public_host_material().unwrap()
    }
}

fn signing_keys(seed: u8) -> Vec<SigningKey> {
    (0..N)
        .map(|index| SigningKey::from_bytes(&[seed + index as u8; 32]))
        .collect()
}

fn verifier(keys: &[SigningKey]) -> AuthenticatedQuorumVerifier {
    AuthenticatedQuorumVerifier::new(
        keys.iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap()
}

fn config(
    fixture: &CollectiveFixture,
    hosted_session: [u8; 32],
    same_opening_verifier: AuthenticatedQuorumVerifier,
    decision_verifier: AuthenticatedQuorumVerifier,
) -> CollectiveDarkAmmConfig {
    let decision_policy = AttestedPrivateDecisionPolicy::new(
        VALUE_BITS,
        fixture.params.plaintext_modulus(),
        Duration::from_secs(5),
        decision_verifier,
    )
    .unwrap();
    CollectiveDarkAmmConfig::new(
        hosted_session,
        fixture.params.clone(),
        fixture.keygen.clone(),
        fixture.collective(),
        same_opening_verifier,
        decision_policy,
    )
    .unwrap()
}

fn decision_receipt(
    candidate_nonce: [u8; 32],
    equal: bool,
    keys: &[SigningKey],
    decision_verifier: &AuthenticatedQuorumVerifier,
) -> (DecisionTranscript, AttestedDecisionReceipt) {
    let session = PartyMpcSession::equality(
        candidate_nonce,
        N,
        VALUE_BITS,
        BfvParams::fold_set().plaintext_modulus(),
        Duration::from_secs(5),
    )
    .unwrap();
    let mut transcript_rng = StdRng08::seed_from_u64(if equal { 0x9401 } else { 0x9400 });
    let transcript = simulate_decision_transcript(equal, &session, &mut transcript_rng).unwrap();
    assert!(transcript.is_reveal_only(&session));
    let expected = ExpectedDecisionContext {
        session: &session,
        roster_digest: decision_verifier.roster_digest(),
        transcript: &transcript,
        equal,
    };
    let draft = AttestedDecisionReceipt::issue(
        &expected,
        ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        ),
    )
    .unwrap();
    let signatures = [0usize, 2]
        .map(|index| {
            decision_verifier
                .sign_claim(&draft.claim_digest(), index, &keys[index])
                .unwrap()
        })
        .to_vec();
    let evidence = decision_verifier
        .assemble_evidence(&draft.claim_digest(), &signatures)
        .unwrap();
    AttestedDecisionReceipt::issue(&expected, evidence)
        .map(|receipt| (transcript, receipt))
        .unwrap()
}

#[test]
fn collective_two_phase_game_session_is_atomic_and_restartable_without_host_secret() {
    let fixture = CollectiveFixture::new();
    let same_opening_keys = signing_keys(0xa1);
    let decision_keys = signing_keys(0xb1);
    let same_opening_authority = Tier1SameOpeningAuthority::new(
        same_opening_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap();
    let decision_verifier = verifier(&decision_keys);

    let witness = PrivateAmmWitness::try_new(
        100,
        900,
        50,
        300,
        [1_000, 1_001, 1_002, 1_003, 1_004, 1_005, 1_006, 1_007],
        [2_000, 2_001, 2_002, 2_003, 2_004, 2_005, 2_006, 2_007],
    )
    .unwrap();
    let seed_public = DarkAmmPublicSession::try_from_collective(
        HOSTED_SESSION,
        &fixture.params,
        &fixture.keygen,
        &fixture.collective(),
        90_000,
        400,
        1_000,
        0,
        [1; 8],
    )
    .unwrap();
    let (proof, statement) = prove_zk(seed_public.private_amm_receipt_session(), &witness).unwrap();
    let material = fixture.initial_material();
    let mut host = CollectiveDarkAmmSession::new(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        material.clone(),
        statement.old_root,
        0,
    )
    .unwrap();
    let public = host.public_session().unwrap();
    let public_wire = public.to_wire_bytes();
    assert_eq!(&public_wire[..8], b"DBAPv003");
    assert_eq!(
        DarkAmmPublicSession::from_wire_bytes(&public_wire).unwrap(),
        public
    );
    for retired_magic in [b"DBAPv001", b"DBAPv002"] {
        let mut retired = public_wire.clone();
        retired[..8].copy_from_slice(retired_magic);
        assert!(
            DarkAmmPublicSession::from_wire_bytes(&retired).is_err(),
            "retired public-session version must fail closed"
        );
    }
    let proved = produce_proved_encrypted_swap_seeded(
        &public,
        50,
        300,
        200,
        400,
        statement,
        proof.to_postcard().unwrap(),
        [0xc1; 32],
        [0xc2; 32],
    )
    .unwrap();
    let (dx, dy) = proved.bounded_ciphertexts(fixture.params.arc()).unwrap();
    let decoded_proof = proved.decoded_private_amm_proof().unwrap();
    let authority_collective = fixture.collective();
    let opening_context = AmmSameOpeningContext {
        privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
        hosted_session: HOSTED_SESSION,
        sequence: 0,
        dx_bound: proved.dx_bound(),
        dy_bound: proved.dy_bound(),
        params: &fixture.params,
        keygen: &fixture.keygen,
        collective: &authority_collective,
        dx_ciphertext: &dx.ct,
        dy_ciphertext: &dy.ct,
        proof: &decoded_proof,
        statement,
    };
    let dx_opening = ExactBfvAmountOpening::new(50, [0xc1; 32]);
    let dy_opening = ExactBfvAmountOpening::new(300, [0xc2; 32]);
    let endorsements = [0usize, 2]
        .map(|index| {
            same_opening_authority
                .endorse(
                    &opening_context,
                    &witness,
                    &dx_opening,
                    &dy_opening,
                    index,
                    &same_opening_keys[index],
                )
                .unwrap()
        })
        .to_vec();
    let same_opening_receipt = same_opening_authority
        .assemble_receipt(&endorsements)
        .unwrap();
    assert_eq!(same_opening_receipt.claim.bfv.n_parties, N as u64);
    let request = SameOpeningProvedEncryptedSwapRequest::new(proved, same_opening_receipt);
    let request_wire = request.to_wire_bytes();

    // Cross-session ingress is rejected before any replay or pending mutation.
    let mut other_session = CollectiveDarkAmmSession::new(
        config(
            &fixture,
            [0x99; 32],
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        material,
        statement.old_root,
        0,
    )
    .unwrap();
    let other_before = other_session.checkpoint_wire_bytes();
    assert!(matches!(
        other_session.stage_same_opening_request(&request_wire),
        Err(CollectiveDarkAmmError::Refused(_))
    ));
    assert_eq!(other_session.checkpoint_wire_bytes(), other_before);

    let committed_before = host.public_host_material().material_digest();
    let staged = host.stage_same_opening_request(&request_wire).unwrap();
    assert_eq!(staged.sequence, 0);
    assert_eq!(staged.new_root, statement.new_root);
    assert!(host.has_pending_candidate());
    assert_eq!(
        host.public_host_material().material_digest(),
        committed_before
    );
    assert_eq!(host.current_root(), statement.old_root);
    assert_eq!(host.next_sequence(), 0);
    assert_eq!(host.same_opening_replay_revision(), 0);
    assert_eq!(host.decision_replay_revision(), 0);
    assert_eq!(
        host.stage_same_opening_request(&request_wire),
        Err(CollectiveDarkAmmError::PendingCandidateExists)
    );

    // The public pending carrier survives restart only after full
    // proof/signature reconstruction and a consumed replay-slot check.
    let pending_checkpoint = host.checkpoint_wire_bytes();
    let mut host = CollectiveDarkAmmSession::restore_from_checkpoint(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        &pending_checkpoint,
    )
    .unwrap();
    assert!(host.has_pending_candidate());
    assert_eq!(host.checkpoint_wire_bytes(), pending_checkpoint);

    // A false decision, a cross-candidate decision, and residual-only evidence
    // each preserve every byte of authoritative state, including replay sets.
    let (false_transcript, false_receipt) = decision_receipt(
        staged.candidate_nonce,
        false,
        &decision_keys,
        &decision_verifier,
    );
    let before_false = host.checkpoint_wire_bytes();
    assert!(
        host.commit_attested_decision(&false_transcript, &false_receipt)
            .is_err()
    );
    assert_eq!(host.checkpoint_wire_bytes(), before_false);

    let (cross_transcript, cross_receipt) =
        decision_receipt([0xd1; 32], true, &decision_keys, &decision_verifier);
    let before_cross = host.checkpoint_wire_bytes();
    assert!(
        host.commit_attested_decision(&cross_transcript, &cross_receipt)
            .is_err()
    );
    assert_eq!(host.checkpoint_wire_bytes(), before_cross);

    let (transcript, receipt) = decision_receipt(
        staged.candidate_nonce,
        true,
        &decision_keys,
        &decision_verifier,
    );
    let mut residual_only = receipt.clone();
    residual_only.computation_integrity = ComputationIntegrityEvidence::BindingOnly(
        ComputationIntegrityResidual::OutputOnlySelfAssertion,
    );
    let before_evidence = host.checkpoint_wire_bytes();
    assert!(
        host.commit_attested_decision(&transcript, &residual_only)
            .is_err()
    );
    assert_eq!(host.checkpoint_wire_bytes(), before_evidence);

    let committed = host
        .commit_attested_decision(&transcript, &receipt)
        .unwrap();
    assert_eq!(committed.committed_sequence, 0);
    assert_eq!(committed.next_sequence, 1);
    assert_eq!(committed.new_root, statement.new_root);
    assert_eq!(
        committed.same_opening_claim_digest,
        staged.same_opening_claim_digest
    );
    assert_eq!(committed.decision_claim_digest, receipt.claim_digest());
    assert!(!host.has_pending_candidate());
    assert_eq!(host.current_root(), statement.new_root);
    assert_eq!(host.next_sequence(), 1);
    assert_eq!(host.same_opening_replay_revision(), 1);
    assert_eq!(host.decision_replay_revision(), 1);
    assert_ne!(
        host.public_host_material().material_digest(),
        committed_before
    );

    let committed_checkpoint = host.checkpoint_wire_bytes();
    let mut restarted = CollectiveDarkAmmSession::restore_from_checkpoint(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier.clone(),
        ),
        &committed_checkpoint,
    )
    .unwrap();
    assert_eq!(restarted.checkpoint_wire_bytes(), committed_checkpoint);
    let before_stale = restarted.checkpoint_wire_bytes();
    assert!(matches!(
        restarted.stage_same_opening_request(&request_wire),
        Err(CollectiveDarkAmmError::Refused(_))
    ));
    assert_eq!(restarted.checkpoint_wire_bytes(), before_stale);

    // Explicit cancellation clears only the public pending carrier. Phase one
    // did not burn the sequence slot, so the exact request (or a competing
    // verified same-sequence request) may be staged after restart.
    let mut cancelled = CollectiveDarkAmmSession::new(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            decision_verifier,
        ),
        fixture.initial_material(),
        statement.old_root,
        0,
    )
    .unwrap();
    let before_cancel_stage = cancelled.checkpoint_wire_bytes();
    let staged_for_cancel = cancelled.stage_same_opening_request(&request_wire).unwrap();
    assert_eq!(cancelled.same_opening_replay_revision(), 0);
    let committed_material = cancelled.public_host_material().material_digest();
    let abandoned = cancelled.abandon_pending().unwrap();
    assert_eq!(abandoned, staged_for_cancel);
    assert!(!cancelled.has_pending_candidate());
    assert_eq!(
        cancelled.public_host_material().material_digest(),
        committed_material
    );
    assert_eq!(cancelled.current_root(), statement.old_root);
    assert_eq!(cancelled.next_sequence(), 0);
    let abandoned_checkpoint = cancelled.checkpoint_wire_bytes();
    assert_eq!(abandoned_checkpoint, before_cancel_stage);
    let mut cancelled = CollectiveDarkAmmSession::restore_from_checkpoint(
        config(
            &fixture,
            HOSTED_SESSION,
            same_opening_authority.verifier().clone(),
            verifier(&decision_keys),
        ),
        &abandoned_checkpoint,
    )
    .unwrap();
    let restaged = cancelled.stage_same_opening_request(&request_wire).unwrap();
    assert_eq!(restaged, staged_for_cancel);
    assert!(cancelled.has_pending_candidate());
    assert_eq!(cancelled.same_opening_replay_revision(), 0);
}
