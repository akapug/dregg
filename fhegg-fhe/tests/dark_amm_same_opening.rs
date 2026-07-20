#![cfg(feature = "amm-input-binding")]

//! Tier-1 private-AMM BFV↔HidingFri same-opening authority teeth.

use dregg_circuit_prove::dark_amm_private::{
    self, DarkAmmPrivateZkProof, PrivateAmmWitness, PublicStatement,
};
use ed25519_dalek::SigningKey;
use fhe::bfv::{BfvParametersBuilder, Ciphertext};
use fhegg_fhe::amm_same_opening::{
    canonical_bfv_parameters_digest, AmmAmount, AmmPrivacyTier, AmmSameOpeningClaim,
    AmmSameOpeningContext, AmmSameOpeningError, AmmSameOpeningReceipt, ExactBfvAmountOpening,
    Tier1SameOpeningAuthority, Tier1SameOpeningEndorsement, SAME_OPENING_CLAIM_WIRE_LEN,
    SAME_OPENING_ENDORSEMENT_WIRE_LEN,
};
use fhegg_fhe::attestation::{InMemoryReplayGuard, QuorumVerifierError, SnapshotReplayGuard};
use fhegg_fhe::threshold::{
    BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
};

const HOSTED_SESSION: [u8; 32] = [0x71; 32];
const SEQUENCE: u64 = 9;
const PROOF_SESSION: u32 = 77;
const DX_BOUND: u64 = 200;
const DY_BOUND: u64 = 400;

fn blind(base: u32) -> [u32; 8] {
    core::array::from_fn(|lane| base + lane as u32)
}

fn collective_keygen(keygen: &KeygenSession, params: &BfvParams) -> CollectivePublicKey {
    let mut coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    for party in 0..keygen.n_parties() {
        let (_, contribution) = ThresholdParty::join(keygen, party, params).expect("party keygen");
        coordinator
            .accept(contribution)
            .expect("public key contribution");
    }
    coordinator.finish().expect("collective public key")
}

struct Fixture {
    params: BfvParams,
    keygen: KeygenSession,
    collective: CollectivePublicKey,
    witness: PrivateAmmWitness,
    proof: DarkAmmPrivateZkProof,
    statement: PublicStatement,
    dx_opening: ExactBfvAmountOpening,
    dy_opening: ExactBfvAmountOpening,
    dx_ciphertext: Ciphertext,
    dy_ciphertext: Ciphertext,
    signing_keys: Vec<SigningKey>,
    authority: Tier1SameOpeningAuthority,
}

impl Fixture {
    fn new() -> Self {
        let params = BfvParams::fold_set();
        let keygen = KeygenSession::from_seed(3, [0x44; 32]).expect("keygen session");
        let collective = collective_keygen(&keygen, &params);
        let witness = PrivateAmmWitness::try_new(100, 900, 50, 300, blind(1_000), blind(2_000))
            .expect("exact constant-product witness");
        let (proof, statement) =
            dark_amm_private::prove_zk(PROOF_SESSION, &witness).expect("HidingFri proof");
        let dx_opening = ExactBfvAmountOpening::new(witness.dx, [0x51; 32]);
        let dy_opening = ExactBfvAmountOpening::new(witness.dy, [0x52; 32]);
        let dx_ciphertext = dx_opening
            .encrypt(&params, &collective)
            .expect("deterministic dx encryption");
        let dy_ciphertext = dy_opening
            .encrypt(&params, &collective)
            .expect("deterministic dy encryption");
        let signing_keys = [0xa1u8, 0xa2, 0xa3]
            .into_iter()
            .map(|seed| SigningKey::from_bytes(&[seed; 32]))
            .collect::<Vec<_>>();
        let authority = Tier1SameOpeningAuthority::new(
            signing_keys
                .iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            2,
        )
        .expect("2-of-3 authority");
        Self {
            params,
            keygen,
            collective,
            witness,
            proof,
            statement,
            dx_opening,
            dy_opening,
            dx_ciphertext,
            dy_ciphertext,
            signing_keys,
            authority,
        }
    }

    fn context(&self) -> AmmSameOpeningContext<'_> {
        AmmSameOpeningContext {
            privacy_tier: AmmPrivacyTier::Tier1IssuerVisible,
            hosted_session: HOSTED_SESSION,
            sequence: SEQUENCE,
            dx_bound: DX_BOUND,
            dy_bound: DY_BOUND,
            params: &self.params,
            keygen: &self.keygen,
            collective: &self.collective,
            dx_ciphertext: &self.dx_ciphertext,
            dy_ciphertext: &self.dy_ciphertext,
            proof: &self.proof,
            statement: self.statement,
        }
    }

    fn receipt(&self) -> AmmSameOpeningReceipt {
        let context = self.context();
        // Deliberately arrive out of order; assembly must emit canonical
        // signer order so its own strict wire always round-trips.
        let endorsements = [2usize, 0]
            .into_iter()
            .map(|signer| {
                self.authority
                    .endorse(
                        &context,
                        &self.witness,
                        &self.dx_opening,
                        &self.dy_opening,
                        signer,
                        &self.signing_keys[signer],
                    )
                    .expect("issuer independently validates same opening")
            })
            .collect::<Vec<_>>();
        self.authority
            .assemble_receipt(&endorsements)
            .expect("2-of-3 receipt")
    }
}

#[test]
fn exact_opening_receipt_roundtrips_verifies_and_replay_survives_restart() {
    let fixture = Fixture::new();
    let receipt = fixture.receipt();
    assert_eq!(
        receipt
            .signatures
            .iter()
            .map(|signature| signature.signer_index)
            .collect::<Vec<_>>(),
        vec![0, 2]
    );
    let claim_wire = receipt.claim.canonical_bytes();
    assert_eq!(claim_wire.len(), SAME_OPENING_CLAIM_WIRE_LEN);
    assert_eq!(receipt.claim.dx_bound, DX_BOUND);
    assert_eq!(receipt.claim.dy_bound, DY_BOUND);
    assert_eq!(
        receipt.claim.parameter_digest,
        canonical_bfv_parameters_digest(fixture.params.arc())
    );
    let different_variance = BfvParametersBuilder::new()
        .set_degree(fixture.params.degree())
        .set_plaintext_modulus(fixture.params.plaintext_modulus())
        .set_moduli(fixture.params.moduli())
        .set_variance(1)
        .build_arc()
        .expect("same arithmetic parameters with different error variance");
    assert_eq!(different_variance.degree(), fixture.params.degree());
    assert_eq!(different_variance.moduli(), fixture.params.moduli());
    assert_eq!(
        different_variance.plaintext(),
        fixture.params.plaintext_modulus()
    );
    assert_ne!(
        canonical_bfv_parameters_digest(&different_variance),
        receipt.claim.parameter_digest,
        "same-opening authority must bind error variance, not only arithmetic parameters"
    );
    let mut substituted_parameters = receipt.clone();
    substituted_parameters.claim.parameter_digest =
        canonical_bfv_parameters_digest(&different_variance);
    assert_eq!(
        substituted_parameters.verify(
            &fixture.context(),
            fixture.authority.verifier(),
            &mut InMemoryReplayGuard::default(),
        ),
        Err(AmmSameOpeningError::BindingMismatch)
    );
    assert_eq!(
        AmmSameOpeningClaim::from_canonical_bytes(&claim_wire).expect("claim roundtrip"),
        receipt.claim
    );
    let mut wrong_tier = claim_wire.clone();
    wrong_tier[8] = 2;
    assert_eq!(
        AmmSameOpeningClaim::from_canonical_bytes(&wrong_tier),
        Err(AmmSameOpeningError::MalformedWire)
    );
    let mut old_version = claim_wire.clone();
    old_version[..8].copy_from_slice(b"FHASO002");
    assert_eq!(
        AmmSameOpeningClaim::from_canonical_bytes(&old_version),
        Err(AmmSameOpeningError::MalformedWire)
    );
    let mut invalid_bound = receipt.claim.clone();
    invalid_bound.dx_bound = 0;
    assert_eq!(
        AmmSameOpeningClaim::from_canonical_bytes(&invalid_bound.canonical_bytes()),
        Err(AmmSameOpeningError::MalformedWire)
    );

    let endorsement = fixture
        .authority
        .endorse(
            &fixture.context(),
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            1,
            &fixture.signing_keys[1],
        )
        .expect("valid party-one endorsement");
    let endorsement_wire = endorsement.to_wire_bytes();
    assert_eq!(endorsement_wire.len(), SAME_OPENING_ENDORSEMENT_WIRE_LEN);
    assert_eq!(
        Tier1SameOpeningEndorsement::from_wire_bytes(&endorsement_wire)
            .expect("endorsement roundtrip"),
        endorsement
    );
    for end in 0..endorsement_wire.len() {
        assert!(
            Tier1SameOpeningEndorsement::from_wire_bytes(&endorsement_wire[..end]).is_err(),
            "truncated endorsement length {end}"
        );
    }
    let mut wrong_magic = endorsement_wire.clone();
    wrong_magic[0] ^= 1;
    assert_eq!(
        Tier1SameOpeningEndorsement::from_wire_bytes(&wrong_magic),
        Err(AmmSameOpeningError::MalformedWire)
    );
    let mut retired_endorsement = endorsement_wire.clone();
    retired_endorsement[..8].copy_from_slice(b"FHASE002");
    assert_eq!(
        Tier1SameOpeningEndorsement::from_wire_bytes(&retired_endorsement),
        Err(AmmSameOpeningError::MalformedWire)
    );
    let mut trailing_endorsement = endorsement_wire.clone();
    trailing_endorsement.push(0);
    assert_eq!(
        Tier1SameOpeningEndorsement::from_wire_bytes(&trailing_endorsement),
        Err(AmmSameOpeningError::MalformedWire)
    );
    let signer_offset = 8 + SAME_OPENING_CLAIM_WIRE_LEN;
    let mut out_of_roster = endorsement_wire.clone();
    out_of_roster[signer_offset..signer_offset + 4]
        .copy_from_slice(&endorsement.claim.issuer_roster_len.to_be_bytes());
    assert_eq!(
        Tier1SameOpeningEndorsement::from_wire_bytes(&out_of_roster),
        Err(AmmSameOpeningError::MalformedWire)
    );

    // The artifact decoder is deliberately roster-independent. A validly
    // encoded claim substitution therefore parses, but the authority refuses
    // to combine it with an endorsement of another claim.
    let mut substituted = endorsement.clone();
    substituted.claim.sequence += 1;
    let substituted = Tier1SameOpeningEndorsement::from_wire_bytes(&substituted.to_wire_bytes())
        .expect("structurally valid substituted claim");
    assert_eq!(
        fixture
            .authority
            .assemble_receipt(&[endorsement.clone(), substituted]),
        Err(AmmSameOpeningError::EndorsementClaimMismatch)
    );

    let wire = receipt.to_wire_bytes();
    assert_eq!(
        AmmSameOpeningReceipt::from_wire_bytes(&wire).expect("receipt roundtrip"),
        receipt
    );
    let mut retired_receipt = wire.clone();
    retired_receipt[..8].copy_from_slice(b"FHASR002");
    assert_eq!(
        AmmSameOpeningReceipt::from_wire_bytes(&retired_receipt),
        Err(AmmSameOpeningError::MalformedWire)
    );
    for end in 0..wire.len() {
        assert!(
            AmmSameOpeningReceipt::from_wire_bytes(&wire[..end]).is_err(),
            "truncated receipt length {end}"
        );
    }
    let mut trailing = wire;
    trailing.push(0);
    assert_eq!(
        AmmSameOpeningReceipt::from_wire_bytes(&trailing),
        Err(AmmSameOpeningError::MalformedWire)
    );

    let mut replay = SnapshotReplayGuard::new(receipt.claim.replay_context());
    let verified = receipt
        .verify(
            &fixture.context(),
            fixture.authority.verifier(),
            &mut replay,
        )
        .expect("full exact-opening verification");
    assert_eq!(verified.hosted_session(), HOSTED_SESSION);
    assert_eq!(verified.sequence(), SEQUENCE);
    assert_eq!(verified.old_root(), fixture.statement.old_root);
    assert_eq!(verified.new_root(), fixture.statement.new_root);
    assert_eq!(verified.k(), fixture.statement.k);
    assert_eq!(verified.dx_bound(), DX_BOUND);
    assert_eq!(verified.dy_bound(), DY_BOUND);

    let snapshot = replay.to_wire_bytes();
    let mut replay =
        SnapshotReplayGuard::from_wire_bytes(receipt.claim.replay_context(), &snapshot)
            .expect("durable replay restart");
    assert_eq!(
        receipt.verify(
            &fixture.context(),
            fixture.authority.verifier(),
            &mut replay
        ),
        Err(AmmSameOpeningError::ReplayDetected)
    );

    let mut forged = receipt.clone();
    forged.signatures[1].signature[17] ^= 1;
    let mut fresh = InMemoryReplayGuard::default();
    assert_eq!(
        forged.verify(&fixture.context(), fixture.authority.verifier(), &mut fresh),
        Err(AmmSameOpeningError::Quorum(
            QuorumVerifierError::InvalidSignature { index: 2 }
        ))
    );
    receipt
        .verify(&fixture.context(), fixture.authority.verifier(), &mut fresh)
        .expect("failed signature did not burn replay slot");

    let duplicate = fixture
        .authority
        .endorse(
            &fixture.context(),
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        )
        .expect("valid party-zero endorsement");
    assert_eq!(
        fixture
            .authority
            .assemble_receipt(&[duplicate.clone(), duplicate]),
        Err(AmmSameOpeningError::Quorum(
            QuorumVerifierError::DuplicateSigner { index: 0 }
        ))
    );
}

#[test]
fn issuer_and_consumer_refuse_every_cross_representation_substitution() {
    let fixture = Fixture::new();
    let context = fixture.context();
    let receipt = fixture.receipt();

    let underdeclared_dx = AmmSameOpeningContext {
        dx_bound: u64::from(fixture.witness.dx) - 1,
        ..context
    };
    assert_eq!(
        fixture.authority.endorse(
            &underdeclared_dx,
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::InvalidAmountBound {
            amount: AmmAmount::Dx
        })
    );
    let zero_dy_bound = AmmSameOpeningContext {
        dy_bound: 0,
        ..context
    };
    assert_eq!(
        fixture.authority.endorse(
            &zero_dy_bound,
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::InvalidAmountBound {
            amount: AmmAmount::Dy
        })
    );
    let modulus_dx_bound = AmmSameOpeningContext {
        dx_bound: fixture.params.plaintext_modulus(),
        ..context
    };
    assert_eq!(
        fixture.authority.endorse(
            &modulus_dx_bound,
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::InvalidAmountBound {
            amount: AmmAmount::Dx
        })
    );

    let wrong_dx_opening = ExactBfvAmountOpening::new(fixture.witness.dx, [0x99; 32]);
    assert_eq!(
        fixture.authority.endorse(
            &context,
            &fixture.witness,
            &wrong_dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::BfvReencryptionMismatch {
            amount: AmmAmount::Dx
        })
    );

    let zero_seed = ExactBfvAmountOpening::new(fixture.witness.dx, [0; 32]);
    assert_eq!(
        fixture.authority.endorse(
            &context,
            &fixture.witness,
            &zero_seed,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::InvalidEncryptionSeed {
            amount: AmmAmount::Dx
        })
    );
    let reused_seed = ExactBfvAmountOpening::new(fixture.witness.dy, [0x51; 32]);
    assert_eq!(
        fixture.authority.endorse(
            &context,
            &fixture.witness,
            &fixture.dx_opening,
            &reused_seed,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::ReusedEncryptionSeed)
    );

    let alternate_dy_opening = ExactBfvAmountOpening::new(fixture.witness.dy, [0x62; 32]);
    let alternate_dy = alternate_dy_opening
        .encrypt(&fixture.params, &fixture.collective)
        .expect("alternate exact dy encryption");
    let substituted_dy_ciphertext = AmmSameOpeningContext {
        dy_ciphertext: &alternate_dy,
        ..context
    };
    assert_eq!(
        fixture.authority.endorse(
            &substituted_dy_ciphertext,
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::BfvReencryptionMismatch {
            amount: AmmAmount::Dy
        })
    );

    let wrong_dy_opening = ExactBfvAmountOpening::new(fixture.witness.dy, [0x98; 32]);
    assert_eq!(
        fixture.authority.endorse(
            &context,
            &fixture.witness,
            &fixture.dx_opening,
            &wrong_dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::BfvReencryptionMismatch {
            amount: AmmAmount::Dy
        })
    );

    let wrong_value_opening = ExactBfvAmountOpening::new(51, [0x51; 32]);
    assert_eq!(
        fixture.authority.endorse(
            &context,
            &fixture.witness,
            &wrong_value_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::WitnessOpeningMismatch {
            amount: AmmAmount::Dx
        })
    );

    let dy_substituted_witness =
        PrivateAmmWitness::try_new(200, 600, 50, 120, blind(5_000), blind(6_000))
            .expect("exact witness retaining dx but changing dy");
    assert_eq!(
        fixture.authority.endorse(
            &context,
            &dy_substituted_witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::WitnessOpeningMismatch {
            amount: AmmAmount::Dy
        })
    );

    let alternate_dx_opening = ExactBfvAmountOpening::new(fixture.witness.dx, [0x61; 32]);
    let alternate_dx = alternate_dx_opening
        .encrypt(&fixture.params, &fixture.collective)
        .expect("alternate exact encryption");
    let substituted_ciphertext = AmmSameOpeningContext {
        dx_ciphertext: &alternate_dx,
        ..context
    };
    assert_eq!(
        fixture.authority.endorse(
            &substituted_ciphertext,
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::BfvReencryptionMismatch {
            amount: AmmAmount::Dx
        })
    );

    let alternate_witness =
        PrivateAmmWitness::try_new(100, 900, 80, 400, blind(3_000), blind(4_000))
            .expect("second exact constant-product witness");
    assert_eq!(
        fixture.authority.endorse(
            &context,
            &alternate_witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::WitnessOpeningMismatch {
            amount: AmmAmount::Dx
        })
    );

    let alternate_statement =
        dark_amm_private::statement(PROOF_SESSION, &alternate_witness).expect("other statement");
    let substituted_statement = AmmSameOpeningContext {
        statement: alternate_statement,
        ..context
    };
    assert_eq!(
        fixture.authority.endorse(
            &substituted_statement,
            &fixture.witness,
            &fixture.dx_opening,
            &fixture.dy_opening,
            0,
            &fixture.signing_keys[0],
        ),
        Err(AmmSameOpeningError::StatementMismatch)
    );

    let (second_proof, second_statement) =
        dark_amm_private::prove_zk(PROOF_SESSION, &fixture.witness)
            .expect("fresh randomized proof");
    assert_eq!(second_statement, fixture.statement);
    let proof_substitution = AmmSameOpeningContext {
        proof: &second_proof,
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, proof_substitution);
    assert_binding_refusal(&receipt, &fixture, substituted_ciphertext);
    assert_binding_refusal(&receipt, &fixture, substituted_dy_ciphertext);

    let host_session_substitution = AmmSameOpeningContext {
        hosted_session: [0x72; 32],
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, host_session_substitution);

    let sequence_substitution = AmmSameOpeningContext {
        sequence: SEQUENCE + 1,
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, sequence_substitution);

    let bound_substitution = AmmSameOpeningContext {
        dx_bound: DX_BOUND + 1,
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, bound_substitution);

    let root_substitution = AmmSameOpeningContext {
        statement: PublicStatement {
            old_root: {
                let mut root = fixture.statement.old_root;
                root[3] += 1;
                root
            },
            ..fixture.statement
        },
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, root_substitution);

    let k_substitution = AmmSameOpeningContext {
        statement: PublicStatement {
            k: fixture.statement.k + 1,
            ..fixture.statement
        },
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, k_substitution);

    let proof_session_substitution = AmmSameOpeningContext {
        statement: PublicStatement {
            session: PROOF_SESSION + 1,
            ..fixture.statement
        },
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, proof_session_substitution);

    let other_collective = collective_keygen(&fixture.keygen, &fixture.params);
    let key_substitution = AmmSameOpeningContext {
        collective: &other_collective,
        ..context
    };
    assert_binding_refusal(&receipt, &fixture, key_substitution);

    let alternate_keys = [0xb1u8, 0xb2, 0xb3]
        .into_iter()
        .map(|seed| SigningKey::from_bytes(&[seed; 32]))
        .collect::<Vec<_>>();
    let alternate_authority = Tier1SameOpeningAuthority::new(
        alternate_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .expect("substituted authority");
    assert_eq!(
        receipt.verify(
            &context,
            alternate_authority.verifier(),
            &mut InMemoryReplayGuard::default(),
        ),
        Err(AmmSameOpeningError::BindingMismatch)
    );
}

fn assert_binding_refusal(
    receipt: &AmmSameOpeningReceipt,
    fixture: &Fixture,
    substituted: AmmSameOpeningContext<'_>,
) {
    assert_eq!(
        receipt.verify(
            &substituted,
            fixture.authority.verifier(),
            &mut InMemoryReplayGuard::default(),
        ),
        Err(AmmSameOpeningError::BindingMismatch)
    );
}
