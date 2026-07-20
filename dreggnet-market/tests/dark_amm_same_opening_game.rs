//! Strict v3 Dark Pool host weld: real HidingFri proof, deterministic BFV
//! openings, 2-of-3 Tier-1 authority receipt, mutation, and journal restart.

#![cfg(feature = "dark-amm-game")]

use dregg_circuit_prove::dark_amm_private::{DIGEST_WIDTH, PrivateAmmWitness, prove_zk};
use dreggnet_market::dark_amm_game::{
    DARK_AMM_OFFERING_KEY, DARK_AMM_OPERATION, DARK_AMM_PROVED_OPERATION,
    DARK_AMM_SAME_OPENING_DISCLOSURE, DARK_AMM_SAME_OPENING_OPERATION, DarkAmmGameOffering,
    DarkAmmHostKeyMaterial, DarkAmmPrivateSwapAuthority, SameOpeningProvedEncryptedSwapRequest,
    produce_proved_encrypted_swap_seeded,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{DreggIdentity, OfferingHost, SessionConfig, SessionId};
use ed25519_dalek::SigningKey;
use fhegg_fhe::amm_same_opening::Tier1SameOpeningAuthority;
use rand_09::SeedableRng;
use rand_09::rngs::StdRng;

const SESSION_SEED: u64 = 0xA771_5300;

fn host_keys(seed: u64) -> DarkAmmHostKeyMaterial {
    let mut rng = StdRng::seed_from_u64(seed);
    DarkAmmHostKeyMaterial::generate(&mut rng).expect("deployment BFV keys")
}

fn blind(base: u32) -> [u32; DIGEST_WIDTH] {
    core::array::from_fn(|lane| base + lane as u32)
}

fn authority_keys() -> Vec<SigningKey> {
    [0x71, 0x72, 0x73]
        .map(|seed| SigningKey::from_bytes(&[seed; 32]))
        .into_iter()
        .collect()
}

fn public_authority_keys(keys: &[SigningKey]) -> Vec<[u8; 32]> {
    keys.iter()
        .map(|key| key.verifying_key().to_bytes())
        .collect()
}

fn statement_offset(v3: &[u8]) -> usize {
    // DBAMv003 || len(v2) || DBAMv002 || len(v1) || v1 || statement...
    let v2_start = 16;
    let encrypted_len = u64::from_le_bytes(
        v3[v2_start + 8..v2_start + 16]
            .try_into()
            .expect("v2 length"),
    ) as usize;
    v2_start + 16 + encrypted_len
}

#[test]
fn exact_opening_v3_is_strict_atomic_and_restart_replayable() {
    let key_material = host_keys(0xD3);
    let key_wire = key_material.to_secret_wire_bytes();
    let legacy_public = DarkAmmGameOffering::demo(key_material.clone())
        .public_session_for_seed(SESSION_SEED)
        .unwrap();
    let witness =
        PrivateAmmWitness::try_new(100, 900, 50, 300, blind(1_000), blind(2_000)).unwrap();
    let (proof, statement) = prove_zk(legacy_public.private_amm_receipt_session(), &witness)
        .expect("real HidingFri proof");
    let proof_bytes = proof.to_postcard().unwrap();

    let issuers = authority_keys();
    let issuer_public = public_authority_keys(&issuers);
    let authority = Tier1SameOpeningAuthority::new(issuer_public.clone(), 2).unwrap();
    let offering = DarkAmmGameOffering::demo_same_opening_required(
        key_material.clone(),
        statement.old_root,
        issuer_public.clone(),
        2,
    )
    .unwrap();
    let public = offering.public_session_for_seed(SESSION_SEED).unwrap();

    let proved = produce_proved_encrypted_swap_seeded(
        &public,
        50,
        300,
        200,
        400,
        statement,
        proof_bytes.clone(),
        [0x31; 32],
        [0x32; 32],
    )
    .unwrap();
    let private_authority = DarkAmmPrivateSwapAuthority::try_new(
        &public,
        witness.clone(),
        [0x31; 32],
        [0x32; 32],
        &proved,
    )
    .unwrap();
    let endorsements = [2usize, 0]
        .map(|index| {
            private_authority
                .endorse_same_opening(&public, &proved, &authority, index, &issuers[index])
                .unwrap()
        })
        .to_vec();
    let request = private_authority
        .assemble_same_opening_request(&public, proved.clone(), &authority, &endorsements)
        .unwrap();
    let request_wire = request.to_wire_bytes();
    assert_eq!(
        SameOpeningProvedEncryptedSwapRequest::from_wire_bytes(&request_wire).unwrap(),
        request
    );
    assert!(
        SameOpeningProvedEncryptedSwapRequest::from_wire_bytes(&proved.to_wire_bytes()).is_err(),
        "proved-v2 must never decode as v3"
    );
    assert_eq!(request.same_opening_receipt().claim.bfv.n_parties, 1);
    assert_eq!(
        request.same_opening_receipt().claim.bfv.opening_threshold,
        1
    );
    assert_eq!(request.same_opening_receipt().claim.dx_bound, 200);
    assert_eq!(request.same_opening_receipt().claim.dy_bound, 400);
    assert_eq!(
        request
            .same_opening_receipt()
            .signatures
            .iter()
            .map(|signature| signature.signer_index)
            .collect::<Vec<_>>(),
        vec![0, 2]
    );

    // A second, independently encrypted request for the same private proof is
    // valid in isolation. Its receipt must not be swappable onto the first.
    let alternate_proved = produce_proved_encrypted_swap_seeded(
        &public,
        50,
        300,
        200,
        400,
        statement,
        proof_bytes,
        [0x41; 32],
        [0x42; 32],
    )
    .unwrap();
    let alternate_private = DarkAmmPrivateSwapAuthority::try_new(
        &public,
        witness,
        [0x41; 32],
        [0x42; 32],
        &alternate_proved,
    )
    .unwrap();
    let alternate_endorsements = [0usize, 1]
        .map(|index| {
            alternate_private
                .endorse_same_opening(
                    &public,
                    &alternate_proved,
                    &authority,
                    index,
                    &issuers[index],
                )
                .unwrap()
        })
        .to_vec();
    let alternate = alternate_private
        .assemble_same_opening_request(
            &public,
            alternate_proved,
            &authority,
            &alternate_endorsements,
        )
        .unwrap();
    let swapped = SameOpeningProvedEncryptedSwapRequest::new(
        proved.clone(),
        alternate.same_opening_receipt().clone(),
    )
    .to_wire_bytes();

    let store = InMemoryResumeStore::new();
    let id = SessionId::new("same-opening-dark-pool");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — exact-opening pool",
        offering,
    );
    host.open_session(
        DARK_AMM_OFFERING_KEY,
        id.clone(),
        SessionConfig::with_seed(SESSION_SEED),
    )
    .unwrap();
    let operations = host.binary_operations(DARK_AMM_OFFERING_KEY, &id).unwrap();
    assert_eq!(operations.len(), 1);
    assert_eq!(operations[0].name, DARK_AMM_SAME_OPENING_OPERATION);
    assert_eq!(operations[0].disclosure, DARK_AMM_SAME_OPENING_DISCLOSURE);
    assert!(operations.iter().all(|operation| {
        operation.name != DARK_AMM_OPERATION && operation.name != DARK_AMM_PROVED_OPERATION
    }));

    let actor = DreggIdentity("veiled-trader".into());
    let mut refuse = |operation: &str, wire: &[u8]| {
        assert!(
            host.invoke_binary_operation(
                DARK_AMM_OFFERING_KEY,
                &id,
                operation,
                wire,
                actor.clone(),
            )
            .is_err()
        );
        assert_eq!(
            store
                .load(DARK_AMM_OFFERING_KEY, &id)
                .unwrap()
                .operations
                .len(),
            0,
            "refusal must not journal or mutate"
        );
    };

    refuse(DARK_AMM_PROVED_OPERATION, &proved.to_wire_bytes());
    refuse(DARK_AMM_SAME_OPENING_OPERATION, &proved.to_wire_bytes());
    refuse(DARK_AMM_SAME_OPENING_OPERATION, &swapped);

    let mut tampered_signature = request_wire.clone();
    *tampered_signature.last_mut().unwrap() ^= 0x80;
    refuse(DARK_AMM_SAME_OPENING_OPERATION, &tampered_signature);

    // Exact public pins in the nested v1/v2 body: session, key, sequence, k,
    // and old root all fail before mutation. Offsets are protocol-versioned.
    for offset in [40usize, 72, 104] {
        let mut tampered = request_wire.clone();
        tampered[offset] ^= 1;
        refuse(DARK_AMM_SAME_OPENING_OPERATION, &tampered);
    }
    // The public caps used by MulEngine's wrap proof are issuer-attested too.
    // Changing either nested v1 bound while retaining the exact ciphertext and
    // proof must fail the v3 receipt, even when the changed bound is otherwise
    // syntactically legal.
    for offset in [112usize, 120] {
        let mut tampered = request_wire.clone();
        tampered[offset] ^= 1;
        refuse(DARK_AMM_SAME_OPENING_OPERATION, &tampered);
    }
    for statement_lane in [2usize, 3] {
        let mut tampered = request_wire.clone();
        let offset = statement_offset(&tampered) + statement_lane * 4;
        tampered[offset] ^= 1;
        refuse(DARK_AMM_SAME_OPENING_OPERATION, &tampered);
    }

    // Same exact request and pool, wrong ordered issuer policy.
    let alternate_issuers = [0x51, 0x52, 0x53].map(|seed| SigningKey::from_bytes(&[seed; 32]));
    let alternate_public = public_authority_keys(&alternate_issuers);
    let wrong_roster_offering = DarkAmmGameOffering::demo_same_opening_required(
        key_material,
        statement.old_root,
        alternate_public,
        2,
    )
    .unwrap();
    let wrong_id = SessionId::new("same-opening-wrong-roster");
    let mut wrong_roster_host = OfferingHost::new();
    wrong_roster_host.register(
        DARK_AMM_OFFERING_KEY,
        "Wrong roster test pool",
        wrong_roster_offering,
    );
    wrong_roster_host
        .open_session(
            DARK_AMM_OFFERING_KEY,
            wrong_id.clone(),
            SessionConfig::with_seed(SESSION_SEED),
        )
        .unwrap();
    assert!(
        wrong_roster_host
            .invoke_binary_operation(
                DARK_AMM_OFFERING_KEY,
                &wrong_id,
                DARK_AMM_SAME_OPENING_OPERATION,
                &request_wire,
                actor.clone(),
            )
            .is_err()
    );

    let accepted = host
        .invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_SAME_OPENING_OPERATION,
            &request_wire,
            actor.clone(),
        )
        .unwrap();
    assert_eq!(accepted.operation, DARK_AMM_SAME_OPENING_OPERATION);
    assert!(
        accepted
            .public_fields
            .iter()
            .any(|(key, value)| key == "bfvCustody" && value == "n=1/opening-threshold=1")
    );
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &id)
            .unwrap()
            .operations
            .len(),
        1
    );
    assert!(
        host.invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_SAME_OPENING_OPERATION,
            &request_wire,
            actor.clone(),
        )
        .is_err(),
        "duplicate is stale by root, sequence, and receipt replay after acceptance"
    );
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &id)
            .unwrap()
            .operations
            .len(),
        1
    );
    let surface = format!(
        "{:?}",
        host.render(DARK_AMM_OFFERING_KEY, &id).unwrap().view()
    );
    assert!(surface.contains("Tier-1 exact-opening receipts required"));
    assert!(surface.contains("issuer-visible"));
    drop(host);

    // Restart uses the durable v3 body to rebuild both the pool/root cursor and
    // the same-opening replay set. No live preflight state is carried across.
    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    reopened.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — exact-opening pool",
        DarkAmmGameOffering::demo_same_opening_required(
            DarkAmmHostKeyMaterial::from_secret_wire_bytes(&key_wire).unwrap(),
            statement.old_root,
            issuer_public,
            2,
        )
        .unwrap(),
    );
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    assert!(
        reopened
            .invoke_binary_operation(
                DARK_AMM_OFFERING_KEY,
                &id,
                DARK_AMM_SAME_OPENING_OPERATION,
                &request_wire,
                actor,
            )
            .is_err()
    );
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &id)
            .unwrap()
            .operations
            .len(),
        1
    );
}
