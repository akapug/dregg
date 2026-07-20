//! The proof-required Dark Pool operation verifies a hiding receipt before the
//! encrypted candidate, advances one public root cursor, and restart-replays
//! the exact proof/ciphertext journal without enabling proofless v1.

#![cfg(feature = "dark-amm-game")]

use std::process::Command;

use dregg_circuit_prove::dark_amm_private::{
    DIGEST_WIDTH, PrivateAmmWitness, PublicStatement, prove_zk,
};
use dreggnet_market::dark_amm_game::{
    DARK_AMM_OFFERING_KEY, DARK_AMM_OPERATION, DARK_AMM_PROVED_DISCLOSURE,
    DARK_AMM_PROVED_OPERATION, DarkAmmGameOffering, DarkAmmHostKeyMaterial, DarkAmmPublicSession,
    private_amm_statement_to_wire, produce_proved_encrypted_swap,
};
use dreggnet_offerings::resume::{InMemoryResumeStore, SessionResumeStore};
use dreggnet_offerings::{DreggIdentity, OfferingHost, SessionConfig, SessionId};
use rand_09::SeedableRng;
use rand_09::rngs::StdRng;

const SEED: u64 = 0xA771_5700;

fn keys(seed: u64) -> DarkAmmHostKeyMaterial {
    let mut rng = StdRng::seed_from_u64(seed);
    DarkAmmHostKeyMaterial::generate(&mut rng).expect("deployment BFV keys")
}

fn blind(base: u32) -> [u32; DIGEST_WIDTH] {
    core::array::from_fn(|lane| base + lane as u32)
}

fn witness1() -> PrivateAmmWitness {
    PrivateAmmWitness::try_new(100, 900, 50, 300, blind(1_000), blind(2_000)).unwrap()
}

fn witness2() -> PrivateAmmWitness {
    PrivateAmmWitness::try_new(150, 600, 150, 300, blind(2_000), blind(3_000)).unwrap()
}

fn receipt_material(
    legacy_public: &DarkAmmPublicSession,
    witness: &PrivateAmmWitness,
) -> (Vec<u8>, PublicStatement) {
    let (proof, statement) = prove_zk(legacy_public.private_amm_receipt_session(), witness)
        .expect("hiding receipt proves");
    (proof.to_postcard().expect("proof transport"), statement)
}

#[test]
fn proved_swaps_pin_root_hold_on_tamper_and_restart_replay() {
    let key_material = keys(0xD6);
    let key_wire = key_material.to_secret_wire_bytes();
    // Session binding is independent of the initial root, so an external
    // producer can learn the receipt session before committing its first root.
    let legacy_public = DarkAmmGameOffering::demo(key_material.clone())
        .public_session_for_seed(SEED)
        .unwrap();
    let (proof1, statement1) = receipt_material(&legacy_public, &witness1());
    let (proof2, statement2) = receipt_material(&legacy_public, &witness2());
    assert_eq!(statement1.new_root, statement2.old_root);

    let offering =
        DarkAmmGameOffering::demo_proof_required(key_material.clone(), statement1.old_root)
            .unwrap();
    let public = offering.public_session_for_seed(SEED).unwrap();
    assert_eq!(
        DarkAmmPublicSession::from_wire_bytes(&public.to_wire_bytes()).unwrap(),
        public
    );
    assert_eq!(
        public.proof_context().unwrap().current_root(),
        statement1.old_root
    );

    let dir = std::env::temp_dir().join(format!(
        "dregg-dark-amm-proved-{}-{SEED}",
        std::process::id()
    ));
    std::fs::create_dir(&dir).unwrap();
    let public_file = dir.join("session.dbap");
    let statement_file = dir.join("statement.dbas");
    let proof_file = dir.join("proof.postcard");
    let request_file = dir.join("proved.dbam");
    std::fs::write(&public_file, public.to_wire_bytes()).unwrap();
    std::fs::write(&statement_file, private_amm_statement_to_wire(statement1)).unwrap();
    std::fs::write(&proof_file, &proof1).unwrap();
    let status = Command::new(env!("CARGO_BIN_EXE_dark-amm-tool"))
        .arg("proved-swap")
        .arg(&public_file)
        .arg(&statement_file)
        .arg(&proof_file)
        .args(["50", "300", "200", "400"])
        .arg(&request_file)
        .status()
        .expect("offline proved-swap command runs");
    assert!(status.success());
    let first = std::fs::read(&request_file).unwrap();

    // A valid semantic proof paired with a different encrypted candidate is
    // still refused by the BFV decision. This is the executable, honest tooth
    // around the not-yet-proved same-opening residual.
    let mut mismatch_rng = StdRng::seed_from_u64(41);
    let mismatch = produce_proved_encrypted_swap(
        &public,
        50,
        301,
        200,
        400,
        statement1,
        proof1.clone(),
        &mut mismatch_rng,
    )
    .unwrap()
    .to_wire_bytes();

    let store = InMemoryResumeStore::new();
    let id = SessionId::new("proved-dark-pool");
    let mut host = OfferingHost::new().with_resume_store(Box::new(store.clone()));
    host.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — shielded pool",
        offering,
    );
    host.open_session(
        DARK_AMM_OFFERING_KEY,
        id.clone(),
        SessionConfig::with_seed(SEED),
    )
    .unwrap();
    let operations = host.binary_operations(DARK_AMM_OFFERING_KEY, &id).unwrap();
    assert_eq!(operations.len(), 1);
    assert_eq!(operations[0].name, DARK_AMM_PROVED_OPERATION);
    assert_eq!(operations[0].disclosure, DARK_AMM_PROVED_DISCLOSURE);
    assert!(operations.iter().all(|op| op.name != DARK_AMM_OPERATION));

    assert!(
        host.invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_PROVED_OPERATION,
            &mismatch,
            DreggIdentity("different-opening".into()),
        )
        .unwrap_err()
        .to_string()
        .contains("same-opening is not yet proved")
    );
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &id)
            .unwrap()
            .operations
            .len(),
        0
    );

    let mut wrong_old_root = first.clone();
    let encrypted_len = u64::from_le_bytes(wrong_old_root[8..16].try_into().unwrap()) as usize;
    let first_old_root_byte = 16 + encrypted_len + 3 * 4;
    wrong_old_root[first_old_root_byte] ^= 1;
    let refusal = host
        .invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_PROVED_OPERATION,
            &wrong_old_root,
            DreggIdentity("root-tamper".into()),
        )
        .unwrap_err()
        .to_string();
    assert!(refusal.contains("old root is not the table's current root"));
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &id)
            .unwrap()
            .operations
            .len(),
        0
    );

    let mut corrupted = first.clone();
    *corrupted.last_mut().unwrap() ^= 0x80;
    assert!(
        host.invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_PROVED_OPERATION,
            &corrupted,
            DreggIdentity("proof-tamper".into()),
        )
        .is_err()
    );
    assert_eq!(
        store
            .load(DARK_AMM_OFFERING_KEY, &id)
            .unwrap()
            .operations
            .len(),
        0
    );

    let receipt1 = host
        .invoke_binary_operation(
            DARK_AMM_OFFERING_KEY,
            &id,
            DARK_AMM_PROVED_OPERATION,
            &first,
            DreggIdentity("veiled-trader-a".into()),
        )
        .unwrap();
    assert!(
        receipt1
            .public_fields
            .iter()
            .any(|(k, _)| k == "proofDigest")
    );
    assert!(
        receipt1
            .public_fields
            .iter()
            .any(|(k, _)| k == "statementDigest")
    );

    let next_public = public
        .clone()
        .at_proof_cursor(1, statement1.new_root)
        .unwrap();
    let mut rng = StdRng::seed_from_u64(42);
    let second = produce_proved_encrypted_swap(
        &next_public,
        150,
        300,
        200,
        400,
        statement2,
        proof2,
        &mut rng,
    )
    .unwrap()
    .to_wire_bytes();
    host.invoke_binary_operation(
        DARK_AMM_OFFERING_KEY,
        &id,
        DARK_AMM_PROVED_OPERATION,
        &second,
        DreggIdentity("veiled-trader-b".into()),
    )
    .unwrap();

    let log = store.load(DARK_AMM_OFFERING_KEY, &id).unwrap();
    assert_eq!(log.operations.len(), 2);
    assert!(log.operations.iter().all(|operation| {
        operation.name == DARK_AMM_PROVED_OPERATION
            && operation.replay_disclosure == DARK_AMM_PROVED_DISCLOSURE
            && operation
                .receipt
                .public_fields
                .iter()
                .any(|(k, _)| k == "proofDigest")
    }));
    let surface = format!(
        "{:?}",
        host.render(DARK_AMM_OFFERING_KEY, &id).unwrap().view()
    );
    assert!(surface.contains("2 encrypted swap(s) accepted"));
    assert!(surface.contains("Hiding receipt required"));
    assert!(surface.contains("same dx/dy opening"));
    drop(host);

    let mut reopened = OfferingHost::new().with_resume_store(Box::new(store));
    reopened.register(
        DARK_AMM_OFFERING_KEY,
        "The Dark Bazaar — shielded pool",
        DarkAmmGameOffering::demo_proof_required(
            DarkAmmHostKeyMaterial::from_secret_wire_bytes(&key_wire).unwrap(),
            statement1.old_root,
        )
        .unwrap(),
    );
    let resumed = reopened.resume_all();
    assert_eq!(resumed.len(), 1);
    assert!(resumed[0].1.is_ok(), "{resumed:?}");
    let surface = format!(
        "{:?}",
        reopened.render(DARK_AMM_OFFERING_KEY, &id).unwrap().view()
    );
    assert!(surface.contains("2 encrypted swap(s) accepted"));

    std::fs::remove_dir_all(dir).unwrap();
}
