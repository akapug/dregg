//! No-Rust Tier-1 issuer/assembler lifecycle for the strict Dark AMM v3 wire.

#![cfg(feature = "dark-amm-game")]

use std::path::Path;
use std::process::{Command, Output};

use dreggnet_market::dark_amm_game::{
    DARK_AMM_SAME_OPENING_OPERATION, DarkAmmGameOffering, DarkAmmHostKeyMaterial,
    DarkAmmPrivateState, SameOpeningProvedEncryptedSwapRequest,
};
use dreggnet_offerings::{DreggIdentity, Offering, SessionConfig};
use ed25519_dalek::SigningKey;
use fhegg_fhe::amm_same_opening::Tier1SameOpeningEndorsement;
use rand_09::SeedableRng;
use rand_09::rngs::StdRng;

const SESSION_ID: &str = "same-opening-cli-lifecycle";

fn seed() -> u64 {
    let digest = blake3::hash(SESSION_ID.as_bytes());
    u64::from_le_bytes(digest.as_bytes()[..8].try_into().unwrap())
}

fn path(path: &Path) -> String {
    path.display().to_string()
}

fn invoke(args: &[String]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_dark-amm-tool"))
        .args(args)
        .output()
        .expect("dark-amm-tool executes")
}

fn success(args: &[String]) {
    let output = invoke(args);
    assert!(
        output.status.success(),
        "command failed: {}\nstdout: {}\nstderr: {}",
        args.join(" "),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn refusal(args: &[String], needle: &str) {
    let output = invoke(args);
    assert!(!output.status.success(), "command unexpectedly succeeded");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains(needle),
        "{stderr:?} did not contain {needle:?}"
    );
}

fn protect(path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o600)).unwrap();
    }
}

#[test]
fn separate_issuers_assemble_a_host_acceptable_v3_request() {
    let dir = std::env::temp_dir().join(format!(
        "dregg-dark-amm-same-opening-tool-{}-{}",
        std::process::id(),
        seed()
    ));
    std::fs::create_dir(&dir).unwrap();
    let host_key_file = dir.join("host.dbak");
    let bootstrap_public = dir.join("bootstrap.dbap");
    let state_file = dir.join("state.dbao");
    let public_file = dir.join("public.dbap");
    let bundle = dir.join("bundle");
    let roster_file = dir.join("issuers.roster");
    let endorsement_0 = dir.join("issuer-0.fhase");
    let endorsement_2 = dir.join("issuer-2.fhase");
    let v3_file = dir.join("request-v3.dbam");

    let mut rng = StdRng::seed_from_u64(0xDA_73);
    let host_keys = DarkAmmHostKeyMaterial::generate(&mut rng).unwrap();
    std::fs::write(&host_key_file, host_keys.to_secret_wire_bytes()).unwrap();
    protect(&host_key_file);
    success(&[
        "public-id".into(),
        path(&host_key_file),
        SESSION_ID.into(),
        path(&bootstrap_public),
    ]);
    success(&[
        "private-init".into(),
        path(&bootstrap_public),
        "100".into(),
        "900".into(),
        path(&state_file),
    ]);
    success(&[
        "public-id-private".into(),
        path(&host_key_file),
        SESSION_ID.into(),
        path(&state_file),
        path(&public_file),
    ]);
    success(&[
        "private-swap".into(),
        path(&public_file),
        path(&state_file),
        "50".into(),
        "300".into(),
        "200".into(),
        "400".into(),
        path(&bundle),
    ]);

    let issuer_keys = [0x81, 0x82, 0x83].map(|seed| SigningKey::from_bytes(&[seed; 32]));
    let mut roster = Vec::new();
    let mut issuer_key_files = Vec::new();
    for (index, key) in issuer_keys.iter().enumerate() {
        roster.extend_from_slice(&key.verifying_key().to_bytes());
        let key_file = dir.join(format!("issuer-{index}.key"));
        std::fs::write(&key_file, key.to_bytes()).unwrap();
        protect(&key_file);
        issuer_key_files.push(key_file);
    }
    std::fs::write(&roster_file, roster).unwrap();

    let endorse = |index: usize, output: &Path| {
        vec![
            "same-opening-endorse".into(),
            path(&public_file),
            path(&bundle.join("request.dbam")),
            path(&bundle.join("authority.dbaa")),
            path(&roster_file),
            "2".into(),
            index.to_string(),
            path(&issuer_key_files[index]),
            path(output),
        ]
    };
    success(&endorse(0, &endorsement_0));
    success(&endorse(2, &endorsement_2));
    let parsed_0 =
        Tier1SameOpeningEndorsement::from_wire_bytes(&std::fs::read(&endorsement_0).unwrap())
            .unwrap();
    let parsed_2 =
        Tier1SameOpeningEndorsement::from_wire_bytes(&std::fs::read(&endorsement_2).unwrap())
            .unwrap();
    assert_eq!(parsed_0.signature.signer_index, 0);
    assert_eq!(parsed_2.signature.signer_index, 2);
    assert_eq!(parsed_0.claim, parsed_2.claim);

    refusal(
        &endorse(0, &endorsement_0),
        "refusing to overwrite existing endorsement output",
    );
    let wrong_key_output = dir.join("wrong-key.fhase");
    let mut wrong_key = endorse(1, &wrong_key_output);
    wrong_key[7] = path(&issuer_key_files[0]);
    refusal(&wrong_key, "SignerKeyMismatch");
    assert!(!wrong_key_output.exists());

    let assemble = |output: &Path, endorsements: &[&Path]| {
        let mut args = vec![
            "same-opening-assemble".into(),
            path(&public_file),
            path(&bundle.join("request.dbam")),
            path(&bundle.join("authority.dbaa")),
            path(&roster_file),
            "2".into(),
            path(output),
        ];
        args.extend(endorsements.iter().map(|endorsement| path(endorsement)));
        args
    };
    let duplicate_output = dir.join("duplicate.dbam");
    refusal(
        &assemble(&duplicate_output, &[&endorsement_0, &endorsement_0]),
        "DuplicateSigner",
    );
    assert!(!duplicate_output.exists());
    success(&assemble(&v3_file, &[&endorsement_2, &endorsement_0]));
    let v3_wire = std::fs::read(&v3_file).unwrap();
    let v3 = SameOpeningProvedEncryptedSwapRequest::from_wire_bytes(&v3_wire).unwrap();
    assert_eq!(v3.sequence(), 0);
    assert_eq!(
        v3.same_opening_receipt()
            .signatures
            .iter()
            .map(|signature| signature.signer_index)
            .collect::<Vec<_>>(),
        vec![0, 2]
    );

    let state = DarkAmmPrivateState::from_wire_bytes(&std::fs::read(&state_file).unwrap()).unwrap();
    let offering = DarkAmmGameOffering::demo_same_opening_required(
        host_keys,
        state.root().unwrap(),
        issuer_keys
            .iter()
            .map(|key| key.verifying_key().to_bytes())
            .collect(),
        2,
    )
    .unwrap();
    let mut session = offering.open(SessionConfig::with_seed(seed())).unwrap();
    offering
        .invoke_binary_operation(
            &mut session,
            DARK_AMM_SAME_OPENING_OPERATION,
            &v3_wire,
            DreggIdentity("cli-tier1-trader".into()),
        )
        .unwrap();
    assert_eq!(session.accepted_swaps(), 1);

    std::fs::remove_dir_all(dir).unwrap();
}
