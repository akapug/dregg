//! No-Rust producer lifecycle: owner-only private initialization, proof-context
//! publication, integrated prove+encrypt bundles, and chained successor state.

#![cfg(feature = "dark-amm-game")]

use std::path::Path;
use std::process::{Command, Output};

use dreggnet_market::dark_amm_game::{
    DARK_AMM_PROVED_OPERATION, DarkAmmGameOffering, DarkAmmHostKeyMaterial, DarkAmmPrivateState,
    DarkAmmPrivateSwapAuthority, DarkAmmPublicSession, ProvedEncryptedSwapRequest,
    private_amm_statement_from_wire,
};
use dreggnet_offerings::{DreggIdentity, Offering, SessionConfig};
use rand_09::SeedableRng;
use rand_09::rngs::StdRng;

const SESSION_ID: &str = "private-producer-lifecycle";

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

#[test]
fn private_cli_initializes_proves_encrypts_and_chains_two_transitions() {
    let dir = std::env::temp_dir().join(format!(
        "dregg-dark-amm-private-tool-{}-{}",
        std::process::id(),
        seed()
    ));
    std::fs::create_dir(&dir).unwrap();
    let key_file = dir.join("host.dbak");
    let bootstrap_public = dir.join("bootstrap.dbap");
    let state0_file = dir.join("state-0.dbao");
    let public0_file = dir.join("public-0.dbap");
    let bundle0 = dir.join("bundle-0");
    let public1_file = dir.join("public-1.dbap");
    let bundle1 = dir.join("bundle-1");

    let mut rng = StdRng::seed_from_u64(0xDA_70);
    let keys = DarkAmmHostKeyMaterial::generate(&mut rng).unwrap();
    std::fs::write(&key_file, keys.to_secret_wire_bytes()).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&key_file, std::fs::Permissions::from_mode(0o600)).unwrap();
    }

    success(&[
        "public-id".into(),
        path(&key_file),
        SESSION_ID.into(),
        path(&bootstrap_public),
    ]);
    success(&[
        "private-init".into(),
        path(&bootstrap_public),
        "100".into(),
        "900".into(),
        path(&state0_file),
    ]);
    #[cfg(unix)]
    {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        assert_eq!(
            std::fs::metadata(&state0_file).unwrap().mode() & 0o777,
            0o600
        );
        // A readable-by-group copy is refused even when its checksum is valid.
        let loose = dir.join("state-loose.dbao");
        std::fs::copy(&state0_file, &loose).unwrap();
        std::fs::set_permissions(&loose, std::fs::Permissions::from_mode(0o640)).unwrap();
        let output = dir.join("loose-refused.dbap");
        refusal(
            &[
                "public-id-private".into(),
                path(&key_file),
                SESSION_ID.into(),
                path(&loose),
                path(&output),
            ],
            "remove all group/other permissions",
        );
        assert!(!output.exists());
    }

    let state0_bytes = std::fs::read(&state0_file).unwrap();
    let state0 = DarkAmmPrivateState::from_wire_bytes(&state0_bytes).unwrap();
    assert_eq!(state0.x(), 100);
    assert_eq!(state0.y(), 900);
    assert_eq!(state0.to_wire_bytes(), state0_bytes);

    success(&[
        "public-id-private".into(),
        path(&key_file),
        SESSION_ID.into(),
        path(&state0_file),
        path(&public0_file),
    ]);
    let public0 =
        DarkAmmPublicSession::from_wire_bytes(&std::fs::read(&public0_file).unwrap()).unwrap();
    assert_eq!(
        public0.proof_context().unwrap().current_root(),
        state0.root().unwrap()
    );

    // A different hosted session cannot install this private opening.
    let wrong_public = dir.join("wrong-session.dbap");
    refusal(
        &[
            "public-id-private".into(),
            path(&key_file),
            "another-session".into(),
            path(&state0_file),
            path(&wrong_public),
        ],
        "does not match the public session",
    );
    assert!(!wrong_public.exists());

    // Wrong economics refuses before a bundle directory is published.
    let wrong_quote = dir.join("wrong-quote-bundle");
    refusal(
        &[
            "private-swap".into(),
            path(&public0_file),
            path(&state0_file),
            "50".into(),
            "301".into(),
            "200".into(),
            "400".into(),
            path(&wrong_quote),
        ],
        "invariant mismatch",
    );
    assert!(!wrong_quote.exists());

    success(&[
        "private-swap".into(),
        path(&public0_file),
        path(&state0_file),
        "50".into(),
        "300".into(),
        "200".into(),
        "400".into(),
        path(&bundle0),
    ]);
    for member in [
        "request.dbam",
        "statement.dbas",
        "next-state.dbao",
        "authority.dbaa",
    ] {
        assert!(bundle0.join(member).is_file(), "missing {member}");
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        assert_eq!(std::fs::metadata(&bundle0).unwrap().mode() & 0o777, 0o700);
        assert_eq!(
            std::fs::metadata(bundle0.join("next-state.dbao"))
                .unwrap()
                .mode()
                & 0o777,
            0o600
        );
        assert_eq!(
            std::fs::metadata(bundle0.join("authority.dbaa"))
                .unwrap()
                .mode()
                & 0o777,
            0o600
        );
    }
    let statement0 =
        private_amm_statement_from_wire(&std::fs::read(bundle0.join("statement.dbas")).unwrap())
            .unwrap();
    assert_eq!(statement0.old_root, state0.root().unwrap());
    let state1 = DarkAmmPrivateState::from_wire_bytes(
        &std::fs::read(bundle0.join("next-state.dbao")).unwrap(),
    )
    .unwrap();
    assert_eq!((state1.x(), state1.y()), (150, 600));
    assert_eq!(state1.root().unwrap(), statement0.new_root);
    let request0 = ProvedEncryptedSwapRequest::from_wire_bytes(
        &std::fs::read(bundle0.join("request.dbam")).unwrap(),
    )
    .unwrap();
    let authority0 = DarkAmmPrivateSwapAuthority::from_wire_bytes(
        &std::fs::read(bundle0.join("authority.dbaa")).unwrap(),
    )
    .unwrap();
    authority0.validate_bundle(&public0, &request0).unwrap();
    assert_eq!(authority0.dx_opening_material().0, 50);
    assert_eq!(authority0.dy_opening_material().0, 300);
    let mut tampered_authority = authority0.to_wire_bytes();
    tampered_authority[80] ^= 1;
    assert!(DarkAmmPrivateSwapAuthority::from_wire_bytes(&tampered_authority).is_err());

    let offering =
        DarkAmmGameOffering::demo_proof_required(keys.clone(), state0.root().unwrap()).unwrap();
    let mut session = offering.open(SessionConfig::with_seed(seed())).unwrap();
    offering
        .invoke_binary_operation(
            &mut session,
            DARK_AMM_PROVED_OPERATION,
            &std::fs::read(bundle0.join("request.dbam")).unwrap(),
            DreggIdentity("private-cli-trader-0".into()),
        )
        .unwrap();

    success(&[
        "proved-cursor".into(),
        path(&public0_file),
        path(&bundle0.join("statement.dbas")),
        "1".into(),
        path(&public1_file),
    ]);

    // A stale private opening is rejected against the advanced public root.
    let stale_bundle = dir.join("stale-state-bundle");
    refusal(
        &[
            "private-swap".into(),
            path(&public1_file),
            path(&state0_file),
            "150".into(),
            "300".into(),
            "200".into(),
            "400".into(),
            path(&stale_bundle),
        ],
        "does not match the proof context's current root",
    );
    assert!(!stale_bundle.exists());

    // Checksummed state corruption fails before proving or publishing.
    let tampered_state = dir.join("state-tampered.dbao");
    let mut tampered = std::fs::read(bundle0.join("next-state.dbao")).unwrap();
    *tampered.last_mut().unwrap() ^= 1;
    std::fs::write(&tampered_state, tampered).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(&tampered_state, std::fs::Permissions::from_mode(0o600)).unwrap();
    }
    let tampered_bundle = dir.join("tampered-state-bundle");
    refusal(
        &[
            "private-swap".into(),
            path(&public1_file),
            path(&tampered_state),
            "150".into(),
            "300".into(),
            "200".into(),
            "400".into(),
            path(&tampered_bundle),
        ],
        "checksum mismatch",
    );
    assert!(!tampered_bundle.exists());

    success(&[
        "private-swap".into(),
        path(&public1_file),
        path(&bundle0.join("next-state.dbao")),
        "150".into(),
        "300".into(),
        "200".into(),
        "400".into(),
        path(&bundle1),
    ]);
    let statement1 =
        private_amm_statement_from_wire(&std::fs::read(bundle1.join("statement.dbas")).unwrap())
            .unwrap();
    assert_eq!(statement1.old_root, statement0.new_root);
    let state2 = DarkAmmPrivateState::from_wire_bytes(
        &std::fs::read(bundle1.join("next-state.dbao")).unwrap(),
    )
    .unwrap();
    assert_eq!((state2.x(), state2.y()), (300, 300));
    assert_eq!(state2.root().unwrap(), statement1.new_root);
    offering
        .invoke_binary_operation(
            &mut session,
            DARK_AMM_PROVED_OPERATION,
            &std::fs::read(bundle1.join("request.dbam")).unwrap(),
            DreggIdentity("private-cli-trader-1".into()),
        )
        .unwrap();
    assert_eq!(session.accepted_swaps(), 2);
    assert!(offering.verify(&session).verified);

    // Existing output is checked before another expensive proof and is never
    // replaced, even when it is a directory controlled by the caller.
    let collision = dir.join("bundle-collision");
    std::fs::create_dir(&collision).unwrap();
    std::fs::write(collision.join("sentinel"), b"keep me").unwrap();
    refusal(
        &[
            "private-swap".into(),
            path(&public1_file),
            path(&bundle0.join("next-state.dbao")),
            "150".into(),
            "300".into(),
            "200".into(),
            "400".into(),
            path(&collision),
        ],
        "refusing to overwrite existing bundle directory",
    );
    assert_eq!(
        std::fs::read(collision.join("sentinel")).unwrap(),
        b"keep me"
    );

    std::fs::remove_dir_all(dir).unwrap();
}
