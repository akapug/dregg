//! Durable data plane — the **bind/verify → restart → reconstruct** proof for the
//! domain registry (docs/CLOUD-PROVIDER-READINESS.md data-plane blocker).
//!
//! A domain binding lived only in an in-memory `BTreeMap` and was LOST ON RESTART —
//! so a proven custom domain would stop routing (and lose its cert eligibility) the
//! moment the gateway rebooted. With the durable umem backend ([`dreggnet_umem`])
//! attached, the registry IS a umem cell: a bound / verified `DomainBinding` is laid
//! into the cell's committed heap and sealed to a real Poseidon2 boundary root, so a
//! fresh registry over the same path RECONSTRUCTS the bindings FROM the committed heap —
//! including their Verified state, so routing + the cert `ask` survive.

use dregg_domains::{ChallengeMethod, DOMAINS_CAP, DomainCap, DomainRegistry, MockDns};
use dreggnet_webauth::cred::RootKey;
use dreggnet_webauth::grant::mint_caps;

fn root() -> RootKey {
    RootKey::from_seed([42u8; 32])
}

fn cap(domain: &str) -> DomainCap {
    DomainCap::new(mint_caps(&root(), [DOMAINS_CAP], None).encode(), domain)
}

fn temp_path(tag: &str) -> std::path::PathBuf {
    let mut p = std::env::temp_dir();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    p.push(format!("dreggnet-durable-domains-{tag}-{nanos}.log"));
    p
}

/// Bind + verify a custom domain, "restart", and confirm the binding is
/// reconstructed AS VERIFIED — it still routes and still passes the cert `ask`,
/// owned by the binder, without re-proving control.
#[test]
fn verified_binding_survives_a_restart() {
    let path = temp_path("verified");

    let owner;
    {
        let reg = DomainRegistry::with_authority(root().public())
            .with_durable_store(&path)
            .expect("open durable registry");
        let c = cap("blog.example.com");
        let r = reg
            .bind(&c, "blog.example.com", "blog", ChallengeMethod::Txt)
            .expect("bind");
        owner = r.owner.clone();
        // Prove control via the mock DNS challenge → Verified.
        let dns = MockDns::new().with_txt(&r.challenge.record_name, &r.challenge.expected_value);
        reg.verify("blog.example.com", &dns).expect("verify");
        assert!(reg.is_verified("blog.example.com"));
    }

    // "Restart": a brand-new registry over the same durable path reconstructs the
    // binding — and the Verified state with it.
    let restarted = DomainRegistry::with_authority(root().public())
        .with_durable_store(&path)
        .expect("reopen");
    assert!(
        restarted.is_verified("blog.example.com"),
        "the verified binding is reconstructed as Verified (routing + cert ask survive)"
    );
    assert_eq!(
        restarted.site_for_host("blog.example.com").as_deref(),
        Some("blog"),
        "the verified custom domain still routes after a restart"
    );
    assert_eq!(
        restarted.get("blog.example.com").unwrap().owner,
        owner,
        "owned correctly after restart"
    );

    std::fs::remove_file(&path).ok();
}

/// A pending (unverified) binding survives a restart as Pending, and can be verified
/// AFTER the restart — exactly-once (no duplicate binding on reload).
#[test]
fn pending_binding_survives_and_verifies_after_restart() {
    let path = temp_path("pending");

    {
        let reg = DomainRegistry::with_authority(root().public())
            .with_durable_store(&path)
            .expect("open");
        let r = reg
            .bind(
                &cap("shop.example.com"),
                "shop.example.com",
                "shop",
                ChallengeMethod::Txt,
            )
            .expect("bind");
        // Note the challenge so we can satisfy it after the restart (the nonce is
        // durable, so the published DNS record stays valid across the reboot).
        std::fs::write(path.with_extension("nonce"), &r.challenge.expected_value).unwrap();
        std::fs::write(path.with_extension("rec"), &r.challenge.record_name).unwrap();
        assert!(!reg.is_verified("shop.example.com"));
    }

    let restarted = DomainRegistry::with_authority(root().public())
        .with_durable_store(&path)
        .expect("reopen");
    assert_eq!(restarted.list().len(), 1, "no duplicate binding on reload");
    assert!(
        !restarted.is_verified("shop.example.com"),
        "still pending after restart"
    );

    // Verify AFTER the restart using the durable challenge nonce.
    let rec = std::fs::read_to_string(path.with_extension("rec")).unwrap();
    let nonce = std::fs::read_to_string(path.with_extension("nonce")).unwrap();
    let dns = MockDns::new().with_txt(&rec, &nonce);
    restarted
        .verify("shop.example.com", &dns)
        .expect("verify post-restart");
    assert!(restarted.is_verified("shop.example.com"));

    // And the now-verified state is itself durable across a SECOND restart.
    let again = DomainRegistry::with_authority(root().public())
        .with_durable_store(&path)
        .expect("reopen 2");
    assert!(again.is_verified("shop.example.com"));

    std::fs::remove_file(&path).ok();
    std::fs::remove_file(path.with_extension("nonce")).ok();
    std::fs::remove_file(path.with_extension("rec")).ok();
}
