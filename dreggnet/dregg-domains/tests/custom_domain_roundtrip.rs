//! The custom-domain round-trip, end to end (docs/PERMISSIONLESS-CLOUD-PLAN.md §3.2):
//! bind a domain → issue the challenge → (mock-DNS) verify → the binding verifies →
//! the gateway routes the custom Host to the bound site → the on-demand-TLS `ask`
//! returns 200 for the verified domain and 404 for an unverified one — and the bind
//! is cap-gated (only the owner binds).
//!
//! Drives the same surfaces the gateway adopts (`DomainRegistry` beside a
//! `SiteRegistry`), with a deterministic `MockDns` standing in for live DNS, so the
//! whole flow proves locally with no real DNS and no real certificate.

use dregg_domains::{
    ChallengeMethod, DOMAINS_CAP, DomainCap, DomainError, DomainRegistry, MockDns,
};
use dreggnet_webapp::WebRequest;
use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry};
use dreggnet_webauth::cred::RootKey;
use dreggnet_webauth::grant::mint_caps;
use dreggnet_webauth::subject_of;

/// The trusted root authority that mints the binding credentials (deterministic).
fn root() -> RootKey {
    RootKey::from_seed([42u8; 32])
}

/// A registry gated by the trusted root — the real cap chain.
fn authed_registry() -> DomainRegistry {
    DomainRegistry::with_authority(root().public())
}

/// A real binding cap: a root-minted `domains` credential exercised for `domain`.
fn cap(domain: &str) -> DomainCap {
    DomainCap::new(mint_caps(&root(), [DOMAINS_CAP], None).encode(), domain)
}

/// Publish a `blog` site and return the registry the bound domain serves from.
fn published_blog() -> SiteRegistry {
    let sites = SiteRegistry::new();
    sites
        .publish(
            &PublishCap::for_site("agent:ember", "blog"),
            "blog",
            SiteContent::new()
                .with("/index.html", "<h1>blog.example.com on a dregg cell</h1>")
                .with("/style.css", "h1{color:rebeccapurple}"),
        )
        .expect("publish");
    sites
}

/// The gateway's Caddy on-demand-TLS `ask` decision, modeled exactly as
/// `gateway/src/main.rs::site_exists_ask` does it: a cert is minted iff the host is
/// a published `<name>.example.com` site OR a *verified* custom domain.
fn ask_cert_ok(sites: &SiteRegistry, domains: &DomainRegistry, host: &str) -> bool {
    use dreggnet_webapp::hosting::site_name_from_host;
    let wildcard = site_name_from_host(host)
        .map(|name| sites.get(&name).is_some())
        .unwrap_or(false);
    wildcard || domains.is_verified(host)
}

/// The gateway's host resolution, modeled as `SiteHostHandler` does it: a verified
/// custom domain resolves to its bound site; otherwise fall through to the
/// `<name>.example.com` path.
fn gateway_resolve(sites: &SiteRegistry, domains: &DomainRegistry, host: &str, path: &str) -> u16 {
    let req = WebRequest::get(path);
    if let Some(resp) = domains.resolve(sites, host, &req) {
        return resp.status;
    }
    sites.resolve(host, &req).status
}

#[test]
fn bind_challenge_verify_route_and_ask_gating() {
    let sites = published_blog();
    let domains = authed_registry();

    // ── ① BIND (cap-gated by a REAL credential) ──────────────────────────────
    let domain = "blog.example.com";
    let binding_cap = cap(domain);
    let owner = subject_of(&binding_cap.credential).expect("subject");
    let receipt = domains
        .bind(&binding_cap, domain, "blog", ChallengeMethod::Txt)
        .expect("bind");
    assert_eq!(receipt.site, "blog");
    assert_eq!(receipt.owner, owner);

    // ── ② CHALLENGE ───────────────────────────────────────────────────────────
    // The owner is told exactly what TXT record to publish.
    let challenge = receipt.challenge.clone();
    assert_eq!(challenge.record_type, ChallengeMethod::Txt);
    assert_eq!(challenge.record_name, "_dregg-verify.blog.example.com");
    assert!(challenge.expected_value.starts_with("dregg-verify-"));

    // Before the proof exists: not verified → the gateway does NOT route the custom
    // Host to the site, and the cert `ask` is 404 (no cert for an unverified domain).
    assert!(!domains.is_verified(domain));
    assert!(
        !ask_cert_ok(&sites, &domains, domain),
        "no cert for an unproven domain"
    );
    // The custom Host falls through to the example.com path, which has no
    // `blog.example.com` site → 404.
    assert_eq!(gateway_resolve(&sites, &domains, domain, "/"), 404);

    // ── ③ VERIFY (mock DNS) ──────────────────────────────────────────────────
    // The owner publishes the challenged TXT; the DNS lookup proves control.
    let dns = MockDns::new().with_txt(&challenge.record_name, &challenge.expected_value);
    let binding = domains.verify(domain, &dns).expect("verify");
    assert!(binding.is_verified());
    assert!(
        binding.verified_seq.is_some(),
        "the verifying turn is recorded"
    );

    // ── ④ ROUTE ──────────────────────────────────────────────────────────────
    // The verified custom Host now resolves to the bound `blog` site cell.
    assert_eq!(
        gateway_resolve(&sites, &domains, "blog.example.com", "/"),
        200
    );
    assert_eq!(
        gateway_resolve(&sites, &domains, "blog.example.com:443", "/style.css"),
        200
    );
    // A path the site doesn't have is the site cell's own 404 (resolution worked).
    assert_eq!(
        gateway_resolve(&sites, &domains, "blog.example.com", "/missing"),
        404
    );

    // ── ⑤ THE ASK (cert gating) ──────────────────────────────────────────────
    // Verified custom domain → 200 (Caddy mints a cert); the wildcard site still 200.
    assert!(ask_cert_ok(&sites, &domains, "blog.example.com"));
    assert!(ask_cert_ok(&sites, &domains, "blog.example.com"));
    // An unverified / squatted custom domain → no cert.
    assert!(!ask_cert_ok(&sites, &domains, "squat.attacker.com"));
}

#[test]
fn binding_needs_a_real_cap_and_only_the_owner_rebinds() {
    let domains = authed_registry();
    let domain = "shop.example.com";

    // A self-fabricated credential (a DIFFERENT, untrusted root) cannot bind —
    // the cap is verified against the trusted authority, not self-asserted.
    let attacker_root = RootKey::from_seed([7u8; 32]);
    let forged = DomainCap::new(
        mint_caps(&attacker_root, [DOMAINS_CAP], None).encode(),
        domain,
    );
    assert!(matches!(
        domains.bind(&forged, domain, "blog", ChallengeMethod::Txt),
        Err(DomainError::CapRefused { .. }),
    ));

    // A cap exercised for a DIFFERENT domain cannot bind this one.
    let wrong_domain = cap("other.example.com");
    assert!(matches!(
        domains.bind(&wrong_domain, domain, "blog", ChallengeMethod::Txt),
        Err(DomainError::CapRefused { .. }),
    ));

    // The rightful owner (a real root-minted credential) binds.
    let alice = cap(domain);
    assert!(
        domains
            .bind(&alice, domain, "blog", ChallengeMethod::Txt)
            .is_ok()
    );

    // A second, distinct owner (Mallory) cannot overwrite Alice's binding.
    let mallory = cap(domain);
    assert!(matches!(
        domains.bind(&mallory, domain, "evil", ChallengeMethod::Txt),
        Err(DomainError::OwnerMismatch { .. }),
    ));
    assert_eq!(domains.get(domain).unwrap().site, "blog");
}

#[test]
fn cname_proof_also_routes() {
    let sites = published_blog();
    let domains = authed_registry();
    let domain = "www.example.com";

    let receipt = domains
        .bind(&cap(domain), domain, "blog", ChallengeMethod::Cname)
        .expect("bind");
    // CNAME proof: point the apex at <site>.example.com.
    assert_eq!(receipt.challenge.expected_value, "blog.example.com");

    let dns = MockDns::new().with_cname(domain, "blog.example.com");
    domains.verify(domain, &dns).expect("verify");
    assert_eq!(gateway_resolve(&sites, &domains, domain, "/"), 200);
    assert!(ask_cert_ok(&sites, &domains, domain));
}
