//! The site-publish-over-HTTP + cap-scoped console read surfaces, end-to-end at the
//! handler level over ONE shared signed registry — the proof the live-cloud gap the
//! CLI + console lanes flagged is closed.
//!
//! The unit tests in `gateway::sitepublish` / `gateway::api` cover each handler in
//! isolation; this ties them together the way the running gateway wires them: a
//! client POSTs a built bundle to the publish handler, the SAME registry's static
//! data plane then serves it, the signed bundle re-witnesses it (and a tampered byte
//! is refused), and the console read plane over that same registry returns only the
//! caller's own records (another subject sees none).

use std::sync::Arc;

use dreggnet_bridge::{CapGrade, Lease};
use dreggnet_gateway::SiteHostHandler;
use dreggnet_gateway::api::ApiHandler;
use dreggnet_gateway::funding::{FundingError, FundingSource};
use dreggnet_gateway::sitepublish::{SITE_CAP_PREFIX, SitePublishHandler};

use dregg_domains::DomainRegistry;
use dreggnet_http::{Method, ResponseWriter};
use dreggnet_storage::BucketRegistry;
use dreggnet_webapp::HttpMethod;
use dreggnet_webapp::hosting::{SiteContent, SiteRegistry};
use dreggnet_webapp::verify::{SiteVerifyError, verify_site_bundle};
use dreggnet_webauth::cred::RootKey;
use dreggnet_webauth::grant::mint_caps;
use dreggnet_webauth::subject_of;

const NOW: u64 = 1_000;

/// A stub funding source attesting a generous funded lease for one subject (the
/// owner) — the chain's verified attestation stand-in the wireup tests use.
struct FundsSubject(String);
impl FundingSource for FundsSubject {
    fn funded_leases(&self, app: &str) -> Result<Vec<Lease>, FundingError> {
        if app == self.0 {
            Ok(vec![Lease::funded(
                app,
                CapGrade::MicroVm,
                "computrons",
                1_000_000,
                1,
            )])
        } else {
            Ok(vec![])
        }
    }
}

fn bundle(headline: &str) -> Vec<u8> {
    let content = SiteContent::new()
        .with("/index.html", format!("<h1>{headline}</h1>"))
        .with("/style.css", "h1{color:teal}");
    serde_json::to_vec(&content).unwrap()
}

#[test]
fn publish_over_http_then_serve_verify_and_list() {
    let root = RootKey::from_seed([7u8; 32]);
    // ONE signed registry shared by the publish control plane and the static data
    // plane (and the console read plane) — a publish here is served + listed there.
    let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
    let signer = registry.receipt_signer().unwrap();

    // Two owners, each with their own site-host cap.
    let alice_cred = mint_caps(&root, [format!("{SITE_CAP_PREFIX}alice-blog")], None).encode();
    let bob_cred = mint_caps(&root, [format!("{SITE_CAP_PREFIX}bob-blog")], Some(9_999)).encode();
    let alice = subject_of(&alice_cred).unwrap();
    let bob = subject_of(&bob_cred).unwrap();
    assert_ne!(alice, bob);

    let funding: Arc<dyn FundingSource> = Arc::new(FundsAny);
    struct FundsAny;
    impl FundingSource for FundsAny {
        fn funded_leases(&self, app: &str) -> Result<Vec<Lease>, FundingError> {
            Ok(vec![Lease::funded(
                app,
                CapGrade::MicroVm,
                "computrons",
                1_000_000,
                1,
            )])
        }
    }

    let publish =
        SitePublishHandler::new(Arc::clone(&registry), Some(root.public()), Some(funding));
    let site = SiteHostHandler::new(Arc::clone(&registry));
    let api = ApiHandler::new(
        Arc::clone(&registry),
        Arc::new(DomainRegistry::new()),
        Arc::new(BucketRegistry::new()),
    );

    // ── PUBLISH over HTTP (cap-gated + funded + receipted) ───────────────────────
    let resp = publish.respond(
        HttpMethod::Post,
        "/v1/sites/alice-blog/publish",
        Some(&alice_cred),
        &bundle("alice on the live cloud"),
        NOW,
    );
    assert_eq!(resp.status, 201, "publish: {}", resp.body_str());
    let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    let content_root = v["content_root"].as_str().unwrap().to_string();
    assert_eq!(content_root.len(), 64);
    assert_eq!(
        v["signer"].as_str().unwrap(),
        dreggnet_webapp::hex32(&signer)
    );

    // bob publishes his own site too (a second owner, for the scope teeth).
    assert_eq!(
        publish
            .respond(
                HttpMethod::Post,
                "/v1/sites/bob-blog/publish",
                Some(&bob_cred),
                &bundle("bob secret"),
                NOW,
            )
            .status,
        201
    );

    // ── SERVE: the just-published cell is served by Host on the same registry ─────
    let raw = run_get(&site, "alice-blog.example.com", "/");
    assert!(raw.contains("200 OK"), "served: {raw}");
    assert!(
        raw.contains("alice on the live cloud"),
        "served bytes: {raw}"
    );

    // ── VERIFY: the signed bundle re-witnesses (the dregg-cloud verify path) ──────
    let vb = registry.site_bundle("alice-blog").expect("signed bundle");
    let verified = verify_site_bundle(&vb, Some(signer)).expect("verifies");
    assert_eq!(verified.content_root, content_root);
    assert_eq!(verified.owner, alice);

    // a tampered served byte → verify ✗ (the headline tooth).
    let mut tampered = vb.clone();
    tampered.content.assets.get_mut("/index.html").unwrap().body = b"<h1>OWNED</h1>".to_vec();
    assert!(matches!(
        verify_site_bundle(&tampered, Some(signer)),
        Err(SiteVerifyError::ContentRootMismatch { .. })
    ));

    // ── LIST: the console read plane is cap-scoped (the teeth) ───────────────────
    let alice_sites = list(&api, "/api/sites", &alice);
    assert_eq!(alice_sites.len(), 1);
    assert_eq!(alice_sites[0]["name"], "alice-blog");
    assert!(!alice_sites.iter().any(|s| s["name"] == "bob-blog"));

    let bob_sites = list(&api, "/api/sites", &bob);
    assert_eq!(bob_sites.len(), 1);
    assert_eq!(bob_sites[0]["name"], "bob-blog");
    assert!(!bob_sites.iter().any(|s| s["name"] == "alice-blog"));

    // a stranger owns nothing; no subject fails closed.
    assert!(list(&api, "/api/sites", "dregg:0000000000000000").is_empty());
    assert_eq!(api.respond(HttpMethod::Get, "/api/sites", None).status, 401);
}

#[test]
fn an_unfunded_publish_is_refused_in_the_handler() {
    let root = RootKey::from_seed([7u8; 32]);
    let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
    let cred = mint_caps(&root, [format!("{SITE_CAP_PREFIX}blog")], None).encode();
    let owner = subject_of(&cred).unwrap();
    // The funding source funds a DIFFERENT subject → this owner's publish is uncovered.
    let funding: Arc<dyn FundingSource> = Arc::new(FundsSubject(format!("{owner}-not")));
    let publish =
        SitePublishHandler::new(Arc::clone(&registry), Some(root.public()), Some(funding));
    let r = publish.respond(
        HttpMethod::Post,
        "/v1/sites/blog/publish",
        Some(&cred),
        &bundle("x"),
        NOW,
    );
    assert_eq!(
        r.status,
        402,
        "uncovered owner must be refused: {}",
        r.body_str()
    );
    assert!(registry.get("blog").is_none());
}

fn run_get(site: &SiteHostHandler, host: &str, target: &str) -> String {
    let mut buf = vec![0u8; 64 * 1024];
    let mut w = ResponseWriter::new(&mut buf);
    let res = site.dispatch(Method::Get, host, target, &[], &mut w);
    String::from_utf8_lossy(&buf[..res.bytes_written()]).to_string()
}

fn list(api: &ApiHandler, path: &str, subject: &str) -> Vec<serde_json::Value> {
    let resp = api.respond(HttpMethod::Get, path, Some(subject));
    assert_eq!(resp.status, 200, "{path}: {}", resp.body_str());
    let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    v.as_array().cloned().unwrap_or_default()
}
