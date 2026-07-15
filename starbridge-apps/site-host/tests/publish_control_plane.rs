//! The site-publish control plane end-to-end: the ONE cap-gated, lease-funded,
//! receipted turn a CLI and a gateway both drive.

use std::sync::Arc;

use dregg_agent::cred::RootKey;
use dregg_cell::Cell;
use dregg_ipfs::client::MockIpfs;
use dregg_types::CellId;
use hosted_lease::{HostedLease, LeaseTerms, field_from_u64};
use webauth_core::grant::mint_caps;
use webauth_core::subject_of;

use starbridge_site_host::funding::{LeaseBook, PublishFunding, TopupReason};
use starbridge_site_host::publish::{HttpMethod, SitePublishHandler, WebResponse};
use starbridge_site_host::registry::{
    HostConfig, PUBLISH_CAP_PREFIX, SiteRegistry, verify_receipt,
};
use starbridge_site_host::site::SiteContent;
use starbridge_site_host::{LaunchImage, LaunchListing, landing_page};

const NOW: u64 = 1_000;

fn cid(n: u8) -> CellId {
    CellId::from_bytes([n; 32])
}

/// A funded hosting lease bound to `owner`: rent 100 / 50 blocks from 1000.
fn funded_lease() -> HostedLease {
    let cell = Cell::with_balance([7u8; 32], [9u8; 32], 10_000);
    let terms = LeaseTerms::new(cid(2), cid(7), cid(9), 100, 50, 1000, 0);
    HostedLease::open(cell, terms, field_from_u64(0)).unwrap()
}

/// A signed registry, a handler over it under a fixed root, a lease book funding the
/// owner, and the owner's `site-host/blog` credential.
fn setup() -> (SitePublishHandler, Arc<SiteRegistry>, RootKey, String) {
    let root = RootKey::from_seed([7u8; 32]);
    let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
    let cred = mint_caps(&root, [format!("{PUBLISH_CAP_PREFIX}blog")], None).encode();
    let owner = subject_of(&cred).unwrap();

    let book = LeaseBook::new();
    book.bind(owner, funded_lease());
    let funding: Arc<dyn PublishFunding> = Arc::new(book);

    let h = SitePublishHandler::new(
        Arc::clone(&registry),
        Some(root.public()),
        Some(funding),
        HostConfig::with_apex("example.test"),
    );
    (h, registry, root, cred)
}

fn bundle() -> Vec<u8> {
    let content = SiteContent::new()
        .with("/index.html", "<h1>published</h1>")
        .with("/style.css", "h1{color:teal}");
    serde_json::to_vec(&content).unwrap()
}

fn publish(h: &SitePublishHandler, cred: &str, name: &str, body: &[u8]) -> WebResponse {
    h.respond(
        HttpMethod::Post,
        &format!("/v1/sites/{name}/publish"),
        Some(cred),
        body,
        NOW,
    )
}

#[test]
fn publish_round_trip_serves_and_receipt_re_witnesses() {
    let (h, registry, _root, cred) = setup();

    let resp = publish(&h, &cred, "blog", &bundle());
    assert_eq!(resp.status, 201, "publish: {}", resp.body_str());
    let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
    assert_eq!(v["published"], true);
    let content_root = v["content_root"].as_str().unwrap();
    assert_eq!(content_root.len(), 64, "the wide Poseidon2 commitment");
    assert_eq!(v["url"], "https://blog.example.test/", "parameterized apex");

    // Served: the just-published cell is in the shared registry.
    let cell = registry.get("blog").expect("published cell present");
    assert_eq!(cell.owner, subject_of(&cred).unwrap());
    assert_eq!(cell.content_root, content_root);
    assert_eq!(cell.serve("/").body, b"<h1>published</h1>");

    // Re-witnessable: the signed receipt verifies under the registry's public key,
    // and a tampered owner breaks it.
    let signer = registry.receipt_signer().unwrap();
    let receipt = registry.receipt("blog").unwrap();
    assert!(verify_receipt(&receipt, signer));
    let mut evil = receipt.clone();
    evil.owner = "dregg:someone-else".to_string();
    assert!(!verify_receipt(&evil, signer));
}

#[test]
fn an_unauthorized_publish_is_refused() {
    let (h, registry, root, _cred) = setup();

    // (a) no credential -> 401.
    let r = h.respond(
        HttpMethod::Post,
        "/v1/sites/blog/publish",
        None,
        &bundle(),
        NOW,
    );
    assert_eq!(r.status, 401, "no-cred: {}", r.body_str());

    // (b) a cap for a DIFFERENT site -> 403.
    let wrong = mint_caps(&root, [format!("{PUBLISH_CAP_PREFIX}other")], None).encode();
    let r = publish(&h, &wrong, "blog", &bundle());
    assert_eq!(r.status, 403, "wrong-site cap: {}", r.body_str());

    // (c) a cap minted by a DIFFERENT root -> 403.
    let attacker = RootKey::from_seed([99u8; 32]);
    let forged = mint_caps(&attacker, [format!("{PUBLISH_CAP_PREFIX}blog")], None).encode();
    let r = publish(&h, &forged, "blog", &bundle());
    assert_eq!(r.status, 403, "foreign-root cap: {}", r.body_str());

    assert!(registry.get("blog").is_none(), "nothing was published");
}

#[test]
fn an_unfunded_publish_emits_an_x402_topup_hint() {
    // A valid cap under the right root, but the owner has NO hosting lease -> 402
    // with an x402 topup hint (unfunded), nothing published.
    let root = RootKey::from_seed([7u8; 32]);
    let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
    let funding: Arc<dyn PublishFunding> = Arc::new(LeaseBook::new()); // empty book
    let h = SitePublishHandler::new(
        Arc::clone(&registry),
        Some(root.public()),
        Some(funding),
        HostConfig::with_apex("example.test"),
    )
    .with_topup_endpoint("/v1/leases/topup");
    let cred = mint_caps(&root, [format!("{PUBLISH_CAP_PREFIX}blog")], None).encode();

    let r = publish(&h, &cred, "blog", &bundle());
    assert_eq!(r.status, 402, "unfunded: {}", r.body_str());
    // The x402 header + JSON accepts array carry the topup requirement.
    assert!(
        r.headers
            .iter()
            .any(|(k, v)| k == "X-Payment-Required" && v == "site-host-lease-topup"),
        "x402 header present"
    );
    let v: serde_json::Value = serde_json::from_slice(&r.body).unwrap();
    let hint = &v["accepts"][0];
    assert_eq!(hint["reason"], "Unfunded");
    assert_eq!(hint["retry"], "/v1/sites/blog/publish");
    assert_eq!(hint["topup_endpoint"], "/v1/leases/topup");
    assert!(registry.get("blog").is_none());
}

#[test]
fn a_lapsed_lease_publish_emits_a_lapsed_topup_hint() {
    let root = RootKey::from_seed([7u8; 32]);
    let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
    let cred = mint_caps(&root, [format!("{PUBLISH_CAP_PREFIX}blog")], None).encode();
    let owner = subject_of(&cred).unwrap();

    // Bind a lease then lapse it (non-payment past the due block).
    let mut lease = funded_lease();
    assert!(lease.lapse_if_behind(1100).unwrap());
    let book = LeaseBook::new();
    book.bind(owner, lease);
    let funding: Arc<dyn PublishFunding> = Arc::new(book);
    let h = SitePublishHandler::new(
        Arc::clone(&registry),
        Some(root.public()),
        Some(funding),
        HostConfig::with_apex("example.test"),
    );

    let r = publish(&h, &cred, "blog", &bundle());
    assert_eq!(r.status, 402, "lapsed: {}", r.body_str());
    let v: serde_json::Value = serde_json::from_slice(&r.body).unwrap();
    let hint = &v["accepts"][0];
    assert_eq!(hint["reason"], "Lapsed");
    assert!(hint["lease"].is_string(), "the lapsed hint names the lease");
    assert_eq!(hint["amount"], 100, "the lease's own rent");
    assert!(registry.get("blog").is_none());
}

#[test]
fn no_funding_gate_fails_closed() {
    let root = RootKey::from_seed([7u8; 32]);
    let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
    let h = SitePublishHandler::new(
        Arc::clone(&registry),
        Some(root.public()),
        None, // no funding gate
        HostConfig::local(),
    );
    let cred = mint_caps(&root, [format!("{PUBLISH_CAP_PREFIX}blog")], None).encode();
    let r = publish(&h, &cred, "blog", &bundle());
    assert_eq!(
        r.status,
        402,
        "no funding gate fails closed: {}",
        r.body_str()
    );
    assert!(registry.get("blog").is_none());
}

#[test]
fn routing_predicate_and_method() {
    assert!(SitePublishHandler::serves_path("/v1/sites/blog/publish"));
    assert!(SitePublishHandler::serves_path(
        "/v1/sites/my-site/publish?x=1"
    ));
    assert!(!SitePublishHandler::serves_path("/v1/sites/blog"));
    assert!(!SitePublishHandler::serves_path("/v1/apps/x/machines"));

    let (h, _registry, _root, cred) = setup();
    // A GET is refused (publish is POST).
    let r = h.respond(
        HttpMethod::Get,
        "/v1/sites/blog/publish",
        Some(&cred),
        &bundle(),
        NOW,
    );
    assert_eq!(r.status, 405);
    // A non-publish path is a 404.
    let r = h.respond(
        HttpMethod::Post,
        "/v1/sites/blog",
        Some(&cred),
        &bundle(),
        NOW,
    );
    assert_eq!(r.status, 404);
}

#[test]
fn launch_landing_page_publishes_through_the_same_turn() {
    // The launchpad composition: a launch listing -> a content-addressed landing
    // page -> published through the SAME cap-gated, funded, receipted turn.
    let (h, registry, _root, cred) = setup();
    let ipfs = MockIpfs::new();
    let listing = LaunchListing {
        name: "blog".to_string(), // the site cap authorizes `blog`
        title: "Launch Day".to_string(),
        ticker: Some("LAUNCH".to_string()),
        description: "a launch on the verified rail".to_string(),
        image: Some(LaunchImage {
            content_type: "image/png".to_string(),
            body: b"\x89PNG\r\n\x1a\nFAKE".to_vec(),
        }),
        links: vec![],
    };
    let (content, assets) =
        landing_page(&listing, &ipfs, &HostConfig::with_apex("example.test")).unwrap();
    assert!(
        !assets.metadata_cid.is_empty(),
        "metadata content-addressed"
    );

    let body = serde_json::to_vec(&content).unwrap();
    let r = publish(&h, &cred, "blog", &body);
    assert_eq!(r.status, 201, "launch publish: {}", r.body_str());

    let cell = registry.get("blog").expect("landing page published");
    assert!(
        cell.content.resolve("/").is_some(),
        "the landing page serves"
    );
    assert!(cell.content.resolve("/metadata.json").is_some());
    assert!(cell.content.resolve("/media/launch.png").is_some());
}
