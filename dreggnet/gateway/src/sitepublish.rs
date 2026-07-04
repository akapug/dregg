//! Publish a built static site to the LIVE cloud over HTTP — the control-plane
//! half of `example.com` hosting, reachable from `dregg-cloud deploy --endpoint`.
//!
//! [`crate::SiteHostHandler`] is the static *read* data plane (a published cell
//! served by `Host`). This is the missing *write* control plane: a client POSTs a
//! **built static bundle** and the gateway publishes it through the real, signed
//! [`SiteRegistry`](dreggnet_webapp::SiteRegistry) — the same cap-gated, receipted
//! turn the local `dregg-cloud deploy` runs, but now driveable against the live
//! gateway. The just-published cell is then served at `<name>.example.com` and is
//! `dregg-cloud verify`-able (the served bytes re-witness against the committed
//! Poseidon2 `content_root`, signed publish receipt and all).
//!
//! ```text
//!   POST /v1/sites/<name>/publish                (cap-gated, funded, receipted)
//!     headers: Authorization: Bearer dga1_…      (site-host/<name> cap)
//!     body:    a serialized SiteContent (the built bundle, path → asset)
//!        │  1. authorize  — verify the dga1_ cap → the owner subject
//!        │  2. fund       — a verified funded lease for the owner covers the publish
//!        │  3. publish    — SiteRegistry::publish → SiteCell + signed PublishReceipt
//!        ▼
//!     201 { published, name, owner, content_root, url, signer, receipt }
//! ```
//!
//! ## The cap-gate (owner-scoped publish)
//!
//! The publish is gated on a presented dregg credential (`dga1_…`, the
//! [`dreggnet_webauth`] cap chain) carrying the `site-host/<name>` capability for
//! the site being published, verified against the gateway's configured root
//! authority — exactly the shape [`crate::StorageHandler`] uses for a bucket write.
//! The verified credential's stable subject becomes the published cell's
//! [`owner`](dreggnet_webapp::hosting::SiteCell::owner); a credential for a
//! different site, minted by a different root, or none at all is refused
//! (`401`/`403`). So only the holder of `site-host/<name>` can publish `<name>`.
//!
//! ## The funding gate (LEASE-1a)
//!
//! Like a machine create, a publish is admitted only against a **verified funded
//! lease** the chain attests for the owner ([`FundingSource`]) — never synthesized
//! from the request. No funding source ⇒ the gateway fails **closed** (`402`); a
//! publish the chain does not fund is refused. This keeps the public publish path
//! on the same no-free-resource rail as the machines API.

use std::sync::Arc;

use dreggnet_bridge::CapGrade;
use dreggnet_http::handler::{Handler, HandlerResult};
use dreggnet_http::{Method, Request, ResponseWriter};

use dreggnet_webapp::hosting::{PublishCap, PublishError, SiteContent, SiteRegistry};
use dreggnet_webapp::{HttpMethod, WebResponse};
use dreggnet_webauth::cred::{Credential, PublicKey};
use dreggnet_webauth::grant::cap_context;
use dreggnet_webauth::subject_of;

use dreggnet_webapp::hex32;

use crate::funding::FundingSource;
use crate::webresp::{map_method, write};

/// The cap-token prefix a publish credential must carry: `site-host/<name>` (the
/// same token the [`PublishCap`] is built from).
pub const SITE_CAP_PREFIX: &str = "site-host/";

/// The funded budget (meter units) a single site publish consumes — the demand the
/// funding gate must find a verified funded lease covering. A publish is a single
/// cheap control-plane turn (write the content cell + seal the receipt), so this is
/// a small fixed cost, not a per-byte charge (bandwidth is metered on the serving
/// path, see [`dreggnet_webapp::BandwidthMeter`]).
pub const PUBLISH_BUDGET_UNITS: i64 = 1;

/// The gateway HTTP handler that publishes a built static bundle to the live
/// [`SiteRegistry`] — cap-gated to the owner, funded, and receipted.
///
/// Holds the registry (the shared data plane the [`crate::SiteHostHandler`] serves
/// from — a publish here is visible to the read plane immediately), the root
/// authority a presented `dga1_` credential must chain to, and the
/// [`FundingSource`] the publish is admitted against (LEASE-1a).
pub struct SitePublishHandler {
    registry: Arc<SiteRegistry>,
    /// The root authority a presented `dga1_` credential must chain to. `None`
    /// = no root configured → every publish fails closed (`401`).
    auth_root: Option<PublicKey>,
    /// The chain's attestation of funded leases the publish is admitted against.
    /// `None` = the gateway cannot confirm funding → publishes fail closed (`402`),
    /// the same no-free-resource posture as the machines API.
    funding: Option<Arc<dyn FundingSource>>,
}

impl SitePublishHandler {
    /// Publish into `registry`, verifying credentials under `root` and admitting a
    /// publish only against a funded lease `funding` attests.
    pub fn new(
        registry: Arc<SiteRegistry>,
        root: Option<PublicKey>,
        funding: Option<Arc<dyn FundingSource>>,
    ) -> SitePublishHandler {
        SitePublishHandler {
            registry,
            auth_root: root,
            funding,
        }
    }

    /// The registry this handler publishes into (the inspection surface).
    pub fn registry(&self) -> &Arc<SiteRegistry> {
        &self.registry
    }

    /// Whether this handler serves `path` (a routing decision for the serving
    /// loop): a `POST /v1/sites/<name>/publish`.
    pub fn serves_path(path: &str) -> bool {
        let p = path.split('?').next().unwrap_or(path);
        p.starts_with("/v1/sites/") && p.ends_with("/publish")
    }

    /// The `<name>` a `/v1/sites/<name>/publish` path targets, if well-formed.
    fn name_from_path(path: &str) -> Option<&str> {
        let p = path.split('?').next().unwrap_or(path);
        let rest = p.strip_prefix("/v1/sites/")?;
        let name = rest.strip_suffix("/publish")?;
        if name.is_empty() || name.contains('/') {
            return None;
        }
        Some(name)
    }

    /// Route + serve one publish request, returning the value response (no HTTP
    /// server types). `credential` is the presented `dga1_…` token, `now` the
    /// verifier's clock for credential expiry.
    pub fn respond(
        &self,
        method: HttpMethod,
        target: &str,
        credential: Option<&str>,
        body: &[u8],
        now: u64,
    ) -> WebResponse {
        if method != HttpMethod::Post {
            return WebResponse::error(405, "publish is POST /v1/sites/<name>/publish");
        }
        let Some(name) = Self::name_from_path(target) else {
            return WebResponse::error(404, "not a site-publish path");
        };

        // (1) cap-gate: the presented dga1_ credential must carry site-host/<name>.
        let cap = match self.authorize(name, credential, now) {
            Ok(c) => c,
            Err(deny) => return deny,
        };

        // (2) funding gate (LEASE-1a): a verified funded lease for the owner must
        //     cover the publish. No source / no covered lease ⇒ refuse (no free work).
        if let Err(deny) = self.fund(&cap.holder) {
            return deny;
        }

        // (3) decode the built bundle and publish it (cap-gated + receipted turn).
        let content: SiteContent = match serde_json::from_slice(body) {
            Ok(c) => c,
            Err(e) => {
                return WebResponse::error(
                    400,
                    format!("publish body is not a JSON SiteContent bundle: {e}"),
                );
            }
        };
        match self.registry.publish(&cap, name, content) {
            Ok(receipt) => {
                let signer = self.registry.receipt_signer().map(|k| hex32(&k));
                let body = serde_json::json!({
                    "published": true,
                    "name": receipt.name,
                    "owner": receipt.owner,
                    "content_root": receipt.content_root,
                    "asset_count": receipt.asset_count,
                    "url": format!("https://{}.example.com/", receipt.name),
                    "signer": signer,
                    "receipt": receipt,
                });
                WebResponse {
                    status: 201,
                    content_type: "application/json".to_string(),
                    body: body.to_string().into_bytes(),
                }
            }
            Err(e) => publish_error_response(e),
        }
    }

    /// Verify the presented credential authorizes publishing `name`, returning the
    /// [`PublishCap`] (holder bound to the credential's stable subject) on success,
    /// or the refusal response (`401`/`403`).
    fn authorize(
        &self,
        name: &str,
        credential: Option<&str>,
        now: u64,
    ) -> Result<PublishCap, WebResponse> {
        let Some(root) = &self.auth_root else {
            return Err(WebResponse::error(
                401,
                "site cap-authority not configured (set DREGGNET_WEBAUTH_ROOT_PUBKEY)",
            ));
        };
        let Some(enc) = credential else {
            return Err(WebResponse::error(
                401,
                format!("no dregg credential presented to publish site `{name}`"),
            ));
        };
        let cred = Credential::decode(enc)
            .map_err(|e| WebResponse::error(401, format!("credential did not decode: {e}")))?;
        let required = format!("{SITE_CAP_PREFIX}{name}");
        let ctx = cap_context(&required, now);
        cred.verify(root, &ctx)
            .map_err(|r| WebResponse::error(403, format!("cap `{required}` refused: {r}")))?;
        let holder = subject_of(enc).unwrap_or_else(|| "dregg:unknown".to_string());
        Ok(PublishCap {
            holder,
            cap: required,
        })
    }

    /// The LEASE-1a funding gate: admit the publish only against a verified funded
    /// lease the chain attests for `owner`. `Ok(())` admits; an `Err` is the refusal
    /// response (`402`) to return as-is.
    fn fund(&self, owner: &str) -> Result<(), WebResponse> {
        let Some(funding) = &self.funding else {
            return Err(WebResponse::error(
                402,
                "no verified funding source configured: refusing to publish without confirming real on-chain funding",
            ));
        };
        match funding.authorize(owner, CapGrade::Sandboxed, PUBLISH_BUDGET_UNITS) {
            Ok(Some(_lease)) => Ok(()),
            Ok(None) => Err(WebResponse::error(
                402,
                format!("no verified funded lease for `{owner}` covers a site publish"),
            )),
            Err(e) => Err(WebResponse::error(
                402,
                format!("verified on-chain funding read failed: {e}"),
            )),
        }
    }

    /// Route + serve one request through the `dreggnet-http` [`ResponseWriter`].
    pub fn dispatch(
        &self,
        method: Method,
        target: &str,
        credential: Option<&str>,
        body: &[u8],
        now: u64,
        response: &mut ResponseWriter,
    ) -> HandlerResult {
        let Some(m) = map_method(method) else {
            return write(response, &WebResponse::error(405, "unsupported method"));
        };
        let resp = self.respond(m, target, credential, body, now);
        write(response, &resp)
    }
}

impl Handler for SitePublishHandler {
    fn handle(&self, request: &Request, response: &mut ResponseWriter) -> HandlerResult {
        let cred = bearer_credential(request);
        self.dispatch(
            request.method(),
            request.path(),
            cred.as_deref(),
            &[],
            now_unix(),
            response,
        )
    }
}

/// Extract a `dga1_…` credential from a request: `Authorization: Bearer <tok>`
/// or `X-Dregg-Credential: <tok>`.
fn bearer_credential(request: &Request) -> Option<String> {
    if let Some(auth) = request.header("authorization") {
        let auth = auth.trim();
        if let Some(tok) = auth
            .strip_prefix("Bearer ")
            .or_else(|| auth.strip_prefix("bearer "))
        {
            return Some(tok.trim().to_string());
        }
    }
    request
        .header("x-dregg-credential")
        .map(|c| c.trim().to_string())
        .filter(|c| !c.is_empty())
}

/// Wall-clock unix seconds, for credential expiry checks on the serving path.
fn now_unix() -> u64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
}

/// Map a [`PublishError`] onto the HTTP response the edge returns.
fn publish_error_response(e: PublishError) -> WebResponse {
    let status = match &e {
        PublishError::CapRefused { .. } => 403,
        PublishError::EmptyContent | PublishError::InvalidName(_) => 400,
        PublishError::Persist(_) => 500,
    };
    WebResponse::error(status, e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_bridge::Lease;
    use dreggnet_webapp::SiteRegistry;
    use dreggnet_webapp::hosting::SiteContent;
    use dreggnet_webapp::verify::{SiteVerifyError, verify_site_bundle};
    use dreggnet_webauth::cred::RootKey;
    use dreggnet_webauth::grant::mint_caps;

    use crate::funding::{FundingError, FundingSource};

    const NOW: u64 = 1_000;

    /// A stub funding source standing in for the chain's verified attestation: it
    /// funds the given subject (the owner) generously, so the publish path is
    /// exercised without a live node. Mirrors the gateway's `FundsAnyApp` test stub.
    struct FundsSubject(&'static str);
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

    /// A signed registry (so receipts are re-witnessable), a handler over it under a
    /// fixed root authority funding the owner subject, and the owner credential.
    fn setup() -> (
        SitePublishHandler,
        Arc<SiteRegistry>,
        RootKey,
        [u8; 32],
        String,
    ) {
        let root = RootKey::from_seed([7u8; 32]);
        let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
        let signer = registry.receipt_signer().unwrap();
        let cred = mint_caps(&root, [format!("{SITE_CAP_PREFIX}blog")], None).encode();
        let owner = subject_of(&cred).unwrap();
        let funding: Arc<dyn FundingSource> =
            Arc::new(FundsSubject(Box::leak(owner.clone().into_boxed_str())));
        let h = SitePublishHandler::new(Arc::clone(&registry), Some(root.public()), Some(funding));
        (h, registry, root, signer, cred)
    }

    fn bundle() -> Vec<u8> {
        let content = SiteContent::new()
            .with("/index.html", "<h1>published to the live cloud</h1>")
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
    fn publish_round_trip_serves_and_verifies() {
        let (h, registry, _root, signer, cred) = setup();

        // PUBLISH over HTTP → 201, with the committed content_root + signer.
        let resp = publish(&h, &cred, "blog", &bundle());
        assert_eq!(resp.status, 201, "publish: {}", resp.body_str());
        let v: serde_json::Value = serde_json::from_slice(&resp.body).unwrap();
        assert_eq!(v["published"], true);
        let content_root = v["content_root"].as_str().unwrap();
        assert_eq!(content_root.len(), 64, "the wide Poseidon2 commitment");
        assert_eq!(v["url"], "https://blog.example.com/");

        // SERVED: the just-published cell is in the shared registry, served by Host.
        let cell = registry.get("blog").expect("published cell present");
        assert_eq!(cell.owner, subject_of(&cred).unwrap());
        assert_eq!(cell.content_root, content_root);

        // VERIFIABLE: the signed bundle re-witnesses the served bytes against the
        // committed root, with no trust in the host (the `dregg-cloud verify` path).
        let vb = registry.site_bundle("blog").expect("signed bundle");
        let verified = verify_site_bundle(&vb, Some(signer)).expect("verifies");
        assert_eq!(verified.content_root, content_root);

        // TAMPER TOOTH: a flipped served byte moves the recomputed root → verify ✗.
        let mut tampered = vb.clone();
        tampered.content.assets.get_mut("/index.html").unwrap().body =
            b"<h1>OWNED BY THE HOST</h1>".to_vec();
        assert!(matches!(
            verify_site_bundle(&tampered, Some(signer)),
            Err(SiteVerifyError::ContentRootMismatch { .. })
        ));
    }

    #[test]
    fn an_unauthorized_publish_is_refused() {
        let (h, registry, root, _signer, _owner_cred) = setup();

        // (a) no credential → 401, nothing published.
        let r = h.respond(
            HttpMethod::Post,
            "/v1/sites/blog/publish",
            None,
            &bundle(),
            NOW,
        );
        assert_eq!(r.status, 401, "no-cred: {}", r.body_str());

        // (b) a cap for a DIFFERENT site → 403.
        let wrong = mint_caps(&root, [format!("{SITE_CAP_PREFIX}other")], None).encode();
        let r = publish(&h, &wrong, "blog", &bundle());
        assert_eq!(r.status, 403, "wrong-site cap: {}", r.body_str());

        // (c) a cap minted by a DIFFERENT root → 403.
        let attacker = RootKey::from_seed([99u8; 32]);
        let forged = mint_caps(&attacker, [format!("{SITE_CAP_PREFIX}blog")], None).encode();
        let r = publish(&h, &forged, "blog", &bundle());
        assert_eq!(r.status, 403, "foreign-root cap: {}", r.body_str());

        assert!(registry.get("blog").is_none(), "nothing was published");
    }

    #[test]
    fn an_unfunded_publish_fails_closed() {
        // A signed registry + valid root, but NO funding source ⇒ the gateway cannot
        // confirm funding ⇒ the publish is refused (402), nothing published. The
        // no-free-resource posture, mirroring the machines API.
        let root = RootKey::from_seed([7u8; 32]);
        let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
        let h = SitePublishHandler::new(Arc::clone(&registry), Some(root.public()), None);
        let cred = mint_caps(&root, [format!("{SITE_CAP_PREFIX}blog")], None).encode();
        let r = publish(&h, &cred, "blog", &bundle());
        assert_eq!(r.status, 402, "unfunded: {}", r.body_str());
        assert!(registry.get("blog").is_none());
    }

    #[test]
    fn a_publish_for_an_unfunded_owner_is_refused() {
        // Funding source exists but funds a DIFFERENT subject; the owner's publish is
        // not covered ⇒ 402 (the chain funds no lease for this owner).
        let root = RootKey::from_seed([7u8; 32]);
        let registry = Arc::new(SiteRegistry::signed([42u8; 32]));
        let funding: Arc<dyn FundingSource> = Arc::new(FundsSubject("dregg:somebodyelse0000"));
        let h = SitePublishHandler::new(Arc::clone(&registry), Some(root.public()), Some(funding));
        let cred = mint_caps(&root, [format!("{SITE_CAP_PREFIX}blog")], None).encode();
        let r = publish(&h, &cred, "blog", &bundle());
        assert_eq!(r.status, 402, "owner not funded: {}", r.body_str());
        assert!(registry.get("blog").is_none());
    }

    #[test]
    fn routing_predicate_and_name_parse() {
        assert!(SitePublishHandler::serves_path("/v1/sites/blog/publish"));
        assert!(SitePublishHandler::serves_path(
            "/v1/sites/my-site/publish?x=1"
        ));
        assert!(!SitePublishHandler::serves_path("/v1/sites/blog"));
        assert!(!SitePublishHandler::serves_path("/v1/apps/x/machines"));
        assert_eq!(
            SitePublishHandler::name_from_path("/v1/sites/blog/publish"),
            Some("blog")
        );
        assert_eq!(
            SitePublishHandler::name_from_path("/v1/sites//publish"),
            None
        );
        assert_eq!(
            SitePublishHandler::name_from_path("/v1/sites/a/b/publish"),
            None
        );
    }
}
