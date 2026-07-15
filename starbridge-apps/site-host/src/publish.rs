//! The site-publish control plane — `POST /v1/sites/<name>/publish`.
//!
//! ```text
//!   POST /v1/sites/<name>/publish                (cap-gated, lease-funded, receipted)
//!     headers: Authorization: Bearer dga1_…      (site-host/<name> cap)
//!     body:    a serialized SiteContent (the built bundle, path -> asset)
//!        │  1. authorize  — verify the dga1_ cap -> the owner subject
//!        │  2. fund       — a resident non-lapsed hosting lease covers the owner
//!        │                  (else 402 + an x402 topup hint to auto-fund + retry)
//!        │  3. publish    — SiteRegistry::publish -> SiteCell + signed receipt
//!        ▼
//!     201 { published, name, owner, content_root, url, signer, receipt }
//! ```
//!
//! [`SitePublishHandler::respond`] is the ONE value-level turn both a CLI (calls it
//! directly with a decoded credential) and an HTTP gateway (adapts a request into
//! it) drive — no HTTP-server types in the core. The funding refusal is the
//! improvement: instead of a dead `402`, it carries an x402-style payment
//! requirement ([`crate::funding::TopupHint`]) so a machine client tops up the lease
//! and re-POSTs.

use std::sync::Arc;

use dregg_agent::cred::{Credential, PublicKey};
use serde::Serialize;
use webauth_core::grant::cap_context;
use webauth_core::subject_of;

use crate::funding::{FundingDecision, PublishFunding};
use crate::registry::{HostConfig, PUBLISH_CAP_PREFIX, PublishCap, PublishError, SiteRegistry};
use crate::site::SiteContent;

/// The value-level HTTP method the control plane accepts (no server-crate types).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HttpMethod {
    Get,
    Post,
    Other,
}

/// A value-level HTTP response: status, content-type, headers, body. Header-carrying
/// (unlike a bare body-only response) so the funding refusal can emit the x402
/// `X-Payment-Required` header.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WebResponse {
    pub status: u16,
    pub content_type: String,
    pub headers: Vec<(String, String)>,
    pub body: Vec<u8>,
}

impl WebResponse {
    /// A `text/plain` error response with `status` and `msg`.
    pub fn error(status: u16, msg: impl Into<String>) -> WebResponse {
        WebResponse {
            status,
            content_type: "text/plain; charset=utf-8".to_string(),
            headers: Vec::new(),
            body: msg.into().into_bytes(),
        }
    }

    /// A `application/json` response from a serializable value.
    pub fn json(status: u16, value: &impl Serialize) -> WebResponse {
        WebResponse {
            status,
            content_type: "application/json".to_string(),
            headers: Vec::new(),
            body: serde_json::to_vec(value).unwrap_or_else(|_| b"{}".to_vec()),
        }
    }

    /// The body as a UTF-8 string (lossy) — for logging/tests.
    pub fn body_str(&self) -> String {
        String::from_utf8_lossy(&self.body).into_owned()
    }
}

/// The site-publish control plane: writes a built bundle into `registry`, gated on a
/// `site-host/<name>` credential verified under `auth_root` and funded against
/// `funding`.
pub struct SitePublishHandler {
    registry: Arc<SiteRegistry>,
    /// The root authority a presented `dga1_` credential must chain to. `None` =
    /// no root configured -> every publish fails closed (`401`).
    auth_root: Option<PublicKey>,
    /// The funding gate. `None` = no funding configured -> publishes fail closed
    /// (`402`), the no-free-resource posture.
    funding: Option<Arc<dyn PublishFunding>>,
    /// Host config (the parameterized apex the success URL is built from).
    config: HostConfig,
    /// The endpoint a client funds a hosting lease at (echoed into topup hints).
    topup_endpoint: String,
}

impl SitePublishHandler {
    /// A handler publishing into `registry`, verifying credentials under `root`, and
    /// funding against `funding`, serving under `config`.
    pub fn new(
        registry: Arc<SiteRegistry>,
        root: Option<PublicKey>,
        funding: Option<Arc<dyn PublishFunding>>,
        config: HostConfig,
    ) -> SitePublishHandler {
        SitePublishHandler {
            registry,
            auth_root: root,
            funding,
            config,
            topup_endpoint: "/v1/leases/topup".to_string(),
        }
    }

    /// Override the funding top-up endpoint advertised in x402 hints.
    pub fn with_topup_endpoint(mut self, endpoint: impl Into<String>) -> SitePublishHandler {
        self.topup_endpoint = endpoint.into();
        self
    }

    /// The registry this handler publishes into (the inspection surface).
    pub fn registry(&self) -> &Arc<SiteRegistry> {
        &self.registry
    }

    /// Whether this handler serves `path`: a `POST /v1/sites/<name>/publish`.
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

    /// Route + serve one publish request as a value response (no HTTP-server types).
    /// `credential` is the presented `dga1_…` token, `now` the verifier's clock.
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

        // (2) funding gate: a resident, non-lapsed hosting lease must cover the owner.
        //     A refusal carries the x402 topup hint (auto-fund + retry).
        if let Err(deny) = self.fund(&cap.holder, target) {
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
                let signer = self.registry.receipt_signer().map(hex32);
                let value = serde_json::json!({
                    "published": true,
                    "name": receipt.name,
                    "owner": receipt.owner,
                    "content_root": receipt.content_root,
                    "asset_count": receipt.asset_count,
                    "url": self.config.url_for(&receipt.name),
                    "signer": signer,
                    "receipt": receipt,
                });
                WebResponse::json(201, &value)
            }
            Err(e) => publish_error_response(e),
        }
    }

    /// Verify the presented credential authorizes publishing `name`, returning the
    /// [`PublishCap`] (holder = the credential's stable subject) or the refusal
    /// (`401`/`403`).
    fn authorize(
        &self,
        name: &str,
        credential: Option<&str>,
        now: u64,
    ) -> Result<PublishCap, WebResponse> {
        let Some(root) = &self.auth_root else {
            return Err(WebResponse::error(401, "site cap-authority not configured"));
        };
        let Some(enc) = credential else {
            return Err(WebResponse::error(
                401,
                format!("no credential presented to publish site `{name}`"),
            ));
        };
        let cred = Credential::decode(enc)
            .map_err(|e| WebResponse::error(401, format!("credential did not decode: {e}")))?;
        let required = format!("{PUBLISH_CAP_PREFIX}{name}");
        let ctx = cap_context(&required, now);
        cred.verify(root, &ctx)
            .map_err(|r| WebResponse::error(403, format!("cap `{required}` refused: {r}")))?;
        let holder = subject_of(enc).unwrap_or_else(|| "dregg:unknown".to_string());
        Ok(PublishCap {
            holder,
            cap: required,
        })
    }

    /// The funding gate: admit only against a resident non-lapsed hosting lease.
    /// `Ok(())` admits; an `Err` is the `402` refusal (with the x402 topup hint) to
    /// return as-is. `retry` is the publish path echoed into the hint.
    fn fund(&self, owner: &str, retry: &str) -> Result<(), WebResponse> {
        let Some(funding) = &self.funding else {
            return Err(WebResponse::error(
                402,
                "no funding gate configured: refusing to publish without a covering hosting lease",
            ));
        };
        match funding.authorize_publish(owner, retry, &self.topup_endpoint) {
            FundingDecision::Covered => Ok(()),
            FundingDecision::Denied(hint) => {
                // x402-style 402: a JSON body with an `accepts` payment-requirement
                // array + the `X-Payment-Required` header, so a machine client reads
                // the requirement, funds the lease, and re-POSTs the publish.
                let value = serde_json::json!({
                    "error": hint.detail,
                    "accepts": [hint],
                });
                let mut resp = WebResponse::json(402, &value);
                resp.headers
                    .push(("X-Payment-Required".to_string(), hint.scheme.clone()));
                Err(resp)
            }
        }
    }
}

/// Extract a `dga1_…` credential from HTTP-style headers: `Authorization: Bearer
/// <tok>` or `X-Dregg-Credential: <tok>`. A helper for an HTTP gateway adapter.
pub fn bearer_credential<'a>(header: impl Fn(&str) -> Option<&'a str>) -> Option<String> {
    if let Some(auth) = header("authorization") {
        let auth = auth.trim();
        if let Some(tok) = auth
            .strip_prefix("Bearer ")
            .or_else(|| auth.strip_prefix("bearer "))
        {
            return Some(tok.trim().to_string());
        }
    }
    header("x-dregg-credential")
        .map(|c| c.trim().to_string())
        .filter(|c| !c.is_empty())
}

/// Map a [`PublishError`] onto the HTTP response the edge returns.
fn publish_error_response(e: PublishError) -> WebResponse {
    let status = match &e {
        PublishError::CapRefused { .. } => 403,
        PublishError::EmptyContent | PublishError::InvalidName(_) => 400,
    };
    WebResponse::error(status, e.to_string())
}

/// Lower-hex a 32-byte id.
fn hex32(b: [u8; 32]) -> String {
    use std::fmt::Write as _;
    let mut s = String::with_capacity(64);
    for x in &b {
        let _ = write!(s, "{x:02x}");
    }
    s
}
