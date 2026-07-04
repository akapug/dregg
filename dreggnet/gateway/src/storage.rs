//! Serve the durable object-store core ([`dreggnet_storage::BucketRegistry`])
//! through the gateway — the S3-ish surface on the verified rail.
//!
//! This is the object-store sibling of [`crate::SiteHostHandler`]: where the
//! site handler is the *static read-only* data plane (a published cell served by
//! `Host`), [`StorageHandler`] is the *read/write* data plane — it adapts inbound
//! `PUT/GET/DELETE /storage/<bucket>/<key>` onto the tested
//! [`BucketRegistry`](dreggnet_storage::BucketRegistry) methods: cap-gated,
//! metered, receipted mutations and a public, re-witnessable read.
//!
//! ```text
//!   PUT  /storage/<bucket>          create the bucket          (cap-gated)        → BucketReceipt
//!   GET  /storage/<bucket>          list the object keys       (cap-gated, metered)
//!   PUT  /storage/<bucket>/<key>    store an object            (cap-gated, metered) → PutReceipt
//!   GET  /storage/<bucket>/<key>    read an object (bytes)     (public, trustless)
//!   GET  /storage/<bucket>/<key>?opening   the verified ObjectOpening (re-witnessable)
//!   DELETE /storage/<bucket>/<key> remove an object           (cap-gated, metered) → DeleteReceipt
//! ```
//!
//! ## The cap-gate (owner-scoped writes)
//!
//! A mutation (create / put / delete) and the `list` read are gated on a presented
//! dregg credential (`dga1_…`, the [`dreggnet_webauth`] cap chain) carrying the
//! `storage-bucket/<name>` capability for that bucket, verified against the
//! gateway's configured root authority. The verified credential's stable subject
//! becomes the bucket [`owner`](dreggnet_storage::BucketCell::owner); the registry
//! then enforces that *only that owner's credential* can operate the bucket
//! (`StorageCap.holder == cell.owner`), so a credential for a different bucket — or
//! minted by a different root, or none at all — is refused (`401`/`403`). The
//! object read is **public** (the bucket policy mirrors static hosting: writes are
//! the cap-gated, receipted step; reads are free + self-verifying).
//!
//! ## Real vs reviewed-go (honest)
//!
//! Real + proven here: the `BucketRegistry` is reachable over HTTP, the cap-gate
//! authorizes writes (an unauthorized write is refused), each mutation produces a
//! prev-hash-chained ed25519-signed receipt the caller can re-witness, and the
//! object read serves committed bytes (optionally with its trustless opening). The
//! deliberate flip-on steps shared with the rest of the edge: committing each
//! put/delete as an on-chain `Effect::Write` (the bridge's `dregg_verify` lane),
//! and the live-edge serving (mounting this handler in the production binary
//! behind Caddy) — that wiring is reviewed-go, the code is reachable + tested.

use std::collections::BTreeMap;
use std::sync::{Arc, Mutex};

use dreggnet_http::handler::{Handler, HandlerResult};
use dreggnet_http::{Method, Request, ResponseWriter};

use dreggnet_storage::{Account, BucketRegistry, STORAGE_CAP_PREFIX, StorageCap, StorageError};
use dreggnet_webapp::{HttpMethod, WebResponse};
use dreggnet_webauth::cred::{Credential, PublicKey};
use dreggnet_webauth::grant::cap_context;
use dreggnet_webauth::subject_of;

use crate::webresp::{map_method, write};

/// The path prefix the storage data plane serves under.
pub const STORAGE_PREFIX: &str = "/storage";

/// The default per-holder funded budget (meter units) a first-seen caller's
/// account is opened with. The in-process stand-in for a funded dregg
/// `execution-lease`; generous so the round-trip is never budget-blocked, while
/// the meter still refuses an operation that would exceed it.
pub const DEFAULT_BUDGET_UNITS: i64 = 100_000_000;

/// The gateway HTTP handler that serves a [`BucketRegistry`] over HTTP.
///
/// Holds the registry (the data plane), the root public key write credentials are
/// verified under (the cap-gate), and a per-holder account ledger the registry
/// meters mutations against.
pub struct StorageHandler {
    registry: Arc<BucketRegistry>,
    /// The root authority a presented `dga1_` credential must chain to. `None`
    /// = no root configured → every cap-gated op fails closed (`401`).
    auth_root: Option<PublicKey>,
    default_budget: i64,
    accounts: Mutex<BTreeMap<String, Arc<Account>>>,
}

impl StorageHandler {
    /// Serve `registry`, verifying write credentials under `root` (the gateway's
    /// configured cap-authority), opening per-holder accounts at
    /// [`DEFAULT_BUDGET_UNITS`].
    pub fn new(registry: Arc<BucketRegistry>, root: PublicKey) -> StorageHandler {
        StorageHandler::with_budget(registry, Some(root), DEFAULT_BUDGET_UNITS)
    }

    /// As [`new`](Self::new), with an explicit per-holder budget and an optional
    /// root (`None` fails every cap-gated op closed — the no-authority default).
    pub fn with_budget(
        registry: Arc<BucketRegistry>,
        root: Option<PublicKey>,
        default_budget: i64,
    ) -> StorageHandler {
        StorageHandler {
            registry,
            auth_root: root,
            default_budget,
            accounts: Mutex::new(BTreeMap::new()),
        }
    }

    /// The registry this handler serves (the inspection surface).
    pub fn registry(&self) -> &Arc<BucketRegistry> {
        &self.registry
    }

    /// Whether this handler serves `path` (a routing decision for the serving
    /// loop): the `/storage` root or anything beneath `/storage/`.
    pub fn serves_path(path: &str) -> bool {
        let p = path.split('?').next().unwrap_or(path);
        p == STORAGE_PREFIX || p.starts_with("/storage/")
    }

    /// Route + serve one storage request, returning the value response (no HTTP
    /// server types). `credential` is the presented `dga1_…` token (from a bearer
    /// header), `now` the verifier's clock for credential expiry.
    ///
    /// This is the body-bearing, server-independent core; [`Self::dispatch`] and
    /// [`Handler::handle`] adapt it onto the `dreggnet-http` [`ResponseWriter`].
    pub fn respond(
        &self,
        method: HttpMethod,
        target: &str,
        credential: Option<&str>,
        body: &[u8],
        now: u64,
    ) -> WebResponse {
        let (path, query) = match target.split_once('?') {
            Some((p, q)) => (p, q),
            None => (target, ""),
        };
        // Strip the `/storage` prefix → the `<bucket>[/<key>]` remainder.
        let rest = match path.strip_prefix(STORAGE_PREFIX) {
            Some(r) => r.trim_start_matches('/'),
            None => return WebResponse::error(404, "not a storage path"),
        };
        if rest.is_empty() {
            return self.service_descriptor();
        }
        let (bucket, key) = match rest.split_once('/') {
            Some((b, k)) => (b, k.trim_start_matches('/')),
            None => (rest, ""),
        };

        if key.is_empty() {
            // Bucket-level: create (PUT) / list (GET).
            match method {
                HttpMethod::Put => self.create_bucket(bucket, credential, now),
                HttpMethod::Get => self.list(bucket, credential, now),
                _ => WebResponse::error(405, "method not allowed on a bucket"),
            }
        } else {
            // Object-level: put (PUT) / read (GET) / delete (DELETE).
            match method {
                HttpMethod::Put => self.put(bucket, key, body, credential, now),
                HttpMethod::Get => self.get(bucket, key, query),
                HttpMethod::Delete => self.delete(bucket, key, credential, now),
                _ => WebResponse::error(405, "method not allowed on an object"),
            }
        }
    }

    // -- the operations -------------------------------------------------------

    fn create_bucket(&self, bucket: &str, credential: Option<&str>, now: u64) -> WebResponse {
        let cap = match self.authorize(bucket, credential, now) {
            Ok(c) => c,
            Err(deny) => return deny,
        };
        match self.registry.create_bucket(&cap, bucket) {
            Ok(receipt) => json_status(201, &receipt),
            Err(e) => storage_error_response(e),
        }
    }

    fn put(
        &self,
        bucket: &str,
        key: &str,
        body: &[u8],
        credential: Option<&str>,
        now: u64,
    ) -> WebResponse {
        let cap = match self.authorize(bucket, credential, now) {
            Ok(c) => c,
            Err(deny) => return deny,
        };
        let account = self.account_for(&cap.holder);
        match self
            .registry
            .put(&cap, &account, bucket, key, body.to_vec())
        {
            Ok(receipt) => json_status(201, &receipt),
            Err(e) => storage_error_response(e),
        }
    }

    fn delete(&self, bucket: &str, key: &str, credential: Option<&str>, now: u64) -> WebResponse {
        let cap = match self.authorize(bucket, credential, now) {
            Ok(c) => c,
            Err(deny) => return deny,
        };
        let account = self.account_for(&cap.holder);
        match self.registry.delete(&cap, &account, bucket, key) {
            Ok(receipt) => json_status(200, &receipt),
            Err(e) => storage_error_response(e),
        }
    }

    fn list(&self, bucket: &str, credential: Option<&str>, now: u64) -> WebResponse {
        let cap = match self.authorize(bucket, credential, now) {
            Ok(c) => c,
            Err(deny) => return deny,
        };
        let account = self.account_for(&cap.holder);
        match self.registry.list(&cap, &account, bucket, "/") {
            Ok(keys) => {
                let body = serde_json::json!({ "bucket": bucket, "keys": keys });
                WebResponse::json(body.to_string().into_bytes())
            }
            Err(e) => storage_error_response(e),
        }
    }

    /// The **public, trustless** object read. Serves the committed object bytes
    /// with their content-type; `?opening` returns the re-witnessable
    /// [`ObjectOpening`](dreggnet_storage::ObjectOpening) instead, so a caller can
    /// verify the bytes against the bucket root with no trust in the gateway.
    fn get(&self, bucket: &str, key: &str, query: &str) -> WebResponse {
        let Some(cell) = self.registry.get_bucket(bucket) else {
            return WebResponse::error(404, format!("no bucket named `{bucket}`"));
        };
        if query_has_flag(query, "opening") {
            return match cell.open(key) {
                Some(opening) => match serde_json::to_vec(&opening) {
                    Ok(bytes) => WebResponse::json(bytes),
                    Err(e) => WebResponse::error(500, format!("opening encode failed: {e}")),
                },
                None => WebResponse::error(404, format!("no object `{key}` in bucket `{bucket}`")),
            };
        }
        match cell.content.get(key) {
            Some(object) => WebResponse {
                status: 200,
                content_type: object.content_type.clone(),
                body: object.body.clone(),
            },
            None => WebResponse::error(404, format!("no object `{key}` in bucket `{bucket}`")),
        }
    }

    // -- helpers --------------------------------------------------------------

    /// Verify the presented credential authorizes operating `bucket`, returning
    /// the [`StorageCap`] (holder bound to the credential's stable subject) on
    /// success, or the refusal response (`401`/`403`) to return as-is.
    fn authorize(
        &self,
        bucket: &str,
        credential: Option<&str>,
        now: u64,
    ) -> Result<StorageCap, WebResponse> {
        let Some(root) = &self.auth_root else {
            return Err(WebResponse::error(
                401,
                "storage cap-authority not configured (set DREGGNET_WEBAUTH_ROOT_PUBKEY)",
            ));
        };
        let Some(enc) = credential else {
            return Err(WebResponse::error(
                401,
                format!("no dregg credential presented for bucket `{bucket}`"),
            ));
        };
        let cred = Credential::decode(enc)
            .map_err(|e| WebResponse::error(401, format!("credential did not decode: {e}")))?;
        let required = format!("{STORAGE_CAP_PREFIX}{bucket}");
        let ctx = cap_context(&required, now);
        cred.verify(root, &ctx)
            .map_err(|r| WebResponse::error(403, format!("cap `{required}` refused: {r}")))?;
        let holder = subject_of(enc).unwrap_or_else(|| "dregg:unknown".to_string());
        Ok(StorageCap {
            holder,
            cap: required,
        })
    }

    /// The funded account for `holder`, opening one at the default budget on first
    /// use (the in-process stand-in for a funded lease).
    fn account_for(&self, holder: &str) -> Arc<Account> {
        let mut accounts = self.accounts.lock().expect("accounts poisoned");
        Arc::clone(
            accounts
                .entry(holder.to_string())
                .or_insert_with(|| Arc::new(Account::funded(holder, self.default_budget))),
        )
    }

    /// A small JSON descriptor for `GET /storage` — what the surface is, no
    /// bucket names leaked.
    fn service_descriptor(&self) -> WebResponse {
        let body = serde_json::json!({
            "service": "dreggnet-storage",
            "surface": "PUT/GET/DELETE /storage/<bucket>/<key>",
            "writes": "cap-gated (dga1_ storage-bucket/<name>), metered, receipted",
            "reads": "public, re-witnessable (?opening for the trustless opening)",
        });
        WebResponse::json(body.to_string().into_bytes())
    }

    /// Route + serve one request through the `dreggnet-http` [`ResponseWriter`]. The
    /// serving binary passes the credential it read off the request headers and
    /// the body it read off the socket.
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

impl Handler for StorageHandler {
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

/// Whether the query string carries the bare flag `flag` (`?opening` or
/// `?opening=1`).
fn query_has_flag(query: &str, flag: &str) -> bool {
    query
        .split('&')
        .any(|kv| kv == flag || kv.split('=').next() == Some(flag))
}

/// Serialize a receipt as a JSON response at `status`.
fn json_status<T: serde::Serialize>(status: u16, value: &T) -> WebResponse {
    match serde_json::to_vec(value) {
        Ok(body) => WebResponse {
            status,
            content_type: "application/json".to_string(),
            body,
        },
        Err(e) => WebResponse::error(500, format!("receipt encode failed: {e}")),
    }
}

/// Map a [`StorageError`] onto the HTTP response the edge returns.
fn storage_error_response(e: StorageError) -> WebResponse {
    let status = match &e {
        StorageError::CapRefused { .. } => 403,
        StorageError::InvalidBucketName(_) | StorageError::InvalidKey(_) => 400,
        StorageError::NoSuchBucket(_) | StorageError::NoSuchObject { .. } => 404,
        StorageError::OverBudget(_) => 402,
        // A durable-backend write fault: the mutation could not be made durable, so
        // it is refused as an internal error rather than reported as stored.
        StorageError::Persist(_) => 500,
    };
    WebResponse::error(status, e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_storage::receipt::{ReceiptBody, verify_chain, verify_chain_from};
    use dreggnet_storage::{BucketReceipt, DeleteReceipt, ObjectOpening, PutReceipt};
    use dreggnet_webauth::cred::RootKey;
    use dreggnet_webauth::grant::mint_caps;

    const NOW: u64 = 1_000;

    /// A handler over a *signed* registry (so receipts are re-witnessable), under
    /// a fixed root authority. Returns the handler and the root key for minting
    /// credentials in the test.
    fn handler() -> (StorageHandler, RootKey) {
        let root = RootKey::from_seed([7u8; 32]);
        let registry = Arc::new(BucketRegistry::signed([42u8; 32]));
        let h = StorageHandler::new(registry, root.public());
        (h, root)
    }

    /// A credential granting the `storage-bucket/<bucket>` cap, encoded.
    fn cred_for(root: &RootKey, bucket: &str) -> String {
        mint_caps(root, [format!("{STORAGE_CAP_PREFIX}{bucket}")], None).encode()
    }

    fn put(h: &StorageHandler, cred: &str, bucket: &str, key: &str, body: &[u8]) -> WebResponse {
        h.respond(
            HttpMethod::Put,
            &format!("/storage/{bucket}/{key}"),
            Some(cred),
            body,
            NOW,
        )
    }

    #[test]
    fn round_trip_create_put_get_delete_through_the_gateway() {
        let (h, root) = handler();
        let cred = cred_for(&root, "reports");

        // create
        let created = h.respond(HttpMethod::Put, "/storage/reports", Some(&cred), &[], NOW);
        assert_eq!(created.status, 201, "create: {}", created.body_str());

        // put two objects (a homogeneous sub-chain to verify below)
        let p1 = put(&h, &cred, "reports", "q1.json", br#"{"rev":100}"#);
        assert_eq!(p1.status, 201, "put1: {}", p1.body_str());
        let p2 = put(&h, &cred, "reports", "q2.json", br#"{"rev":200}"#);
        assert_eq!(p2.status, 201, "put2: {}", p2.body_str());

        // get back — bytes match, content-type inferred from the key
        let got = h.respond(HttpMethod::Get, "/storage/reports/q1.json", None, &[], NOW);
        assert_eq!(got.status, 200);
        assert_eq!(got.body, br#"{"rev":100}"#);
        assert_eq!(got.content_type, "application/json");

        // the trustless opening re-witnesses against the bucket root
        let op = h.respond(
            HttpMethod::Get,
            "/storage/reports/q1.json?opening",
            None,
            &[],
            NOW,
        );
        assert_eq!(op.status, 200);
        let opening: ObjectOpening = serde_json::from_slice(&op.body).unwrap();
        assert!(opening.verify(), "served opening must re-witness");
        assert_eq!(opening.object.body, br#"{"rev":100}"#);

        // list (cap-gated) sees both keys
        let listed = h.respond(HttpMethod::Get, "/storage/reports", Some(&cred), &[], NOW);
        assert_eq!(listed.status, 200);
        let v: serde_json::Value = serde_json::from_slice(&listed.body).unwrap();
        assert_eq!(v["keys"].as_array().unwrap().len(), 2);

        // delete one
        let del = h.respond(
            HttpMethod::Delete,
            "/storage/reports/q1.json",
            Some(&cred),
            &[],
            NOW,
        );
        assert_eq!(del.status, 200, "delete: {}", del.body_str());

        // the deleted object is gone
        let gone = h.respond(HttpMethod::Get, "/storage/reports/q1.json", None, &[], NOW);
        assert_eq!(gone.status, 404);

        // the receipt chain verifies end-to-end (the put sub-chain links to the
        // create receipt; the delete links to the last put), all signed by the
        // registry's key — a non-witness re-verification.
        let p1r: PutReceipt = serde_json::from_slice(&p1.body).unwrap();
        let p2r: PutReceipt = serde_json::from_slice(&p2.body).unwrap();
        let delr: DeleteReceipt = serde_json::from_slice(&del.body).unwrap();
        let create_r: BucketReceipt = serde_json::from_slice(&created.body).unwrap();

        assert_eq!(verify_chain(std::slice::from_ref(&create_r)), Ok(()));
        assert_eq!(
            verify_chain_from(&[p1r.clone(), p2r.clone()], create_r.receipt_hash()),
            Ok(()),
            "the put sub-chain must verify against the create receipt"
        );
        assert_eq!(
            verify_chain_from(std::slice::from_ref(&delr), p2r.receipt_hash()),
            Ok(()),
            "the delete must chain off the last put"
        );
    }

    #[test]
    fn unauthorized_write_is_refused() {
        let (h, root) = handler();
        // owner creates the bucket
        let owner = cred_for(&root, "private");
        assert_eq!(
            h.respond(HttpMethod::Put, "/storage/private", Some(&owner), &[], NOW)
                .status,
            201
        );

        // (a) no credential → 401
        let none = h.respond(HttpMethod::Put, "/storage/private/x.txt", None, b"hi", NOW);
        assert_eq!(none.status, 401);

        // (b) a credential for a DIFFERENT bucket → cap refused (403)
        let wrong = cred_for(&root, "other");
        let r = put(&h, &wrong, "private", "x.txt", b"hi");
        assert_eq!(
            r.status,
            403,
            "wrong-bucket cap must be refused: {}",
            r.body_str()
        );

        // (c) a credential minted by a DIFFERENT root → refused
        let attacker = RootKey::from_seed([99u8; 32]);
        let forged = cred_for(&attacker, "private");
        let r = put(&h, &forged, "private", "x.txt", b"hi");
        assert_eq!(
            r.status,
            403,
            "foreign-root cap must be refused: {}",
            r.body_str()
        );

        // (d) the legitimate owner's write succeeds
        let ok = put(&h, &owner, "private", "x.txt", b"hi");
        assert_eq!(
            ok.status,
            201,
            "owner write must succeed: {}",
            ok.body_str()
        );

        // and nothing was written by the refused attempts
        let listed = h.respond(HttpMethod::Get, "/storage/private", Some(&owner), &[], NOW);
        let v: serde_json::Value = serde_json::from_slice(&listed.body).unwrap();
        assert_eq!(v["keys"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn a_second_owners_credential_cannot_operate_anothers_bucket() {
        // Two credentials both holding `storage-bucket/shared`, but the bucket is
        // owned by whoever created it; the registry binds owner == cap.holder, and
        // distinct credentials have distinct stable subjects.
        let (h, root) = handler();
        let a = cred_for(&root, "shared");
        // A second, independently-minted credential for the same cap → different subject.
        let b = mint_caps(&root, [format!("{STORAGE_CAP_PREFIX}shared")], Some(9_999)).encode();
        assert_ne!(subject_of(&a), subject_of(&b));

        assert_eq!(
            h.respond(HttpMethod::Put, "/storage/shared", Some(&a), &[], NOW)
                .status,
            201
        );
        // `b` holds the cap but is not the owner → refused.
        let r = put(&h, &b, "shared", "x.txt", b"hi");
        assert_eq!(r.status, 403, "non-owner must be refused: {}", r.body_str());
    }

    #[test]
    fn no_root_configured_fails_closed() {
        let registry = Arc::new(BucketRegistry::signed([1u8; 32]));
        let h = StorageHandler::with_budget(registry, None, DEFAULT_BUDGET_UNITS);
        let root = RootKey::from_seed([7u8; 32]);
        let cred = cred_for(&root, "b");
        let r = h.respond(HttpMethod::Put, "/storage/b", Some(&cred), &[], NOW);
        assert_eq!(r.status, 401);
    }

    #[test]
    fn routing_predicate() {
        assert!(StorageHandler::serves_path("/storage"));
        assert!(StorageHandler::serves_path("/storage/b"));
        assert!(StorageHandler::serves_path("/storage/b/k.txt?opening"));
        assert!(!StorageHandler::serves_path("/storaged"));
        assert!(!StorageHandler::serves_path("/v1/apps/x/machines"));
        assert!(!StorageHandler::serves_path("/metrics"));
    }
}
