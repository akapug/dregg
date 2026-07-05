//! The cap-scoped registry **read** surfaces the customer console populates from.
//!
//! The console ([`dreggnet-console`]'s `LiveSource`) reads a handful of
//! per-registry list endpoints behind the webauth forward-auth edge and renders
//! "my cloud" — but a console can only ever show a user their OWN cells. This
//! handler is the gateway side of that contract: each surface returns exactly the
//! records owned by the **authenticated subject**, taken from the verified
//! `X-Dregg-Subject` forward-auth header (the `dga1_` cap holder Caddy echoes
//! upstream). The cap-scoping is the tooth: another subject's request sees none of
//! the caller's cells.
//!
//! ```text
//!   GET /api/sites              owned SiteCell records      (name, owner, content_root, bytes)
//!   GET /api/servers            owned persistent servers    (lessee == subject)
//!   GET /api/domains            owned custom-domain bindings (owner == subject)
//!   GET /api/buckets            owned storage buckets        (owner == subject)
//!   GET /api/billing/spend      owned $DREGG spend lines     (owner == subject)
//!   GET /api/billing/balances   { subject: balance }         (the caller's balance only)
//! ```
//!
//! ## The cap-scoping (the teeth)
//!
//! Every surface filters by `owner == subject`, so a request carrying subject
//! `alice` can never observe `bob`'s sites/servers/domains/buckets/spend/balance.
//! A request with NO verified subject fails **closed** (`401`) — the gateway never
//! returns the unscoped, cloud-wide set. The subject MUST come from the verified
//! forward-auth header set by Caddy after it checks the presented capability; the
//! gateway trusts that header exactly as the storage/site write-gates trust the
//! verified credential. (Bind/firewall `:8080` to the internal interface so the
//! header cannot be forged by a direct caller — the same deployment posture as the
//! Caddy `ask`.)
//!
//! ## Honesty law (matches the console's own)
//!
//! A surface with no backing source contributes an **empty list**, never
//! fabricated data — the same law `LiveSource` applies to an unreachable surface.
//! The gateway always holds the site / domain / bucket registries (so those are
//! live); the server fleet + $DREGG ledger are pluggable sources
//! ([`ServerSource`] / [`BillingSource`]) wired when the control plane exposes
//! them, empty until then.

use std::collections::BTreeMap;
use std::sync::Arc;

use dreggnet_http::handler::{Handler, HandlerResult};
use dreggnet_http::{Method, Request, ResponseWriter};
use serde::{Deserialize, Serialize};

use dreggnet_storage::BucketRegistry;
use dreggnet_webapp::{HttpMethod, SiteRegistry, WebResponse};

use dregg_domains::DomainRegistry;

use crate::webresp::{map_method, write};

/// The path prefix the console read surfaces are served under.
pub const API_PREFIX: &str = "/api";

/// A persistent-server record in the shape the console reads (`lessee` is the
/// owner). A [`ServerSource`] yields these; the gateway scopes them to the subject.
/// Field-compatible with `dreggnet_control::ServerRecord`'s serialization.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ServerView {
    /// The server id.
    pub id: String,
    /// The display name.
    pub name: String,
    /// The lessee renting the server — the OWNER the scope filters on.
    pub lessee: String,
    /// Lifecycle state (running/stopped/…).
    pub state: String,
    /// The region.
    pub region: String,
    /// The machine size label.
    pub size: String,
    /// The lease's funded budget (units).
    pub budget_units: i64,
    /// Per-period metered cost (units).
    pub per_period_units: i64,
    /// Periods metered so far.
    pub periods_metered: i64,
}

/// One $DREGG spend ledger line in the shape the console reads (`owner` is the
/// payer). A [`BillingSource`] yields these; the gateway scopes them to the subject.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpendLine {
    /// The cap-account subject the charge is billed to — the OWNER scoped on.
    pub owner: String,
    /// What kind of resource the charge is for (server/site/bucket/…).
    pub resource_kind: String,
    /// The specific resource id.
    pub resource_id: String,
    /// The billing period label.
    pub period: String,
    /// The units charged.
    pub units: i64,
}

/// The persistent-server fleet the `/api/servers` surface reads (across all
/// lessees; the gateway scopes by subject). Wired when the control plane exposes
/// its fleet; absent ⇒ the surface is empty (the honesty law).
pub trait ServerSource: Send + Sync {
    /// Every server record across all lessees.
    fn servers(&self) -> Vec<ServerView>;
}

/// The $DREGG ledger the `/api/billing/*` surfaces read (across all owners; the
/// gateway scopes by subject). Wired when the billing plane exposes it; absent ⇒
/// the surfaces are empty (the honesty law).
pub trait BillingSource: Send + Sync {
    /// Every spend line across all owners.
    fn spend(&self) -> Vec<SpendLine>;
    /// Per-subject $DREGG balances.
    fn balances(&self) -> BTreeMap<String, i64>;
}

/// The gateway HTTP handler that serves the cap-scoped console read surfaces.
pub struct ApiHandler {
    sites: Arc<SiteRegistry>,
    domains: Arc<DomainRegistry>,
    buckets: Arc<BucketRegistry>,
    servers: Option<Arc<dyn ServerSource>>,
    billing: Option<Arc<dyn BillingSource>>,
}

impl ApiHandler {
    /// Serve the site / domain / bucket registries the gateway already holds, with
    /// no server-fleet or billing source (those surfaces are empty until wired).
    pub fn new(
        sites: Arc<SiteRegistry>,
        domains: Arc<DomainRegistry>,
        buckets: Arc<BucketRegistry>,
    ) -> ApiHandler {
        ApiHandler {
            sites,
            domains,
            buckets,
            servers: None,
            billing: None,
        }
    }

    /// Attach the persistent-server fleet source (`/api/servers`).
    pub fn with_servers(mut self, servers: Arc<dyn ServerSource>) -> ApiHandler {
        self.servers = Some(servers);
        self
    }

    /// Attach the $DREGG ledger source (`/api/billing/*`).
    pub fn with_billing(mut self, billing: Arc<dyn BillingSource>) -> ApiHandler {
        self.billing = Some(billing);
        self
    }

    /// Whether this handler serves `path` (a routing decision for the serving
    /// loop): anything beneath `/api/`.
    pub fn serves_path(path: &str) -> bool {
        let p = path.split('?').next().unwrap_or(path);
        p == API_PREFIX || p.starts_with("/api/")
    }

    /// Route + serve one read, scoped to `subject` (the verified `X-Dregg-Subject`).
    /// A missing/empty subject fails closed (`401`) — the unscoped catalog is never
    /// returned.
    pub fn respond(&self, method: HttpMethod, target: &str, subject: Option<&str>) -> WebResponse {
        if method != HttpMethod::Get {
            return WebResponse::error(405, "the console read surfaces are GET-only");
        }
        let path = target.split('?').next().unwrap_or(target);
        let Some(subject) = subject.map(str::trim).filter(|s| !s.is_empty()) else {
            return WebResponse::error(
                401,
                "no verified subject (X-Dregg-Subject); the console reads are cap-scoped",
            );
        };
        match path {
            "/api/sites" => json_array(self.sites_for(subject)),
            "/api/servers" => json_array(self.servers_for(subject)),
            "/api/domains" => json_array(self.domains_for(subject)),
            "/api/buckets" => json_array(self.buckets_for(subject)),
            "/api/billing/spend" => json_array(self.spend_for(subject)),
            "/api/billing/balances" => json_value(self.balances_for(subject)),
            _ => WebResponse::error(404, "unknown console read surface"),
        }
    }

    /// The subject's published sites — compact metadata records (no asset bodies in
    /// a list), in the console's `SiteCell` read shape.
    fn sites_for(&self, subject: &str) -> Vec<serde_json::Value> {
        self.sites
            .names()
            .into_iter()
            .filter_map(|n| self.sites.get(&n))
            .filter(|cell| cell.owner == subject)
            .map(|cell| {
                let bytes: u64 = cell
                    .content
                    .assets
                    .values()
                    .map(|a| a.body.len() as u64)
                    .sum();
                serde_json::json!({
                    "name": cell.name,
                    "owner": cell.owner,
                    "content_root": cell.content_root,
                    "status": "published",
                    "bytes": bytes,
                })
            })
            .collect()
    }

    /// The subject's bound custom domains (the binding records, scoped by owner).
    fn domains_for(&self, subject: &str) -> Vec<serde_json::Value> {
        self.domains
            .list()
            .into_iter()
            .filter(|b| b.owner == subject)
            .filter_map(|b| serde_json::to_value(b).ok())
            .collect()
    }

    /// The subject's storage buckets — compact metadata (objects + bytes, no
    /// object bodies), in the console's `BucketCell` read shape.
    fn buckets_for(&self, subject: &str) -> Vec<serde_json::Value> {
        self.buckets
            .bucket_names()
            .into_iter()
            .filter_map(|n| self.buckets.get_bucket(&n))
            .filter(|cell| cell.owner == subject)
            .map(|cell| {
                let objects = cell.content.objects.len() as u64;
                let bytes: u64 = cell
                    .content
                    .objects
                    .values()
                    .map(|o| o.body.len() as u64)
                    .sum();
                serde_json::json!({
                    "name": cell.name,
                    "owner": cell.owner,
                    "content_root": cell.content_root,
                    "objects": objects,
                    "bytes": bytes,
                })
            })
            .collect()
    }

    /// The subject's persistent servers (scoped by `lessee`).
    fn servers_for(&self, subject: &str) -> Vec<serde_json::Value> {
        let Some(src) = &self.servers else {
            return Vec::new();
        };
        src.servers()
            .into_iter()
            .filter(|s| s.lessee == subject)
            .filter_map(|s| serde_json::to_value(s).ok())
            .collect()
    }

    /// The subject's $DREGG spend lines (scoped by `owner`).
    fn spend_for(&self, subject: &str) -> Vec<serde_json::Value> {
        let Some(src) = &self.billing else {
            return Vec::new();
        };
        src.spend()
            .into_iter()
            .filter(|e| e.owner == subject)
            .filter_map(|e| serde_json::to_value(e).ok())
            .collect()
    }

    /// The subject's $DREGG balance, as a `{ subject: balance }` object (the console
    /// reads a per-subject balance map). Only the caller's own balance is exposed.
    fn balances_for(&self, subject: &str) -> serde_json::Value {
        let balance = self
            .billing
            .as_ref()
            .and_then(|src| src.balances().get(subject).copied())
            .unwrap_or(0);
        serde_json::json!({ subject: balance })
    }

    /// Route + serve one request through the `dreggnet-http` [`ResponseWriter`]. The
    /// serving binary passes the verified `X-Dregg-Subject` it read off the headers.
    pub fn dispatch(
        &self,
        method: Method,
        target: &str,
        subject: Option<&str>,
        response: &mut ResponseWriter,
    ) -> HandlerResult {
        let Some(m) = map_method(method) else {
            return write(response, &WebResponse::error(405, "unsupported method"));
        };
        let resp = self.respond(m, target, subject);
        write(response, &resp)
    }
}

impl Handler for ApiHandler {
    fn handle(&self, request: &Request, response: &mut ResponseWriter) -> HandlerResult {
        let subject = request.header("x-dregg-subject");
        self.dispatch(request.method(), request.path(), subject, response)
    }
}

/// A JSON-array response over the scoped records.
fn json_array(records: Vec<serde_json::Value>) -> WebResponse {
    json_value(serde_json::Value::Array(records))
}

/// A JSON response over an arbitrary value.
fn json_value(value: serde_json::Value) -> WebResponse {
    WebResponse {
        status: 200,
        content_type: "application/json".to_string(),
        body: value.to_string().into_bytes(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use dreggnet_storage::{Account, BucketRegistry, STORAGE_CAP_PREFIX, StorageCap};
    use dreggnet_webapp::hosting::{PublishCap, SiteContent, SiteRegistry};

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    /// An in-memory server fleet (two lessees) for the scope teeth.
    struct Fleet(Vec<ServerView>);
    impl ServerSource for Fleet {
        fn servers(&self) -> Vec<ServerView> {
            self.0.clone()
        }
    }

    /// An in-memory $DREGG ledger (two owners) for the scope teeth.
    struct Ledger {
        spend: Vec<SpendLine>,
        balances: BTreeMap<String, i64>,
    }
    impl BillingSource for Ledger {
        fn spend(&self) -> Vec<SpendLine> {
            self.spend.clone()
        }
        fn balances(&self) -> BTreeMap<String, i64> {
            self.balances.clone()
        }
    }

    fn srv(id: &str, lessee: &str, name: &str) -> ServerView {
        ServerView {
            id: id.into(),
            name: name.into(),
            lessee: lessee.into(),
            state: "running".into(),
            region: "iad".into(),
            size: "small".into(),
            budget_units: 1000,
            per_period_units: 10,
            periods_metered: 3,
        }
    }

    /// A handler whose registries + sources each hold records for TWO subjects, so
    /// the cap-scope is exercised non-vacuously.
    fn two_owner_handler() -> ApiHandler {
        let sites = Arc::new(SiteRegistry::new());
        sites
            .publish(
                &PublishCap::for_site(ALICE, "alice-site"),
                "alice-site",
                SiteContent::new().with("/index.html", "alice"),
            )
            .unwrap();
        sites
            .publish(
                &PublishCap::for_site(BOB, "bob-secret"),
                "bob-secret",
                SiteContent::new().with("/index.html", "bob"),
            )
            .unwrap();

        let buckets = Arc::new(BucketRegistry::new());
        for (owner, name) in [(ALICE, "alice-bkt"), (BOB, "bob-bkt")] {
            let cap = StorageCap {
                holder: owner.to_string(),
                cap: format!("{STORAGE_CAP_PREFIX}{name}"),
            };
            buckets.create_bucket(&cap, name).unwrap();
            let acct = Account::funded(owner, 1_000_000);
            buckets
                .put(&cap, &acct, name, "obj.txt", b"hello".to_vec())
                .unwrap();
        }

        let domains = Arc::new(DomainRegistry::new());

        let fleet = Fleet(vec![
            srv("srv_a", ALICE, "alice-api"),
            srv("srv_b", BOB, "bob-api"),
        ]);
        let mut balances = BTreeMap::new();
        balances.insert(ALICE.to_string(), 500);
        balances.insert(BOB.to_string(), 12_000);
        let ledger = Ledger {
            spend: vec![
                SpendLine {
                    owner: ALICE.into(),
                    resource_kind: "server".into(),
                    resource_id: "srv_a".into(),
                    period: "p1".into(),
                    units: 1,
                },
                SpendLine {
                    owner: BOB.into(),
                    resource_kind: "server".into(),
                    resource_id: "srv_b".into(),
                    period: "p2".into(),
                    units: 450,
                },
            ],
            balances,
        };

        ApiHandler::new(sites, domains, buckets)
            .with_servers(Arc::new(fleet))
            .with_billing(Arc::new(ledger))
    }

    fn get(h: &ApiHandler, path: &str, subject: Option<&str>) -> serde_json::Value {
        let resp = h.respond(HttpMethod::Get, path, subject);
        assert_eq!(resp.status, 200, "{path}: {}", resp.body_str());
        serde_json::from_slice(&resp.body).unwrap()
    }

    #[test]
    fn each_surface_returns_only_the_callers_records() {
        let h = two_owner_handler();

        // Sites: alice sees only alice-site.
        let sites = get(&h, "/api/sites", Some(ALICE));
        let arr = sites.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["name"], "alice-site");
        assert_eq!(arr[0]["owner"], ALICE);
        assert!(arr[0]["bytes"].as_u64().unwrap() > 0);

        // Buckets: alice sees only her bucket, with the object count + bytes.
        let buckets = get(&h, "/api/buckets", Some(ALICE));
        let arr = buckets.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["name"], "alice-bkt");
        assert_eq!(arr[0]["objects"].as_u64().unwrap(), 1);
        assert_eq!(arr[0]["bytes"].as_u64().unwrap(), 5);

        // Servers: alice sees only srv_a.
        let servers = get(&h, "/api/servers", Some(ALICE));
        let arr = servers.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["id"], "srv_a");
        assert_eq!(arr[0]["lessee"], ALICE);

        // Spend + balance: alice sees only her own.
        let spend = get(&h, "/api/billing/spend", Some(ALICE));
        let arr = spend.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["resource_id"], "srv_a");
        let bal = get(&h, "/api/billing/balances", Some(ALICE));
        assert_eq!(bal[ALICE].as_i64().unwrap(), 500);
        assert!(
            bal.get(BOB).is_none(),
            "another subject's balance never leaks"
        );
    }

    #[test]
    fn a_different_subject_sees_none_of_anothers_records() {
        // THE TEETH: bob's request never observes alice's cells, and vice versa.
        let h = two_owner_handler();

        let bob_sites = get(&h, "/api/sites", Some(BOB));
        let arr = bob_sites.as_array().unwrap();
        assert_eq!(arr.len(), 1);
        assert_eq!(arr[0]["name"], "bob-secret");
        assert!(!arr.iter().any(|s| s["name"] == "alice-site"));

        let bob_servers = get(&h, "/api/servers", Some(BOB));
        assert!(
            !bob_servers
                .as_array()
                .unwrap()
                .iter()
                .any(|s| s["id"] == "srv_a")
        );

        // A stranger (a brand-new account) owns nothing → empty across the board.
        let stranger = "dregg:0000000000000000";
        assert!(
            get(&h, "/api/sites", Some(stranger))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            get(&h, "/api/servers", Some(stranger))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            get(&h, "/api/buckets", Some(stranger))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            get(&h, "/api/billing/balances", Some(stranger))[stranger]
                .as_i64()
                .unwrap(),
            0
        );
    }

    #[test]
    fn no_subject_fails_closed() {
        // No verified subject ⇒ 401; the unscoped, cloud-wide catalog is NEVER served.
        let h = two_owner_handler();
        for path in [
            "/api/sites",
            "/api/servers",
            "/api/domains",
            "/api/buckets",
            "/api/billing/spend",
            "/api/billing/balances",
        ] {
            let resp = h.respond(HttpMethod::Get, path, None);
            assert_eq!(
                resp.status, 401,
                "{path} must fail closed without a subject"
            );
            let resp = h.respond(HttpMethod::Get, path, Some("   "));
            assert_eq!(resp.status, 401, "{path} must reject an empty subject");
        }
    }

    #[test]
    fn unset_sources_contribute_empty_not_fabricated() {
        // The honesty law: with no server/billing source, those surfaces are empty
        // (never fabricated), and the always-present registries still serve.
        let sites = Arc::new(SiteRegistry::new());
        sites
            .publish(
                &PublishCap::for_site(ALICE, "s"),
                "s",
                SiteContent::new().with("/index.html", "hi"),
            )
            .unwrap();
        let h = ApiHandler::new(
            sites,
            Arc::new(DomainRegistry::new()),
            Arc::new(BucketRegistry::new()),
        );
        assert_eq!(
            get(&h, "/api/sites", Some(ALICE)).as_array().unwrap().len(),
            1
        );
        assert!(
            get(&h, "/api/servers", Some(ALICE))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert!(
            get(&h, "/api/billing/spend", Some(ALICE))
                .as_array()
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            get(&h, "/api/billing/balances", Some(ALICE))[ALICE]
                .as_i64()
                .unwrap(),
            0
        );
    }

    #[test]
    fn routing_predicate() {
        assert!(ApiHandler::serves_path("/api/sites"));
        assert!(ApiHandler::serves_path("/api/billing/balances"));
        assert!(!ApiHandler::serves_path("/apidocs"));
        assert!(!ApiHandler::serves_path("/v1/apps/x/machines"));
        assert!(!ApiHandler::serves_path("/storage/b"));
    }
}
