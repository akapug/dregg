//! Where the console reads the user's resources FROM — the one seam between the
//! cap-scoping/render core and the live cloud.
//!
//! A [`ResourceSource`] yields the cloud-wide [`Catalog`]; the console then
//! narrows it to exactly the authenticated subject ([`ConsoleView::for_subject`]).
//! The shipped [`FixtureSource`] returns the deterministic demo catalog so the
//! console runs + tests green standalone. The **reviewed-go** swap is a
//! `LiveSource` that aggregates the real read surfaces over HTTP behind the
//! webauth edge — the dregg node / gateway machines API / hosting registry /
//! domains registry / storage registry / meter outbox — exactly as
//! `dreggnet-ops` aggregates them, but each surface filtered to the subject's
//! own cells. That wiring is the live-edge deploy step; the cap-scoping +
//! render + verify here are source-agnostic and complete.

use std::collections::BTreeMap;

use serde_json::Value;

use crate::client::http_get;
use crate::config::ReadApi;
use crate::model::{
    AgentView, ConsoleView, DomainView, ServerView, SiteView, SpendEntry, StorageBucketView,
};
use crate::scope::Catalog;

/// A source of the cloud-wide resource catalog.
pub trait ResourceSource: Send + Sync {
    /// Fetch the current catalog (across all owners). The console scopes it.
    fn catalog(&self) -> Catalog;
}

/// The deterministic demo source — the shipped, green-standalone path.
pub struct FixtureSource;

impl ResourceSource for FixtureSource {
    fn catalog(&self) -> Catalog {
        crate::fixtures::demo_catalog()
    }
}

/// Assemble the cap-scoped console view for `subject` from `source`.
pub fn view_for(source: &dyn ResourceSource, subject: &str) -> ConsoleView {
    ConsoleView::for_subject(&source.catalog(), subject, crate::now_rfc3339())
}

/// **The live source** — aggregates the real resource read surfaces over HTTP
/// into the cloud-wide [`Catalog`] the console then cap-scopes.
///
/// This is the **reviewed-go** path (the tested core runs on [`FixtureSource`]).
/// It reads each surface (sites / servers / agents / domains / storage / spend /
/// balances) at the configured [`ReadApi`] URL and maps the real registry record
/// shapes (`SiteCell.owner`, `ServerRecord.lessee`, `DomainBinding.owner`,
/// `BucketCell.owner`, `SpendEntry.owner`) into the console's view types. The
/// honesty law mirrors the status page: a surface that is unset or unreachable
/// contributes **nothing** (an empty list) — never fabricated data, never another
/// owner's cells. The cap-scoping in [`ConsoleView::for_subject`] then narrows
/// the catalog to exactly the authenticated subject, so the teeth hold against
/// live data exactly as they do against fixtures.
///
/// NAMED CROSS-LANE DEPENDENCY: the per-registry list endpoints
/// (`/api/sites`, `/api/servers`, `/api/domains`, `/api/buckets`,
/// `/api/billing/spend`, `/api/billing/balances`) are owned by the
/// gateway/registry wireup lane; today only the gateway machines API + node read
/// API exist. This source is wired to that contract and parses the real record
/// shapes, so it goes live the moment those endpoints are exposed.
pub struct LiveSource {
    api: ReadApi,
}

impl LiveSource {
    /// Build over the read-API config.
    pub fn new(api: ReadApi) -> Self {
        LiveSource { api }
    }

    /// `GET` a surface and return its parsed JSON, or `None` (unset/unreachable).
    fn get(&self, url: &Option<String>, path: &str) -> Option<Value> {
        let url = self.api.surface(url, path)?;
        match http_get(&url, self.api.timeout, self.api.bearer.as_deref()) {
            Ok(r) if r.ok() => r.json().ok(),
            _ => None,
        }
    }
}

impl ResourceSource for LiveSource {
    fn catalog(&self) -> Catalog {
        let domains = self
            .get(&self.api.domains_url, "/api/domains")
            .map(|v| map_domains(&v))
            .unwrap_or_default();
        let sites = self
            .get(&self.api.sites_url, "/api/sites")
            .map(|v| map_sites(&v, &domains))
            .unwrap_or_default();
        let servers = self
            .get(&self.api.servers_url, "/api/servers")
            .map(|v| map_servers(&v))
            .unwrap_or_default();
        let agents = self
            .get(&self.api.agents_url, "/api/agents")
            .map(|v| map_agents(&v))
            .unwrap_or_default();
        let buckets = self
            .get(&self.api.buckets_url, "/api/buckets")
            .map(|v| map_buckets(&v))
            .unwrap_or_default();
        let spend = self
            .get(&self.api.spend_url, "/api/billing/spend")
            .map(|v| map_spend(&v))
            .unwrap_or_default();
        let balances = self
            .get(&self.api.balances_url, "/api/billing/balances")
            .map(|v| map_balances(&v))
            .unwrap_or_default();

        Catalog {
            sites,
            servers,
            agents,
            domains,
            buckets,
            spend,
            balances,
        }
    }
}

// ── defensive record mapping (pure; tested against the real shapes) ───────────
//
// Each surface is read as a JSON array (an object for balances). Fields are
// pulled by name, tolerant of the raw registry struct OR a future view endpoint,
// and a record missing its OWNER is dropped (it can never be scoped, so showing
// it would risk a cross-owner leak — fail closed).

fn arr(v: &Value) -> &[Value] {
    v.as_array().map(|a| a.as_slice()).unwrap_or(&[])
}

fn s(v: &Value, k: &str) -> Option<String> {
    v.get(k).and_then(|x| x.as_str()).map(|x| x.to_string())
}

fn u64f(v: &Value, k: &str) -> Option<u64> {
    v.get(k).and_then(|x| x.as_u64())
}

fn i64f(v: &Value, k: &str) -> i64 {
    v.get(k).and_then(|x| x.as_i64()).unwrap_or(0)
}

/// `SiteCell` → `SiteView`. Status defaults to "published" (a registry site is
/// published); the bound domain is joined from the verified domains list when the
/// record doesn't carry it; bytes from `bytes` or the content map's total.
fn map_sites(v: &Value, domains: &[DomainView]) -> Vec<SiteView> {
    arr(v)
        .iter()
        .filter_map(|x| {
            let owner = s(x, "owner")?;
            let name = s(x, "name")?;
            let domain = s(x, "domain").or_else(|| {
                domains
                    .iter()
                    .find(|d| d.site == name && d.state == "verified")
                    .map(|d| d.domain.clone())
            });
            Some(SiteView {
                owner,
                name,
                status: s(x, "status").unwrap_or_else(|| "published".into()),
                domain,
                content_root: s(x, "content_root").unwrap_or_default(),
                bytes: u64f(x, "bytes").unwrap_or_else(|| content_bytes(x)),
            })
        })
        .collect()
}

/// Total bytes across a SiteCell/BucketCell `content` map, when present.
fn content_bytes(x: &Value) -> u64 {
    x.get("content")
        .and_then(|c| c.as_object())
        .map(|m| {
            m.values()
                .map(|o| {
                    o.get("bytes")
                        .or_else(|| o.get("size"))
                        .and_then(|b| b.as_u64())
                        .unwrap_or(0)
                })
                .sum()
        })
        .unwrap_or(0)
}

/// `ServerRecord` → `ServerView` (owner is the `lessee`).
fn map_servers(v: &Value) -> Vec<ServerView> {
    arr(v)
        .iter()
        .filter_map(|x| {
            let lessee = s(x, "lessee").or_else(|| s(x, "owner"))?;
            Some(ServerView {
                lessee,
                id: s(x, "id").unwrap_or_default(),
                name: s(x, "name").unwrap_or_default(),
                state: s(x, "state").unwrap_or_default().to_ascii_lowercase(),
                region: s(x, "region").unwrap_or_default(),
                size: s(x, "size").unwrap_or_default(),
                budget_units: i64f(x, "budget_units"),
                per_period_units: i64f(x, "per_period_units"),
                periods_metered: i64f(x, "periods_metered"),
            })
        })
        .collect()
}

/// `DomainBinding` → `DomainView`. The `state` is normalized to verified/pending.
fn map_domains(v: &Value) -> Vec<DomainView> {
    arr(v)
        .iter()
        .filter_map(|x| {
            let owner = s(x, "owner")?;
            let raw_state = s(x, "state").unwrap_or_default().to_ascii_lowercase();
            let state = if raw_state.contains("verif") {
                "verified"
            } else {
                "pending"
            };
            Some(DomainView {
                owner,
                domain: s(x, "domain").unwrap_or_default(),
                site: s(x, "site").unwrap_or_default(),
                state: state.to_string(),
                verified_seq: u64f(x, "verified_seq"),
            })
        })
        .collect()
}

/// `BucketCell` → `StorageBucketView` (objects/bytes from the content map or
/// explicit fields).
fn map_buckets(v: &Value) -> Vec<StorageBucketView> {
    arr(v)
        .iter()
        .filter_map(|x| {
            let owner = s(x, "owner")?;
            let objects = u64f(x, "objects").unwrap_or_else(|| {
                x.get("content")
                    .and_then(|c| c.as_object())
                    .map(|m| m.len() as u64)
                    .unwrap_or(0)
            });
            Some(StorageBucketView {
                owner,
                name: s(x, "name").unwrap_or_default(),
                content_root: s(x, "content_root").unwrap_or_default(),
                objects,
                bytes: u64f(x, "bytes").unwrap_or_else(|| content_bytes(x)),
            })
        })
        .collect()
}

/// `AgentView` records (the deployed-agent surface carries the full re-witnessable
/// run report) — deserialized via serde; a record that doesn't parse is dropped.
fn map_agents(v: &Value) -> Vec<AgentView> {
    arr(v)
        .iter()
        .filter_map(|x| serde_json::from_value::<AgentView>(x.clone()).ok())
        .filter(|a| !a.owner.is_empty())
        .collect()
}

/// `SpendEntry` records — the meter/settle spend ledger lines.
fn map_spend(v: &Value) -> Vec<SpendEntry> {
    arr(v)
        .iter()
        .filter_map(|x| {
            let owner = s(x, "owner")?;
            Some(SpendEntry {
                owner,
                resource_kind: s(x, "resource_kind").unwrap_or_default(),
                resource_id: s(x, "resource_id").unwrap_or_default(),
                period: s(x, "period").unwrap_or_default(),
                units: i64f(x, "units"),
            })
        })
        .collect()
}

/// `{subject: balance}` → the per-subject balance map.
fn map_balances(v: &Value) -> BTreeMap<String, i64> {
    v.as_object()
        .map(|m| {
            m.iter()
                .filter_map(|(k, val)| val.as_i64().map(|b| (k.clone(), b)))
                .collect()
        })
        .unwrap_or_default()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures;
    use crate::model::Owned;

    #[test]
    fn the_fixture_source_scopes_to_the_subject() {
        let src = FixtureSource;
        let view = view_for(&src, fixtures::DEMO_SUBJECT);
        assert_eq!(view.subject, fixtures::DEMO_SUBJECT);
        assert!(!view.sites.is_empty());
        // The second user's resources are absent.
        assert!(view.sites.iter().all(|s| s.owner == fixtures::DEMO_SUBJECT));
        assert!(!view.servers.iter().any(|s| s.id == "srv_other99"));
    }

    // ── LiveSource mapping against the REAL registry record shapes ─────────────
    //
    // Faithful captures of the structs the real surfaces serialize (per the
    // source dig): SiteCell{name,owner,content_root,content}, ServerRecord with
    // `lessee`, DomainBinding{owner,domain,site,state,verified_seq}, BucketCell,
    // SpendEntry, and a {subject:balance} balances object. Two owners, so the
    // cap-scope is exercised non-vacuously over LIVE-shaped data.
    use serde_json::json;

    const ALICE: &str = "dregg:aaaa0000aaaa0000";
    const BOB: &str = "dregg:bbbb1111bbbb1111";

    #[test]
    fn maps_real_server_record_shape_with_lessee_owner() {
        let v = json!([{
            "id": "srv_a1", "app": "myapp", "name": "api", "state": "Running",
            "lessee": ALICE, "cap_grade": "standard", "asset": "DREGG",
            "budget_units": 5000, "per_period_units": 10, "size": "small",
            "region": "iad", "periods_metered": 12, "machine_id": "m-1",
            "last_metered_at": 1700000000, "cell_id": "cell-1", "checkpoint_root": null
        }]);
        let servers = map_servers(&v);
        assert_eq!(servers.len(), 1);
        let s = &servers[0];
        assert_eq!(s.lessee, ALICE); // the lessee IS the owner
        assert_eq!(s.owner(), ALICE);
        assert_eq!(s.state, "running"); // ServerState normalized to lowercase
        assert_eq!(s.budget_units, 5000);
        assert_eq!(s.settled_units(), 120);
    }

    #[test]
    fn maps_real_domain_and_site_shapes_and_joins_the_bound_domain() {
        let domains = map_domains(&json!([{
            "domain": "alice.example", "site": "alice-site", "owner": ALICE,
            "method": "dns-01", "challenge": "tok", "state": "Verified", "verified_seq": 7
        }]));
        assert_eq!(domains.len(), 1);
        assert_eq!(domains[0].state, "verified"); // VerificationState normalized
        assert_eq!(domains[0].owner(), ALICE);

        // SiteCell has no `domain`/`bytes`/`status` — they're defaulted/joined.
        let sites = map_sites(
            &json!([{
                "name": "alice-site", "owner": ALICE, "content_root": "root-a",
                "content": { "index.html": { "bytes": 2048 }, "style.css": { "bytes": 100 } }
            }]),
            &domains,
        );
        assert_eq!(sites.len(), 1);
        let s = &sites[0];
        assert_eq!(s.status, "published"); // registry sites are published
        assert_eq!(s.domain.as_deref(), Some("alice.example")); // joined from domains
        assert_eq!(s.bytes, 2148); // summed from the content map
    }

    #[test]
    fn a_record_missing_its_owner_is_dropped_fail_closed() {
        // A record with no owner can never be scoped — showing it would risk a
        // cross-owner leak, so it is dropped (fail closed), never shown to all.
        let servers = map_servers(&json!([{ "id": "ghost", "name": "no-owner" }]));
        assert!(servers.is_empty());
        let sites = map_sites(&json!([{ "name": "ghost", "content_root": "r" }]), &[]);
        assert!(sites.is_empty());
    }

    #[test]
    fn the_cap_scope_holds_against_live_shaped_two_owner_data() {
        // Build a catalog the way LiveSource does, from real-shaped records owned
        // by two subjects, then prove a user sees ONLY their own cells.
        let servers = map_servers(&json!([
            { "id": "srv_a", "name": "a", "lessee": ALICE, "state": "Running",
              "budget_units": 100, "per_period_units": 1, "periods_metered": 1,
              "region": "iad", "size": "small" },
            { "id": "srv_b", "name": "b-secret", "lessee": BOB, "state": "Running",
              "budget_units": 900, "per_period_units": 9, "periods_metered": 2,
              "region": "lax", "size": "large" }
        ]));
        let spend = map_spend(&json!([
            { "owner": ALICE, "resource_kind": "server", "resource_id": "srv_a",
              "period": "p1", "units": 1 },
            { "owner": BOB, "resource_kind": "server", "resource_id": "srv_b",
              "period": "p2", "units": 450 }
        ]));
        let balances = map_balances(&json!({ ALICE: 500, BOB: 12000 }));

        let cat = Catalog {
            servers,
            spend,
            balances,
            ..Catalog::default()
        };
        let alice = ConsoleView::for_subject(&cat, ALICE, "t".into());
        // Alice sees only her server + her spend, and her balance only.
        assert_eq!(alice.servers.len(), 1);
        assert_eq!(alice.servers[0].id, "srv_a");
        assert!(!alice.servers.iter().any(|s| s.name == "b-secret"));
        assert_eq!(alice.dregg.balance, 500);
        assert_eq!(alice.dregg.total_spent, 1);
        // Bob's view is disjoint.
        let bob = ConsoleView::for_subject(&cat, BOB, "t".into());
        assert_eq!(bob.dregg.balance, 12000);
        assert!(!bob.servers.iter().any(|s| s.id == "srv_a"));
    }

    #[test]
    fn an_unreachable_or_unset_surface_contributes_nothing() {
        // A LiveSource with NO base and NO surface URLs is not live and yields an
        // empty catalog — never fabricated data, never a false resource.
        let api = ReadApi::default();
        assert!(!api.is_live());
        let cat = LiveSource::new(api).catalog();
        assert!(cat.sites.is_empty() && cat.servers.is_empty() && cat.balances.is_empty());
    }

    #[test]
    fn maps_buckets_spend_and_balances_shapes() {
        let buckets = map_buckets(&json!([{
            "name": "assets", "owner": ALICE, "content_root": "bkt-a",
            "content": { "a.png": { "bytes": 1000 }, "b.png": { "bytes": 24 } }
        }]));
        assert_eq!(buckets.len(), 1);
        assert_eq!(buckets[0].objects, 2);
        assert_eq!(buckets[0].bytes, 1024);
        assert_eq!(buckets[0].owner(), ALICE);

        let balances = map_balances(&json!({ ALICE: 7, BOB: -3 }));
        assert_eq!(balances.get(ALICE), Some(&7));
        assert_eq!(balances.get(BOB), Some(&-3));
    }
}
