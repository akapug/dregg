//! **The cap-scoping teeth.** The console shows a signed-in user ONLY their own
//! cells — a user can never see another user's resources.
//!
//! The authority model is the dregg webauth `dga1_` forward-auth: Caddy verifies
//! the presented capability and echoes the credential's stable **subject**
//! (`dregg:<16 hex>`, [`dreggnet_webauth::subject_of`]) onto the upstream request
//! as `X-Dregg-Subject`. That subject IS the cap holder, and every resource
//! surface (domains, storage, …) already records its `owner`/`lessee` as that
//! same subject. So scoping is one rule applied uniformly:
//!
//! > a resource is in the user's view **iff** `resource.owner() == subject`.
//!
//! [`scope`] filters any `Owned` collection by that rule; [`ConsoleView::for_subject`]
//! assembles the whole "my stuff" view from the cloud-wide [`Catalog`]. The
//! subject is taken from the *verified* forward-auth header — never a query
//! param a caller could spoof (the server enforces this; see the bin), so a user
//! cannot widen their view to someone else's cells.

use crate::model::{
    AgentView, ConsoleView, DomainView, DreggLedgerView, Owned, ServerView, SiteView, SpendEntry,
    StorageBucketView,
};

/// Keep only the items owned by `subject` — the single cap-scoping filter every
/// surface rides. Pure, total, order-preserving.
pub fn scope<T: Owned + Clone>(items: &[T], subject: &str) -> Vec<T> {
    items
        .iter()
        .filter(|i| i.owner() == subject)
        .cloned()
        .collect()
}

/// The cloud-wide resource set across *all* users — what an unscoped aggregator
/// (the live resource surfaces) would return. The console NEVER serves this; it
/// is the input [`ConsoleView::for_subject`] narrows to exactly one subject.
#[derive(Clone, Debug, Default)]
pub struct Catalog {
    /// Every published site, across all owners.
    pub sites: Vec<SiteView>,
    /// Every persistent server, across all lessees.
    pub servers: Vec<ServerView>,
    /// Every deployed agent, across all deployers.
    pub agents: Vec<AgentView>,
    /// Every bound custom domain, across all owners.
    pub domains: Vec<DomainView>,
    /// Every storage bucket, across all owners.
    pub buckets: Vec<StorageBucketView>,
    /// Every $DREGG spend line, across all owners.
    pub spend: Vec<SpendEntry>,
    /// Per-subject $DREGG balances.
    pub balances: std::collections::BTreeMap<String, i64>,
}

impl Catalog {
    /// The set of distinct subjects that own *anything* in the catalog (for the
    /// operator's sense of who has cells; the console itself never enumerates it
    /// to a user).
    pub fn subjects(&self) -> std::collections::BTreeSet<String> {
        let mut s = std::collections::BTreeSet::new();
        for x in &self.sites {
            s.insert(x.owner.clone());
        }
        for x in &self.servers {
            s.insert(x.lessee.clone());
        }
        for x in &self.agents {
            s.insert(x.owner.clone());
        }
        for x in &self.domains {
            s.insert(x.owner.clone());
        }
        for x in &self.buckets {
            s.insert(x.owner.clone());
        }
        for x in &self.spend {
            s.insert(x.owner.clone());
        }
        for k in self.balances.keys() {
            s.insert(k.clone());
        }
        s
    }
}

impl ConsoleView {
    /// **Assemble the cap-scoped view** for `subject`: every collection filtered
    /// to the subject's own cells, and the $DREGG ledger summed from exactly the
    /// subject's spend lines. The teeth: nothing another subject owns can appear.
    pub fn for_subject(catalog: &Catalog, subject: &str, generated_at: String) -> ConsoleView {
        let entries = scope(&catalog.spend, subject);
        let total_spent = entries.iter().map(|e| e.units).sum();
        let dregg = DreggLedgerView {
            subject: subject.to_string(),
            balance: catalog.balances.get(subject).copied().unwrap_or(0),
            total_spent,
            entries,
        };
        ConsoleView {
            subject: subject.to_string(),
            generated_at,
            sites: scope(&catalog.sites, subject),
            servers: scope(&catalog.servers, subject),
            agents: scope(&catalog.agents, subject),
            domains: scope(&catalog.domains, subject),
            buckets: scope(&catalog.buckets, subject),
            dregg,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures;

    fn alice() -> &'static str {
        "dregg:aaaa0000aaaa0000"
    }
    fn bob() -> &'static str {
        "dregg:bbbb1111bbbb1111"
    }

    /// A catalog with resources owned by two distinct subjects.
    fn two_user_catalog() -> Catalog {
        let mut cat = Catalog::default();
        // Alice: a site, a server, a domain, a bucket, spend, a balance.
        cat.sites.push(SiteView {
            owner: alice().into(),
            name: "alice-site".into(),
            status: "published".into(),
            domain: Some("alice.example".into()),
            content_root: "root-a".into(),
            bytes: 100,
        });
        cat.servers.push(ServerView {
            lessee: alice().into(),
            id: "srv_alice".into(),
            name: "alice-srv".into(),
            state: "running".into(),
            region: "iad".into(),
            size: "small".into(),
            budget_units: 1000,
            per_period_units: 10,
            periods_metered: 3,
        });
        cat.domains.push(DomainView {
            owner: alice().into(),
            domain: "alice.example".into(),
            site: "alice-site".into(),
            state: "verified".into(),
            verified_seq: Some(7),
        });
        cat.buckets.push(StorageBucketView {
            owner: alice().into(),
            name: "alice-bucket".into(),
            content_root: "bkt-a".into(),
            objects: 4,
            bytes: 2048,
        });
        cat.spend.push(SpendEntry {
            owner: alice().into(),
            resource_kind: "server".into(),
            resource_id: "srv_alice".into(),
            period: "p3".into(),
            units: 30,
        });
        cat.balances.insert(alice().into(), 500);

        // Bob: a site, a server, a domain, a bucket, spend, a balance.
        cat.sites.push(SiteView {
            owner: bob().into(),
            name: "bob-secret".into(),
            status: "published".into(),
            domain: None,
            content_root: "root-b".into(),
            bytes: 200,
        });
        cat.servers.push(ServerView {
            lessee: bob().into(),
            id: "srv_bob".into(),
            name: "bob-srv".into(),
            state: "running".into(),
            region: "lax".into(),
            size: "large".into(),
            budget_units: 9000,
            per_period_units: 90,
            periods_metered: 5,
        });
        cat.domains.push(DomainView {
            owner: bob().into(),
            domain: "bob.example".into(),
            site: "bob-secret".into(),
            state: "pending".into(),
            verified_seq: None,
        });
        cat.buckets.push(StorageBucketView {
            owner: bob().into(),
            name: "bob-bucket".into(),
            content_root: "bkt-b".into(),
            objects: 9,
            bytes: 9000,
        });
        cat.spend.push(SpendEntry {
            owner: bob().into(),
            resource_kind: "server".into(),
            resource_id: "srv_bob".into(),
            period: "p5".into(),
            units: 450,
        });
        cat.balances.insert(bob().into(), 12_000);
        cat
    }

    // ── TOOTH: a user sees ONLY their own resources, never another's ──────────
    #[test]
    fn a_user_sees_only_their_own_cells() {
        let cat = two_user_catalog();
        let view = ConsoleView::for_subject(&cat, alice(), "t".into());

        // Everything alice sees is alice's.
        assert!(view.sites.iter().all(|s| s.owner == alice()));
        assert!(view.servers.iter().all(|s| s.lessee == alice()));
        assert!(view.domains.iter().all(|d| d.owner == alice()));
        assert!(view.buckets.iter().all(|b| b.owner == alice()));
        assert!(view.dregg.entries.iter().all(|e| e.owner == alice()));

        // She has exactly her own (one of each).
        assert_eq!(view.sites.len(), 1);
        assert_eq!(view.servers.len(), 1);
        assert_eq!(view.domains.len(), 1);
        assert_eq!(view.buckets.len(), 1);
        assert_eq!(view.sites[0].name, "alice-site");

        // NONE of bob's resources leak into alice's view.
        assert!(!view.sites.iter().any(|s| s.name == "bob-secret"));
        assert!(!view.servers.iter().any(|s| s.id == "srv_bob"));
        assert!(!view.buckets.iter().any(|b| b.name == "bob-bucket"));
        assert!(!view.domains.iter().any(|d| d.domain == "bob.example"));
    }

    // ── TOOTH: the $DREGG ledger is scoped + summed per-subject ────────────────
    #[test]
    fn the_dregg_ledger_is_scoped_and_summed() {
        let cat = two_user_catalog();
        let alice_v = ConsoleView::for_subject(&cat, alice(), "t".into());
        let bob_v = ConsoleView::for_subject(&cat, bob(), "t".into());

        assert_eq!(alice_v.dregg.balance, 500);
        assert_eq!(alice_v.dregg.total_spent, 30, "only alice's spend lines");
        assert_eq!(bob_v.dregg.balance, 12_000);
        assert_eq!(bob_v.dregg.total_spent, 450, "only bob's spend lines");
        // Alice's ledger never carries a bob charge.
        assert!(
            alice_v
                .dregg
                .entries
                .iter()
                .all(|e| e.resource_id != "srv_bob")
        );
    }

    // ── TOOTH: two subjects' views are DISJOINT ────────────────────────────────
    #[test]
    fn two_subjects_views_are_disjoint() {
        let cat = two_user_catalog();
        let a = ConsoleView::for_subject(&cat, alice(), "t".into());
        let b = ConsoleView::for_subject(&cat, bob(), "t".into());
        let a_sites: std::collections::BTreeSet<_> = a.sites.iter().map(|s| &s.name).collect();
        let b_sites: std::collections::BTreeSet<_> = b.sites.iter().map(|s| &s.name).collect();
        assert!(
            a_sites.is_disjoint(&b_sites),
            "no shared sites across subjects"
        );
    }

    // ── an unknown subject (a brand-new account) sees an EMPTY view ─────────────
    #[test]
    fn an_unknown_subject_sees_nothing() {
        let cat = two_user_catalog();
        let view = ConsoleView::for_subject(&cat, "dregg:0000000000000000", "t".into());
        assert!(
            view.is_empty(),
            "a stranger's subject owns nothing in the catalog"
        );
        assert_eq!(view.dregg.balance, 0);
    }

    // ── the agent fixture is scoped too (its run report rides along) ───────────
    #[test]
    fn the_agent_panel_is_scoped_and_carries_the_real_report() {
        // The shipped fixture catalog binds its agents to a known subject.
        let cat = fixtures::demo_catalog();
        let subject = fixtures::DEMO_SUBJECT;
        let view = ConsoleView::for_subject(&cat, subject, "t".into());
        assert!(
            !view.agents.is_empty(),
            "the demo user has a deployed agent"
        );
        for a in &view.agents {
            assert_eq!(a.owner, subject);
            // The agent panel carries the real budget bound + receipts + QA.
            assert!(a.budget() > 0);
            assert_eq!(
                a.consumed() + a.headroom(),
                a.budget(),
                "the could-have bound"
            );
            assert!(a.receipts() > 0, "the run sealed receipts");
        }
        // Another subject does not see the demo user's agents.
        let other = ConsoleView::for_subject(&cat, "dregg:ffffffffffffffff", "t".into());
        assert!(other.agents.is_empty());
    }
}
