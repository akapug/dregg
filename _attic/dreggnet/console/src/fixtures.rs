//! Deterministic demo data — a real, re-witnessable agent run + a populated
//! [`Catalog`] — so the console renders and tests green WITHOUT a live cloud.
//!
//! The agent report is NOT hand-built: it is produced by the real
//! `dreggnet_exec::agent` braid (deploy → run-with-toolkit → seal a signed
//! receipt chain), so [`crate::verify`] re-witnesses a genuine proof and the
//! forge teeth bite a genuine signature. The fixtures are the same shape the
//! live resource surfaces emit; the reviewed-go step swaps this source for the
//! live HTTP aggregation behind the webauth edge.

use std::collections::BTreeMap;

use dreggnet_exec::agent::{
    AgentAction, AgentCloud, AgentRunReport, AgentSpec, PlannedBrain, ToolKit, ToolOutcome,
    WitnessedRun,
};

use crate::model::{AgentView, DomainView, ServerView, SiteView, SpendEntry, StorageBucketView};
use crate::scope::Catalog;

/// The demo user's subject (the shape `dreggnet_webauth::subject_of` yields).
pub const DEMO_SUBJECT: &str = "dregg:demo0001demo0001";
/// A second user, so the catalog is multi-tenant and the scoping is non-trivial.
pub const OTHER_SUBJECT: &str = "dregg:other0002other000";
/// The deployed content root the demo agent's QA ran against (a site's commitment).
pub const DEMO_CONTENT_ROOT: &str = "demo-content-root-poseidon2";

/// A toolkit whose `verify_deploy` returns a passing, execution-witnessed verdict
/// bound to [`DEMO_CONTENT_ROOT`] — the QA proof the agent panel surfaces.
struct DemoToolkit;

impl ToolKit for DemoToolkit {
    fn invoke(
        &self,
        service: &str,
        _budget: Option<i64>,
        _cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        match service {
            "verify_deploy" => ToolOutcome::pass("deploy verified: 12/12 checks green")
                .with_witness(WitnessedRun {
                    command: "verify_deploy[lang=wat,tier=Sandboxed,entry=run]".to_string(),
                    code_root: DEMO_CONTENT_ROOT.to_string(),
                    exit: 0,
                    output_digest: [7u8; 32],
                }),
            "run_tests" => {
                ToolOutcome::pass("tests: 34 passed, 0 failed").with_witness(WitnessedRun {
                    command: "run_tests[lang=wat,tier=Sandboxed,entry=run]".to_string(),
                    code_root: DEMO_CONTENT_ROOT.to_string(),
                    exit: 0,
                    output_digest: [9u8; 32],
                })
            }
            _ => ToolOutcome::pass("ok"),
        }
    }
}

/// Build the demo agent's real run report + the deployed content root its QA
/// must match. Deterministic (seeded cloud), so the receipt chain is reproducible.
pub fn demo_agent_report() -> (AgentRunReport, String) {
    let cloud = AgentCloud::from_seed([42u8; 32]);
    let spec = AgentSpec::new("agent:deploy-bot", 50)
        .with_service("run_tests")
        .with_service("verify_deploy")
        .with_cell("/deploy");
    let handle = cloud.deploy(&spec).expect("deploy the demo agent");
    let plan = vec![
        AgentAction::CellWrite {
            path: "/deploy".into(),
            value: "demo-site".into(),
        },
        AgentAction::Invoke {
            service: "run_tests".into(),
        },
        AgentAction::Invoke {
            service: "verify_deploy".into(),
        },
    ];
    let report = cloud.run_with_toolkit(&handle, &mut PlannedBrain::new(plan), &DemoToolkit);
    (report, DEMO_CONTENT_ROOT.to_string())
}

/// The demo user's deployed-agent view (the panel: budget bound + receipts + QA).
pub fn demo_agent_view(owner: &str) -> AgentView {
    let (report, deployed_root) = demo_agent_report();
    AgentView {
        owner: owner.to_string(),
        id: report.agent.clone(),
        caps: vec![
            "invoke:run_tests".to_string(),
            "invoke:verify_deploy".to_string(),
            "cell-read:/deploy".to_string(),
            "cell-write:/deploy".to_string(),
        ],
        report,
        deployed_root,
    }
}

/// A populated, multi-tenant catalog: the demo user's full "my stuff" plus a
/// second user's resources (so the cap-scoping is exercised, not vacuous).
pub fn demo_catalog() -> Catalog {
    let mut cat = Catalog::default();

    // ── the demo user ─────────────────────────────────────────────────────────
    cat.sites.push(SiteView {
        owner: DEMO_SUBJECT.into(),
        name: "demo-site".into(),
        status: "published".into(),
        domain: Some("demo.example".into()),
        content_root: DEMO_CONTENT_ROOT.into(),
        bytes: 4_096,
    });
    cat.sites.push(SiteView {
        owner: DEMO_SUBJECT.into(),
        name: "blog".into(),
        status: "published".into(),
        domain: None,
        content_root: "blog-content-root".into(),
        bytes: 12_800,
    });
    cat.servers.push(ServerView {
        lessee: DEMO_SUBJECT.into(),
        id: "srv_demo01".into(),
        name: "api-server".into(),
        state: "running".into(),
        region: "iad".into(),
        size: "small".into(),
        budget_units: 5_000,
        per_period_units: 10,
        periods_metered: 144,
    });
    cat.agents.push(demo_agent_view(DEMO_SUBJECT));
    cat.domains.push(DomainView {
        owner: DEMO_SUBJECT.into(),
        domain: "demo.example".into(),
        site: "demo-site".into(),
        state: "verified".into(),
        verified_seq: Some(12),
    });
    cat.domains.push(DomainView {
        owner: DEMO_SUBJECT.into(),
        domain: "staging.demo.example".into(),
        site: "demo-site".into(),
        state: "pending".into(),
        verified_seq: None,
    });
    cat.buckets.push(StorageBucketView {
        owner: DEMO_SUBJECT.into(),
        name: "assets".into(),
        content_root: "assets-root".into(),
        objects: 27,
        bytes: 1_048_576,
    });
    for (period, units) in [("p142", 10), ("p143", 10), ("p144", 10)] {
        cat.spend.push(SpendEntry {
            owner: DEMO_SUBJECT.into(),
            resource_kind: "server".into(),
            resource_id: "srv_demo01".into(),
            period: period.into(),
            units,
        });
    }
    cat.spend.push(SpendEntry {
        owner: DEMO_SUBJECT.into(),
        resource_kind: "agent".into(),
        resource_id: "agent:deploy-bot".into(),
        period: "run-1".into(),
        units: 2,
    });
    cat.balances.insert(DEMO_SUBJECT.into(), 9_968);

    // ── a second user (must never appear in the demo user's view) ──────────────
    cat.sites.push(SiteView {
        owner: OTHER_SUBJECT.into(),
        name: "other-private".into(),
        status: "published".into(),
        domain: None,
        content_root: "other-root".into(),
        bytes: 512,
    });
    cat.servers.push(ServerView {
        lessee: OTHER_SUBJECT.into(),
        id: "srv_other99".into(),
        name: "other-srv".into(),
        state: "running".into(),
        region: "lax".into(),
        size: "large".into(),
        budget_units: 50_000,
        per_period_units: 90,
        periods_metered: 10,
    });
    cat.agents.push(demo_agent_view(OTHER_SUBJECT));
    cat.buckets.push(StorageBucketView {
        owner: OTHER_SUBJECT.into(),
        name: "other-bucket".into(),
        content_root: "other-bkt".into(),
        objects: 3,
        bytes: 4_096,
    });
    cat.spend.push(SpendEntry {
        owner: OTHER_SUBJECT.into(),
        resource_kind: "server".into(),
        resource_id: "srv_other99".into(),
        period: "p10".into(),
        units: 900,
    });
    cat.balances.insert(OTHER_SUBJECT.into(), 100_000);

    cat
}
