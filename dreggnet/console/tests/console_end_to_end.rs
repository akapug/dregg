//! End-to-end: assemble a cap-scoped console view from the fixture source,
//! render it, and re-witness the agent panel — the whole "a logged-in user sees
//! their resources (and not another's), the agent panel shows the bound + the QA
//! proof + re-verifies, and verify-anything works" claim, exercised top to bottom.

use dreggnet_console::model::ConsoleView;
use dreggnet_console::source::{FixtureSource, view_for};
use dreggnet_console::verify::verify_agent_report;
use dreggnet_console::{fixtures, render};

#[test]
fn a_logged_in_user_sees_their_stuff_and_it_re_witnesses() {
    let src = FixtureSource;

    // 1. The signed-in user gets their cap-scoped view.
    let view: ConsoleView = view_for(&src, fixtures::DEMO_SUBJECT);
    assert_eq!(view.subject, fixtures::DEMO_SUBJECT);
    assert!(!view.sites.is_empty() && !view.agents.is_empty() && !view.servers.is_empty());

    // 2. Cap-scoping: NOTHING in the view belongs to anyone else.
    assert!(view.sites.iter().all(|s| s.owner == fixtures::DEMO_SUBJECT));
    assert!(
        view.servers
            .iter()
            .all(|s| s.lessee == fixtures::DEMO_SUBJECT)
    );
    assert!(
        view.agents
            .iter()
            .all(|a| a.owner == fixtures::DEMO_SUBJECT)
    );
    assert!(
        view.buckets
            .iter()
            .all(|b| b.owner == fixtures::DEMO_SUBJECT)
    );
    assert!(
        view.domains
            .iter()
            .all(|d| d.owner == fixtures::DEMO_SUBJECT)
    );

    // 3. The agent panel: the budget BOUND + the QA proof.
    let agent = &view.agents[0];
    assert_eq!(
        agent.consumed() + agent.headroom(),
        agent.budget(),
        "the could-have bound"
    );
    assert!(
        agent.qa_passed(),
        "the demo agent's declared tests ran green on the deployed code"
    );

    // 4. The re-verify: the panel re-witnesses in-page (chain ✓ · bound ✓ · QA ✓).
    let verdict = verify_agent_report(
        &agent.report,
        &agent.deployed_root,
        Some((&view.subject, &agent.owner)),
    );
    assert!(verdict.ok, "{}", verdict.detail);
    assert_eq!(verdict.owner_scope_ok, Some(true));

    // 5. The render shows the real, scoped data and never another user's.
    let html = render::render_page(&view, "/.dregg-auth");
    assert!(html.contains("api-server") && html.contains("agent:deploy-bot"));
    assert!(!html.contains("other-private") && !html.contains(fixtures::OTHER_SUBJECT));

    // 6. The $DREGG ledger is the user's own, summed.
    assert_eq!(view.dregg.subject, fixtures::DEMO_SUBJECT);
    assert_eq!(
        view.dregg.total_spent,
        view.dregg.entries.iter().map(|e| e.units).sum::<i64>()
    );
    assert!(view.dregg.balance > 0);
}

#[test]
fn another_user_logging_in_sees_a_disjoint_view() {
    let src = FixtureSource;
    let demo = view_for(&src, fixtures::DEMO_SUBJECT);
    let other = view_for(&src, fixtures::OTHER_SUBJECT);
    // The two signed-in users see disjoint sites.
    let demo_sites: std::collections::BTreeSet<_> = demo.sites.iter().map(|s| &s.name).collect();
    let other_sites: std::collections::BTreeSet<_> = other.sites.iter().map(|s| &s.name).collect();
    assert!(demo_sites.is_disjoint(&other_sites));
    assert!(
        other
            .sites
            .iter()
            .all(|s| s.owner == fixtures::OTHER_SUBJECT)
    );
}
