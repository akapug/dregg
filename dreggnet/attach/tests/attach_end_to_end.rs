//! End-to-end: a logged-in user types a goal → the transcript streams → the
//! budget draws → receipts accumulate → verify-in-browser re-witnesses (✓; a
//! tampered receipt → ✗); another user's session is isolated. The whole "drive a
//! hosted agent in the browser, cap-scoped, verify-don't-trust" claim, top to
//! bottom over the shipped demo driver.

use dreggnet_attach::render;
use dreggnet_attach::session::GoalRequest;
use dreggnet_attach::store::SessionStore;
use dreggnet_attach::stream::transcript_stream;
use dreggnet_attach::transcript::{BudgetMeter, transcript_of};
use dreggnet_attach::verify::verify_session;

const ALICE: &str = "dregg:aaaa0000aaaa0000";
const BOB: &str = "dregg:bbbb1111bbbb1111";

#[test]
fn a_user_drives_streams_and_verifies_their_agent_cap_scoped() {
    let store = SessionStore::new();

    // 1. Alice types a natural-language goal + sets a budget + picks the bundle.
    let req = GoalRequest::new("clone the repo, run the tests, and verify the deploy", 50)
        .with_service("run_tests")
        .with_service("verify_deploy")
        .with_cell("/goal");
    let session = store.create(&req, ALICE).unwrap();
    assert_eq!(session.owner, ALICE);
    assert_eq!(
        session.goal(),
        "clone the repo, run the tests, and verify the deploy"
    );

    // 2. The transcript streams the reason→act→observe steps.
    let steps = transcript_of(&session);
    assert!(!steps.is_empty());
    assert!(
        steps.iter().any(|s| s.admitted && s.tool_summary.is_some()),
        "an admitted tool call surfaced a real verdict"
    );
    // The cap-gate ✗ is visible (the out-of-bundle probe was refused).
    assert!(
        steps.iter().any(|s| !s.admitted),
        "the cap-gate refused a tool — the teeth are non-vacuous"
    );

    // 3. The budget draws down + receipts accumulate, within the ceiling.
    let meter = BudgetMeter::of(&session);
    assert!(meter.consumed > 0, "the budget drew down");
    assert_eq!(
        meter.consumed + meter.headroom,
        meter.budget,
        "the could-have bound"
    );
    assert!(
        session.receipts() >= 2,
        "receipts accumulated per admitted action"
    );

    // 4. The SSE stream is well-formed (meta … steps … done).
    let body = transcript_stream(&session);
    assert!(body.contains("event: meta\ndata: "));
    assert!(body.contains("event: step\ndata: "));
    assert!(body.contains("event: done\ndata: "));

    // 5. Verify-in-browser re-witnesses the chain + the bound (✓).
    let ok = verify_session(&session, ALICE);
    assert!(ok.ok, "{}", ok.detail);
    assert_eq!(ok.owner_scope_ok, Some(true));
    assert_eq!(ok.consumed + ok.headroom, ok.budget);

    // 6. A tampered receipt is caught (✗).
    let mut tampered = store.get_for_subject(&session.id, ALICE).unwrap();
    let i = tampered
        .run
        .run
        .receipts
        .iter()
        .position(|r| r.tool_ok.is_some())
        .unwrap();
    tampered.run.run.receipts[i].tool_ok = Some(false);
    let bad = verify_session(&tampered, ALICE);
    assert!(!bad.ok, "a forged verdict breaks the receipt signature");

    // 7. Cap-scoping: Bob's session is isolated from Alice (and vice-versa).
    let bob_session = store
        .create(
            &GoalRequest::new("bob's PRIVATE goal", 30).with_service("run_tests"),
            BOB,
        )
        .unwrap();
    assert!(
        store.get_for_subject(&bob_session.id, ALICE).is_none(),
        "Alice cannot reach Bob's session by id"
    );
    assert!(
        store.get_for_subject(&session.id, BOB).is_none(),
        "Bob cannot reach Alice's session by id"
    );
    // Each sees only their own in "my sessions".
    let alice_list = store.list_for(ALICE);
    let bob_list = store.list_for(BOB);
    assert!(alice_list.iter().all(|s| s.owner == ALICE));
    assert!(bob_list.iter().all(|s| s.owner == BOB));
    assert!(!alice_list.iter().any(|s| s.goal().contains("PRIVATE")));

    // 8. The page renders Alice's cockpit with her real session, not Bob's.
    let html = render::render_page(ALICE, "/.dregg-auth", 50, &alice_list);
    assert!(html.contains("give your agent a goal"));
    assert!(html.contains(&session.id));
    assert!(html.contains("verify in browser"));
    assert!(
        !html.contains("PRIVATE"),
        "Bob's goal never leaks into Alice's page"
    );
}
