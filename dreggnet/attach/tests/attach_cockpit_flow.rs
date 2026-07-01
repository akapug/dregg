//! End-to-end for the **upgraded cockpit superpowers**: drive a session, then
//! exercise the two flagship cockpit actions a judge sees — (1) the **verify +
//! tamper self-demo** (the genuine chain re-witnesses ✓, the same chain with one
//! flipped line shatters ✗), and (2) **fork & attenuate** (a child with strictly
//! less authority, owned by the same subject, independently re-witnessable, and
//! cap-scoped so you can only fork your own). All over the shipped demo driver.

use dreggnet_attach::render;
use dreggnet_attach::session::GoalRequest;
use dreggnet_attach::store::SessionStore;
use dreggnet_attach::transcript::transcript_of;
use dreggnet_attach::verify::{tamper_demo, verify_session};

const ALICE: &str = "dregg:aaaa0000aaaa0000";
const BOB: &str = "dregg:bbbb1111bbbb1111";

fn goal() -> GoalRequest {
    GoalRequest::new("run the tests, verify the deploy, check health", 60)
        .with_service("run_tests")
        .with_service("verify_deploy")
        .with_service("check_health")
        .with_cell("/goal")
}

#[test]
fn verify_then_tamper_self_demo_is_visceral_and_honest() {
    let store = SessionStore::new();
    let s = store.create(&goal(), ALICE).unwrap();

    // The genuine chain re-witnesses (✓ — the agent stayed in its box).
    let held = verify_session(&s, ALICE);
    assert!(held.ok, "{}", held.detail);
    assert!(!held.tamper_demo);
    assert_eq!(held.consumed + held.headroom, held.budget);

    // The tamper self-demo, on the SAME session, shatters (✗) and names the flip.
    let shattered = tamper_demo(&s);
    assert!(shattered.tamper_demo);
    assert!(!shattered.ok, "flipping one sealed line breaks the proof");
    assert!(shattered.tampered_what.is_some());
    assert!(shattered.detail.contains("did NOT re-witness"));

    // The demo is non-destructive: the stored session still re-witnesses.
    let again = verify_session(&store.get_for_subject(&s.id, ALICE).unwrap(), ALICE);
    assert!(again.ok, "the tamper demo worked on a private clone");
}

#[test]
fn fork_is_a_real_attenuated_re_witnessable_child() {
    let store = SessionStore::new();
    let parent = store.create(&goal(), ALICE).unwrap();

    let child = store
        .fork_for(&parent.id, ALICE)
        .expect("alice forks her own");
    // Owned by the same subject, linked to the parent, attenuated ceiling.
    assert_eq!(child.owner, ALICE);
    assert_eq!(child.parent.as_deref(), Some(parent.id.as_str()));
    assert!(
        child.budget() < parent.budget(),
        "the fork can do strictly less"
    );
    // The child is a genuine session with its own re-witnessable chain + transcript.
    assert!(verify_session(&child, ALICE).ok, "the fork re-witnesses");
    assert!(
        !transcript_of(&child).is_empty(),
        "the fork produced a transcript"
    );

    // The fork badge renders in Alice's "my sessions".
    let html = render::render_page(ALICE, "/.dregg-auth", 60, &store.list_for(ALICE));
    assert!(html.contains(&child.id));
    assert!(html.contains("⑂ fork"));
}

#[test]
fn you_can_only_fork_your_own_session() {
    let store = SessionStore::new();
    let alice = store.create(&goal(), ALICE).unwrap();
    // Bob cannot fork Alice's session (cap-scoped; no existence oracle).
    assert!(store.fork_for(&alice.id, BOB).is_none());
    // Bob's "my sessions" never gains a child of Alice's.
    assert!(store.list_for(BOB).is_empty());
}

#[test]
fn the_live_transcript_tells_the_reason_act_observe_story() {
    let store = SessionStore::new();
    let s = store.create(&goal(), ALICE).unwrap();
    let steps = transcript_of(&s);

    // Every admitted step carries a typed family + a signed, linked receipt — the
    // signed chain the cockpit shows accumulating line by line.
    let admitted: Vec<_> = steps.iter().filter(|s| s.admitted).collect();
    assert!(admitted.len() >= 3, "the granted services each ran");
    assert!(
        admitted
            .iter()
            .all(|s| s.receipt_seq.is_some() && s.sig_fp.is_some())
    );
    assert_eq!(admitted[0].prev_fp.as_deref(), Some("genesis"));
    // The cap-gate ✗ is visible in-band (the out-of-bundle probe).
    assert!(steps.iter().any(|s| !s.admitted && s.cost == 0));
}
