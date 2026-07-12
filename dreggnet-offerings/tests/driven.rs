//! **The driven end-to-end proof** — the Offering/Frontend model, DRIVEN over the REAL
//! dungeon-on-dregg substrate, with NO Discord anywhere:
//!
//! - open a [`DungeonOffering`] session, list its cap-gated affordances ([`Offering::actions`]);
//! - advance a winning line — each move a real [`TurnReceipt`] ([`Outcome::Landed`]);
//! - an illegal move is a real executor refusal ([`Outcome::Refused`]) that commits nothing
//!   (the anti-ghost tooth);
//! - [`Offering::verify`] re-verifies the whole chain by replay;
//! - [`Offering::render`] produces a deos affordance [`Surface`] (a `ViewNode`);
//! - a [`MockFrontend`] presents the surface + collects an [`Action`] round-trip, which the
//!   core then resolves on the substrate as one real turn.

use dreggnet_offerings::dungeon::{DungeonOffering, KEEP_NAME, TURN_CHOOSE};
use dreggnet_offerings::mock::{MockEvent, MockFrontend};
use dreggnet_offerings::{
    Action, DreggIdentity, Frontend, Offering, Outcome, RunCost, SessionConfig, SessionId,
};
use dungeon_on_dregg::{KP_CLAIM_RED, KP_PRESS_ON, KP_TRADE_BLOWS};

/// Open a session, list its actions: the gatehall offers >1 candidate move, the ungated
/// press-on is enabled, and its price is the free tier by default (paid tier prices the narrator).
#[test]
fn open_lists_cap_gated_affordances_and_prices() {
    let off = DungeonOffering::new();
    let s = off
        .open(SessionConfig::with_seed(3))
        .expect("the Keep opens");
    let acts = off.actions(&s);
    assert!(acts.len() >= 2, "the gatehall offers >1 candidate move");

    let press = acts
        .iter()
        .find(|a| a.arg == KP_PRESS_ON as i64)
        .expect("the ungated press-on affordance is present");
    assert_eq!(press.turn, TURN_CHOOSE);
    assert!(press.enabled, "an ungated affordance is enabled");

    assert_eq!(
        off.price(press),
        RunCost::free(),
        "default is the free tier"
    );
    assert_eq!(
        DungeonOffering::paid(1).price(press),
        RunCost::credits(1),
        "the paid tier prices the confined narrator"
    );
}

/// Advance a winning line — press on into the hall, claim the crown for the Red Hand — each a
/// real landed [`TurnReceipt`]; the receipt count grows; the actor is attributed; the whole
/// chain re-verifies by replay.
#[test]
fn advance_a_winning_line_each_a_real_turnreceipt() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(9)).expect("open");
    assert_eq!(s.current_passage_name().as_deref(), Some("gatehall"));
    assert_eq!(s.receipts_len(), 1, "genesis is the first verified turn");

    let actor = DreggIdentity("party".to_string());

    match off.advance(
        &mut s,
        Action::new("press on", TURN_CHOOSE, KP_PRESS_ON as i64, true),
        actor.clone(),
    ) {
        Outcome::Landed { receipt, ended } => {
            assert!(!ended, "pressing on does not end the Keep");
            assert_ne!(receipt.turn_hash, [0u8; 32], "a genuine committed turn");
        }
        other => panic!("a legal move must land a real receipt, got {other:?}"),
    }
    assert_eq!(s.receipts_len(), 2, "a real verified turn landed");
    assert_eq!(
        s.current_passage_name().as_deref(),
        Some("hall"),
        "the world advanced to the plundered hall"
    );

    assert!(
        off.advance(
            &mut s,
            Action::new("claim red", TURN_CHOOSE, KP_CLAIM_RED as i64, true),
            actor.clone(),
        )
        .landed(),
        "claiming the crown lands"
    );
    assert_eq!(s.receipts_len(), 3);
    assert_eq!(s.actor_of_step(0), Some(&actor), "the mover is attributed");

    let report = off.verify(&s);
    assert!(
        report.verified,
        "the honest line re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 3);
}

/// An illegal move (a killing blow past the HP floor) is a real executor refusal: the affordance
/// is shown as a dimmed cap-tooth (`!enabled`), but the executor is the sole referee — firing it
/// commits nothing, lands no receipt, moves the world not at all (the anti-ghost tooth). The
/// honest prefix still re-verifies.
#[test]
fn an_illegal_move_is_refused_no_receipt_anti_ghost() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(8)).expect("open");
    let actor = DreggIdentity("party".to_string());

    // Two survivable trade-blows (hp 50 → 30 → 10), each a real committed turn.
    for _ in 0..2 {
        assert!(
            off.advance(
                &mut s,
                Action::new("trade blows", TURN_CHOOSE, KP_TRADE_BLOWS as i64, true),
                actor.clone(),
            )
            .landed(),
            "a survivable blow lands"
        );
    }
    assert_eq!(s.read_var("hp"), 10, "two blows dropped hp to 10");
    let before = s.receipts_len();

    // At hp 10 the trade-blows affordance is now a dimmed cap-tooth (its `{ hp >= 21 }` fails).
    let acts = off.actions(&s);
    let blow = acts
        .iter()
        .find(|a| a.arg == KP_TRADE_BLOWS as i64)
        .expect("the trade-blows affordance is still offered");
    assert!(
        !blow.enabled,
        "the killing blow is a dimmed cap-tooth affordance (condition eval)"
    );

    // Fire it anyway — the REAL executor refuses (FieldGte on the post-state).
    match off.advance(&mut s, blow.clone(), actor.clone()) {
        Outcome::Refused(_) => {}
        other => panic!("a killing blow must be a real executor refusal, got {other:?}"),
    }
    assert_eq!(
        s.receipts_len(),
        before,
        "no receipt landed for the refused move"
    );
    assert_eq!(s.read_var("hp"), 10, "hp unchanged after the refusal");
    assert_eq!(
        s.current_passage_name().as_deref(),
        Some("gatehall"),
        "still in the gatehall — the world did not move"
    );
    assert!(
        off.verify(&s).verified,
        "the honest prefix re-verifies after the refusal"
    );
}

/// `render` produces a deos affordance [`Surface`] (a `ViewNode`); a [`MockFrontend`] presents
/// it + the actions, collects a press back into the typed [`Action`] + the actor identity, and
/// the core resolves that action on the substrate as one real turn. The full frontend-agnostic
/// lifecycle: spin → present → collect → advance → re-present → teardown.
#[test]
fn render_is_a_deos_surface_and_a_frontend_round_trips_an_action() {
    let off = DungeonOffering::new();
    let mut s = off.open(SessionConfig::with_seed(3)).expect("open");

    // render → a deos ViewNode Section titled with the Keep + the room.
    let surface = off.render(&s);
    match surface.view() {
        deos_view::ViewNode::Section { title, .. } => {
            assert!(
                title.starts_with(KEEP_NAME),
                "the surface names the Keep + room"
            );
        }
        other => panic!("a rendered surface must be a deos Section, got {other:?}"),
    }

    let mut fe = MockFrontend::new();
    let sid = SessionId::new("chan:1");
    fe.spin_session(sid.clone());
    fe.present(&sid, &surface, &off.actions(&s));
    assert!(
        !fe.presented_actions(&sid).is_empty(),
        "the frontend presents the cap-gated affordances"
    );

    // A frontend collects a press → the typed Action + the firing actor's identity.
    let ev = MockEvent::press(&sid, "alice", TURN_CHOOSE, KP_PRESS_ON as i64);
    let (got_sid, action, actor) = fe
        .collect(ev)
        .expect("a press maps back to a presented affordance");
    assert_eq!(got_sid, sid);
    assert_eq!(action.arg, KP_PRESS_ON as i64);
    assert_eq!(
        actor,
        fe.identity("alice".to_string()),
        "the same user derives the same dregg identity"
    );

    // The CORE resolves the collected action on the substrate — one real turn.
    assert!(
        off.advance(&mut s, action, actor).landed(),
        "the collected action lands a real turn"
    );
    assert_eq!(s.current_passage_name().as_deref(), Some("hall"));

    // Re-render + re-present (the lifecycle), then teardown archives the surface.
    fe.present(&sid, &off.render(&s), &off.actions(&s));
    fe.teardown(&sid);
    assert!(!fe.is_open(&sid), "teardown archives the session surface");
}

/// A frontend refuses to collect an affordance it never presented (an event the surface did not
/// offer), and identity derivation is deterministic + distinct per user.
#[test]
fn a_frontend_refuses_an_unpresented_affordance_and_identity_is_deterministic() {
    let mut fe = MockFrontend::new();
    let sid = SessionId::new("s");
    fe.spin_session(sid.clone());

    // Nothing with real actions presented yet (spin only) → a press collects None.
    let ev = MockEvent::press(&sid, "bob", TURN_CHOOSE, 0);
    assert!(
        fe.collect(ev).is_none(),
        "an unpresented affordance is not collected"
    );

    assert_eq!(
        fe.identity("bob".to_string()),
        fe.identity("bob".to_string())
    );
    assert_ne!(
        fe.identity("bob".to_string()),
        fe.identity("carol".to_string())
    );
}
