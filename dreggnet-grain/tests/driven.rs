//! **Driving OFFERING #2 end to end** — open a confined grain session, land real
//! cap-bounded grain turns, hit the REAL confinement wall (the executor refuses an
//! over-cap turn), re-verify the committed chain, and render the surface. Nothing is
//! mocked: `advance` drives a genuine `dregg_sdk::ToolGateway::invoke` on a real
//! `dregg_cell::Cell` grain worker; the refusal is the executor's own `calls_made`
//! caveat, and it is proven NON-VACUOUS — the identical action lands under a larger
//! grant.

use dreggnet_grain::{GrainOffering, GrainSession, TURN_ACT};
use dreggnet_offerings::{Action, DreggIdentity, Offering, Outcome, SessionConfig};

fn act() -> Action {
    Action::new("Take one confined grain action", TURN_ACT, 1, true)
}

fn renter() -> DreggIdentity {
    DreggIdentity("dga1_renter".to_string())
}

/// Land `n` in-cap grain turns; assert each is a genuine committed turn.
fn drive_landed(off: &GrainOffering, s: &mut GrainSession, n: usize) {
    for i in 0..n {
        let out = off.advance(s, act(), renter());
        match out {
            Outcome::Landed { receipt, .. } => {
                assert_ne!(
                    receipt.turn_hash, [0u8; 32],
                    "turn {i}: a genuine turn hash"
                );
            }
            Outcome::Refused(why) => panic!("turn {i} should have landed, refused: {why}"),
        }
    }
}

// ── THE HAPPY PATH + THE CONFINEMENT WALL ─────────────────────────────────────
#[test]
fn a_confined_grain_lands_turns_then_the_executor_refuses_the_over_cap_move() {
    // A grain confined to exactly 2 metered turns.
    let off = GrainOffering::new(2);
    let mut s = off
        .open(SessionConfig::with_seed(1))
        .expect("the grain admits");

    assert_eq!(s.budget(), 2);
    assert_eq!(s.calls_made(), 0, "no committed turns yet");

    // Two in-cap actions land as genuine committed kernel turns.
    drive_landed(&off, &mut s, 2);
    assert_eq!(s.calls_made(), 2, "two grain turns committed on the ledger");
    assert_eq!(s.receipts_len(), 2);
    assert!(s.is_exhausted(), "the grain has spent its whole grant");

    // THE CONFINEMENT TOOTH: a third action is a REAL executor refusal — the grain
    // cannot act beyond its granted cap. Nothing commits, no landed turn recorded.
    let out = off.advance(&mut s, act(), renter());
    match out {
        Outcome::Refused(why) => {
            assert!(!why.is_empty(), "the executor names its refusal: {why}");
        }
        Outcome::Landed { .. } => panic!("an over-cap grain turn must NOT land"),
    }
    assert_eq!(s.calls_made(), 2, "the refused move committed nothing");
    assert_eq!(
        s.receipts_len(),
        2,
        "no landed turn recorded for the refusal"
    );

    // The committed chain re-verifies against real kernel state.
    let report = off.verify(&s);
    assert!(
        report.verified,
        "the committed grain chain re-verifies: {}",
        report.detail
    );
    assert_eq!(report.turns, 2);
}

// ── NON-VACUITY: the SAME action lands under a larger grant ────────────────────
#[test]
fn the_refusal_tracks_the_cap_not_the_action() {
    // The identical action that was refused at cap 2 lands cleanly when the grain is
    // granted a larger cap — so the refusal is the executor's RATE caveat biting, not
    // a hardcoded reject of the action.
    let off = GrainOffering::new(4);
    let mut s = off
        .open(SessionConfig::with_seed(2))
        .expect("the grain admits");

    drive_landed(&off, &mut s, 4);
    assert_eq!(s.calls_made(), 4, "all four land under the larger grant");

    // The 5th is refused — the wall moved with the cap.
    assert!(
        matches!(off.advance(&mut s, act(), renter()), Outcome::Refused(_)),
        "the 5th action is refused at cap 4"
    );
    assert!(off.verify(&s).verified);
}

// ── A REFUSED MOVE IS NON-DESTRUCTIVE: verify + render still hold ──────────────
#[test]
fn a_refused_move_leaves_the_session_verifiable_and_renderable() {
    let off = GrainOffering::new(1);
    let mut s = off.open(SessionConfig::with_seed(3)).expect("admits");

    assert!(off.advance(&mut s, act(), renter()).landed(), "first lands");
    assert!(
        matches!(off.advance(&mut s, act(), renter()), Outcome::Refused(_)),
        "second refused (cap 1)"
    );

    // verify holds over exactly the one landed turn.
    let report = off.verify(&s);
    assert!(report.verified);
    assert_eq!(report.turns, 1);

    // render produces a real deos Surface naming the confinement + the (dimmed) move.
    let surface = off.render(&s);
    let rendered = format!("{:?}", surface.view());
    assert!(
        rendered.contains("Confined grain"),
        "surface titles the grain"
    );
    assert!(
        rendered.contains("calls_made caveat"),
        "surface names the real confinement mechanism"
    );
    assert!(
        rendered.contains("Verified turns"),
        "surface shows the verified-turn count"
    );

    // actions() dims the spent move (cap tooth shown, not hidden).
    let actions = off.actions(&s);
    assert_eq!(actions.len(), 1);
    assert!(
        !actions[0].enabled,
        "the spent grain action is shown dimmed"
    );
}

// ── AN UNKNOWN AFFORDANCE IS REFUSED (input validation, not the cap tooth) ─────
#[test]
fn an_unknown_affordance_is_refused() {
    let off = GrainOffering::new(3);
    let mut s = off.open(SessionConfig::with_seed(4)).expect("admits");
    let out = off.advance(
        &mut s,
        Action::new("bogus", "escape-the-jail", 1, true),
        renter(),
    );
    assert!(matches!(out, Outcome::Refused(_)), "unknown verb refused");
    assert_eq!(s.calls_made(), 0, "nothing committed");
}
