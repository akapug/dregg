//! THE DESCENT — the OPT-IN SETTLE, driven end to end.
//!
//! "Private fast play, opt-in verifiable settlement": a run PLAYS entirely LOCALLY (the
//! in-process executor — private + fast, no node submit), and when a player finishes a run
//! worth keeping they SETTLE it — anchoring the run's 32-byte commitment on the deployed node
//! chain via the EXISTING Federation seam (`NodeTarget::Federation` → `EmitEvent`-of-commitment).
//!
//! Driven here against a `StubNode` (the seam's in-memory node double, no live server):
//!   * a WON run plays locally (the node stays EMPTY through play) then SETTLES (the run's real
//!     final `turn_hash` lands on the node's finalized log);
//!   * an UNFINISHED run and a LOST run do NOT settle (refused, node untouched) — non-vacuous;
//!   * a rejecting node fails the settle fail-closed;
//!   * the DEFAULT (Local) offering settles privately in-process (nothing leaves the process).
//!
//! HONEST SCOPE: what's real here is the WIRING — a won run's commitment is submitted through the
//! Federation seam + confirmed landed on the (stub) node. The DEPLOY is a live node running so the
//! anchor is actually explorer-visible + archived (the seam submits to a `NodeTarget`; the live
//! devnet is that node). Federation anchors the 32-byte COMMITMENT — a fingerprint receipt in the
//! explorer — NOT the dungeon's HP/gold state (that is the chain-native lift). This is the bridge
//! to the ZK-leaderboard: settle a commitment now → settle a fold-PROOF later.

use dregg_node_target::{FederationSink, NodeTarget, StubNode};
use dreggnet_offerings::DreggIdentity;
use dreggnet_offerings::character::{CharacterStore, InMemoryCharacterStore};
use dreggnet_offerings::daily_descent::{
    CORRIDOR_ON, DailyDescentOffering, DailyRun, GATE_FALL, GATE_HEAL, GATE_MEASURED, GATE_PRESS,
    GATE_RECKLESS, HOARD_FORCE, HOARD_SEIZE, KEY_TAKE, SettleError,
};
use procgen_dregg::beacon::DailyBeacon;

// A REAL, PUBLISHED drand `quicknet` round (round 1_000_000) — here it is "today's beacon".
const DRAND_QUICKNET_ROUND: u64 = 1_000_000;
const DRAND_QUICKNET_SIG_HEX: &str = "83ad29e4c409f9470fc2ef02f90214df49e02b441a1a241a82d622d9f608ef98fd8b11a029f1bee9d9e83b45088abe72";

fn todays_beacon() -> DailyBeacon {
    DailyBeacon::quicknet(
        DRAND_QUICKNET_ROUND,
        hex::decode(DRAND_QUICKNET_SIG_HEX).expect("the drand signature decodes"),
    )
}

fn player(name: &str) -> DreggIdentity {
    DreggIdentity(name.to_string())
}

/// Drive a CAREFUL winning line to the hoard (heals once if the beacon drew a tough warden).
fn drive_win<S: CharacterStore>(off: &DailyDescentOffering<S>, run: &mut DailyRun) {
    for _ in 0..64 {
        let Some(room) = run.current_room() else {
            break;
        };
        let ci = match room.as_str() {
            "gate" => {
                if run.read_var("warden_hp") == 0 {
                    GATE_PRESS
                } else if run.read_var("hp") >= 16 {
                    GATE_MEASURED
                } else {
                    GATE_HEAL
                }
            }
            "keyroom" => KEY_TAKE,
            "hoardgate" => HOARD_FORCE,
            "hoard" => HOARD_SEIZE,
            r if r.starts_with("corridor") => CORRIDOR_ON,
            other => panic!("unexpected room in a winning line: {other}"),
        };
        assert!(
            off.advance(run, ci).landed(),
            "a careful move was refused in {room}"
        );
    }
}

/// Drive a LOSING line: a reckless opener burns HP to the fall threshold, then fall into defeat.
fn drive_loss<S: CharacterStore>(off: &DailyDescentOffering<S>, run: &mut DailyRun) {
    assert!(off.advance(run, GATE_RECKLESS).landed(), "reckless opener");
    assert!(run.read_var("hp") <= 20, "at the brink");
    assert!(off.advance(run, GATE_FALL).landed(), "the fall commits");
    assert_eq!(run.current_room().as_deref(), Some("downed"));
    assert!(off.advance(run, 0).landed(), "the defeat passage ends");
}

/// THE HARD GATE: a won run PLAYS LOCALLY (the node is EMPTY through play — private/fast, no
/// submit) and then SETTLES — the run's real final `turn_hash` lands on the node's finalized log.
#[test]
fn a_won_run_plays_locally_then_settles_its_commitment_to_the_node() {
    let node = StubNode::new();
    // Opt this offering into settlement on the (stub) federation node.
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new())
        .with_node_target(NodeTarget::federation(node.clone()));
    assert!(
        off.settles_to_a_node(),
        "a Federation settle target is opted in"
    );

    let mut run = off
        .open(player("winner-settles"), &todays_beacon())
        .expect("open today");

    // PLAY — entirely local. Not one play turn touches the node.
    drive_win(&off, &mut run);
    assert!(run.is_won(), "the careful line reached the hoard — a win");
    assert_eq!(run.read_var("gold"), 500, "the hoard is seized");
    assert_eq!(
        node.len(),
        0,
        "PLAY IS PRIVATE + LOCAL: no play turn submitted to the node"
    );

    // SETTLE — the opt-in anchor. The run's final commitment lands on the node.
    let settlement = off.settle(&run).expect("a verified won run settles");
    assert!(
        settlement.anchored(),
        "the commitment was anchored on the node"
    );
    assert_eq!(
        settlement.commitment,
        run.final_commitment(),
        "the anchored fingerprint IS the run's final committed turn_hash"
    );
    assert!(
        node.contains(&run.final_commitment()),
        "the run's fingerprint is on the node's finalized log (explorer-visible)"
    );
    assert_eq!(
        node.len(),
        1,
        "exactly one anchor — the settle, not the play"
    );
    node.verify().expect("the node's finalized log verifies");
}

/// NON-VACUOUS refusal: an UNFINISHED run does NOT settle (only a real finished win does). The
/// node is untouched.
#[test]
fn an_unfinished_run_does_not_settle() {
    let node = StubNode::new();
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new())
        .with_node_target(NodeTarget::federation(node.clone()));

    let mut run = off
        .open(player("quitter"), &todays_beacon())
        .expect("open today");
    // Play a couple of real local turns but do NOT finish the run.
    assert!(off.advance(&mut run, GATE_MEASURED).landed());
    assert!(off.advance(&mut run, GATE_MEASURED).landed());
    assert!(!run.is_won(), "the run is not finished");

    let refused = off.settle(&run);
    assert!(
        matches!(refused, Err(SettleError::NotWon)),
        "an unfinished run does not settle, got {refused:?}"
    );
    assert_eq!(node.len(), 0, "nothing anchored — the node is untouched");
}

/// NON-VACUOUS refusal: a genuinely LOST run (fell into the defeat room) does NOT settle — it
/// never reached the win. The node is untouched.
#[test]
fn a_lost_run_does_not_settle() {
    let node = StubNode::new();
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new())
        .with_node_target(NodeTarget::federation(node.clone()));

    let mut run = off
        .open(player("loser"), &todays_beacon())
        .expect("open today");
    drive_loss(&off, &mut run);
    assert!(run.is_ended() && !run.is_won(), "a lost, finished run");

    let refused = off.settle(&run);
    assert!(
        matches!(refused, Err(SettleError::NotWon)),
        "a lost run does not settle, got {refused:?}"
    );
    assert_eq!(node.len(), 0, "nothing anchored — the node is untouched");
}

/// FAIL-CLOSED: a node that refuses the anchor fails the settle — the run is a real win, but the
/// settle reports the commitment did not replicate (`SettleError::Federation`).
#[test]
fn a_rejecting_node_fails_the_settle_fail_closed() {
    let node = StubNode::rejecting();
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new())
        .with_node_target(NodeTarget::federation(node.clone()));

    let mut run = off
        .open(player("winner-vs-hostile-node"), &todays_beacon())
        .expect("open today");
    drive_win(&off, &mut run);
    assert!(run.is_won(), "a real win");

    let refused = off.settle(&run);
    assert!(
        matches!(refused, Err(SettleError::Federation(_))),
        "a rejecting node fails the settle fail-closed, got {refused:?}"
    );
    assert_eq!(node.len(), 0, "nothing landed — fail-closed");
}

/// A player's kept runs form a LINKED SETTLEMENT CHAIN on a chain-enforcing node: two won runs
/// (of two different days) settle in order, the second linking onto the first's commitment, and
/// the node's finalized log is exactly that chain. A chain-enforcing node REFUSES an anchor whose
/// `prev` does not extend the head (fail-closed) — non-vacuous.
#[test]
fn kept_runs_form_a_linked_settlement_chain_on_a_chain_enforcing_node() {
    let node = StubNode::linked();
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new())
        .with_node_target(NodeTarget::federation(node.clone()));

    // Two DIFFERENT days (distinct beacon epochs → distinct worlds → distinct commitments).
    let seed_a = procgen_dregg::daily_seed(&[1u8; 32]);
    let seed_b = procgen_dregg::daily_seed(&[2u8; 32]);

    let mut run_a = off
        .open_from_seed(player("chainer"), seed_a)
        .expect("open day A");
    drive_win(&off, &mut run_a);
    assert!(run_a.is_won());

    let mut run_b = off
        .open_from_seed(player("chainer"), seed_b)
        .expect("open day B");
    drive_win(&off, &mut run_b);
    assert!(run_b.is_won());
    assert_ne!(
        run_a.final_commitment(),
        run_b.final_commitment(),
        "two different days settle two distinct commitments"
    );

    // The first anchor opens the chain (prev = None); the second LINKS onto it.
    let s_a = off
        .settle_linked(&run_a, None)
        .expect("the first run opens the settlement chain");
    let s_b = off
        .settle_linked(&run_b, Some(s_a.commitment))
        .expect("the second run links onto the first");

    assert!(
        s_a.anchored() && s_b.anchored(),
        "both anchored on the node"
    );
    assert_eq!(
        node.chain(),
        vec![s_a.commitment, s_b.commitment],
        "the node's finalized log IS the player's linked settlement chain"
    );
    node.verify().expect("the finalized chain verifies");

    // FAIL-CLOSED: a fresh won run that tries to anchor with the WRONG prev (not the head) is
    // refused by the chain-enforcing node — the chain cannot be forked or spliced.
    let mut run_c = off
        .open_from_seed(player("chainer"), procgen_dregg::daily_seed(&[3u8; 32]))
        .expect("open day C");
    drive_win(&off, &mut run_c);
    let forked = off.settle_linked(&run_c, Some([0xAB; 32]));
    assert!(
        matches!(forked, Err(SettleError::Federation(_))),
        "a broken prev-link is refused fail-closed, got {forked:?}"
    );
    assert_eq!(
        node.len(),
        2,
        "the forked anchor landed nothing — the chain is still just A→B"
    );
}

/// The DEFAULT offering (Local, no node opted in): PLAY is private, and SETTLE succeeds as an
/// in-process no-op — nothing leaves the process (`Settlement::anchored` is false).
#[test]
fn the_default_offering_settles_privately_in_process() {
    let off = DailyDescentOffering::new(InMemoryCharacterStore::new());
    assert!(
        !off.settles_to_a_node(),
        "the default offering is Local — private, no node"
    );

    let mut run = off
        .open(player("private-player"), &todays_beacon())
        .expect("open today");
    drive_win(&off, &mut run);
    assert!(run.is_won());

    let settlement = off
        .settle(&run)
        .expect("a Local settle is an in-process no-op");
    assert!(
        !settlement.anchored(),
        "nothing was anchored off-process — the run stays private"
    );
    assert_eq!(
        settlement.commitment,
        run.final_commitment(),
        "the settlement still names the run's fingerprint"
    );
}
