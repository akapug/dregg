//! **Branch-and-stitch multiplayer — the distributed-Houyhnhnm flagship, runnable.**
//!
//! Two participants — `ada` and `boris` — fork ONE shared verified world, diverge on their
//! own independent verified branches, and stitch back through a SINGLE gated door. Three
//! escalating beats, each a real `World` fork → real verified turns → a settlement-sound
//! stitch, printed as an arc and asserted as an integration test:
//!
//!   A. DISJOINT edits MERGE clean — conservation + authority preserved, main untouched.
//!   B. a SAME-address clash is REFUSED fail-closed — both attributed readings live.
//!   C. a `gift` cap revoked on MAIN between branch and settlement is LINEAR-DROPPED while
//!      the disjoint state still settles (the proven `settlement_soundness` gate, live).
//!
//! It drags in no cockpit / Matrix / GPU stack: it composes
//! [`starbridge_v2::branch_stitch_session::BranchStitchSession`] — the transport-free
//! primitive lifted from `ForkMembraneHost::stitch_pair` — over `embedded-executor` only.
//!
//! Run (gpui-free, no GPU):  `cargo run -p starbridge-branch-stitch-multiplayer`

use dregg_cell::{AuthRequired, CellId};
use dregg_turn::umem::UKey;

use starbridge_v2::branch_stitch_session::BranchStitchSession;
use starbridge_v2::world::{make_open_cell, revoke_capability, set_field, World};

/// The role cells of the shared world the two participants co-inhabit.
struct Cast {
    room: CellId,
    ada: CellId,
    boris: CellId,
    board: CellId,
    doc_ada: CellId,
    doc_boris: CellId,
    gift: CellId,
    offstage: CellId,
}

/// Build the shared world with ORDINARY cap-gated genesis (no GM self-grant): a `room` focus
/// reaching both principals + the shared `board`, each principal holding their own doc, the
/// room holding a `gift` cap (the conferrable authority later revoked), and an `offstage`
/// cell granted to NOBODY (the confinement foil — it must never ride the cap-bounded cull).
fn shared_world() -> (World, Cast) {
    let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
    let board = w.genesis_cell(0x5D, 0);
    let doc_ada = w.genesis_cell(0xA1, 0);
    let doc_boris = w.genesis_cell(0xB2, 0);
    let gift = w.genesis_cell(0x91, 0);
    let offstage = w.genesis_cell(0xEE, 0);

    let mut ada = make_open_cell(0x0A, 0);
    ada.capabilities.grant(board, AuthRequired::None).unwrap();
    ada.capabilities.grant(doc_ada, AuthRequired::None).unwrap();
    let ada_id = w.genesis_install(ada);

    let mut boris = make_open_cell(0x0B, 0);
    boris.capabilities.grant(board, AuthRequired::None).unwrap();
    boris
        .capabilities
        .grant(doc_boris, AuthRequired::None)
        .unwrap();
    let boris_id = w.genesis_install(boris);

    let mut room = make_open_cell(0x40, 0);
    room.capabilities.grant(ada_id, AuthRequired::None).unwrap();
    room.capabilities
        .grant(boris_id, AuthRequired::None)
        .unwrap();
    room.capabilities.grant(board, AuthRequired::None).unwrap();
    room.capabilities
        .grant(gift, AuthRequired::None)
        .expect("the room holds the gift cap at branch time");
    let room_id = w.genesis_install(room);

    (
        w,
        Cast {
            room: room_id,
            ada: ada_id,
            boris: boris_id,
            board,
            doc_ada,
            doc_boris,
            gift,
            offstage,
        },
    )
}

fn field(cell: CellId, slot: u64) -> UKey {
    UKey::Field { cell, slot }
}

/// BEAT A — DISJOINT edits merge clean (distributed reversible multiplayer).
fn beat_a() {
    println!("\n── BEAT A · disjoint edits MERGE clean ─────────────────────────────────────");
    let (world, cast) = shared_world();
    let session = BranchStitchSession::open(world, cast.room, 3);
    let _ = cast.offstage; // granted to nobody — never rides the cap-bounded cull (see the
                           // session unit test's `beat_a_disjoint_edits_merge_clean`).

    let mut ada = session.fork();
    ada.drive(ada.turn(cast.ada, vec![set_field(cast.doc_ada, 0, [0x11; 32])]))
        .expect("ada drives her own doc — a real verified turn");
    ada.drive(ada.turn(cast.ada, vec![set_field(cast.board, 0, [0xAA; 32])]))
        .expect("ada drives board.field[0]");

    let mut boris = session.fork();
    boris
        .drive(boris.turn(cast.boris, vec![set_field(cast.doc_boris, 0, [0x22; 32])]))
        .expect("boris drives his own doc");
    boris
        .drive(boris.turn(cast.boris, vec![set_field(cast.board, 1, [0xBB; 32])]))
        .expect("boris drives board.field[1]");

    let v = session.stitch(&ada, &boris);
    assert!(
        v.settles(),
        "disjoint edits settle: {:?}",
        v.state_conflicts
    );
    assert!(
        v.settled_root.is_some(),
        "a settled stitch has a binding root"
    );
    assert!(
        v.dropped_authority.is_empty(),
        "nothing authority-dropped (gift still held): {:?}",
        v.dropped_authority
    );
    for key in [
        field(cast.doc_ada, 0),
        field(cast.doc_boris, 0),
        field(cast.board, 0),
        field(cast.board, 1),
    ] {
        assert!(v.merged.contains(&key), "merged names {key:?}");
    }
    // Reversible: main stayed pristine — divergence was imaginary until applied.
    assert_eq!(
        session
            .base()
            .ledger()
            .get(&cast.board)
            .unwrap()
            .state
            .fields[0],
        [0u8; 32],
        "main untouched (reversible)"
    );
    println!(
        "   ✓ {} addresses folded clean (ada+boris both kept), main pristine, no authority dropped",
        v.merged.len()
    );
}

/// BEAT B — a SAME-address clash is REFUSED fail-closed (both readings preserved).
fn beat_b() {
    println!("\n── BEAT B · same-address clash REFUSED fail-closed ─────────────────────────");
    let (world, cast) = shared_world();
    let session = BranchStitchSession::open(world, cast.room, 3);

    let mut ada = session.fork();
    ada.drive(ada.turn(cast.ada, vec![set_field(cast.board, 0, [0x11; 32])]))
        .expect("ada writes board.field[0] = 11");
    let mut boris = session.fork();
    boris
        .drive(boris.turn(cast.boris, vec![set_field(cast.board, 0, [0x22; 32])]))
        .expect("boris writes board.field[0] = 22");

    let v = session.stitch(&ada, &boris);
    assert!(
        !v.settles(),
        "a same-address clash does NOT settle (fail-closed)"
    );
    assert!(
        v.settled_root.is_none(),
        "no settled root while the conflict is live"
    );
    assert_eq!(
        v.state_conflicts,
        vec![field(cast.board, 0)],
        "the conflict names the EXACT diverged address — both readings kept, no silent LWW"
    );
    println!(
        "   ✓ board.field[0] is a held ValueCollision (ada=11 vs boris=22), stitch withheld — no lost write"
    );
}

/// BEAT C — a `gift` cap revoked on MAIN between branch and settlement is LINEAR-DROPPED.
fn beat_c() {
    println!("\n── BEAT C · revoked-before-tip cap LINEAR-DROPPED (settlement-sound) ────────");
    let (world, cast) = shared_world();
    let mut session = BranchStitchSession::open(world, cast.room, 3);

    let mut ada = session.fork();
    ada.drive(ada.turn(cast.ada, vec![set_field(cast.board, 0, [0xAA; 32])]))
        .expect("ada drives board.field[0]");
    let mut boris = session.fork();
    boris
        .drive(boris.turn(cast.boris, vec![set_field(cast.board, 1, [0xBB; 32])]))
        .expect("boris drives board.field[1]");

    // BEFORE the revoke: gift is held at the tip → it RIDES (non-vacuity, polarity 1).
    let before = session.stitch(&ada, &boris);
    assert!(
        before
            .admitted_authority
            .iter()
            .any(|c| c.target == cast.gift),
        "before the revoke gift is admitted (held at the tip)"
    );
    assert!(
        !before
            .dropped_authority
            .iter()
            .any(|c| c.target == cast.gift),
        "before the revoke nothing is authority-dropped"
    );
    assert!(
        before.settles(),
        "the disjoint state settles before the revoke"
    );
    println!("   · before revoke: gift held at tip → admitted; disjoint state settles");

    // THE REVOCATION (non-monotone, on MAIN / the settlement tip): the room revokes its own
    // gift cap with a REAL verified turn.
    let slot = session
        .base()
        .ledger()
        .get(&cast.room)
        .unwrap()
        .capabilities
        .iter()
        .find(|c| c.target == cast.gift)
        .map(|c| c.slot)
        .expect("the room's gift cap slot");
    let revoke = session
        .base()
        .turn(cast.room, vec![revoke_capability(cast.room, slot)]);
    assert!(
        session.base_mut().commit_turn(revoke).is_committed(),
        "the room revokes gift on main with a real verified turn"
    );
    println!("   · revoked gift on MAIN — the settlement-tip authority view changed");

    // AFTER the revoke: the SAME stitch drops gift while the disjoint state still settles
    // (non-vacuity, polarity 2 — the drop IS the revocation, not a blanket refusal).
    let after = session.stitch(&ada, &boris);
    assert!(
        after
            .dropped_authority
            .iter()
            .any(|c| c.target == cast.gift),
        "after the revoke gift is LINEAR-DROPPED (revoke_before_tip_unsettleable): {:?}",
        after.dropped_authority
    );
    assert!(
        !after
            .admitted_authority
            .iter()
            .any(|c| c.target == cast.gift),
        "the revoked gift is no longer admitted"
    );
    assert!(
        after.settles() && after.settled_root.is_some(),
        "the disjoint state pushout still settles — authority drop is orthogonal (pushout-correct)"
    );
    assert!(
        after.merged.contains(&field(cast.board, 0))
            && after.merged.contains(&field(cast.board, 1)),
        "the disjoint board edits still fold clean"
    );
    assert_ne!(
        before.dropped_authority, after.dropped_authority,
        "non-vacuous BOTH ways: the drop appeared only AFTER the revoke"
    );
    println!(
        "   ✓ gift LINEAR-DROPPED after the revoke; state still settles — a cap I revoked cannot ride the stitch"
    );
}

/// Run the three-beat arc (shared by `main` and the integration test).
fn run_arc() {
    println!("\n=== BRANCH-AND-STITCH MULTIPLAYER — the distributed-Houyhnhnm flagship ===");
    println!(
        "two participants fork one shared verified world, diverge, and stitch under a proven gate"
    );
    beat_a();
    beat_b();
    beat_c();
    println!(
        "\n=== distributed · reversible · capability-secure · witnessed multiplayer — REAL ===\n"
    );
}

fn main() {
    run_arc();
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole arc, as an acceptance test: Beat A merges, Beat B refuses fail-closed, Beat C
    /// drops the revoked-before-tip cap (non-vacuous both ways). Each beat asserts internally.
    #[test]
    fn three_beat_branch_and_stitch_multiplayer() {
        run_arc();
    }

    #[test]
    fn beat_a_merges_clean() {
        beat_a();
    }

    #[test]
    fn beat_b_refuses_conflict() {
        beat_b();
    }

    #[test]
    fn beat_c_drops_revoked_authority() {
        beat_c();
    }
}
