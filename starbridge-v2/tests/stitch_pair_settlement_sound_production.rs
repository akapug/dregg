//! SETTLEMENT-SOUND IN THE PRODUCTION MEMBRANE — the authority gate fires through the live
//! `ForkMembraneHost::stitch_pair`, not just the standalone demo.
//!
//! The companion `branch_stitch_settlement_sound_multiplayer.rs` exercises the settlement gate
//! ([`settle_umem_stitch`]) directly. This test proves the SAME gate is wired into the
//! PRODUCTION membrane path the chat / multiplayer lane actually calls — `stitch_pair` on a
//! running `ForkMembraneHost` — so a real fork → drive → stitch through the live host is
//! settlement-sound:
//!
//!   * the focus holds a `gift` cap at branch time; both driven forks would confer it back;
//!   * BETWEEN branch and settlement the focus REVOKES that cap on MAIN (the live source world,
//!     the settlement tip) with a real verified `RevokeCapability` turn;
//!   * `stitch_pair` reads authority AT THE TIP: the revoked-before-tip `gift` confer is
//!     LINEAR-DROPPED — surfaced as a first-class `ConflictReason::AuthorityRevoked` object —
//!     while the still-held `board` confer rides. The state pushout (disjoint field edits)
//!     folds clean and settles, ORTHOGONAL to the authority drop.
//!
//! It is non-vacuous BOTH ways: a `stitch_pair` BEFORE the revoke drops nothing (gift rides),
//! and the SAME call AFTER the revoke drops gift — so the drop is the revocation, not a blanket
//! refusal (`Dregg2.Circuit.SettlementSoundness.settledRevView`, live in production).
//!
//! Run (gpui-free, no GPU):
//!   cd starbridge-v2 && cargo test --no-default-features \
//!     --features "embedded-executor dev-surfaces" \
//!     --test stitch_pair_settlement_sound_production -- --nocapture

#![cfg(all(feature = "dev-surfaces", feature = "embedded-executor"))]

use deos_matrix::membrane::{ConflictReason, FrustumCut, MembraneHost};
use dregg_cell::{AuthRequired, CellId};

use starbridge_v2::shared_fork::{ForkMembraneHost, MembraneFrustum};
use starbridge_v2::umem_membrane::dropped_cap_event_id;
use starbridge_v2::world::{make_open_cell, revoke_capability, set_field, World};

/// A world whose `focus` principal holds the shared `board` (the disjoint-edit surface) and a
/// `gift` cap (the conferrable authority later REVOKED on main). Returns `(world, focus, board,
/// gift)`.
fn focus_world() -> (World, CellId, CellId, CellId) {
    let mut w = World::new().with_executor_signing_key([0x42u8; 32]);
    let board = w.genesis_cell(0x5D, 0);
    let gift = w.genesis_cell(0x91, 0);
    let mut focus = make_open_cell(0x40, 0);
    focus
        .capabilities
        .grant(board, AuthRequired::None)
        .expect("focus holds the board");
    focus
        .capabilities
        .grant(gift, AuthRequired::None)
        .expect("focus holds the gift cap at branch time");
    let focus = w.genesis_install(focus);
    (w, focus, board, gift)
}

#[test]
fn stitch_pair_drops_revoked_before_tip_authority_in_production() {
    let (world, focus, board, gift) = focus_world();
    eprintln!(
        "\n=== PRODUCTION stitch_pair settlement-sound: a revoked-before-tip cap LINEAR-DROPS ==="
    );

    // ── THE MEMBRANE: mint the cap-bounded cull around the focus (captures board + gift). ──
    let owner_fork = world.fork();
    let mut host = ForkMembraneHost::new(owner_fork, focus);
    let cut = FrustumCut {
        focus_cell: [0u8; 32],
        max_depth: 3,
        authority_bounded: true,
        cell_count: 0,
    };
    let env = host
        .mint(focus.0, cut)
        .expect("the owner mints the membrane");
    let frustum = MembraneFrustum::from_snapshot_bytes(&env.snapshot).expect("snapshot decodes");

    // ── REHYDRATE two driven forks of the SAME branch (the multiplayer pair). ─────────────
    let (h_a, _) = host.rehydrate(&env).expect("fork a rehydrates");
    let (h_b, _) = host.rehydrate(&env).expect("fork b rehydrates");

    // Author against a fresh rehydrate (identical chain head), drive through the host executor.
    let author = |ops: Vec<dregg_turn::action::Effect>| {
        let driver = frustum
            .rehydrate(env.frustum_root)
            .expect("driver rehydrates");
        postcard::to_stdvec(&driver.turn(focus, ops)).expect("turn serializes")
    };
    // DISJOINT field edits → the STATE pushout folds clean (orthogonal to the authority gate).
    host.drive(&h_a, &author(vec![set_field(board, 0, [0xAA; 32])]))
        .expect("fork a drives board.field[0]");
    host.drive(&h_b, &author(vec![set_field(board, 1, [0xBB; 32])]))
        .expect("fork b drives board.field[1]");

    let gift_event = dropped_cap_event_id(&gift);

    // ── BEFORE THE REVOKE: gift is held at the tip → it RIDES (no authority drop). ────────
    let before = host.stitch_pair(&h_a, &h_b).expect("stitch before revoke");
    assert!(
        !before
            .dropped
            .iter()
            .any(|d| d.reason == ConflictReason::AuthorityRevoked),
        "before the revoke nothing is authority-dropped (gift is held at the tip): {:?}",
        before.dropped
    );
    assert!(
        before.settled_root.is_some(),
        "the disjoint state pushout settles (clean) before the revoke"
    );
    eprintln!("  · before revoke: gift held at tip → no authority drop; state settles ✓");

    // ── THE REVOCATION (non-monotone, on MAIN / the settlement tip). ─────────────────────
    let revoke_turn = {
        let w = host.source_world();
        let slot = w
            .ledger()
            .get(&focus)
            .unwrap()
            .capabilities
            .iter()
            .find(|c| c.target == gift)
            .map(|c| c.slot)
            .expect("focus's gift cap slot");
        w.turn(focus, vec![revoke_capability(focus, slot)])
    };
    assert!(
        host.source_world_mut()
            .commit_turn(revoke_turn)
            .is_committed(),
        "the focus revokes its own gift cap on the live source (the settlement tip)"
    );
    eprintln!("  · revoked gift on MAIN — the settlement-tip authority view changed");

    // ── AFTER THE REVOKE: the SAME stitch_pair drops gift (settlement-sound, in production). ─
    let after = host.stitch_pair(&h_a, &h_b).expect("stitch after revoke");
    let auth_drops: Vec<_> = after
        .dropped
        .iter()
        .filter(|d| d.reason == ConflictReason::AuthorityRevoked)
        .collect();
    assert_eq!(
        auth_drops.len(),
        1,
        "exactly one authority drop after the revoke: {:?}",
        after.dropped
    );
    assert_eq!(
        auth_drops[0].event, gift_event,
        "the linear DROP names the EXACT revoked cap (gift)"
    );
    // The state pushout is UNTOUCHED by the gate — disjoint edits still settle.
    assert!(
        after.settled_root.is_some(),
        "the state pushout still settles — authority drops are orthogonal (pushout-correct)"
    );
    assert!(
        !after.merged.is_empty(),
        "the disjoint board edits still fold clean into the merged set"
    );
    eprintln!(
        "  · after revoke: gift LINEAR-DROPPED (AuthorityRevoked) in the PRODUCTION stitch_pair; \
         state still settles ✓"
    );
    eprintln!(
        "=== settlement-soundness authority gate LIVE in the production membrane (stitch_pair) ===\n"
    );
}
