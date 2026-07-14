//! THE SEASON ABSTRACTION, DRIVEN end-to-end (not named).
//!
//! A season RUNS its epoch + a season-scoped no-cheat leaderboard of verified wins;
//! a TAIL-APPEND upgrade CONTINUES the season (same id, board persists, epoch tag
//! bumped); a GEOMETRY-WIDEN upgrade ENDS it into a NEW season (new id/epoch) whose
//! hall-of-fame is carried forward (verifiable via the snapshot) while the active
//! board is reset; a prestige badge carries per-identity across the boundary; and a
//! forged carry-forward / forged hall-of-fame entry is REFUSED (riding
//! genesis-snapshot's tamper-refusal), while the no-cheat board refuses a forged win
//! so it never becomes a champion.

use dregg_epoch::{EpochCompat, EpochManifest, check_compatibility, local_manifest};
use dregg_genesis_snapshot::{EntryReject, ImportError, seed_genesis};
use dregg_season::{
    CarryForwardPolicy, DriftClass, Season, SeasonTransition, advance_season, epoch_delta_class,
    identity_of,
};
use dungeon_on_dregg::{
    CH_CLAIM, CH_DESCEND, CH_LEAVE_LANTERN, CH_RETREAT, CH_TAKE_LANTERN, DUNGEON,
};
use ugc_dregg::{
    Completion, Registry, RejectReason, Universe, UniverseId, WinCondition, record_playthrough,
};

// ── Epoch deltas: a tail-append keeps registry_fp; a geometry-widen moves it. ──

fn base_epoch() -> EpochManifest {
    local_manifest()
}

/// A tail-append successor: registry_fp UNCHANGED (existing VKs byte-identical), the
/// tag bumps + a staged new caveat tag rides in the tail. A non-breaking upgrade.
fn tail_append_epoch() -> EpochManifest {
    let mut e = base_epoch();
    e.descriptor_set_tag = format!("{}+tail1", e.descriptor_set_tag);
    e.known_caveat_tags.insert(22);
    e
}

/// A geometry-widen successor: registry_fp MOVES → a new VK-epoch → a re-genesis.
fn geometry_widen_epoch() -> EpochManifest {
    let mut e = base_epoch();
    e.registry_fp = "cafebabe".repeat(8);
    e.descriptor_set_tag = "v14-geom/w204/r24".to_string();
    e
}

// ── The season's world + winning paths of varied lengths (varied turns). ──

fn salt_shore() -> Universe {
    Universe::authored(
        "The Salt Shore Descent",
        "attested-dm-salvage",
        DUNGEON,
        WinCondition::ended_with(&[("gold", 500)]),
    )
    .expect("the salt-shore dungeon is a valid, deployable universe")
}

/// Fast win: take lantern, descend, claim — 3 turns.
const WIN_FAST: [usize; 3] = [CH_TAKE_LANTERN, CH_DESCEND, CH_CLAIM];
/// A detour win — retreat once — 5 turns.
const WIN_MID: [usize; 5] = [
    CH_TAKE_LANTERN,
    CH_RETREAT,
    CH_TAKE_LANTERN,
    CH_DESCEND,
    CH_CLAIM,
];
/// A longer detour win — retreat twice — 7 turns.
const WIN_SLOW: [usize; 7] = [
    CH_TAKE_LANTERN,
    CH_RETREAT,
    CH_TAKE_LANTERN,
    CH_RETREAT,
    CH_TAKE_LANTERN,
    CH_DESCEND,
    CH_CLAIM,
];

/// Submit a real, verified win for `player` onto the season board.
fn win(board: &mut Registry, u: &Universe, id: UniverseId, player: &str, moves: &[usize]) {
    let play = record_playthrough(u, moves).expect("the honest win drives cleanly");
    board
        .submit(Completion {
            universe: id,
            player: player.into(),
            play,
            claimed_turns: moves.len(),
        })
        .expect("a real, complete win is accepted by the no-cheat board");
}

/// A season 1, RUN: salt-shore published, three verified wins ranked by turns
/// (ada=3, bea=5, cid=7). Policy carries the top-2 hall-of-fame + prestige.
fn ran_season_one() -> (Season, UniverseId) {
    let mut season = Season::genesis(
        1,
        base_epoch(),
        "the-descent:s1-salt-shore",
        1_000,
        CarryForwardPolicy::hall_of_fame(2).with_prestige(),
    );
    let u = salt_shore();
    let id = season.board.publish(u.clone());
    win(&mut season.board, &u, id, "ada", &WIN_FAST);
    win(&mut season.board, &u, id, "bea", &WIN_MID);
    win(&mut season.board, &u, id, "cid", &WIN_SLOW);
    (season, id)
}

// ═══════════════════════════════════════════════════════════════════════════════

#[test]
fn a_season_runs_a_no_cheat_board_and_ranks_champions() {
    let (season, id) = ran_season_one();
    // The season-scoped leaderboard ranks the verified wins by turns.
    let board = season.board.leaderboard(id);
    assert_eq!(board.len(), 3);
    assert_eq!((board[0].player.as_str(), board[0].turns), ("ada", 3));
    assert_eq!((board[1].player.as_str(), board[1].turns), ("bea", 5));
    assert_eq!((board[2].player.as_str(), board[2].turns), ("cid", 7));

    // Top-2 champions (the hall-of-fame the policy carries): ada then bea; cid cut.
    let champs = season.champions(2);
    assert_eq!(champs.len(), 2);
    assert_eq!(
        (champs[0].player.as_str(), champs[0].rank, champs[0].turns),
        ("ada", 1, 3)
    );
    assert_eq!(
        (champs[1].player.as_str(), champs[1].rank, champs[1].turns),
        ("bea", 2, 5)
    );
    assert_eq!(champs[0].identity, identity_of("ada"));
    assert_eq!(champs[0].universe, id);
}

#[test]
fn a_forged_win_never_reaches_the_board_so_never_a_champion() {
    // The no-cheat verify tooth: a forged completion is refused on replay, so a
    // cheater can never enter the hall-of-fame.
    let (mut season, id) = ran_season_one();
    let u = salt_shore();
    let mut forged = record_playthrough(&u, &WIN_FAST).expect("record the honest win");
    forged.steps[0].choice_index = CH_LEAVE_LANTERN; // retcon: leave the lantern
    let out = season.board.submit(Completion {
        universe: id,
        player: "mallory".into(),
        play: forged,
        claimed_turns: 3,
    });
    assert!(
        matches!(out, Err(RejectReason::FailedVerification(_))),
        "a forged win must be refused by the no-cheat board, got {out:?}"
    );
    // Mallory is nowhere in the champions.
    assert!(season.champions(8).iter().all(|c| c.player != "mallory"));
}

#[test]
fn tail_append_continues_the_same_season() {
    let (s1, id) = ran_season_one();
    let before_fp = s1.manifest.epoch.registry_fp.clone();
    let before_tag = s1.manifest.epoch.descriptor_set_tag.clone();
    let new_epoch = tail_append_epoch();

    // The drift class inferred from the epoch delta agrees it is a tail-append.
    assert_eq!(
        epoch_delta_class(&s1.manifest.epoch, &new_epoch),
        DriftClass::TailAppend
    );

    let t = advance_season(s1, new_epoch, DriftClass::TailAppend, 9_999).unwrap();
    assert!(!t.is_boundary(), "a tail-append is NOT a season boundary");
    let s = t.into_season();

    // Same season: id unchanged, the board (its verified wins) persists.
    assert_eq!(s.season_id(), 1, "the season id is unchanged");
    assert_eq!(
        s.board.leaderboard(id).len(),
        3,
        "the leaderboard persists across a tail-append"
    );
    // The epoch tag BUMPED but the VK-epoch identity (registry_fp) is the same —
    // non-breaking (Compatible). This is the non-vacuous contrast with the boundary.
    assert_eq!(s.manifest.epoch.registry_fp, before_fp, "same VK-epoch");
    assert_ne!(
        s.manifest.epoch.descriptor_set_tag, before_tag,
        "tag bumped"
    );
    // The handshake never reports a registry-fp mismatch across a tail-append: it is
    // the SAME VK-epoch (a new staged caveat tag reads as client-behind UnknownTags,
    // a verifier-code catch-up, NOT a re-genesis). Contrast the boundary case, which
    // IS a RegistryFpMismatch.
    assert!(
        !matches!(
            check_compatibility(&base_epoch(), &s.manifest.epoch),
            EpochCompat::RegistryFpMismatch { .. }
        ),
        "a tail-append is the same VK-epoch — never a registry-fp mismatch"
    );
}

#[test]
fn geometry_widen_ends_the_season_carries_forward_and_resets() {
    let (s1, id) = ran_season_one();
    let new_epoch = geometry_widen_epoch();

    // The epoch delta is a geometry-widen (registry_fp moved → a new VK-epoch); the
    // handshake keys on the same signal.
    assert_eq!(
        epoch_delta_class(&s1.manifest.epoch, &new_epoch),
        DriftClass::GeometryWiden
    );
    assert!(matches!(
        check_compatibility(&base_epoch(), &new_epoch),
        EpochCompat::RegistryFpMismatch { .. }
    ));

    let t = advance_season(s1, new_epoch.clone(), DriftClass::GeometryWiden, 2_000).unwrap();
    assert!(t.is_boundary(), "a geometry-widen IS a season boundary");

    let SeasonTransition::Boundary {
        season,
        carry,
        carried_cells,
    } = t
    else {
        unreachable!()
    };

    // A NEW season: fresh id + the widened epoch.
    assert_eq!(season.season_id(), 2);
    assert_eq!(season.manifest.epoch.registry_fp, new_epoch.registry_fp);

    // The ACTIVE leaderboard + characters RESET — a fresh, empty board.
    assert_eq!(
        season.board.universes().count(),
        0,
        "the new season's active board is empty"
    );
    assert!(season.board.leaderboard(id).is_empty());

    // The HALL-OF-FAME (top-2 champions) is CARRIED FORWARD into the new season.
    assert_eq!(season.hall_of_fame.len(), 2);
    assert_eq!(season.hall_of_fame[0].player, "ada");
    assert_eq!(season.hall_of_fame[0].turns, 3);
    assert_eq!(season.hall_of_fame[1].player, "bea");
    assert_eq!(season.hall_of_fame[1].from_season, 1, "earned in season 1");

    // Prestige carried per identity (ada + bea honored once each).
    assert_eq!(season.prestige.len(), 2);
    assert_eq!(season.prestige[&identity_of("ada")].seasons_honored, 1);
    assert_eq!(season.prestige[&identity_of("bea")].best_turns, 5);

    // VERIFIABLE VIA THE SNAPSHOT: the carry re-seeds the new genesis cleanly, and
    // the carried-cell count is the 2 champions + 2 prestige badges.
    assert_eq!(carried_cells, 4);
    let seeded = seed_genesis(&carry, season.federation_id()).expect("the carry re-seeds cleanly");
    assert_eq!(seeded.cells.len(), 4);
}

#[test]
fn prestige_persists_and_accrues_across_two_boundaries() {
    // Season 1: ada, bea, cid win. Boundary → season 2 (prestige ada=1, bea=1).
    let (s1, _) = ran_season_one();
    let mut s2 = advance_season(s1, geometry_widen_epoch(), DriftClass::GeometryWiden, 2_000)
        .unwrap()
        .into_season();
    assert_eq!(s2.season_id(), 2);
    assert_eq!(s2.prestige[&identity_of("ada")].seasons_honored, 1);
    assert_eq!(s2.prestige[&identity_of("bea")].seasons_honored, 1);

    // Season 2 RUNS: only ada plays (and wins). Then a second geometry-widen boundary.
    let u = salt_shore();
    let id = s2.board.publish(u.clone());
    win(&mut s2.board, &u, id, "ada", &WIN_FAST);

    let mut e3 = geometry_widen_epoch();
    e3.registry_fp = "d00dfeed".repeat(8); // a third distinct VK-epoch
    let s3 = advance_season(s2, e3, DriftClass::GeometryWiden, 3_000)
        .unwrap()
        .into_season();

    assert_eq!(s3.season_id(), 3);
    // ada reached the hall-of-fame in BOTH seasons → prestige accrued to 2.
    assert_eq!(
        s3.prestige[&identity_of("ada")].seasons_honored,
        2,
        "ada's prestige accrues across the boundary"
    );
    // bea did not play season 2, but their season-1 badge PERSISTS across the boundary.
    assert_eq!(
        s3.prestige[&identity_of("bea")].seasons_honored,
        1,
        "bea's prestige persists per-identity even without playing"
    );
    // Season 3's active hall-of-fame reflects only season 2's champions (ada).
    assert_eq!(s3.hall_of_fame.len(), 1);
    assert_eq!(s3.hall_of_fame[0].player, "ada");
    assert_eq!(s3.hall_of_fame[0].from_season, 2);
}

#[test]
fn a_forged_carry_forward_is_refused() {
    let (s1, _) = ran_season_one();
    let SeasonTransition::Boundary { season, carry, .. } =
        advance_season(s1, geometry_widen_epoch(), DriftClass::GeometryWiden, 2_000).unwrap()
    else {
        unreachable!()
    };
    let fed = season.federation_id();

    // Non-vacuity: the honest carry seeds cleanly.
    assert!(seed_genesis(&carry, fed).is_ok());

    // Forge a carried HALL-OF-FAME entry: rewrite the champion cell's stored score.
    // This changes the cell's state_commitment, breaking the migration-voucher
    // binding — genesis-snapshot's tamper-refusal bites.
    let mut forged = carry.clone();
    forged.entries[0].cell.state.fields[3][0] ^= 0xFF;
    let err = seed_genesis(&forged, fed).expect_err("a forged carry-forward is refused");
    assert!(
        matches!(
            err,
            ImportError::Entry {
                index: 0,
                kind: EntryReject::VoucherMismatch,
            }
        ),
        "expected VoucherMismatch on the forged champion, got {err:?}"
    );
}
