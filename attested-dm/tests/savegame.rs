//! SAVE / LOAD PERSISTENCE — a session serializes to a portable `SaveGame`, round-trips through
//! JSON, and reconstructs + RE-VERIFIES on load (chain integrity + from-genesis re-execution). A
//! saved-then-loaded session continues IDENTICALLY; a tampered save is REFUSED fail-closed.

use attested_dm::{
    chain_receipt_id, genesis_prev, loot_chest_demo, sunken_vault, DmAttestationCarrier,
    GameStatus, LoadError, SaveGame, WorldEffect, DEFAULT_DM_SEED,
};

/// The canonical sunken-vault solve (14 legal moves → WIN).
const SUNKEN_SOLVE: &[&str] = &[
    "go north",
    "take lantern",
    "go down",
    "go down",
    "take rusted_key",
    "go north",
    "use rusted_key on iron_door",
    "go east",
    "take sword",
    "go north",
    "attack warden",
    "go east",
    "take amulet",
    "go up",
];

/// The loot-demo win: open the chest (a random draw), take the crown, climb out.
const LOOT_SOLVE: &[&str] = &["open hoard_chest", "take crown", "go up"];

const LOOT_TABLE: &[&str] = &["ruby", "emerald", "sapphire", "moonstone"];

/// Play a fresh sunken-vault session through the given commands (asserting each lands).
fn play_sunken(cmds: &[&str]) -> attested_dm::GameSession {
    let mut game = attested_dm::GameSession::open(sunken_vault());
    for cmd in cmds {
        assert!(
            game.command("hero", cmd).landed(),
            "`{cmd}` should land in the sunken vault"
        );
    }
    game
}

// ─────────────────────────────────────────────────────────────────────────────
// (1) ROUND-TRIP IDENTITY — save halfway, JSON round-trip, load, verify BOTH tiers,
//     continue to a WIN with an IDENTICAL final chain to an unsaved playthrough.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn save_load_round_trips_identically_and_continues_to_an_identical_win() {
    let split = 7; // save partway through the 14-move solve
    let (first, rest) = SUNKEN_SOLVE.split_at(split);

    // Play HALFWAY, then save + JSON round-trip.
    let mid = play_sunken(first);
    assert_eq!(mid.status(), GameStatus::Playing);
    let save = mid.save();
    assert_eq!(save.len(), split, "the save captures every landed turn");
    let json = save.to_json();
    let reparsed = SaveGame::from_json(&json).expect("the save round-trips through JSON");

    // LOAD into a fresh session against a freshly-reconstructed map.
    let loaded = attested_dm::GameSession::load(&reparsed, sunken_vault())
        .expect("an honest save loads and re-verifies");

    // The loaded session VERIFIES on BOTH tiers (integrity + re-execution).
    let report = loaded.verify_report();
    assert!(report.chain.is_ok(), "loaded chain must verify: {report:?}");
    assert!(
        report.replay.is_ok(),
        "loaded replay must verify: {report:?}"
    );

    // The reconstructed state matches the pre-save state exactly.
    assert_eq!(loaded.world().scene, mid.world().scene);
    assert_eq!(loaded.world().flags, mid.world().flags);
    assert_eq!(loaded.world().inventory, mid.world().inventory);
    assert_eq!(loaded.world().receipts(), mid.world().receipts());

    // CONTINUE the loaded session to the win.
    let mut loaded = loaded;
    for cmd in rest {
        assert!(
            loaded.command("hero", cmd).landed(),
            "`{cmd}` should land after load"
        );
    }
    assert_eq!(loaded.status(), GameStatus::Won);
    assert!(loaded.verify_report().both_ok());

    // IDENTICAL to an unsaved playthrough: the full receipt chain matches turn-for-turn.
    let unsaved = play_sunken(SUNKEN_SOLVE);
    assert_eq!(unsaved.status(), GameStatus::Won);
    assert_eq!(
        loaded.world().receipts(),
        unsaved.world().receipts(),
        "a saved-then-loaded-then-continued session yields the identical chain"
    );
    assert_eq!(loaded.world().scene, unsaved.world().scene);
    assert_eq!(loaded.world().flags, unsaved.world().flags);
    assert_eq!(loaded.world().inventory, unsaved.world().inventory);
}

// ─────────────────────────────────────────────────────────────────────────────
// (2) FAIL-CLOSED — a tampered SAVED FLAG is refused (WorldMismatch), non-vacuous.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_tampered_saved_flag_is_refused_on_load() {
    let game = play_sunken(SUNKEN_SOLVE);
    let mut save = game.save();

    // Sanity: the honest save loads fine.
    assert!(attested_dm::GameSession::load(&save, sunken_vault()).is_ok());

    // FLIP a saved world flag (the ledger is left intact, so both verification tiers still pass —
    // the tamper is caught ONLY by the state-vs-replay consistency check).
    let flag = "warden_defeated".to_string();
    assert_eq!(
        save.flags.get(&flag).copied(),
        Some(1),
        "the honest save records warden_defeated = 1"
    );
    save.flags.insert(flag, 0); // cheat the flag back to 0

    match attested_dm::GameSession::load(&save, sunken_vault()) {
        Err(LoadError::WorldMismatch { .. }) => {}
        Err(e) => panic!("a tampered saved flag must be WorldMismatch, got {e:?}"),
        Ok(_) => panic!("a tampered saved flag must be refused, but load succeeded"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// (3) FAIL-CLOSED — a tampered LEDGER EFFECT (receipt left stale) is refused (ChainBroken).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_tampered_ledger_effect_is_refused_on_load() {
    let game = play_sunken(SUNKEN_SOLVE);
    let mut save = game.save();

    // Rewrite the effect of turn #0 ("go north" → AdvanceScene) but leave its stored receipt as
    // is: the receipt no longer recomputes over the tampered effect → the integrity tier bites.
    assert!(save.ledger[0].effect.is_some());
    save.ledger[0].effect = Some(WorldEffect::AdvanceScene("nowhere".to_string()));

    match attested_dm::GameSession::load(&save, sunken_vault()) {
        Err(LoadError::ChainBroken(_)) => {}
        Err(e) => panic!("a tampered ledger effect must be ChainBroken, got {e:?}"),
        Ok(_) => panic!("a tampered ledger effect must be refused, but load succeeded"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// (4) FAIL-CLOSED — a RE-LINKED forged effect (chain made internally consistent) is refused by
//     the re-execution tier (ReplayMismatch), proving tier 2 is load-bearing on load.
// ─────────────────────────────────────────────────────────────────────────────

/// Re-link a tampered `SaveGame` ledger into an internally-consistent hash chain: re-derive each
/// turn's deterministic attestation and recompute its receipt/prev over its (possibly rewritten)
/// fields — exactly what a forger who understands the chain does so the integrity tier still passes.
fn relink_saved(save: &mut SaveGame) {
    let carrier = DmAttestationCarrier::from_seed(&DEFAULT_DM_SEED);
    let mut prev = genesis_prev();
    for (i, e) in save.ledger.iter_mut().enumerate() {
        e.seq = i as u64;
        e.prev = prev;
        let (att, _field) = carrier
            .attest_narration(&e.narration)
            .expect("the recorded narration re-attests");
        e.receipt = chain_receipt_id(
            e.seq,
            &e.prev,
            &e.narration,
            &e.effect,
            &e.prompt_binding,
            &e.game_binding,
            &e.randomness,
            &att,
        );
        prev = e.receipt;
    }
}

#[test]
fn a_relinked_forged_drop_is_refused_by_re_execution_on_load() {
    // Play the loot game to a win under a pinned seed, then forge the drawn gem and re-link.
    let mut game = attested_dm::GameSession::open(loot_chest_demo()).with_randomness([0x11; 32]);
    for cmd in LOOT_SOLVE {
        assert!(game.command("hero", cmd).landed());
    }
    assert_eq!(game.status(), GameStatus::Won);

    let honest_gem = game
        .world()
        .inventory
        .iter()
        .find(|i| LOOT_TABLE.contains(&i.as_str()))
        .cloned()
        .expect("the chest granted one table gem");
    let forged_gem = LOOT_TABLE
        .iter()
        .find(|g| **g != honest_gem)
        .unwrap()
        .to_string();

    let mut save = game.save();
    // The loot draw is turn #0: rewrite the granted gem, keep the (valid) draw evidence, re-link.
    save.ledger[0].effect = Some(WorldEffect::Batch(vec![
        WorldEffect::GrantItem(forged_gem.clone()),
        WorldEffect::SetFlag("opened_hoard_chest".to_string(), 1),
    ]));
    relink_saved(&mut save);

    // The integrity tier now ACCEPTS the re-linked forgery — but re-execution re-draws the honest
    // gem from the verified seed and rejects the lie.
    match attested_dm::GameSession::load(&save, loot_chest_demo()) {
        Err(LoadError::ReplayMismatch(_)) => {}
        Err(e) => panic!("a re-linked forged drop must be ReplayMismatch, got {e:?}"),
        Ok(_) => panic!("a re-linked forged drop must be refused, but load succeeded"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// (5) RANDOMNESS-PRESERVING — a save in the MIDDLE of the loot game keeps the draw record,
//     re-verifies, and continues to a win.
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn a_mid_loot_game_save_preserves_the_randomness_and_replays() {
    // Play just the random turn (open the chest), then save mid-game.
    let mut game = attested_dm::GameSession::open(loot_chest_demo()).with_randomness([0x22; 32]);
    assert!(game.command("hero", "open hoard_chest").landed());
    assert_eq!(game.status(), GameStatus::Playing);

    let save = game.save();
    // The randomness record rides through serialization.
    assert!(
        save.ledger[0].randomness.is_some(),
        "the loot draw's randomness record is captured"
    );
    let json = save.to_json_bytes();
    let reparsed: SaveGame = serde_json::from_slice(&json).expect("the loot save round-trips");
    assert_eq!(
        reparsed.ledger[0].randomness, save.ledger[0].randomness,
        "the randomness record survives the JSON round-trip byte-for-byte"
    );

    let mut loaded = attested_dm::GameSession::load(&reparsed, loot_chest_demo())
        .expect("a mid-loot-game save re-verifies and loads");
    assert!(
        loaded.world().ledger[0].randomness.is_some(),
        "the reconstructed ledger still carries the draw"
    );
    assert!(loaded.verify_report().both_ok(), "both tiers re-verify");

    // The drawn gem matches the pre-save draw, and the game finishes.
    assert_eq!(loaded.world().inventory, game.world().inventory);
    for cmd in &LOOT_SOLVE[1..] {
        assert!(loaded.command("hero", cmd).landed());
    }
    assert_eq!(loaded.status(), GameStatus::Won);
    assert!(loaded.verify_report().both_ok());
}

// ─────────────────────────────────────────────────────────────────────────────
// (6) WRONG MAP — loading against a different world is refused (WorldMismatch).
// ─────────────────────────────────────────────────────────────────────────────

#[test]
fn loading_against_the_wrong_map_is_refused() {
    let game = play_sunken(&SUNKEN_SOLVE[..4]);
    let save = game.save();
    match attested_dm::GameSession::load(&save, loot_chest_demo()) {
        Err(LoadError::WorldMismatch { .. }) => {}
        Err(e) => panic!("loading against the wrong map must be WorldMismatch, got {e:?}"),
        Ok(_) => panic!("loading against the wrong map must be refused, but load succeeded"),
    }
    // ...and against the RIGHT map it loads.
    assert!(attested_dm::GameSession::load(&save, sunken_vault()).is_ok());
}
