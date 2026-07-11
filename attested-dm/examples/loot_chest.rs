//! THE GLIMMERING HOARD — a provably-fair loot chest, bound into the receipt chain.
//!
//! Run: `cargo run -p attested-dm --example loot_chest`
//!
//! The chest, on `Use`, drops ONE gem from a committed table `{ruby, emerald, sapphire, moonstone}`
//! via a single unbiased, seed-determined draw (the `dregg-dice` crate). The outcome is
//! WORLD-RESOLVED from the verified draw — never the AI's prose — and BOUNDED to the table. The
//! draw's `RandomnessRequest` (its event id binds game/seq/pre-state/action/purpose/draw-count) and
//! its `RandomnessEvidence` ride the turn's receipt. `verify_replay` then re-derives the event id,
//! re-verifies the evidence to recover the seed, rebuilds the draw stream, and re-runs the resolver
//! — proving the recorded drop is exactly `table[draw]`. A forged drop is caught.
//!
//! Honest scope: the recorded evidence is the CommitReveal slice — it prevents either party from
//! CHOOSING the outcome, and the draw is fully reconstructible/checkable; it does not close
//! selective abort (the registered-VRF + delayed-beacon `Hybrid` source is the follow-up).

use attested_dm::{
    loot_chest_demo, verify_ledger_replay, GameSession, GameStatus, PlayResult, ReplayMismatch,
    WorldEffect,
};

const TABLE: &[&str] = &["ruby", "emerald", "sapphire", "moonstone"];

/// The gem in the inventory (the drop = inventory ∩ the committed table).
fn drawn_gem(game: &GameSession) -> String {
    game.world()
        .inventory
        .iter()
        .find(|i| TABLE.contains(&i.as_str()))
        .cloned()
        .expect("the chest grants exactly one table gem")
}

/// Play THE GLIMMERING HOARD to a WIN under `seed`: open the chest, take the crown, climb out.
fn play(seed: [u8; 32]) -> GameSession {
    let mut game = GameSession::open(loot_chest_demo()).with_randomness(seed);
    for cmd in ["open hoard_chest", "take crown", "go up"] {
        match game.command("hero", cmd) {
            PlayResult::Landed { .. } => {}
            other => panic!("`{cmd}` should land, got {other:?}"),
        }
    }
    assert_eq!(game.status(), GameStatus::Won);
    game
}

fn main() {
    println!("== THE GLIMMERING HOARD — a provably-fair loot chest (attested-dm) ==\n");

    // Two different session seeds → two different, verifiable draws (seed-determined).
    for (label, seed) in [("seed A", [0x11u8; 32]), ("seed B", [0x22u8; 32])] {
        let game = play(seed);
        let gem = drawn_gem(&game);
        let report = game.verify_report();
        assert!(report.chain.is_ok() && report.replay.is_ok());
        println!("  {label}: the chest drops the {gem}");
        println!("           chain:  valid  (untampered receipt hash-chain)");
        println!("           replay: valid  (randomness reproduced — the draw is the fair draw)\n");
    }

    // Now forge ONE drop and re-link the chain so integrity still passes — replay catches it.
    println!("  now forge the drop (the AI claims a richer gem) and re-link the chain:");
    let game = play([0x11u8; 32]);
    let honest_gem = drawn_gem(&game);
    let forged_gem = TABLE
        .iter()
        .find(|g| **g != honest_gem)
        .unwrap()
        .to_string();
    let map = game.map().clone();
    let config = game.dm().config().clone();
    let mut world = game.world().clone();

    // The loot turn is seq 0. Rewrite its granted gem, keep the (valid) draw evidence, re-link.
    world.ledger[0].effect = Some(WorldEffect::Batch(vec![
        WorldEffect::GrantItem(forged_gem.clone()),
        WorldEffect::SetFlag("opened_hoard_chest".into(), 1),
    ]));
    relink(&mut world.ledger);
    println!("    forged drop: {honest_gem}  ->  {forged_gem}");

    // Integrity STILL passes (the receipt recomputes over the recorded, forged effect)...
    match world.verify_ledger(&config) {
        Ok(()) => println!("    chain:  valid  (integrity accepts the re-linked forgery)"),
        Err(e) => println!("    chain:  BROKEN — {e}"),
    }
    // ...but re-execution re-draws the honest gem from the verified seed and rejects the lie.
    match verify_ledger_replay(&map, &world.ledger) {
        Ok(()) => println!("    replay: valid  (unexpected!)"),
        Err(ReplayMismatch::Effect { seq, .. }) => println!(
            "    replay: CAUGHT at turn #{seq}: the resolver re-draws the {honest_gem}, not the \
             {forged_gem}"
        ),
        Err(other) => println!("    replay: CAUGHT: {other}"),
    }

    println!(
        "\n  the AI may narrate the treasure, but it cannot choose it: the drop is a fair,\n  \
         reconstructible draw bound into the chain — a forged roll is rejected on replay."
    );
}

/// Re-link a mutated ledger into an internally-consistent chain (recompute seq/prev/receipt over
/// each entry's own fields, including its randomness record) — what a forger who understands the
/// chain does so `verify_ledger` still passes.
fn relink(ledger: &mut [attested_dm::LedgerEntry]) {
    let mut prev = attested_dm::genesis_prev();
    for (i, e) in ledger.iter_mut().enumerate() {
        e.seq = i as u64;
        e.prev = prev;
        e.receipt = attested_dm::chain_receipt_id(
            e.seq,
            &e.prev,
            &e.narration,
            &e.effect,
            &e.prompt_binding,
            &e.game_binding,
            &e.randomness,
            &e.attestation,
        );
        prev = e.receipt;
    }
}
