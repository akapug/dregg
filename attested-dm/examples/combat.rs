//! # combat — the turn-based tactical COMBAT ENGINE, played and verified.
//!
//! A party of two (Rhea the fighter, Sol the mage) fights a Sentinel in an initiative-ordered
//! encounter whose damage is rolled from the turn's VERIFIED `dregg_dice` stream. The fight is a
//! closed deterministic machine: initiative order, per-combatant abilities (strike / guard / a
//! cooldown special), targeting, per-round shields, and terminal victory. Combat rides the closed
//! `Use` channel — NO new `GameAction`; the AI would only narrate, the WORLD rolls the die.
//!
//! This prints the fight blow by blow (each verified roll + the resulting HP), then the two
//! independent verification verdicts: chain integrity AND from-genesis re-execution (`verify_replay`
//! reproduces every damage roll). Run with:
//!
//! ```text
//! cargo run -p attested-dm --example combat
//! ```

use attested_dm::{arena_gauntlet, EncounterRule, GameSession, GameStatus, PlayResult};

fn hp_line(enc: &EncounterRule, game: &GameSession) -> String {
    let w = game.world();
    enc.combatants
        .iter()
        .map(|c| format!("{} {}hp", c.name, enc.hp(w, &c.id).max(0)))
        .collect::<Vec<_>>()
        .join("  ·  ")
}

fn play(game: &mut GameSession, enc: &EncounterRule, cmd: &str) {
    match game.command("hero", cmd) {
        PlayResult::Landed {
            narration, status, ..
        } => {
            println!("  > {cmd:<22} | {}", narration);
            println!("      state: [{}]  status={:?}", hp_line(enc, game), status);
        }
        other => println!("  > {cmd:<22} | REFUSED: {other:?}"),
    }
}

fn main() {
    let map = arena_gauntlet();
    let enc = map.encounter_for("arena").unwrap().clone();
    let mut game = GameSession::open(map);

    println!("THE ARENA GAUNTLET — turn-based combat with verified rolls\n");
    println!("Initiative order (higher acts first, ties by id):");
    for (i, c) in enc.order().iter().enumerate() {
        println!(
            "  {}. {:<12} init {:>2}  {:?}  {}hp",
            i, c.name, c.initiative, c.team, c.max_hp
        );
    }
    println!(
        "\nEach round the Sentinel strikes AFTER Rhea but BEFORE Sol, at the lowest-HP party member.\n"
    );

    // Walk into the arena. The reliquary exit is barred until the Sentinel falls.
    play(&mut game, &enc, "go north");

    // Illegal moves are REFUSED in-band (no receipt): the reliquary is still gated,
    // and a strike aimed at nothing is not a legal action.
    println!("\n-- the world refuses illegal moves (no receipt) --");
    match game.command("hero", "go north") {
        PlayResult::Refused(r) => println!("  gated exit: {r}"),
        other => println!("  unexpected: {other:?}"),
    }
    match game.command("hero", "use strike on rhea") {
        PlayResult::Refused(r) => println!("  strike an ally: {r}"),
        other => println!("  unexpected: {other:?}"),
    }

    println!("\n-- the fight (every blow is a VERIFIED roll the WORLD computes) --");
    // Drive the party ADAPTIVELY: ask the engine whose turn it is (`current_actor`), then pick a
    // sensible ability for that combatant. Rhea leads with `cleave` when it is off cooldown; Sol
    // wards itself when the Sentinel's next blow could drop it, else bolts. The WORLD rolls each
    // blow from the verified stream — the choices are tactics, not damage authority.
    let mut guard = 0;
    while enc.active(game.world()) && guard < 40 {
        guard += 1;
        let actor = match enc.current_actor(game.world()) {
            Some(c) => c.id.clone(),
            None => break,
        };
        let cmd = match actor.as_str() {
            // Rhea: cleave if available (cooldown flag 0), else strike.
            "rhea" => {
                let cd = game
                    .world()
                    .flags
                    .get(&enc.cooldown_flag("rhea", "cleave"))
                    .copied()
                    .unwrap_or(0);
                if cd == 0 {
                    "use cleave on sentinel"
                } else {
                    "use strike on sentinel"
                }
            }
            // Sol is fragile: ward when low, else bolt.
            "sol" => {
                if enc.hp(game.world(), "sol") <= 6 {
                    "use ward"
                } else {
                    "use bolt on sentinel"
                }
            }
            _ => "use strike on sentinel",
        };
        play(&mut game, &enc, cmd);
    }

    println!("\nSentinel felled: {}", !enc.active(game.world()));
    println!(
        "sentinel_down flag: {:?}",
        game.world().flags.get("sentinel_down")
    );

    // The gate is open now — claim the trophy to WIN.
    println!("\n-- the reliquary opens; claim the trophy --");
    play(&mut game, &enc, "go north");
    play(&mut game, &enc, "take trophy");
    println!("\nFINAL STATUS: {:?}", game.status());

    // ── Two independent verification claims, reported separately ──
    println!("\n-- verification (both tiers) --");
    let report = game.verify_report();
    println!("  chain integrity : {:?}", report.chain.is_ok());
    println!("  replay (re-exec): {:?}", report.replay.is_ok());
    println!(
        "  => verify_replay re-derived every combat seed, rebuilt every draw stream, and re-ran the\n     resolver from genesis: {}",
        if report.both_ok() {
            "the whole fight reproduces."
        } else {
            "MISMATCH!"
        }
    );
    assert!(
        report.both_ok(),
        "the honest fight must verify on both tiers"
    );
    assert_eq!(game.status(), GameStatus::Won);
    println!("\nThe party wins by verified rolls; a forged blow would be caught by replay.");
}
