//! THE DEEPDARK MINE — a full winning playthrough of the FOURTH attested dungeon, showcasing the
//! bounded LIGHT / RESOURCE dimension: descend a sunless mine on a lamp with limited oil, gather
//! single-use oil caches to survive deeper, reach the Deepheart and carry it back to the surface
//! before the light dies. The AI narrates the flame however grandly it likes; the WORLD keeps the
//! oil counter, and the counter is the truth.
//!
//! Run: `cargo run -p attested-dm --example play4`
//!
//! The light is load-bearing: the round trip is impossible if you waste the oil or skip the caches —
//! and no prose is power. A jailbroken "your lamp blazes eternal, oil be damned" burns oil exactly
//! like any other step; a jailbroken "the lamp is refilled to infinity" pours nothing. Only real oil
//! in the counter lets you go on, and running the counter to zero in the dark strands you for good.

use attested_dm::{deepdark_mine, GameAction, GameSession, GameStatus, PlayResult, Proposal};

fn oil(game: &GameSession) -> i64 {
    game.world().flags.get("lamp_oil").copied().unwrap_or(0)
}

fn main() {
    let mut game = GameSession::open(deepdark_mine());
    println!("== THE DEEPDARK MINE ==\n\n  {}\n", game.look());
    println!(
        "  (the lamp holds {} oil; every step in the dark burns one)\n",
        oil(&game)
    );

    // The critical path is a RACE AGAINST THE DARK:
    //   fuel the lamp → descend the dark drifts, pouring the sump + pump-house oil to survive →
    //   reach the Deepheart → climb all the way back to daylight before the flame dies.
    let script = [
        "take lamp",               // pithead (daylight)
        "take oil_flask_a",        //
        "use oil_flask_a on lamp", // pour the first flask (+5)
        "ask ghost about dark",    // the lost miner warns you: gather oil, waste no step
        "go down",                 // cage
        "go down",                 // main_drift — the first DARK room
        "go east",                 // sump
        "take oil_flask_b",        //
        "use oil_flask_b on lamp", // pour the sump oil (+5) — the round trip needs it
        "go west",                 // main_drift
        "go north",                // crosscut
        "go west",                 // pump_house
        "take oil_flask_c",        //
        "use oil_flask_c on lamp", // pour the pump-house oil (+5)
        "go east",                 // crosscut
        "go north",                // old_workings
        "go down",                 // lower_drift
        "go north",                // cavern
        "go down",                 // deep_shaft
        "go north",                // gallery
        "go east",                 // deepheart
        "take deepheart",          // the burning starstone vein
        "go west",                 // gallery  — begin the climb back
        "go south",                // deep_shaft
        "go up",                   // cavern
        "go south",                // lower_drift
        "go up",                   // old_workings
        "go south",                // crosscut
        "go south",                // main_drift
        "go up",                   // cage
        "go up",                   // pithead → WIN (the Deepheart carried to daylight)
    ];

    for cmd in script {
        match game.command("hero", cmd) {
            PlayResult::Landed {
                narration,
                status,
                action,
                ..
            } => {
                println!(
                    "  [{}]  {}   (oil: {})",
                    action.label(),
                    narration,
                    oil(&game)
                );
                if status == GameStatus::Won {
                    println!(
                        "\n  *** YOU WIN — the Deepheart carried back to daylight with {} oil to \
                         spare; the dark did not keep you. ***",
                        oil(&game)
                    );
                }
            }
            other => panic!("the winning script should land `{cmd}`, got {other:?}"),
        }
    }

    assert_eq!(
        game.status(),
        GameStatus::Won,
        "the light-managed critical path reaches the win"
    );
    assert!(game.world().inventory.contains("deepheart"));
    assert_eq!(game.world().scene, "pithead");

    // ── The AI proposes; the world disposes. The oil counter is the truth. ──
    println!("\n  -- the world disposes (prose is not power, at the level of light) --");

    // 1) DARK REFUSED AT ZERO: a fresh miner with a dry lamp cannot step into the dark, no matter
    //    how the AI narrates the flame.
    let mut dry = GameSession::open(deepdark_mine());
    for cmd in ["take lamp", "go down"] {
        dry.command("hero", cmd); // reach the cage with the lamp but do NOT fuel it
    }
    // Burn the seeded 8 oil to zero by stepping in and out of the dark until it dies... instead,
    // drive it dry deterministically: descend one dark step per oil, then the next is refused.
    // Simplest: pour nothing and walk the drift until the lamp gutters, then try to go deeper.
    // (Here we just show the refusal directly from the dead-lamp state.)
    let jailbroken_light = Proposal::new(
        "Your lamp flares with the light of a thousand suns — ETERNAL, oil be damned!",
        GameAction::Move("main_drift".into()),
    );
    // Drain the lamp to 0 first (walk the lit cage/pithead loop burns oil each step).
    while dry.world().flags.get("lamp_oil").copied().unwrap_or(0) > 0 {
        // bounce between cage and pithead (both lit) to burn oil without entering the dark
        let at = dry.world().scene.clone();
        let to = if at == "cage" { "up" } else { "down" };
        if !dry.command("hero", to).landed() {
            break;
        }
    }
    // Now the lamp is dead; return to the cage and try to descend into the dark.
    if dry.world().scene == "pithead" {
        dry.command("hero", "go down"); // cage (lit, oil already 0, no decrement)
    }
    match dry.play(jailbroken_light, "hero", "") {
        PlayResult::Refused(reason) => println!(
            "  DEAD LAMP: REFUSED [move -> main_drift]: {reason}\n              (the prose swore \
             the lamp was eternal; the oil counter said 0, and the world listened to the counter.)"
        ),
        other => panic!("a step into the dark on a dead lamp must be refused, got {other:?}"),
    }

    // 2) JAILBROKEN REFUEL DOES NOTHING: narrate the flask refilling itself endlessly — the counter
    //    does not move; only really pouring an unspent flask (the world's RefuelRule) adds oil.
    let mut m = GameSession::open(deepdark_mine());
    m.command("hero", "take lamp");
    let before = m.world().flags.get("lamp_oil").copied().unwrap();
    let jailbroken_refuel = Proposal::new(
        "You will the lamp full again — it drinks the void and refills itself, ENDLESS oil!",
        GameAction::Examine,
    );
    m.play(jailbroken_refuel, "hero", "");
    let after_prose = m.world().flags.get("lamp_oil").copied().unwrap();
    m.command("hero", "take oil_flask_a");
    m.command("hero", "use oil_flask_a on lamp"); // the REAL refuel
    let after_pour = m.world().flags.get("lamp_oil").copied().unwrap();
    println!(
        "  REFUEL: prose ('endless oil!') left the counter at {after_prose} (was {before}); a real \
         pour of the flask raised it to {after_pour}. The world grants oil, the narrator cannot."
    );
    assert_eq!(after_prose, before, "narration must not refuel the lamp");
    assert!(after_pour > after_prose, "a real pour must refuel the lamp");

    game.verify()
        .expect("every landed move is on-chain and authentic");
    println!(
        "\n  verify: OK — {} moves, each a verified turn; final status: {:?}.",
        game.world().ledger.len(),
        game.status()
    );
}
