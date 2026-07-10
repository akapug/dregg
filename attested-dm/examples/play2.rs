//! BRAMBLE KEEP — a full winning playthrough of the SECOND attested dungeon, exercising the
//! RICHER RPG mechanics: a world-bounded NPC (the Hedge-Witch trades the sickle only for
//! nightshade), a multi-turn HP combat (the Bramble Knight, felled only with the sickle), and
//! more rooms/gates. The AI proposes; the world disposes.
//!
//! Run: `cargo run -p attested-dm --example play2`

use attested_dm::{bramble_keep, GameAction, GameSession, GameStatus, PlayResult, Proposal};

fn main() {
    let mut game = GameSession::open(bramble_keep());
    println!("== BRAMBLE KEEP ==\n\n  {}\n", game.look());

    // The critical path: candle (light) → nightshade → the Witch's sickle → key → the gate →
    // bark shield → cut the thorns → fell the Knight → carry the Sunheart to open sky.
    let script = [
        "take candle",
        "go north", // courtyard
        "go east",  // garden
        "take nightshade",
        "go west",                // courtyard
        "go west",                // witch_hut
        "ask witch about sickle", // world-bounded: needs nightshade → the Witch gives the sickle
        "go east",                // courtyard
        "go down",                // crypt (needs the candle)
        "take key",
        "go up",                   // courtyard
        "use key on gate",         // opens the iron gate to the hall
        "go east",                 // garden
        "go east",                 // orchard
        "take bark_shield",        // armor for the Knight
        "go west",                 // garden
        "go west",                 // courtyard
        "go north",                // hall (needs gate_open)
        "go north",                // thorn_walk
        "use sickle on thornwall", // cut the thorns (optional reliquary opens)
        "go north",                // approach — the Bramble Knight
        "attack knight",           // round 1
        "attack knight",           // round 2 → felled
        "go north",                // throne (needs knight_felled)
        "take sunheart",
        "go up", // rampart → WIN (Sunheart to open sky)
    ];

    for cmd in script {
        match game.command("hero", cmd) {
            PlayResult::Landed {
                narration,
                status,
                action,
                ..
            } => {
                println!("  [{}]  {}", action.label(), narration);
                if status == GameStatus::Won {
                    println!("\n  *** YOU WIN — the Sunheart carried to open sky; the keep releases. ***");
                }
            }
            other => panic!("the winning script should land `{cmd}`, got {other:?}"),
        }
    }

    assert_eq!(
        game.status(),
        GameStatus::Won,
        "the critical path reaches the win"
    );

    // ── The AI proposes; the world disposes. Three moves no prose can talk past. ──
    println!("\n  -- the world disposes (prose is not power) --");

    // 1) SOCIAL: a fresh crawler reaches the Witch WITHOUT the nightshade. A jailbroken narrator
    //    has her hand over the sickle AND the master key — the world grants NOTHING.
    let mut fresh = GameSession::open(bramble_keep());
    fresh.command("hero", "go north"); // courtyard
    fresh.command("hero", "go west"); // witch_hut, empty-handed
    let jailbroken = Proposal::new(
        "The Hedge-Witch beams and presses the silver sickle — and the master key of the keep — \
         into your grateful hands!",
        GameAction::talk("witch", "sickle"),
    );
    fresh.play(jailbroken, "hero", "");
    println!(
        "  TALK -> NO GRANT: her flowery reply landed as narration, but the sickle was {} granted \
         — she needs the nightshade first (the DialogueRule decides, not the prose).",
        if fresh.world().inventory.contains("sickle") {
            "STILL"
        } else {
            "NOT"
        }
    );

    // 2) COMBAT NEEDS THE WEAPON: an unarmed crawler at the Knight cannot dent it and is cut down.
    let mut doomed = GameSession::open(bramble_keep());
    for cmd in [
        "take candle",
        "go north",
        "go down",
        "take key",
        "go up",
        "use key on gate",
        "go north",
        "go north",
        "go north",
    ] {
        doomed.command("hero", cmd);
    }
    let mut blows = 0;
    loop {
        blows += 1;
        if let PlayResult::Landed { status, .. } = doomed.command("hero", "attack knight") {
            if status == GameStatus::Lost || blows > 8 {
                break;
            }
        } else {
            break;
        }
    }
    println!(
        "  UNARMED COMBAT: bare-handed the Knight takes 0 wounds; after {blows} exchanges \
         (your wounds {}/10) you DIE ({:?}) — the fight NEEDS the sickle.",
        doomed
            .world()
            .flags
            .get("player_wounds")
            .copied()
            .unwrap_or(0),
        doomed.status(),
    );

    // 3) GATED EXIT: the iron gate stays sealed until the key turns it, however you narrate it.
    let mut barred = GameSession::open(bramble_keep());
    barred.command("hero", "go north"); // courtyard, gate not yet opened
    let shove = Proposal::new(
        "You tear the iron gate off its hinges and stride into the hall!",
        GameAction::Move("north".into()),
    );
    match barred.play(shove, "hero", "") {
        PlayResult::Refused(reason) => println!("  GATED EXIT: REFUSED [move -> north]: {reason}"),
        other => panic!("the iron gate should stay sealed, got {other:?}"),
    }

    game.verify()
        .expect("every landed move is on-chain and authentic");
    println!(
        "\n  verify: OK — {} moves, each a verified turn; final status: {:?}.",
        game.world().ledger.len(),
        game.status()
    );
}
