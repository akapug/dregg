//! SAVE / LOAD — pause a dungeon mid-crawl, serialize it, resume it, and finish.
//!
//! Run: `cargo run -p attested-dm --example savegame`
//!
//! A [`GameSession`] serializes to a portable [`SaveGame`] (world identity + the current world
//! state + the FULL receipt ledger + the randomness provider) as JSON. [`GameSession::load`]
//! reconstructs it and **re-verifies fail-closed** on BOTH tiers — the tamper-evident hash chain
//! (integrity) AND a from-genesis re-execution (every recorded effect is the rule-correct
//! resolution of its bound action) — before handing the session back. A tampered save is REFUSED;
//! an honest one resumes IDENTICALLY. This is what unlocks resumable web play and cross-session
//! (Discord) play: a run is a portable, self-verifying object.

use attested_dm::{sunken_vault, GameSession, GameStatus, LoadError, SaveGame, WorldEffect};

const SOLVE: &[&str] = &[
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

fn drive(game: &mut GameSession, cmds: &[&str]) {
    for cmd in cmds {
        assert!(game.command("hero", cmd).landed(), "`{cmd}` should land");
    }
}

fn main() {
    println!("== SAVE / LOAD — a resumable, self-verifying dungeon run (attested-dm) ==\n");

    // (1) Play HALFWAY through the Sunken Vault, then SAVE.
    let split = 7;
    let (first, rest) = SOLVE.split_at(split);
    let mut game = GameSession::open(sunken_vault());
    drive(&mut game, first);
    println!(
        "  played {split} turns — scene: {}, holding: {:?}",
        game.world().scene,
        game.world().inventory
    );

    let save = game.save();
    let json = save.to_json();
    println!(
        "\n  SAVE: {} bytes of JSON, {} ledger turns captured",
        json.len(),
        save.len()
    );
    let snippet: String = json.lines().take(9).collect::<Vec<_>>().join("\n");
    println!("  ---- save snippet ----\n{snippet}\n  ...(truncated)\n");

    // (2) Round-trip through JSON and LOAD into a fresh session (a stranger's re-verify on load).
    let reparsed = SaveGame::from_json(&json).expect("the save round-trips through JSON");
    let mut loaded = GameSession::load(&reparsed, sunken_vault())
        .expect("an honest save loads and re-verifies on both tiers");
    let report = loaded.verify_report();
    println!(
        "  LOAD: re-verified  chain={}  replay={}  (integrity + from-genesis re-execution)",
        if report.chain.is_ok() {
            "valid"
        } else {
            "BROKEN"
        },
        if report.replay.is_ok() {
            "valid"
        } else {
            "BROKEN"
        },
    );
    assert!(report.both_ok());

    // (3) CONTINUE the resumed session to the win.
    drive(&mut loaded, rest);
    assert_eq!(loaded.status(), GameStatus::Won);
    println!(
        "\n  RESUMED to victory — scene: {}, holding the {}.",
        loaded.world().scene,
        "amulet"
    );
    assert!(loaded.verify_report().both_ok());

    // (4) The resumed run is IDENTICAL to an unsaved one — same final receipt chain.
    let mut unsaved = GameSession::open(sunken_vault());
    drive(&mut unsaved, SOLVE);
    assert_eq!(loaded.world().receipts(), unsaved.world().receipts());
    println!("  the resumed chain is byte-identical to an unsaved playthrough (head matches).");

    // (5) A TAMPERED save is REFUSED fail-closed.
    println!("\n  now tamper the save and try to load it:");
    let mut tampered = game.save();
    tampered.ledger[0].effect = Some(WorldEffect::AdvanceScene("nowhere".into()));
    match GameSession::load(&tampered, sunken_vault()) {
        Err(LoadError::ChainBroken(b)) => {
            println!("    rewrote turn #0's effect (stale receipt)  ->  REFUSED: {b}")
        }
        Err(e) => panic!("a tampered save must be ChainBroken, got {e:?}"),
        Ok(_) => panic!("a tampered save must be refused, but load succeeded"),
    }

    println!(
        "\n  a run is a portable object that RE-VERIFIES itself on load — resumable web play,\n  \
         cross-session (Discord) play, and the overworld ride on exactly this."
    );
}
