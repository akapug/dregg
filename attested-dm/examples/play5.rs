//! THE VENOMOUS DEEP — a full winning playthrough of the FIFTH attested dungeon, showcasing the
//! bounded CONSUMABLE + STATUS-EFFECT dimension: drink the wyrm's bile to walk its venom-ford, race
//! a cure against the poison ticking in your blood, and ward yourself before you wake the Bone Wyrm.
//! The AI narrates every draught however grandly it likes ("this elixir makes you INVINCIBLE"); the
//! WORLD heals exactly the salve's N and ticks exactly the counter, no more.
//!
//! Run: `cargo run -p attested-dm --example play5`
//!
//! The consumables + statuses are LOAD-BEARING: unwinnable without the bile (the ford's key), the
//! shield (surviving the Wyrm), and the antidote (surviving the venom on the way out). And no prose
//! is power — a jailbroken over-heal heals exactly 4, and a spent draught is gone for good.

use attested_dm::{venom_deep, GameAction, GameSession, GameStatus, PlayResult, Proposal};

fn flag(game: &GameSession, k: &str) -> i64 {
    game.world().flags.get(k).copied().unwrap_or(0)
}

/// The player's wounds / active statuses, for the running log.
fn vitals(game: &GameSession) -> String {
    format!(
        "wounds {}/12, venom {}, warded {}",
        flag(game, "player_wounds"),
        flag(game, "venom"),
        flag(game, "warded"),
    )
}

fn main() {
    let mut game = GameSession::open(venom_deep());
    println!("== THE VENOMOUS DEEP ==\n\n  {}\n", game.look());

    // The critical path: gather the draughts + the harpoon → drink the bile to cross the venom-ford
    // (now the poison ticks a wound each step) → ward yourself and fell the Bone Wyrm → drink the
    // antidote to still the venom → carry the Venom Heart out to the surface before it takes you.
    let script = [
        "take salve",            // gatehouse — a healing draught for the road
        "go east",               // stillroom (side)
        "take silver_censer",    //   atmosphere
        "go west",               // gatehouse
        "go down",               // undercroft
        "take antidote",         //   the cure
        "take shield_draught",   //   the ward
        "go north",              // armoury
        "take harpoon",          //   the Wyrm's bane
        "take wyrm_bile",        //   the ford's key AND the poison
        "go south",              // undercroft
        "go east",               // ossuary
        "ask oracle about wyrm", //   the Drowned Oracle tells the wyrm's undoing (lore, no power)
        "go west",               // undercroft
        "go down",               // ford_bank
        "use wyrm_bile",         //   DRINK — venom floods your blood (venom = 8); now you may cross
        "go north",              // venom_ford  — poison ticks (+2)
        "go north",              // drowned_stair (+2)
        "go up",                 // wyrm_hall (+2)
        "use shield_draught",    //   WARD yourself before you strike (warded = 8)
        "attack wyrm",           //   harpoon strike — warded, you take only 2
        "attack wyrm",           //   again
        "attack wyrm",           //   the felling blow — the Wyrm clatters apart
        "use antidote",          //   STILL the venom (venom = 0) before it takes you on the climb
        "use salve",             //   heal the fight's wounds (exactly 4)
        "go north",              // inner_shrine (the wyrm_felled gate opens)
        "take venom_heart",      //   the green-fire relic
        "go up",                 // ascent
        "go up",                 // crypt_gate
        "go up",                 // surface → WIN (the Heart carried to open sky)
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
                    "  [{}]  {}   ({})",
                    action.label(),
                    narration,
                    vitals(&game)
                );
                if status == GameStatus::Won {
                    println!(
                        "\n  *** YOU WIN — the Venom Heart carried to the surface; the ford bore you, \
                         the ward held, and the antidote beat the venom. ***"
                    );
                }
            }
            other => panic!("the winning script should land `{cmd}`, got {other:?}"),
        }
    }

    assert_eq!(
        game.status(),
        GameStatus::Won,
        "the consumable/status-managed critical path reaches the win"
    );
    assert!(game.world().inventory.contains("venom_heart"));
    assert_eq!(game.world().scene, "surface");

    // ── The AI proposes; the world disposes. The counter is the truth. ──
    println!("\n  -- the world disposes (prose is not power, at the level of what you drink) --");

    // 1) JAILBROKEN OVER-HEAL DOES EXACTLY N: bring a fresh diver to a wounded state, then narrate a
    //    salve that "makes you INVINCIBLE, healed to full and BEYOND" — the world heals exactly 4.
    let mut m = GameSession::open(venom_deep());
    for cmd in [
        "take salve",
        "go down",
        "go north",
        "take harpoon",
        "take wyrm_bile",
        "go south",
        "go down",
        "use wyrm_bile", // venom = 8
        "go north",      // venom_ford: +2
        "go north",      // drowned_stair: +2  → wounds now 4
    ] {
        m.command("hero", cmd);
    }
    let wounds_before = m.world().flags.get("player_wounds").copied().unwrap_or(0);
    let over_heal = Proposal::new(
        "You quaff the salve and are made WHOLE — nay, INVINCIBLE: every wound erased, your \
         flesh restored past mortal limit, healed to full and beyond!",
        GameAction::Use("salve".into(), None),
    );
    m.play(over_heal, "hero", "");
    let wounds_after = m.world().flags.get("player_wounds").copied().unwrap_or(0);
    println!(
        "  OVER-HEAL: prose swore 'INVINCIBLE, healed beyond' — the world took wounds from \
         {wounds_before} to {wounds_after} (exactly 4, clamped at 0). The salve heals what the \
         rule says, not what the narrator claims."
    );
    assert_eq!(
        wounds_after,
        (wounds_before - 4).max(0),
        "the over-heal narration heals exactly the rule's N, no more"
    );

    // 2) A SPENT DRAUGHT IS GONE: the salve just drunk left the pack — a second use finds nothing to
    //    drink and is REFUSED (world unchanged, no receipt). Consumption is real, not narrated.
    assert!(
        !m.world().inventory.contains("salve"),
        "the drunk salve really left the inventory"
    );
    let receipts_before = m.world().ledger.len();
    match m.command("hero", "use salve") {
        PlayResult::Refused(reason) => println!(
            "  SPENT: a second `use salve` REFUSED: {reason}\n         (the draught was drunk; no \
             prose refills it, and the refusal lands no receipt.)"
        ),
        other => panic!("using a spent consumable must be refused, got {other:?}"),
    }
    assert_eq!(
        m.world().ledger.len(),
        receipts_before,
        "a refused (spent) use lands NO receipt — the anti-ghost tooth"
    );

    game.verify()
        .expect("every landed move is on-chain and authentic");
    println!(
        "\n  verify: OK — {} moves, each a verified turn; final status: {:?}.",
        game.world().ledger.len(),
        game.status()
    );
}
