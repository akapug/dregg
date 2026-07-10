//! THE SUNKEN VAULT — a full winning playthrough of the attested dungeon-crawler.
//!
//! Run: `cargo run -p attested-dm --example play`
//!
//! The AI dungeon-master narrates vividly and proposes a typed move each turn; the WORLD
//! RESOLVES every move by its own deterministic rules. You cannot narrate through a locked
//! door, cannot take an item that is not there, cannot pass the Warden without the sword,
//! cannot win without carrying the amulet to the gate. The AI proposes; the world disposes.
//!
//! This drives the canonical solve, then shows three moves the world REFUSES no matter how
//! the AI narrates them, and finally re-verifies the whole playthrough as a hash chain.

use attested_dm::{sunken_vault, GameAction, GameSession, GameStatus, PlayResult, Proposal};

fn main() {
    let mut game = GameSession::open(sunken_vault());
    println!("== THE SUNKEN VAULT ==\n");
    println!("  {}\n", game.look());

    // The critical path: every gate forces the order.
    let script = [
        ("go north", "into the salt antechamber"),
        ("take lantern", "a light against the dark"),
        ("go down", "down the (now lit) stair"),
        ("go down", "into the flooded cistern"),
        ("take rusted_key", "the key in the grate"),
        ("go north", "to the drowned vestry"),
        ("use rusted_key on iron_door", "the lock gives"),
        ("go east", "through the opened iron door"),
        ("take sword", "one blade still keen"),
        ("go north", "into the Warden's hall"),
        ("attack warden", "sword against drowned plate"),
        ("go east", "past the fallen Warden"),
        ("take amulet", "the Drowned Amulet"),
        ("go up", "toward grey daylight"),
    ];

    for (cmd, why) in script {
        match game.command("hero", cmd) {
            PlayResult::Landed {
                receipt,
                narration,
                status,
                action,
            } => {
                println!(
                    "  turn #{:>2}  {}  [{}]",
                    receipt.seq,
                    hex8(&receipt.id),
                    action.label()
                );
                println!("            {narration}  ({why})");
                if status == GameStatus::Won {
                    println!("\n  *** YOU WIN — the amulet is carried into the light. ***");
                }
            }
            other => panic!("the winning script should land `{cmd}`, got {other:?}"),
        }
    }

    // ── The AI proposes; the world disposes. Three refusals no prose can talk past. ──
    println!("\n  -- the world disposes (refused moves leave no receipt) --");
    let ledger_before = game.world().ledger.len();

    // A fresh crawler at the shore: the same rules bite from the start.
    let mut fresh = GameSession::open(sunken_vault());
    fresh.command("hero", "go north"); // to the antechamber, no lantern

    // 1) A jailbroken narrator insists the dark stair is passable. The world says: locked.
    show_refusal(
        &mut fresh,
        Proposal::new(
            "The shadows peel back and the stair welcomes you down!",
            GameAction::Move("down".into()),
        ),
        "narrate the dark stair open without a lantern",
    );
    // 2) Take an item that is not here.
    show_refusal(
        &mut fresh,
        Proposal::new(
            "You pocket the amulet with a grin.",
            GameAction::Take("amulet".into()),
        ),
        "take the amulet that is rooms away",
    );
    // 3) Attack a foe that is not present.
    show_refusal(
        &mut fresh,
        Proposal::new(
            "You cut the Warden down where it stands!",
            GameAction::Attack("warden".into()),
        ),
        "attack the Warden who is not in this room",
    );

    println!(
        "\n  refused moves landed nothing: winner's ledger still {ledger_before} turns; \
         the fresh crawler's ledger is {} turn(s).",
        fresh.world().ledger.len()
    );

    // The whole winning playthrough re-verifies as an authentic hash chain.
    game.verify()
        .expect("every landed move is authentic, well-formed, injection-free, and on-chain");
    println!(
        "\n  verify: OK — {} moves, each a verified turn; final status: {:?}.",
        game.world().ledger.len(),
        game.status()
    );
}

fn show_refusal<B: attested_dm::GameBrain>(
    game: &mut GameSession<B>,
    proposal: Proposal,
    what: &str,
) {
    let action = proposal.action.label();
    match game.play(proposal, "hero", "") {
        PlayResult::Refused(reason) => {
            println!("  REFUSED [{action}]: {reason}  (tried to {what})")
        }
        other => panic!("the world should refuse to {what}, got {other:?}"),
    }
}

fn hex8(id: &[u8; 32]) -> String {
    id[..4].iter().map(|b| format!("{b:02x}")).collect()
}
