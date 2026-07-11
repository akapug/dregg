//! `universe` — ONE assembled universe, played START to WIN on real WorldCell turns.
//!
//! ```text
//! cargo run -p dungeon-on-dregg --example universe
//! ```
//!
//! Not four separate demo functions — ONE continuous playthrough composing the
//! committed pieces of the collective-fiction rebuild, each a REAL turn on the real
//! dregg substrate:
//!
//!   1. **Cross-cell gated progression** (`multicell::World`) — a GRAPH of real cells.
//!      Take the lantern on its OWN cell to open the gated stair on ANOTHER cell; the
//!      gate is a real executor `ObservedFieldEquals` predicate reading the peer cell's
//!      finalized owner (refused before the item is taken; commits after).
//!   2. **Dice-rolled combat** (`dice_combat`) — a real `dregg_dice::DrawStream` draw
//!      is the blow's damage, bound into the real `TurnReceipt` via `EmitEvent` and
//!      REPRODUCED on replay (a forged roll would be caught).
//!   3. **A narrated turn** (`narrator`, a scripted `Brain`) — the AI narrates; the
//!      WORLD resolves the typed Command (prose is not power); the narration binds into
//!      the real receipt.
//!   4. **A real WIN state** — the hoard seized, the scene ENDED — reached by a chain
//!      of real `TurnReceipt`s that link `pre == prev.post`.
//!
//! Honest scope (printed at the end): verification is O(N) replay (`reverify_draw` +
//! `verify_chain_linkage`), not a succinct light client; the dice source is the
//! reproducible `Deterministic` one (non-grindable `ServerVrf`/`Hybrid` is a named
//! `dregg-dice` follow-up); the `deos-hermes` jail is out of scope.

use dregg_app_framework::TurnReceipt;
use dungeon_on_dregg::dice_combat::{
    COMBAT_DIE_SIDES, CombatReceipt, bound_draw, reverify_draw, strike,
};
use dungeon_on_dregg::multicell::{DOOR_SLOT, OWNER_SLOT, World};
use dungeon_on_dregg::narrator::{
    Brain, Command, Narrated, ScriptedBrain, bound_narration_commit, narrate_turn,
};
use dungeon_on_dregg::{
    KP_CAST_WARD, KP_CLAIM_RED, KP_DESCEND, KP_PRESS_ON, KP_SEIZE, ROOM_GATEHALL, ROOM_HALL,
    ROOM_SANCTUM, deploy_keep, keep_scene,
};
use spween_dregg::Value;

fn hex8(f: &[u8; 32]) -> String {
    f[..8].iter().map(|b| format!("{b:02x}")).collect()
}

fn main() {
    println!("═══════════════════════════════════════════════════════════════════");
    println!(" ONE UNIVERSE, PLAYED START → WIN on the REAL dregg WorldCell substrate");
    println!("═══════════════════════════════════════════════════════════════════\n");

    // A running chain of the keep world's real receipts (dice + narrated), collected in
    // order so we can prove they link pre == prev.post at the end.
    let mut chain: Vec<(String, TurnReceipt)> = Vec::new();

    // ── ACT I — the cross-cell gate (a GRAPH of real cells) ────────────────────────
    println!("── ACT I · The cross-cell gate (multicell: shore ▸ lantern ▸ stair) ──\n");
    let world = World::deploy();
    world.enter_shore().expect("enter the shore (room A)");
    println!("  entered the shore (room A) — a real cap-bounded turn");

    // Before the lantern is taken, room B's cross-cell gate is FAIL-CLOSED.
    let refused = world.open_stair_honest();
    println!(
        "  stair (room B) opened BEFORE taking the lantern → {}  (cross-cell gate fail-closed)",
        if refused.is_err() { "REFUSED" } else { "?!" }
    );
    assert!(refused.is_err(), "the cross-cell gate must refuse first");
    assert_eq!(
        world.read(world.stair(), DOOR_SLOT as usize),
        Some([0u8; 32])
    );

    // Take the lantern on its OWN cell — now its finalized commitment IS the gate root.
    let take = world
        .take_lantern()
        .expect("take the lantern on its own cell");
    println!(
        "  took the lantern (its OWN cell) → owner set; lantern now at the gate root  [turn {}…]",
        hex8(&take.turn_hash)
    );
    assert_eq!(
        world.read(world.lantern(), OWNER_SLOT as usize),
        Some(world.tag())
    );

    // The cross-cell gated open now COMMITS — its admission read ANOTHER cell's state.
    let open = world
        .open_stair_honest()
        .expect("with the peer item taken + witness, the gate opens");
    println!(
        "  stair (room B) opened AFTER → COMMITS  [turn {}…]  the way into the keep is open\n",
        hex8(&open.turn_hash)
    );
    assert_eq!(
        world.read(world.stair(), DOOR_SLOT as usize),
        Some(world.tag())
    );

    // ── ACT II — the keep: dice combat, then a narrated march to the hoard ─────────
    println!("── ACT II · The Warden's Keep (one WorldCell, a chaining receipt run) ──\n");
    let scene = keep_scene();
    let mut keep = deploy_keep(70);
    // Seed the fight/budget the KEEP intro passage would set at genesis (the direct
    // apply/narrate path drives the executor as sole referee, bypassing the intro
    // entry-effects — the same seeding the keep_tests do).
    keep.seed_var("hp", Value::Int(50));
    keep.seed_var("mana_budget", Value::Int(50));
    println!(
        "  the gate-warden bars the way — HP {}\n",
        keep.read_var("hp")
    );

    // Dice-rolled combat: each blow's damage is a real dregg-dice draw bound into the turn.
    let mut seq = 0u64;
    let mut combat: Vec<CombatReceipt> = Vec::new();
    while keep.read_var("hp") > 20 {
        let hp_before = keep.read_var("hp");
        let blow = strike(&keep, seq, COMBAT_DIE_SIDES).expect("a dice blow commits");
        let bd = bound_draw(&blow.receipt).expect("the draw is bound into the receipt");
        println!(
            "  🎲 blow {seq}: rolled d{COMBAT_DIE_SIDES} = {roll} → {dmg} damage · HP {hp_before} → {hp_after}  \
             [draw bound in receipt {th}…, roll={bound_roll}]",
            roll = blow.draw.roll,
            dmg = blow.draw.damage,
            hp_after = keep.read_var("hp"),
            th = hex8(&blow.receipt.turn_hash),
            bound_roll = bd.roll,
        );
        chain.push((format!("dice blow {seq}"), blow.receipt.clone()));
        combat.push(blow);
        seq += 1;
    }
    println!(
        "  the warden reels (HP {}) — press on\n",
        keep.read_var("hp")
    );

    // The narrated march to the hoard: a scripted Brain narrates each move; the WORLD
    // resolves the typed Command (prose is not power); each narration binds into its
    // real receipt. One narrated turn per keep story-beat, ending at the WIN.
    let mut brain = ScriptedBrain::new(vec![
        Narrated::new(
            Command::at(ROOM_GATEHALL, KP_PRESS_ON),
            "Bloodied but standing, you step over the reeling warden into the plundered hall.",
        ),
        Narrated::new(
            Command::at(ROOM_HALL, KP_CLAIM_RED),
            "You close your fist on the reliquary crown — the Red Hand claims it first.",
        ),
        Narrated::new(
            Command::at(ROOM_HALL, KP_DESCEND),
            "The collapsing stair groans and sheds stone as you descend into the sanctum.",
        ),
        Narrated::new(
            Command::at(ROOM_SANCTUM, KP_CAST_WARD),
            "You draw on your finite reserve of will and set the sealing ward alight.",
        ),
        Narrated::new(
            Command::at(ROOM_SANCTUM, KP_SEIZE),
            "The old wards fall quiet. You seize the sunken hoard — the keep is yours.",
        ),
    ]);

    for _ in 0..5 {
        let view = dungeon_on_dregg::narrator::scene_view(&keep, &scene);
        let proposal = brain.propose(&view);
        let r = narrate_turn(&keep, &scene, &proposal)
            .unwrap_or_else(|e| panic!("the narrated move {:?} commits: {e}", proposal.command));
        println!(
            "  📜 {room:>8}#{ch}: {narration}  [narration bound {nb}…]",
            room = proposal.command.room,
            ch = proposal.command.choice,
            narration = proposal.narration,
            nb = hex8(&bound_narration_commit(&r.receipt).expect("narration bound")),
        );
        chain.push((
            format!(
                "narrated {}#{}",
                proposal.command.room, proposal.command.choice
            ),
            r.receipt,
        ));
    }

    // ── WIN ────────────────────────────────────────────────────────────────────────
    let won = keep.read_passage().is_none() && keep.read_var("gold") == 500;
    println!(
        "\n  ⇒ WIN: scene ended = {}, gold = {}, crown = Red({}), depth = {}, mana spent = {}",
        keep.read_passage().is_none(),
        keep.read_var("gold"),
        keep.read_var("relic_owner"),
        keep.read_var("depth"),
        keep.read_var("mana_spent"),
    );
    assert!(won, "the universe reached a real WIN state");

    // ── The receipts are REAL and CHAIN (pre == prev.post), and the dice REPRODUCE ──
    println!("\n── Verification (O(N) replay — honest scope below) ──\n");
    for pair in chain.windows(2) {
        let (label_prev, prev) = &pair[0];
        let (label, cur) = &pair[1];
        assert_eq!(
            cur.pre_state_hash, prev.post_state_hash,
            "receipt chain broke: `{label}`.pre != `{label_prev}`.post"
        );
        assert_ne!(cur.turn_hash, [0u8; 32]);
    }
    println!(
        "  ✓ keep receipt chain links: {} real turns, each pre == prev.post",
        chain.len()
    );

    for blow in &combat {
        let rederived = reverify_draw(blow).expect("each dice draw REPRODUCES on replay");
        assert_eq!(rederived, blow.draw.roll);
    }
    println!(
        "  ✓ every dice draw REPRODUCES on replay ({} blows re-derived to the same roll)",
        combat.len()
    );

    // The forged-roll tooth is real: rewrite a bound roll and watch replay catch it.
    let mut forged = combat[0].clone();
    let topic = dregg_app_framework::symbol(dungeon_on_dregg::dice_combat::DICE_TOPIC);
    if let Some(ev) = forged
        .receipt
        .emitted_events
        .iter_mut()
        .find(|e| e.topic == topic)
    {
        ev.data[2] = dregg_app_framework::field_from_u64(1);
        ev.data[3] = dregg_app_framework::field_from_u64(1);
        forged.draw.roll = 1;
        forged.draw.damage = 1;
    }
    match reverify_draw(&forged) {
        Err(e) => println!("  ✓ a forged (gentler) roll is CAUGHT on replay — {e}"),
        Ok(_) => panic!("a forged roll must be caught"),
    }

    println!("\n── Honest scope ──");
    println!("  • verification is O(N) reverify_draw + verify_chain_linkage (replay), NOT a");
    println!("    succinct light client (that is a separate, Lane-D-gated workstream).");
    println!("  • the dice source here is the reproducible `Deterministic` one; the");
    println!("    non-grindable `ServerVrf`/`Hybrid` (LB-VRF + drand-BLS) sources exist in");
    println!("    dregg-dice and wiring their evidence into this binding is a named follow-up.");
    println!("  • the confined `deos-hermes` LLM jail is out of scope for this example.");
    println!("\n  Everything above is a REAL turn on the real WorldCell/executor substrate.");
}
