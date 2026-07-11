//! DRIVE the richer dungeon — "The Warden's Keep" — on the REAL dregg executor and
//! PRINT the proof for each mechanic:
//!   * the installed tooth is a real `StateConstraint` case (printed verbatim);
//!   * a LEGAL move lands a real `TurnReceipt` (turn/pre/post hashes printed);
//!   * an ILLEGAL move (killing blow / rival second claim / overspend / climb-back /
//!     heap re-claim) is a REAL executor refusal — reason printed verbatim — that
//!     commits NOTHING (the cell field is shown unchanged afterward).
//!
//! Run:  cargo run -p dungeon-on-dregg --example keep

use dungeon_on_dregg::{
    CROWN_HEAP_KEY, KP_CAST_WARD, KP_CLAIM_BLUE, KP_CLAIM_RED, KP_CLIMB_BACK, KP_DESCEND,
    KP_TRADE_BLOWS, ROOM_GATEHALL, ROOM_HALL, ROOM_SANCTUM, STASH_METHOD, case_constraints,
    choice_at, deploy_keep, keep_compiled, keep_scene, stash_effect,
};
use spween_dregg::{Value, choice_method};

fn hx(b: &[u8; 32]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect::<String>()
}

fn main() {
    let s = keep_scene();
    let story = keep_compiled();

    println!("=== THE WARDEN'S KEEP — richer game mechanics on the REAL dregg executor ===\n");
    println!("world-cell slot layout (dungeon state on real cell fields):");
    println!("  passage(room) -> slot 0");
    let mut slots: Vec<_> = story.var_slots.iter().collect();
    slots.sort_by_key(|(_, s)| **s);
    for (name, slot) in slots {
        println!("  {name:<12} -> slot {slot}");
    }
    println!();

    // ── #1 combat HP floor — a compiler-emitted FieldGte(hp, 1) ────────────────────
    println!("--- #1 COMBAT HP FLOOR (FieldGte, `hp` slot) ---");
    println!(
        "installed tooth on trade-blows: {:?}",
        case_constraints(&story, &choice_method(ROOM_GATEHALL, KP_TRADE_BLOWS))
    );
    let mut world = deploy_keep(1);
    world.seed_var("hp", Value::Int(50));
    let blow = choice_at(&s, ROOM_GATEHALL, KP_TRADE_BLOWS);
    for _ in 0..2 {
        let r = world
            .apply_choice(ROOM_GATEHALL, KP_TRADE_BLOWS, &blow)
            .expect("survivable blow");
        println!(
            "  LEGAL blow  -> hp={:<3} receipt turn={} pre={} post={}",
            world.read_var("hp"),
            &hx(&r.turn_hash)[..16],
            &hx(&r.pre_state_hash)[..16],
            &hx(&r.post_state_hash)[..16],
        );
    }
    match world.apply_choice(ROOM_GATEHALL, KP_TRADE_BLOWS, &blow) {
        Err(e) => println!("  ILLEGAL killing blow REFUSED: {e}"),
        Ok(_) => println!("  !! killing blow unexpectedly committed"),
    }
    println!(
        "  anti-ghost: hp still {} (nothing committed)\n",
        world.read_var("hp")
    );

    // ── #2 loot / first-grabber-wins — WriteOnce(relic_owner) ──────────────────────
    println!("--- #2 LOOT / FIRST-GRABBER-WINS (WriteOnce, `relic_owner` slot) ---");
    println!(
        "installed tooth on claim-red: {:?}",
        case_constraints(&story, &choice_method(ROOM_HALL, KP_CLAIM_RED))
    );
    let world = deploy_keep(2);
    let claim_red = choice_at(&s, ROOM_HALL, KP_CLAIM_RED);
    let claim_blue = choice_at(&s, ROOM_HALL, KP_CLAIM_BLUE);
    let r = world
        .apply_choice(ROOM_HALL, KP_CLAIM_RED, &claim_red)
        .expect("first claim");
    println!(
        "  LEGAL Red claim  -> relic_owner={} receipt turn={}",
        world.read_var("relic_owner"),
        &hx(&r.turn_hash)[..16]
    );
    match world.apply_choice(ROOM_HALL, KP_CLAIM_BLUE, &claim_blue) {
        Err(e) => println!("  ILLEGAL Blue re-claim REFUSED: {e}"),
        Ok(_) => println!("  !! rival claim unexpectedly committed"),
    }
    println!(
        "  anti-ghost: relic_owner still {} (Red keeps the crown)\n",
        world.read_var("relic_owner")
    );

    // ── #3 spell mana budget — FieldLteField(mana_spent, mana_budget) ──────────────
    println!("--- #3 SPELL MANA BUDGET (FieldLteField, `mana_spent` <= `mana_budget`) ---");
    println!(
        "installed tooth on cast-ward: {:?}",
        case_constraints(&story, &choice_method(ROOM_SANCTUM, KP_CAST_WARD))
    );
    let mut world = deploy_keep(3);
    world.seed_var("mana_budget", Value::Int(50));
    let ward = choice_at(&s, ROOM_SANCTUM, KP_CAST_WARD);
    let r = world
        .apply_choice(ROOM_SANCTUM, KP_CAST_WARD, &ward)
        .expect("first ward");
    println!(
        "  LEGAL ward (30<=50) -> mana_spent={} receipt turn={}",
        world.read_var("mana_spent"),
        &hx(&r.turn_hash)[..16]
    );
    match world.apply_choice(ROOM_SANCTUM, KP_CAST_WARD, &ward) {
        Err(e) => println!("  ILLEGAL ward (60>50) REFUSED: {e}"),
        Ok(_) => println!("  !! overspend unexpectedly committed"),
    }
    println!(
        "  anti-ghost: mana_spent still {} (no will spent)\n",
        world.read_var("mana_spent")
    );

    // ── #4 one-way descent ratchet — Monotonic(depth) ──────────────────────────────
    println!("--- #4 ONE-WAY DESCENT RATCHET (Monotonic, `depth` slot) ---");
    let world = deploy_keep(4);
    let descend = choice_at(&s, ROOM_HALL, KP_DESCEND);
    let climb = choice_at(&s, ROOM_SANCTUM, KP_CLIMB_BACK);
    let r = world
        .apply_choice(ROOM_HALL, KP_DESCEND, &descend)
        .expect("descend");
    println!(
        "  LEGAL descend (0->1) -> depth={} receipt turn={}",
        world.read_var("depth"),
        &hx(&r.turn_hash)[..16]
    );
    match world.apply_choice(ROOM_SANCTUM, KP_CLIMB_BACK, &climb) {
        Err(e) => println!("  ILLEGAL climb-back (1->0) REFUSED: {e}"),
        Ok(_) => println!("  !! climb-back unexpectedly committed"),
    }
    println!(
        "  anti-ghost: depth still {} (one-way)\n",
        world.read_var("depth")
    );

    // ── #5 heap-keyed inventory — HeapField WriteOnce, collection > 16 slots ────────
    println!("--- #5 HEAP-KEYED INVENTORY (HeapField WriteOnce, keys >= 16) ---");
    println!(
        "installed tooth on `{STASH_METHOD}`: {:?}",
        case_constraints(&story, STASH_METHOD)
    );
    let world = deploy_keep(5);
    let cell = world.cell_id();
    let r = world
        .apply_raw(STASH_METHOD, vec![stash_effect(cell, CROWN_HEAP_KEY, 1)])
        .expect("first crown stash");
    println!(
        "  LEGAL crown stash -> heap[{CROWN_HEAP_KEY}]={:?} receipt turn={}",
        world.read_heap(CROWN_HEAP_KEY),
        &hx(&r.turn_hash)[..16]
    );
    for k in 16u64..36 {
        world
            .apply_raw(STASH_METHOD, vec![stash_effect(cell, k, 1)])
            .expect("stash overflow item");
    }
    println!("  stashed 20 more items into heap keys 16..36 (beyond the 15 usable register slots)");
    match world.apply_raw(STASH_METHOD, vec![stash_effect(cell, CROWN_HEAP_KEY, 2)]) {
        Err(e) => println!("  ILLEGAL crown re-claim REFUSED: {e}"),
        Ok(_) => println!("  !! heap re-claim unexpectedly committed"),
    }
    println!(
        "  anti-ghost: heap[{CROWN_HEAP_KEY}] still {:?}\n",
        world.read_heap(CROWN_HEAP_KEY)
    );

    println!("=== every tooth above is a real StateConstraint the EmbeddedExecutor re-checks; ===");
    println!("=== a legal move lands a real TurnReceipt, an illegal move commits NOTHING.     ===");
}
