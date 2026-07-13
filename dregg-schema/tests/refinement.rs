//! Refinement by TRANSLATION VALIDATION on the real executor: the emitted
//! `CellProgram` admits EXACTLY the declared-component moves. Driven per archetype (a
//! legal move commits; each illegal move is Refused), then a schema-declared game plays
//! a real verified turn chain that re-verifies by deterministic replay.

use dregg_schema::{SchemaGame, descent_schema};

// The seeded baseline every refinement case starts from.
const HP: u64 = 20;
const FLOOR: u64 = 5;
const GOLD: u64 = 10;
const OWNER: u64 = 1000;
const SHIELD: u64 = 5;
const ITEMS: u64 = 3;

/// Deploy the descent schema on a real WorldCell and seed a known baseline (the
/// permissive genesis turn). Returns the deployed game ready for `move_()` turns.
fn fresh(seed: u8) -> SchemaGame {
    let game = SchemaGame::deploy(descent_schema(), seed).expect("deploy");
    game.seed()
        .set("hp", HP)
        .set("floor", FLOOR)
        .set("gold", GOLD)
        .set("owner", OWNER)
        .set("shield", SHIELD)
        .set("items", ITEMS)
        .commit()
        .expect("genesis seed commits");
    // The seed landed and reads back.
    assert_eq!(game.get("hp"), Some(HP));
    assert_eq!(game.get("items"), Some(ITEMS));
    game
}

#[test]
fn stat_upper_bound_refines() {
    let game = fresh(1);
    // Legal: within [0, 20].
    game.move_().set("hp", 15).commit().expect("hp=15 commits");
    assert_eq!(game.get("hp"), Some(15));
    // Illegal: over the cap → FieldLte bites → Refused, nothing commits.
    let err = game.move_().set("hp", 21).commit().unwrap_err();
    assert!(
        matches!(err, dregg_schema::GameError::World(_)),
        "got {err}"
    );
    assert_eq!(game.get("hp"), Some(15), "refused move must not commit");
}

#[test]
fn stat_lower_bound_refines() {
    let game = fresh(2);
    // Legal: floor stays within [1, 99].
    game.move_()
        .set("floor", 6)
        .commit()
        .expect("floor=6 commits");
    assert_eq!(game.get("floor"), Some(6));
    // Illegal: below the floor min (1) → FieldGte bites → Refused.
    let err = game.move_().set("floor", 0).commit().unwrap_err();
    assert!(
        matches!(err, dregg_schema::GameError::World(_)),
        "got {err}"
    );
    assert_eq!(game.get("floor"), Some(6));
}

#[test]
fn resource_monotonicity_refines() {
    let game = fresh(3);
    // Legal: a resource only accrues.
    game.move_()
        .set("gold", 25)
        .commit()
        .expect("gold up commits");
    assert_eq!(game.get("gold"), Some(25));
    // Illegal: a decrease → Monotonic bites → Refused.
    let err = game.move_().set("gold", 20).commit().unwrap_err();
    assert!(
        matches!(err, dregg_schema::GameError::World(_)),
        "got {err}"
    );
    assert_eq!(game.get("gold"), Some(25));
}

#[test]
fn identity_write_once_refines() {
    let game = fresh(4);
    // Legal: a move that leaves the identity unchanged commits.
    game.move_()
        .set("gold", 11)
        .commit()
        .expect("non-owner move commits");
    assert_eq!(game.get("owner"), Some(OWNER));
    // Legal: re-writing the SAME value is not a change.
    game.move_()
        .set("owner", OWNER)
        .commit()
        .expect("owner=same commits");
    // Illegal: rewriting a set identity to a new value → WriteOnce bites → Refused.
    let err = game.move_().set("owner", 2000).commit().unwrap_err();
    assert!(
        matches!(err, dregg_schema::GameError::World(_)),
        "got {err}"
    );
    assert_eq!(game.get("owner"), Some(OWNER));
}

#[test]
fn cross_field_invariant_refines() {
    let game = fresh(5);
    // Legal: shield <= hp (5 -> 20, hp is 20).
    game.move_()
        .set("shield", 20)
        .commit()
        .expect("shield<=hp commits");
    assert_eq!(game.get("shield"), Some(20));
    // Illegal: shield > hp → FieldLteOther bites → Refused.
    let err = game.move_().set("shield", 21).commit().unwrap_err();
    assert!(
        matches!(err, dregg_schema::GameError::World(_)),
        "got {err}"
    );
    assert_eq!(game.get("shield"), Some(20));
}

#[test]
fn collection_monotonicity_refines() {
    let game = fresh(6);
    // Legal: the heap-keyed collection counter grows.
    game.move_()
        .set("items", 7)
        .commit()
        .expect("items up commits");
    assert_eq!(game.get("items"), Some(7));
    // Illegal: a shrink → HeapField Monotonic bites → Refused.
    let err = game.move_().set("items", 2).commit().unwrap_err();
    assert!(
        matches!(err, dregg_schema::GameError::World(_)),
        "got {err}"
    );
    assert_eq!(game.get("items"), Some(7));
}

#[test]
fn a_combined_legal_move_commits() {
    let game = fresh(7);
    // A single turn touching several components at once, all invariants respected.
    game.move_()
        .set("hp", 14)
        .set("gold", 12)
        .set("shield", 10) // 10 <= 14
        .set("floor", 6)
        .set("items", 5)
        .commit()
        .expect("combined legal move commits");
    assert_eq!(game.get("hp"), Some(14));
    assert_eq!(game.get("gold"), Some(12));
    assert_eq!(game.get("shield"), Some(10));
    assert_eq!(game.get("floor"), Some(6));
    assert_eq!(game.get("items"), Some(5));

    // A single turn with ONE violated invariant refuses the WHOLE turn (all-or-nothing).
    let err = game
        .move_()
        .set("gold", 20) // fine
        .set("shield", 99) // 99 > hp(14): the whole turn is refused
        .commit()
        .unwrap_err();
    assert!(
        matches!(err, dregg_schema::GameError::World(_)),
        "got {err}"
    );
    assert_eq!(
        game.get("gold"),
        Some(12),
        "the fine write must not commit either"
    );
    assert_eq!(game.get("shield"), Some(10));
}

/// A schema-declared game plays a real verified turn chain and re-verifies by
/// deterministic replay (a fresh, identically-seeded deploy reproduces the exact
/// committed state — the "verify holds" property).
#[test]
fn descent_plays_a_verified_turn_chain() {
    // The move script: (component, value) per turn. Baseline is hp=20, gold=10,
    // shield=5, floor=5, items=3 (see `fresh`). Stats may move within bounds; the
    // resource (gold) and collection (items) only accrue; the shield stays <= hp.
    let script: &[(&str, u64)] = &[
        ("hp", 14),    // take damage (stat, may decrease)
        ("gold", 15),  // find gold (resource, up from 10)
        ("shield", 8), // raise the shield (<= hp)
        ("floor", 6),  // descend (stat)
        ("items", 4),  // pick up items (collection, up from 3)
        ("gold", 19),  // more gold (up)
        ("hp", 10),    // more damage — stays >= shield (8), invariant holds
        ("items", 7),  // collect more (up)
    ];

    let play = |seed: u8| -> (Vec<u64>, Option<u64>) {
        let game = fresh(seed);
        for (comp, val) in script {
            game.move_()
                .set(comp, *val)
                .commit()
                .unwrap_or_else(|e| panic!("chain move {comp}={val} refused: {e}"));
        }
        // Final reads reflect the whole chain.
        assert_eq!(game.get("hp"), Some(10));
        assert_eq!(game.get("gold"), Some(19));
        assert_eq!(game.get("shield"), Some(8));
        assert_eq!(game.get("floor"), Some(6));
        assert_eq!(game.get("owner"), Some(OWNER));
        assert_eq!(game.get("items"), Some(7));
        (game.snapshot(), game.get("items"))
    };

    // Deterministic replay: same schema + seed + script ⇒ identical committed state.
    let (snap_a, items_a) = play(42);
    let (snap_b, items_b) = play(42);
    assert_eq!(snap_a, snap_b, "replay reproduces the exact register state");
    assert_eq!(items_a, items_b, "replay reproduces the heap collection");
}
