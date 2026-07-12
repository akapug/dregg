//! Driving tests for procgen-dregg: the committed-seed pipeline PARSES + VALIDATES
//! through the real `attested_dm` DSL, is byte-identical on re-generation, and is
//! non-vacuous (a different seed yields a different dungeon).

use attested_dm::{GameSession, GameStatus, PlayResult, Severity, parse_dungeon, validate};
use procgen_dregg::{
    CommittedSeed, DRAW_COUNT, MAX_ROOMS, MIN_ROOMS, daily_seed, dungeon_request, generate,
    regenerate, verify_generation,
};

fn seed(byte: u8) -> CommittedSeed {
    CommittedSeed::from_bytes([byte; 32])
}

/// A distinct seed for every index in 0..256, so the variety sweeps below draw from
/// genuinely different committed values (not just the 0-byte-repeat family).
fn seed_n(n: u32) -> CommittedSeed {
    let mut b = [0u8; 32];
    b[..4].copy_from_slice(&n.to_le_bytes());
    b[4] = (n % 251) as u8;
    b[16] = (n.wrapping_mul(2654435761) & 0xff) as u8;
    CommittedSeed::from_bytes(b)
}

/// A generated dungeon PARSES and VALIDATES with zero errors through the shipped
/// attested-dm engine — a first-class, sound, playable dungeon.
#[test]
fn generated_dungeon_parses_and_validates() {
    for b in 0u8..40 {
        let dungeon = generate(&seed(b));
        // fail-closed parse: refuses dangling exits, unreachable objectives, …
        let world = parse_dungeon(&dungeon.source).unwrap_or_else(|e| {
            panic!(
                "seed {b}: generated dungeon failed to parse: {e}\n---\n{}",
                dungeon.source
            )
        });
        // and validate() reports NO errors (belt-and-suspenders over parse_dungeon).
        let issues = validate(&world);
        let errors: Vec<_> = issues
            .iter()
            .filter(|i| i.severity == Severity::Error)
            .collect();
        assert!(
            errors.is_empty(),
            "seed {b}: validator errors: {errors:?}\n---\n{}",
            dungeon.source
        );

        assert!(dungeon.room_count >= MIN_ROOMS && dungeon.room_count <= MAX_ROOMS);
        // The world has at least one gated exit (the DSL keyword `requires`).
        assert!(
            dungeon.source.contains("requires item"),
            "seed {b}: no gated exit emitted"
        );
    }
}

/// Reproducibility: the SAME committed seed yields byte-identical output.
#[test]
fn same_seed_is_byte_identical() {
    for b in [0u8, 7, 42, 200, 255] {
        let a = generate(&seed(b)).source;
        let c = regenerate(&seed(b));
        assert_eq!(a, c, "seed {b}: re-generation diverged");
    }
}

/// Non-vacuity: DIFFERENT seeds yield DIFFERENT dungeons (the generator actually
/// consumes the draw stream). If they were all identical, the reproducibility
/// test above would be meaningless.
#[test]
fn different_seeds_differ() {
    let a = generate(&seed(1)).source;
    let b = generate(&seed(2)).source;
    let c = generate(&seed(99)).source;
    assert_ne!(a, b);
    assert_ne!(a, c);
    assert_ne!(b, c);

    // A broad spread: across many seeds we see genuine variety, not two outputs.
    use std::collections::BTreeSet;
    let distinct: BTreeSet<String> = (0u8..60).map(|x| generate(&seed(x)).source).collect();
    assert!(
        distinct.len() > 20,
        "too little variety: {} distinct of 60",
        distinct.len()
    );
}

/// The seed commitment binds the dungeon: a verifier who holds the committed seed
/// and the evidence re-derives the seed through the pure dregg-dice verifier,
/// re-generates, and confirms byte-identity. A wrong seed is rejected.
#[test]
fn committed_seed_binds_the_dungeon() {
    let s = seed(123);
    let dungeon = generate(&s);
    assert!(
        verify_generation(&s, &dungeon.evidence, &dungeon.source),
        "honest dungeon must verify against its committed seed"
    );
    // A different seed's evidence must NOT verify this source.
    let other = generate(&seed(124));
    assert!(
        !verify_generation(&s, &other.evidence, &dungeon.source) || other.source == dungeon.source,
        "evidence from a different seed must not verify this source"
    );
    // And the honest source is NOT the honest source for a different seed.
    assert!(!verify_generation(
        &seed(124),
        &dungeon.evidence,
        &dungeon.source
    ));
}

/// The request commitment is the receipt-shaped value published BEFORE generation,
/// and it is stable for a given seed and moves for a different one.
#[test]
fn request_commitment_is_stable_and_binding() {
    let c1 = dungeon_request(&seed(5)).commitment();
    let c1b = dungeon_request(&seed(5)).commitment();
    let c2 = dungeon_request(&seed(6)).commitment();
    assert_eq!(c1, c1b);
    assert_ne!(c1, c2);
    // The transcript commitment likewise binds every draw.
    let d = generate(&seed(5));
    assert_eq!(
        d.transcript_commitment(),
        d.evidence.draw_transcript_commitment
    );
}

/// The draw stream is the REAL dregg-dice reject-free unbiased one: the fixed
/// DRAW_COUNT is bound into the request, and every legal index is drawable while
/// an out-of-range index is refused (not silently reused).
#[test]
fn draws_are_the_real_dregg_dice_stream() {
    let s = seed(77);
    let req = dungeon_request(&s);
    assert_eq!(req.draw_count, DRAW_COUNT);

    // Reconstruct the verified stream and exercise the bounded, reject-free draw.
    let (_, _, stream) = procgen_dregg::verified_stream(&s);
    assert_eq!(stream.draw_count(), DRAW_COUNT);
    // Every legal index yields a bounded value; the boundary index is refused.
    for i in 0..DRAW_COUNT {
        let v = stream.draw_bounded(i, 20).expect("legal index");
        assert!(v < 20);
    }
    assert!(
        stream.draw_bounded(DRAW_COUNT, 20).is_err(),
        "out-of-range draw must be refused"
    );
    // A 1-based die is in range.
    let d20 = stream.draw_die(0, 20).unwrap();
    assert!((1..=20).contains(&d20));
}

/// The daily-seed helper: a committed epoch value yields a stable seed, and
/// distinct epochs yield distinct dungeons ("a new fair dungeon every day").
#[test]
fn daily_seed_gives_a_fresh_dungeon_per_epoch() {
    let epoch_a = [0xA5u8; 32];
    let epoch_b = [0xB6u8; 32];
    let s_a = daily_seed(&epoch_a);
    let s_a2 = daily_seed(&epoch_a);
    let s_b = daily_seed(&epoch_b);
    assert_eq!(s_a, s_a2, "same epoch -> same seed");
    assert_ne!(s_a, s_b, "different epoch -> different seed");

    let day_a = generate(&s_a);
    let day_b = generate(&s_b);
    parse_dungeon(&day_a.source).expect("daily dungeon A parses");
    parse_dungeon(&day_b.source).expect("daily dungeon B parses");
    assert_ne!(day_a.source, day_b.source, "a new day is a new dungeon");
    // Reproducible: re-derive the same day's dungeon from the same epoch.
    assert_eq!(day_a.source, generate(&daily_seed(&epoch_a)).source);
}

// ─────────────────────────────────────────────────────────────────────────────
// DRIVING THE RICHER GENERATION — biomes, layouts, encounters, loot, npc, spells.
// Every enrichment is a fixed indexed draw, so the whole richer world stays
// seed-deterministic + verifiable, and existing tests above stay green.
// ─────────────────────────────────────────────────────────────────────────────

/// The FULL enriched world stays SOUND: a wide seed sweep parses AND validates with
/// zero errors through the shipped engine — every drawn biome, layout, encounter,
/// consumable, npc, and spell is a first-class, valid `.dungeon` construct.
#[test]
fn richer_generation_parses_and_validates_across_a_wide_sweep() {
    for n in 0u32..200 {
        let d = generate(&seed_n(n));
        let world = parse_dungeon(&d.source).unwrap_or_else(|e| {
            panic!(
                "seed {n}: enriched dungeon failed to parse: {e}\n---\n{}",
                d.source
            )
        });
        let errors: Vec<_> = validate(&world)
            .into_iter()
            .filter(|i| i.severity == Severity::Error)
            .collect();
        assert!(
            errors.is_empty(),
            "seed {n}: validator errors on enriched world: {errors:?}\n---\n{}",
            d.source
        );
        // The gate that isolates the objective is still emitted.
        assert!(
            d.source.contains("requires item"),
            "seed {n}: no gated exit"
        );
        // A boss always guards the gated approach.
        assert!(d.source.contains("combat "), "seed {n}: no boss encounter");
    }
}

/// All four LAYOUT SHAPES actually appear across seeds (real structural variety),
/// and each is a valid, connected, winnable-shaped world.
#[test]
fn every_layout_shape_appears() {
    use std::collections::BTreeSet;
    let mut shapes: BTreeSet<String> = BTreeSet::new();
    for n in 0u32..200 {
        let src = generate(&seed_n(n)).source;
        for line in src.lines() {
            if let Some(rest) = line.strip_prefix("# biome:") {
                if let Some(l) = rest.split("layout:").nth(1) {
                    let label = l.split('|').next().unwrap_or("").trim().to_string();
                    shapes.insert(label);
                }
            }
        }
    }
    for want in ["sprawl", "corridor", "hub", "branch"] {
        assert!(
            shapes.contains(want),
            "layout `{want}` never appeared across the sweep; saw {shapes:?}"
        );
    }
}

/// All six BIOMES appear across seeds — the thematic variety is real, not a single
/// family dressed up.
#[test]
fn all_biomes_appear() {
    use std::collections::BTreeSet;
    let mut names: BTreeSet<String> = BTreeSet::new();
    for n in 0u32..256 {
        for line in generate(&seed_n(n)).source.lines() {
            if let Some(rest) = line.strip_prefix("name: ") {
                names.insert(rest.trim().to_string());
            }
        }
    }
    for want in [
        "The Sunken Vault",
        "The Clockwork Orchard",
        "The Ember Observatory",
        "The Venom Warren",
        "The Frost Cathedral",
        "The Obsidian Reach",
    ] {
        assert!(
            names.contains(want),
            "biome `{want}` never appeared; saw {names:?}"
        );
    }
}

/// ENCOUNTERS + LOOT + FEATURES are genuinely drawn: across the sweep we see roaming
/// guardians, healing draughts, the biome hazard (status + tainted cache + antidote),
/// hazard-off worlds, lore NPCs, and blessing shrines — none of them universal, all
/// of them present.
#[test]
fn encounters_loot_and_features_are_real_and_varied() {
    let mut hostiles = 0; // roaming guardians (not the boss)
    let mut potions = 0;
    let mut statuses = 0; // biome hazard live
    let mut hazard_off = 0;
    let mut traps = 0;
    let mut antidotes = 0;
    let mut npcs = 0;
    let mut spells = 0;
    for n in 0u32..256 {
        let src = generate(&seed_n(n)).source;
        if src.contains("\nhostile ") {
            hostiles += 1;
        }
        if src.contains("consumable ") && src.contains("-> heal ") {
            potions += 1;
        }
        if src.lines().any(|l| l.starts_with("status ")) {
            statuses += 1;
        }
        if src.contains("hazard: off") {
            hazard_off += 1;
        }
        if src.contains("-> status ") {
            traps += 1;
        }
        if src.contains("-> cure ") {
            antidotes += 1;
        }
        if src.contains("\nnpc ") {
            npcs += 1;
        }
        if src.lines().any(|l| l.starts_with("spell ")) {
            spells += 1;
        }
    }
    // Each feature appears in a healthy fraction — real, and not on every seed.
    assert!(
        hostiles > 40,
        "too few roaming-guardian worlds: {hostiles}/256"
    );
    assert!(
        potions > 40,
        "too few healing-draught worlds: {potions}/256"
    );
    assert!(statuses > 80, "too few hazard-live worlds: {statuses}/256");
    assert!(hazard_off > 20, "hazard is never off: {hazard_off}/256");
    assert!(traps > 20, "tainted caches never appear: {traps}/256");
    assert!(antidotes > 20, "antidotes never appear: {antidotes}/256");
    assert!(
        npcs > 20 && npcs < 236,
        "lore NPCs absent or universal: {npcs}/256"
    );
    assert!(
        spells > 20 && spells < 236,
        "blessing shrines absent or universal: {spells}/256"
    );
}

/// Distinct ROOM-TYPE NAMES abound: the archetype draw (naming style + role word)
/// layered over each biome's adjectives/nouns yields a large, varied namespace of
/// room types — not four repeated names.
#[test]
fn many_distinct_room_type_names_appear() {
    use std::collections::BTreeSet;
    let mut names: BTreeSet<String> = BTreeSet::new();
    for n in 0u32..200 {
        for line in generate(&seed_n(n)).source.lines() {
            let t = line.trim_start();
            if let Some(rest) = t.strip_prefix("room room") {
                if let Some(q1) = rest.find('"') {
                    if let Some(q2) = rest[q1 + 1..].find('"') {
                        names.insert(rest[q1 + 1..q1 + 1 + q2].to_string());
                    }
                }
            }
        }
    }
    assert!(
        names.len() > 120,
        "too few distinct room-type names: {} (variety is thin)",
        names.len()
    );
}

/// DETERMINISM across the wide sweep: every seed regenerates byte-for-byte, and the
/// enriched output is stable across repeated generation.
#[test]
fn richer_generation_is_deterministic_across_the_sweep() {
    for n in 0u32..200 {
        let s = seed_n(n);
        let a = generate(&s).source;
        let b = regenerate(&s);
        let c = generate(&s).source;
        assert_eq!(a, b, "seed {n}: regenerate diverged");
        assert_eq!(a, c, "seed {n}: repeated generate diverged");
    }
}

/// VERIFIABILITY of the enriched output: the honest source verifies against its
/// committed seed, ANY single-byte tamper of the source is caught, and a different
/// seed's evidence does not verify this source.
#[test]
fn tampered_enriched_source_is_caught() {
    for n in [3u32, 17, 42, 99, 150] {
        let s = seed_n(n);
        let d = generate(&s);
        assert!(
            verify_generation(&s, &d.evidence, &d.source),
            "seed {n}: honest enriched source must verify"
        );

        // Flip one byte somewhere in the body → verification must fail.
        let mut bytes = d.source.clone().into_bytes();
        let mid = bytes.len() / 2;
        // pick a position on an ASCII letter to keep it valid utf8 + meaningful.
        let pos = (mid..bytes.len())
            .find(|&i| bytes[i].is_ascii_alphabetic())
            .unwrap_or(mid);
        bytes[pos] ^= 0x20; // flip letter case
        let tampered = String::from_utf8(bytes).unwrap();
        assert_ne!(
            tampered, d.source,
            "seed {n}: tamper must change the source"
        );
        assert!(
            !verify_generation(&s, &d.evidence, &tampered),
            "seed {n}: a tampered enriched source must NOT verify"
        );

        // A different seed's evidence must not verify this source.
        let other = generate(&seed_n(n + 1000));
        assert!(
            !verify_generation(&s, &other.evidence, &d.source),
            "seed {n}: another seed's evidence must not verify this source"
        );
    }
}

/// The enriched world is a FIRST-CLASS engine world, not just parser-clean: it opens
/// in the real `GameSession`, plays a legal move, and its receipt chain verifies —
/// so combat blocks, consumables, NPCs, and spells are all engine-accepted.
#[test]
fn a_generated_enriched_world_opens_plays_and_verifies() {
    for n in [1u32, 8, 40, 77, 201] {
        let d = generate(&seed_n(n));
        let world = parse_dungeon(&d.source).expect("enriched world parses");
        // room0 always has an ungated exit to room1 (room1's parent is always 0).
        let dir = d
            .source
            .lines()
            .find_map(|l| {
                let t = l.trim_start();
                let parts: Vec<&str> = t.split_whitespace().collect();
                if parts.len() >= 4 && parts[0] == "exit" && parts[2] == "->" && parts[3] == "room1"
                {
                    Some(parts[1].to_string())
                } else {
                    None
                }
            })
            .expect("room0 has an exit to room1");

        let mut game = GameSession::open(world);
        match game.command("hero", &format!("go {dir}")) {
            PlayResult::Landed { .. } => {}
            other => panic!("seed {n}: legal move `go {dir}` from start should land: {other:?}"),
        }
        assert_eq!(
            game.status(),
            GameStatus::Playing,
            "seed {n}: still playable"
        );
        game.verify().unwrap_or_else(|e| {
            panic!("seed {n}: enriched world's receipt chain must verify: {e:?}")
        });
    }
}
