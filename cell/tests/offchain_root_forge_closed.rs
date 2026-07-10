//! **THE OFF-CHAIN LANE-0 FORGE IS CLOSED — heap_root, fields_root, cap_root.**
//!
//! The soundness bug this pins: the per-cell off-chain artifacts (the BLAKE3
//! whole-cell state commitment `compute_canonical_state_commitment`, and the
//! `cell.state.heap_root` / `cell.state.fields_root` registers a ledgerless
//! verifier compares) used to encode each map-root as its ~31-bit LANE-0 felt
//! (`babybear_to_bytes32` / `felt_to_bytes32` — 4 bytes of ONE BabyBear felt,
//! the rest zero). The in-circuit binding was ALREADY faithful (the rotated
//! `heap_root`/`fields_root`/`cap_root` column groups carry the full 8-felt
//! `node8` root, GENTIAN-welded), but the OFF-CHAIN copy was a lane-0 projection:
//! two GENUINELY-DIFFERENT states colliding on lane 0 produced the SAME off-chain
//! root and the SAME commitment — a forge a ledgerless verifier could not detect.
//!
//! The fix widens the off-chain encoding to the FAITHFUL 8-felt packing
//! (`digest8_to_bytes32` — lane `i` in bytes `[4i..4i+4]`, ~124-bit), the SAME
//! value the circuit binds. bytes `[0..4]` still equal the historical lane-0
//! projection, so a lane-0 COLLISION is still visible here — but the completion
//! lanes 1..7 (bytes `[4..32]`) now SEPARATE the two states, off-chain, with no
//! ledger and no STARK to consult.
//!
//! Each pinned pair below was found by the `#[ignore]`d birthday generator at the
//! bottom (the CELL's own producers, folding through `fold_bytes32` /
//! `cap_ref_to_leaf`, so the collision is faithful to the deployed leaf shape).
//! Regenerate with:
//!   cargo test -p dregg-cell --test offchain_root_forge_closed -- --ignored --nocapture

use std::collections::BTreeMap;

use dregg_cell::state::{compute_fields_root, compute_heap_root};
use dregg_cell::{
    AuthRequired, CapabilitySet, Cell, CellId, compute_canonical_capability_root,
    compute_canonical_capability_root_wide, compute_canonical_state_commitment,
};

// The one fixed 32-byte value stored at the colliding address / field (the forge
// axis is the KEY, not the value — two genuinely-different states are "value V at
// address A" vs "value V at address B").
const FORGE_VALUE: [u8; 32] = [0xAB; 32];
const CELL_KEY: [u8; 32] = [0x11; 32];
const CELL_TOKEN: [u8; 32] = [0x22; 32];
const CAP_TOKEN: [u8; 32] = [0x33; 32];

// ── Pinned lane-0-colliding pairs (found by the generator below). ─────────────
// HEAP: two heap keys (collection 1) whose WIDE heap roots share lane 0 (bytes
// [0..4]) but differ in the completion lanes.
const HEAP_KEY_A: u32 = 2561;
const HEAP_KEY_B: u32 = 43178;
// FIELDS: two field keys (>= STATE_SLOTS) whose WIDE fields roots share lane 0.
const FIELDS_KEY_A: u64 = 29556;
const FIELDS_KEY_B: u64 = 33693;
// CAP: two cap-target seeds whose WIDE cap roots share lane 0.
const CAP_SEED_A: u64 = 19551;
const CAP_SEED_B: u64 = 41061;

fn heap_map(key: u32) -> BTreeMap<(u32, u32), [u8; 32]> {
    let mut m = BTreeMap::new();
    m.insert((1u32, key), FORGE_VALUE);
    m
}

fn fields_map(key: u64) -> BTreeMap<u64, [u8; 32]> {
    let mut m = BTreeMap::new();
    m.insert(key, FORGE_VALUE);
    m
}

fn cap_target(seed: u64) -> CellId {
    let mut pk = [0u8; 32];
    pk[0..8].copy_from_slice(&seed.to_le_bytes());
    pk[8] = 0x5A; // domain-ish separator so seeds don't alias trivial keys
    CellId::derive_raw(&pk, &CAP_TOKEN)
}

fn caps(seed: u64) -> CapabilitySet {
    let mut c = CapabilitySet::new();
    c.grant(cap_target(seed), AuthRequired::Signature);
    c
}

/// HEAP: the lane-0-colliding pair now separates in the wide off-chain
/// `heap_root` AND in the whole-cell state commitment.
#[test]
fn heap_root_lane0_forge_closed_offchain() {
    assert_ne!(
        HEAP_KEY_A, HEAP_KEY_B,
        "pinned pair not set — run the generator"
    );

    let ra = compute_heap_root(&heap_map(HEAP_KEY_A));
    let rb = compute_heap_root(&heap_map(HEAP_KEY_B));

    // LANE 0 (bytes [0..4]) COLLIDES: the historical lane-0 encoding was
    // `[lane0 ‖ 24 zero bytes]`, so the OLD off-chain roots were byte-identical
    // for these two genuinely-different heaps — THE FORGE.
    assert_eq!(ra[0..4], rb[0..4], "lane-0 must collide (the closed hole)");
    // The FAITHFUL wide root SEPARATES them (completion lanes 1..7).
    assert_ne!(
        ra, rb,
        "wide heap_root must separate the lane-0-colliding heaps"
    );
    assert_ne!(ra[4..32], rb[4..32], "the separation lives in lanes 1..7");

    // End to end: two cells identical except for the one heap entry now carry
    // different `heap_root` (lane-0 still collides) AND different commitments.
    let mut cell_a = Cell::new(CELL_KEY, CELL_TOKEN);
    let mut cell_b = Cell::new(CELL_KEY, CELL_TOKEN);
    assert!(cell_a.state.set_heap(1, HEAP_KEY_A, FORGE_VALUE));
    assert!(cell_b.state.set_heap(1, HEAP_KEY_B, FORGE_VALUE));
    assert_eq!(
        cell_a.state.heap_root[0..4],
        cell_b.state.heap_root[0..4],
        "the stored heap_root still collides on lane 0"
    );
    assert_ne!(
        cell_a.state.heap_root, cell_b.state.heap_root,
        "the stored heap_root separates on the wide lanes"
    );
    assert_ne!(
        compute_canonical_state_commitment(&cell_a),
        compute_canonical_state_commitment(&cell_b),
        "the off-chain state commitment now separates the lane-0-colliding heaps"
    );
}

/// FIELDS: same closure for the overflow-`fields_root` plane.
#[test]
fn fields_root_lane0_forge_closed_offchain() {
    assert_ne!(
        FIELDS_KEY_A, FIELDS_KEY_B,
        "pinned pair not set — run the generator"
    );

    let ra = compute_fields_root(&fields_map(FIELDS_KEY_A));
    let rb = compute_fields_root(&fields_map(FIELDS_KEY_B));
    assert_eq!(ra[0..4], rb[0..4], "lane-0 must collide (the closed hole)");
    assert_ne!(
        ra, rb,
        "wide fields_root must separate the lane-0-colliding maps"
    );
    assert_ne!(ra[4..32], rb[4..32], "the separation lives in lanes 1..7");

    let mut cell_a = Cell::new(CELL_KEY, CELL_TOKEN);
    let mut cell_b = Cell::new(CELL_KEY, CELL_TOKEN);
    assert!(cell_a.state.set_field_ext(FIELDS_KEY_A, FORGE_VALUE));
    assert!(cell_b.state.set_field_ext(FIELDS_KEY_B, FORGE_VALUE));
    assert_eq!(
        cell_a.state.fields_root[0..4],
        cell_b.state.fields_root[0..4],
        "the stored fields_root still collides on lane 0"
    );
    assert_ne!(
        cell_a.state.fields_root, cell_b.state.fields_root,
        "the stored fields_root separates on the wide lanes"
    );
    assert_ne!(
        compute_canonical_state_commitment(&cell_a),
        compute_canonical_state_commitment(&cell_b),
        "the off-chain state commitment now separates the lane-0-colliding field maps"
    );
}

/// CAP: same closure for the capability-root plane. Here the OLD off-chain
/// encoding (`compute_canonical_capability_root`, lane-0 `felt_to_bytes32`) is
/// FULLY byte-identical for the pair — so the pre-fix commitment provably
/// collided — while the wide encoding separates.
#[test]
fn cap_root_lane0_forge_closed_offchain() {
    assert_ne!(
        CAP_SEED_A, CAP_SEED_B,
        "pinned pair not set — run the generator"
    );

    let caps_a = caps(CAP_SEED_A);
    let caps_b = caps(CAP_SEED_B);
    assert_ne!(
        cap_target(CAP_SEED_A),
        cap_target(CAP_SEED_B),
        "the two c-lists must target genuinely-different cells"
    );

    // The OLD lane-0 encoding is byte-IDENTICAL (32 bytes) — the pre-fix
    // off-chain cap_root, and thus the pre-fix commitment, collided outright.
    assert_eq!(
        compute_canonical_capability_root(&caps_a),
        compute_canonical_capability_root(&caps_b),
        "the lane-0 cap_root encoding fully collides (the closed hole)"
    );
    // The FAITHFUL wide encoding SEPARATES them.
    let wa = compute_canonical_capability_root_wide(&caps_a);
    let wb = compute_canonical_capability_root_wide(&caps_b);
    assert_eq!(
        wa[0..4],
        wb[0..4],
        "wide bytes [0..4] are the colliding lane 0"
    );
    assert_ne!(
        wa, wb,
        "the wide cap_root separates the lane-0-colliding c-lists"
    );
    assert_ne!(wa[4..32], wb[4..32], "the separation lives in lanes 1..7");

    let mut cell_a = Cell::new(CELL_KEY, CELL_TOKEN);
    let mut cell_b = Cell::new(CELL_KEY, CELL_TOKEN);
    cell_a
        .capabilities
        .grant(cap_target(CAP_SEED_A), AuthRequired::Signature);
    cell_b
        .capabilities
        .grant(cap_target(CAP_SEED_B), AuthRequired::Signature);
    assert_ne!(
        compute_canonical_state_commitment(&cell_a),
        compute_canonical_state_commitment(&cell_b),
        "the off-chain state commitment now separates the lane-0-colliding c-lists"
    );
}

// ── Birthday generators for the pinned pairs. `#[ignore]`d — they PRODUCE the
// constants above, they are not CI assertions. Run with `--ignored --nocapture`
// and paste the printed pairs. ───────────────────────────────────────────────

fn lane0(root: &[u8; 32]) -> u32 {
    u32::from_le_bytes([root[0], root[1], root[2], root[3]])
}

#[test]
#[ignore]
fn search_lane0_collisions() {
    use std::collections::HashMap;

    // HEAP.
    let mut seen: HashMap<u32, u32> = HashMap::new();
    for key in 1u32..40_000_000 {
        let r = compute_heap_root(&heap_map(key));
        let l0 = lane0(&r);
        if let Some(&prev) = seen.get(&l0) {
            if compute_heap_root(&heap_map(prev)) != r {
                println!("HEAP_KEY_A = {prev}; HEAP_KEY_B = {key}; lane0 = {l0}");
                break;
            }
        }
        seen.insert(l0, key);
    }

    // FIELDS.
    let mut seen: HashMap<u32, u64> = HashMap::new();
    for key in 16u64..40_000_000 {
        let r = compute_fields_root(&fields_map(key));
        let l0 = lane0(&r);
        if let Some(&prev) = seen.get(&l0) {
            if compute_fields_root(&fields_map(prev)) != r {
                println!("FIELDS_KEY_A = {prev}; FIELDS_KEY_B = {key}; lane0 = {l0}");
                break;
            }
        }
        seen.insert(l0, key);
    }

    // CAP.
    let mut seen: HashMap<u32, u64> = HashMap::new();
    for seed in 1u64..40_000_000 {
        let w = compute_canonical_capability_root_wide(&caps(seed));
        let l0 = lane0(&w);
        if let Some(&prev) = seen.get(&l0) {
            if compute_canonical_capability_root_wide(&caps(prev)) != w {
                println!("CAP_SEED_A = {prev}; CAP_SEED_B = {seed}; lane0 = {l0}");
                break;
            }
        }
        seen.insert(l0, seed);
    }
}
