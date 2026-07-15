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
//! # Each colliding pair is DERIVED, not pinned
//!
//! These tests used to carry hand-pasted collision constants, found by an
//! `#[ignore]`d birthday generator and copied in by hand. That made the crown
//! jewel's teeth a function of whether someone remembered to re-run a generator:
//! when `compute_heap_root` / `compute_fields_root` changed underneath them the
//! pins went stale, the pairs stopped colliding on lane 0, and **2 of these 3
//! tests failed their own setup precondition** — the heap and fields planes were
//! providing zero forge protection while the file sat red.
//!
//! So there are no constants. Each test runs the birthday search itself, at test
//! time, against the CELL's own live producers (folding through `fold_bytes32` /
//! `cap_ref_to_leaf`, so the collision is faithful to the deployed leaf shape),
//! and derives a pair that collides on lane 0 **of the root function as it
//! exists right now**. A change to a root function can no longer silently disarm
//! the regression: the search simply finds a pair against the new function, and
//! if it cannot, that is a loud failure with a stated meaning (see
//! [`find_lane0_collision`]) rather than a stale-pin false red.
//!
//! The search is cheap and that is not luck — lane 0 is one ~31-bit BabyBear
//! felt, so the birthday bound is ~2^15.5 ≈ 46k candidates. The budget below is
//! generous by ~40× against that expectation.

use std::collections::{BTreeMap, HashMap};

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

/// Candidate budget for the birthday search. Lane 0 is one BabyBear felt
/// (~2^31), so a collision is expected after ~sqrt(π/2 · 2^31) ≈ 46k
/// candidates. 2M is ~40× that — exhausting it does not mean "unlucky", it
/// means the root function no longer has a ~31-bit lane 0, which is a
/// structural change this test must report rather than paper over.
const SEARCH_BUDGET: usize = 2_000_000;

/// Lane 0 of a wide root: bytes `[0..4]`, the historical projection.
fn lane0(root: &[u8; 32]) -> u32 {
    u32::from_le_bytes([root[0], root[1], root[2], root[3]])
}

/// Derive a pair of DISTINCT keys whose wide roots **collide on lane 0** but
/// **differ overall** — i.e. exactly the forge the old lane-0 off-chain encoding
/// admitted and the wide encoding must close. Returns `(key_a, key_b, root_a,
/// root_b)`.
///
/// This replaces the hand-pasted constants. It runs against `root_of` **as it
/// is today**, so a change to a root function cannot leave a stale pin behind:
/// there is no pin.
///
/// Two keys mapping to the same lane 0 AND the same wide root are not a forge
/// (they are the same state as far as the wide encoding is concerned), so the
/// search skips them and keeps looking — the pair must be genuinely separated
/// by the completion lanes or it proves nothing.
///
/// **Panics** (loudly, with the meaning stated) if the budget is exhausted. A
/// silent skip here would be a green that means the forge regression stopped
/// running — the precise failure this rewrite exists to make impossible.
fn find_lane0_collision<K, F>(
    plane: &str,
    keys: impl Iterator<Item = K>,
    root_of: F,
) -> (K, K, [u8; 32], [u8; 32])
where
    K: Copy + std::fmt::Debug,
    F: Fn(K) -> [u8; 32],
{
    let mut seen: HashMap<u32, (K, [u8; 32])> = HashMap::new();
    let mut tried = 0usize;

    for k in keys.take(SEARCH_BUDGET) {
        tried += 1;
        let r = root_of(k);
        match seen.get(&lane0(&r)) {
            // Lane 0 collides AND the wide roots differ — the forge pair.
            Some(&(prev, prev_root)) if prev_root != r => {
                println!(
                    "{plane}: derived lane-0 collision after {tried} candidates: \
                     {prev:?} vs {k:?} (lane0 = {})",
                    lane0(&r)
                );
                return (prev, k, prev_root, r);
            }
            // Same lane 0, same wide root: not a separation, keep searching.
            Some(_) => {}
            None => {
                seen.insert(lane0(&r), (k, r));
            }
        }
    }

    panic!(
        "{plane}: no lane-0 collision in {tried} candidates. Lane 0 is one ~31-bit BabyBear \
         felt, so the birthday expectation is ~46k — exhausting {SEARCH_BUDGET} means the \
         root function's lane-0 projection changed shape (it is no longer ~31-bit, or the \
         key space no longer varies it). This test's premise is that a lane-0 collision \
         EXISTS and the wide encoding separates it; if the premise is gone, the test must \
         be re-derived, not silently passed."
    );
}

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
    // ── HONEST POLE FIRST: the producer is deterministic. If it were not, a
    // `assert_ne!` between two roots below would be measuring noise, and every
    // separation claim in this test would be vacuous.
    assert_eq!(
        compute_heap_root(&heap_map(7)),
        compute_heap_root(&heap_map(7)),
        "honest pole: compute_heap_root must be deterministic — else the separation \
         assertions below prove nothing"
    );

    // Derive the colliding pair against the LIVE producer (no pins).
    let (heap_key_a, heap_key_b, ra, rb) =
        find_lane0_collision("HEAP", 1u32.., |k| compute_heap_root(&heap_map(k)));
    assert_ne!(
        heap_key_a, heap_key_b,
        "the search must return two genuinely different keys"
    );

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
    assert!(cell_a.state.set_heap(1, heap_key_a, FORGE_VALUE));
    assert!(cell_b.state.set_heap(1, heap_key_b, FORGE_VALUE));
    assert_eq!(
        cell_a.state.heap_root.to_bytes32()[0..4],
        cell_b.state.heap_root.to_bytes32()[0..4],
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
    // ── HONEST POLE FIRST: the producer is deterministic.
    assert_eq!(
        compute_fields_root(&fields_map(17)),
        compute_fields_root(&fields_map(17)),
        "honest pole: compute_fields_root must be deterministic — else the separation \
         assertions below prove nothing"
    );

    // Derive the colliding pair against the LIVE producer (no pins). Field keys
    // must be >= STATE_SLOTS to land in the overflow map.
    let (fields_key_a, fields_key_b, ra, rb) =
        find_lane0_collision("FIELDS", 16u64.., |k| compute_fields_root(&fields_map(k)));
    assert_ne!(
        fields_key_a, fields_key_b,
        "the search must return two genuinely different keys"
    );
    assert_eq!(ra[0..4], rb[0..4], "lane-0 must collide (the closed hole)");
    assert_ne!(
        ra, rb,
        "wide fields_root must separate the lane-0-colliding maps"
    );
    assert_ne!(ra[4..32], rb[4..32], "the separation lives in lanes 1..7");

    let mut cell_a = Cell::new(CELL_KEY, CELL_TOKEN);
    let mut cell_b = Cell::new(CELL_KEY, CELL_TOKEN);
    assert!(cell_a.state.set_field_ext(fields_key_a, FORGE_VALUE));
    assert!(cell_b.state.set_field_ext(fields_key_b, FORGE_VALUE));
    assert_eq!(
        cell_a.state.fields_root.to_bytes32()[0..4],
        cell_b.state.fields_root.to_bytes32()[0..4],
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
    // ── HONEST POLE FIRST: the producer is deterministic.
    assert_eq!(
        compute_canonical_capability_root_wide(&caps(3)),
        compute_canonical_capability_root_wide(&caps(3)),
        "honest pole: compute_canonical_capability_root_wide must be deterministic — else \
         the separation assertions below prove nothing"
    );

    // Derive the colliding pair against the LIVE producer (no pins).
    let (cap_seed_a, cap_seed_b, _wa_derived, _wb_derived) =
        find_lane0_collision("CAP", 1u64.., |s| {
            compute_canonical_capability_root_wide(&caps(s))
        });

    let caps_a = caps(cap_seed_a);
    let caps_b = caps(cap_seed_b);
    assert_ne!(
        cap_target(cap_seed_a),
        cap_target(cap_seed_b),
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
        .grant(cap_target(cap_seed_a), AuthRequired::Signature);
    cell_b
        .capabilities
        .grant(cap_target(cap_seed_b), AuthRequired::Signature);
    assert_ne!(
        compute_canonical_state_commitment(&cell_a),
        compute_canonical_state_commitment(&cell_b),
        "the off-chain state commitment now separates the lane-0-colliding c-lists"
    );
}

// The birthday generator that used to live here is GONE, and its absence is the
// fix. It was `#[ignore]`d, so nothing ran it; it PRINTED constants a human
// pasted above; and when a root function changed, the pasted constants silently
// became a pair that no longer collided — turning the crown jewel red on its own
// setup while reporting nothing about the forge. The search is now
// `find_lane0_collision` at the top of this file, called by each test at test
// time. There is no generator to remember to run, and no constant to go stale.
