//! Differential cross-check: the deployed Rust 4-ary Poseidon2 note-commitment accumulator
//! (`commit/src/poseidon2_tree.rs`) AGREES with the Lean-authored model
//! (`metatheory/Dregg2/Circuit/CommitmentTreeAccumulator.lean`).
//!
//! Architectural law #1 makes the Lean module the author of this accumulator; the Rust tree is
//! DEBT slated for retirement (emit the Lean object, delete the hand-rolled append/root). Until
//! then this test closes the divergence akapug flagged (no cross-check between the two): it
//! machine-checks, in Rust, exactly the properties the Lean module proves abstractly.
//!
//! Two teeth:
//!
//!   1. SHORTCUT SOUNDNESS OVER THE REAL POSEIDON2. `Poseidon2MerkleTree::root` uses an
//!      empty-subtree optimization (`first_leaf >= len => empty_hash_at_level`). `ref_root` below
//!      is the PURE recursion with NO shortcut — the byte-for-byte image of Lean `nodeAt`/`root`
//!      (`| 0, i => leafAt ; | k+1, i => H [child 4i .. 4i+3]`). Asserting they agree on many
//!      sequences over the ACTUAL `hash_4_to_1` is the Rust witness of Lean `emptyHash_correct`
//!      (the optimization equals the pure recursion) — the one place the two could diverge.
//!
//!   2. STRUCTURAL SHAPE, NUMERICALLY, CROSS-LANGUAGE. A tiny toy hash (`M=7`, `EMPTY=3`, depth 1),
//!      decoupled from Poseidon2, reproduces the exact integer the Lean `#guard` pins
//!      (`rootTiny [5] = 11490`). Since the toy is order/position-sensitive, matching the literal
//!      confirms both implementations compute the SAME tree shape: fan-out 4, position indexing,
//!      EMPTY_LEAF padding — not just the same multiset.

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_4_to_1;
use dregg_commit::poseidon2_tree::{EMPTY_LEAF, Poseidon2MerkleTree};

/// Padded leaf lookup — the image of Lean `leafAt` (and Rust `get_leaf`): EMPTY_LEAF out of bounds.
fn leaf_at(leaves: &[BabyBear], i: usize) -> BabyBear {
    if i < leaves.len() {
        leaves[i]
    } else {
        EMPTY_LEAF
    }
}

/// PURE 4-ary recursion with NO empty-subtree shortcut — the byte image of Lean `nodeAt`.
fn node_at(leaves: &[BabyBear], level: u32, index: usize) -> BabyBear {
    if level == 0 {
        return leaf_at(leaves, index);
    }
    hash_4_to_1(&[
        node_at(leaves, level - 1, 4 * index),
        node_at(leaves, level - 1, 4 * index + 1),
        node_at(leaves, level - 1, 4 * index + 2),
        node_at(leaves, level - 1, 4 * index + 3),
    ])
}

/// The pure-recursion root (Lean `root H depth leaves = nodeAt H leaves depth 0`).
fn ref_root(depth: u32, leaves: &[BabyBear]) -> BabyBear {
    node_at(leaves, depth, 0)
}

/// Build the DEPLOYED tree (optimized `root`, empty-subtree shortcut + cached root) from a slice.
fn deployed_root(depth: usize, leaves: &[BabyBear]) -> BabyBear {
    let mut tree = Poseidon2MerkleTree::with_depth(depth);
    for &l in leaves {
        tree.append(l);
    }
    tree.root()
}

/// A small deterministic LCG so the "random" sequences are reproducible without an rng dep.
fn lcg_seq(seed: u64, n: usize) -> Vec<BabyBear> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            BabyBear::new((s >> 33) as u32)
        })
        .collect()
}

#[test]
fn tooth1_deployed_root_equals_pure_recursion_over_real_poseidon2() {
    // The empty-subtree SHORTCUT (`compute_node_at_level`'s `first_leaf >= len` branch) must equal
    // the pure recursion `ref_root` on every population level — this is Lean `emptyHash_correct`,
    // witnessed on the deployed `hash_4_to_1`.
    for depth in [2usize, 3, 4] {
        let cap = 4usize.pow(depth as u32);
        // Cover the whole spectrum: empty, sparse, half, full-1, exactly full.
        let sizes = [0, 1, 2, 3, 7, cap / 2, cap.saturating_sub(1), cap];
        for &n in &sizes {
            let n = n.min(cap);
            for seed in [1u64, 42, 0xDEADBEEF, 7777] {
                let leaves = lcg_seq(seed, n);
                let dep = deployed_root(depth, &leaves);
                let refr = ref_root(depth as u32, &leaves);
                assert_eq!(
                    dep, refr,
                    "deployed (shortcut) root != pure recursion: depth={depth} n={n} seed={seed}"
                );
            }
        }
    }
}

#[test]
fn tooth1_empty_tree_matches_pure_recursion() {
    // The all-empty accumulator (Lean `root_empty`: root [] = emptyHash depth): the shortcut path
    // is taken at the apex, so this specifically exercises `empty_hash_at_level(depth)`.
    for depth in [1usize, 2, 5, 8] {
        assert_eq!(deployed_root(depth, &[]), ref_root(depth as u32, &[]));
    }
}

#[test]
fn tooth1_append_is_incremental_offpath_unchanged() {
    // Lean `append_offpath_unchanged`: appending at p=len changes the root only along p's path;
    // every OTHER position's leaf-read is unchanged. We witness the consequence: recomputing the
    // deployed root after each append agrees with the pure recursion at every prefix (so the
    // incremental/cached path never diverges from a from-scratch pure build).
    let depth = 3usize;
    let leaves = lcg_seq(2024, 4usize.pow(depth as u32));
    let mut tree = Poseidon2MerkleTree::with_depth(depth);
    for k in 0..=leaves.len() {
        assert_eq!(
            tree.root_immutable(),
            ref_root(depth as u32, &leaves[..k]),
            "incremental deployed root diverged from pure recursion at prefix {k}"
        );
        if k < leaves.len() {
            tree.append(leaves[k]);
        }
    }
}

// ---------------------------------------------------------------------------------------------
// Tooth 2 — the tiny toy that ties the Lean #guard golden to Rust numerically (structure only).
// ---------------------------------------------------------------------------------------------

/// Lean `cTiny`: a positional Horner sponge seeded by length, `M = 7` (order/position-sensitive).
fn c_tiny(xs: &[i128]) -> i128 {
    let mut acc = xs.len() as i128;
    for &x in xs {
        acc = acc * 7 + x;
    }
    acc
}

/// Lean `rootTiny`: a depth-1 4-ary root with the tiny sentinel `EMPTY = 3`.
fn root_tiny(leaves: &[i128]) -> i128 {
    let g = |i: usize| if i < leaves.len() { leaves[i] } else { 3 };
    c_tiny(&[g(0), g(1), g(2), g(3)])
}

#[test]
fn tooth2_tiny_toy_reproduces_lean_golden() {
    // Lean: `#guard decide (rootTiny [5] = 11490)`. Matching the SAME integer here confirms the two
    // implementations agree on the tree SHAPE (fan-out 4 + position index + EMPTY padding),
    // independent of the (opaque-in-Lean) Poseidon2 permutation.
    assert_eq!(root_tiny(&[5]), 11490);
    // More shapes, each mirrored by a Lean #guard, to pin position + padding sensitivity:
    // rootTiny [] = cTiny[3,3,3,3] = ((((4)*7+3)*7+3)*7+3)*7+3 = 10804
    assert_eq!(root_tiny(&[]), 10804);
    // rootTiny [1,2] = cTiny[1,2,3,3] : a partial fill still pads positions 2,3 with the sentinel.
    // (((4*7+1)*7+2)*7+3)*7+3 = 10069
    assert_eq!(root_tiny(&[1, 2]), 10069);
    // Position sensitivity: swapping the two leaves changes the root (not a multiset).
    assert_ne!(root_tiny(&[1, 2]), root_tiny(&[2, 1]));
}

#[test]
fn tooth2_empty_leaf_is_the_deployed_sentinel() {
    // Lean `EMPTY_LEAF = 233492975` = 0x0DEAD1EF, the exact deployed constant.
    assert_eq!(EMPTY_LEAF.0, 0x0DEAD1EF);
    assert_eq!(EMPTY_LEAF.0, 233492975);
}

// ---------------------------------------------------------------------------------------------
// Tooth 3 — BYTE-IDENTICAL to the Lean root COMPUTED OVER THE REAL POSEIDON2 (the safety gate).
//
// `metatheory/Dregg2/Circuit/Emit/CommitmentTreeAppendEmit.lean` instantiates the chunk-1
// accumulator `root` at the KAT-locked BabyBear Poseidon2-w16 permutation (`hash4to1Real` =
// the real `hash_4_to_1`), so `rootReal depth (mkSeq n)` COMPUTES the deployed note-tree root
// in Lean, and `#guard`-pins the EXACT integers below. Here we assert the DEPLOYED Rust tree
// (`Poseidon2MerkleTree::root().0`) reproduces those same integers. Together:
//     Lean  #guard (rootReal = g)   ∧   Rust  assert (deployed = g)
//   ⇒ deployed = rootReal  byte-for-byte, on every empty/sparse/half/full case at depths 2–4
//   and at every append prefix — the byte-identical gate a cutover MUST clear before any root
//   computation changes. (The Rust root computation itself is HELD, not deleted: an
//   `EffectVmDescriptor2` is an AIR acceptor, not a root evaluator — the deployed sorted-map
//   heap root `heap_root.rs::compute_heap_root` is likewise hand-Rust; the emitted descriptor
//   only CONSTRAINS the write. So the note-tree root stays Rust, now PROVEN byte-identical to its
//   Lean author over the real hash.)
// ---------------------------------------------------------------------------------------------

/// `[1, 2, …, n]` as deployed leaves — the Lean `mkSeq n` mirror (`BabyBear::new(i)`).
fn seq(n: u32) -> Vec<BabyBear> {
    (1..=n).map(BabyBear::new).collect()
}

#[test]
fn tooth3_deployed_root_equals_lean_real_poseidon2_golden() {
    // KAT: the node hash agrees with Lean `hash4to1Real [0,1,2,3]`.
    assert_eq!(
        hash_4_to_1(&[
            BabyBear::new(0),
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
        ])
        .0,
        319108099,
        "hash_4_to_1 KAT diverged from Lean hash4to1Real"
    );

    // (depth, n, deployed golden) — each `= rootReal depth (mkSeq n)` #guard-pinned in Lean.
    let cases: &[(usize, u32, u32)] = &[
        (2, 0, 1354085513),
        (2, 3, 1895531837),
        (2, 4, 1834518077),
        (2, 8, 198394206),
        (2, 15, 983932440),
        (2, 16, 1501679053),
        (3, 0, 62072511),
        (3, 3, 78377282),
        (3, 32, 746309470),
        (3, 63, 552841819),
        (3, 64, 230905478),
        (4, 0, 1331265460),
        (4, 3, 1948100911),
        (4, 128, 851116238),
        (4, 256, 524603802),
    ];
    for &(depth, n, golden) in cases {
        assert_eq!(
            deployed_root(depth, &seq(n)).0,
            golden,
            "deployed root != Lean rootReal golden: depth={depth} n={n}"
        );
    }
}

#[test]
fn tooth3_append_prefixes_equal_lean_golden() {
    // Lean pins `rootReal 2` at each append prefix of `[1..5]`; the DEPLOYED incremental root must
    // match at every prefix (the cached/incremental path never diverges from a from-scratch build).
    let goldens = [
        1354085513u32,
        1206744973,
        570831052,
        1895531837,
        1834518077,
        895893929,
    ];
    let base = seq(5);
    for (k, &g) in goldens.iter().enumerate() {
        assert_eq!(
            deployed_root(2, &base[..k]).0,
            g,
            "deployed prefix root != Lean golden at k={k}"
        );
    }
}
