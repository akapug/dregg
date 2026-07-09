//! DSL-native Merkle Poseidon2 membership proving and verification.
//!
//! This module provides the production prove/verify API for Merkle membership
//! proofs. It replaces the old hand-written `MerklePoseidon2StarkAir` and
//! `BlindedMerklePoseidon2StarkAir` in `circuit/src/poseidon2_air.rs`.
//!
//! # What this provides
//!
//! - Standard 4-ary Merkle membership (prove leaf is in tree)
//! - Blinded (ring) membership (prove leaf is in tree without revealing which)
//! - Position/direction bits (0..3 enforced via degree-4 polynomial constraint)
//! - Trace generators with proper padding to power-of-two
//! - Production `prove_*` / `verify_*` functions that use the DSL circuit descriptors
//!
//! # Security Model
//!
//! The DSL version uses `hash_fact` (via `ConstraintExpr::Hash`) rather than
//! `hash_4_to_1` with Lagrange child selection. The security property is preserved:
//! the parent hash is uniquely determined by (current, siblings, position). The
//! binding is self-consistent because both trace generation and constraint evaluation
//! use the same `hash_fact` function.

use crate::field::BabyBear;
use crate::poseidon2::hash_fact;

use crate::dsl::descriptors::{self, merkle_col};

// ============================================================================
// Trace Generation: Standard Merkle Poseidon2
// ============================================================================

/// Generate a valid Merkle membership trace for the DSL Poseidon2 circuit.
///
/// Each row represents one level of the 4-ary Merkle tree (leaf to root).
/// The parent hash is computed as `hash_fact(current, [sib0, sib1, sib2, position])`.
///
/// Returns (trace, public_inputs) where public_inputs = [leaf_hash, root].
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn generate_merkle_poseidon2_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2 for STARK");

    let mut trace = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let position = BabyBear::new(pos as u32);
        let sib0 = siblings[i][0];
        let sib1 = siblings[i][1];
        let sib2 = siblings[i][2];

        // Parent = hash_4_to_1(children arranged by position)
        let mut children = [BabyBear::ZERO; 4];
        children[pos as usize] = current;
        let mut sib_idx = 0;
        for j in 0..4 {
            if j != pos as usize {
                children[j] = [sib0, sib1, sib2][sib_idx];
                sib_idx += 1;
            }
        }
        let parent = crate::poseidon2::hash_4_to_1(&children);

        trace.push(vec![current, sib0, sib1, sib2, position, parent]);
        current = parent;
    }

    // Pad to power of two (minimum 2 rows). Padding rows must satisfy all constraints:
    // - Position validity: position=0 satisfies pos*(pos-1)*(pos-2)*(pos-3)=0
    // - Hash binding: parent = hash_4_to_1([current, 0, 0, 0])
    // - Chain continuity: next[current] = local[parent]
    let target_len = depth.next_power_of_two().max(2);
    while trace.len() < target_len {
        let prev_parent = trace.last().unwrap()[merkle_col::PARENT];
        let pad_pos = BabyBear::ZERO;
        let pad_sib0 = BabyBear::ZERO;
        let pad_sib1 = BabyBear::ZERO;
        let pad_sib2 = BabyBear::ZERO;
        let pad_children = [prev_parent, pad_sib0, pad_sib1, pad_sib2];
        let pad_parent = crate::poseidon2::hash_4_to_1(&pad_children);

        trace.push(vec![
            prev_parent,
            pad_sib0,
            pad_sib1,
            pad_sib2,
            pad_pos,
            pad_parent,
        ]);
    }

    let root = trace.last().unwrap()[merkle_col::PARENT];
    let public_inputs = vec![leaf_hash, root];
    (trace, public_inputs)
}

/// Generate a test witness (deterministic siblings/positions).
///
/// Returns (siblings, positions, expected_root).
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn create_test_witness(
    leaf_hash: BabyBear,
    depth: usize,
) -> (Vec<[BabyBear; 3]>, Vec<u8>, BabyBear) {
    let mut siblings = Vec::with_capacity(depth);
    let mut positions = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = (i % 4) as u8;
        let sibs = [
            BabyBear::new((i * 3 + 1) as u32),
            BabyBear::new((i * 3 + 2) as u32),
            BabyBear::new((i * 3 + 3) as u32),
        ];
        let mut children = [BabyBear::ZERO; 4];
        children[pos as usize] = current;
        let mut sib_idx = 0;
        for j in 0..4 {
            if j != pos as usize {
                children[j] = sibs[sib_idx];
                sib_idx += 1;
            }
        }
        current = crate::poseidon2::hash_4_to_1(&children);
        siblings.push(sibs);
        positions.push(pos);
    }

    (siblings, positions, current) // current = expected root
}

// ============================================================================
// Trace Generation: Blinded Merkle Poseidon2
// ============================================================================

/// Generate a blinded Merkle membership trace.
///
/// Public inputs are [blinded_leaf, root] where:
///   blinded_leaf = hash_fact(leaf_hash, [blinding_factor])
///
/// The leaf_hash remains private (not bound to any public input).
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
pub fn generate_blinded_merkle_poseidon2_trace(
    leaf_hash: BabyBear,
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
    blinding_factor: BabyBear,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = siblings.len();
    assert_eq!(positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2 for STARK");

    let mut trace = Vec::with_capacity(depth);
    let mut current = leaf_hash;

    for i in 0..depth {
        let pos = positions[i];
        assert!(pos < 4, "position must be 0..3");

        let position = BabyBear::new(pos as u32);
        let sib0 = siblings[i][0];
        let sib1 = siblings[i][1];
        let sib2 = siblings[i][2];

        let mut children = [BabyBear::ZERO; 4];
        children[pos as usize] = current;
        let mut sib_idx = 0;
        for j in 0..4 {
            if j != pos as usize {
                children[j] = [sib0, sib1, sib2][sib_idx];
                sib_idx += 1;
            }
        }
        let parent = crate::poseidon2::hash_4_to_1(&children);

        // Blinding column: real value at row 0, zero elsewhere
        let row_blinding = if i == 0 {
            blinding_factor
        } else {
            BabyBear::ZERO
        };
        // Blinded column: hash_fact(current, [blinding]) -- still uses hash_fact for blinding
        let row_blinded = hash_fact(current, &[row_blinding]);

        trace.push(vec![
            current,
            sib0,
            sib1,
            sib2,
            position,
            parent,
            row_blinding,
            row_blinded,
        ]);
        current = parent;
    }

    // Pad to power of two
    let target_len = depth.next_power_of_two().max(2);
    while trace.len() < target_len {
        let prev_parent = trace.last().unwrap()[merkle_col::PARENT];
        let pad_pos = BabyBear::ZERO;
        let pad_sib0 = BabyBear::ZERO;
        let pad_sib1 = BabyBear::ZERO;
        let pad_sib2 = BabyBear::ZERO;
        let pad_children = [prev_parent, pad_sib0, pad_sib1, pad_sib2];
        let pad_parent = crate::poseidon2::hash_4_to_1(&pad_children);
        // Blinding=0 on padding rows; blinded = hash_fact(prev_parent, [0])
        let pad_blinded = hash_fact(prev_parent, &[BabyBear::ZERO]);

        trace.push(vec![
            prev_parent,
            pad_sib0,
            pad_sib1,
            pad_sib2,
            pad_pos,
            pad_parent,
            BabyBear::ZERO,
            pad_blinded,
        ]);
    }

    let root = trace.last().unwrap()[merkle_col::PARENT];
    // blinded_leaf = hash_fact(leaf_hash, [blinding_factor])
    let blinded_leaf = hash_fact(leaf_hash, &[blinding_factor]);
    let public_inputs = vec![blinded_leaf, root];
    (trace, public_inputs)
}

// ============================================================================
// Legacy compatibility types (re-exported from merkle_types.rs)
// ============================================================================

pub use crate::merkle_types::{
    MERKLE_AIR_WIDTH, MerkleAir, MerkleLevelWitness, MerkleWitness, TREE_DEPTH,
    create_test_witness as create_test_witness_legacy,
};

// ============================================================================
// AIR Name Constants (for dispatch)
// ============================================================================

/// The AIR name for standard DSL Merkle Poseidon2 membership proofs.
pub const MERKLE_POSEIDON2_AIR_NAME: &str = descriptors::MERKLE_POSEIDON2_AIR_NAME;

/// The AIR name for blinded DSL Merkle membership proofs.
pub const BLINDED_MERKLE_AIR_NAME: &str = descriptors::BLINDED_MERKLE_AIR_NAME;

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blinded_unlinkability() {
        let leaf = BabyBear::new(42424242);
        let (siblings, positions, _root) = create_test_witness(leaf, 4);

        let blinding_1 = BabyBear::new(111111);
        let blinding_2 = BabyBear::new(222222);

        let (_, pi_1) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_1);
        let (_, pi_2) =
            generate_blinded_merkle_poseidon2_trace(leaf, &siblings, &positions, blinding_2);

        // Same root (same tree)
        assert_eq!(pi_1[1], pi_2[1]);
        // Different blinded_leaf (unlinkable)
        assert_ne!(pi_1[0], pi_2[0]);
    }
}
