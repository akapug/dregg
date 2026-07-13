//! Positional keccak256 Merkle-inclusion verifier -- the on-chain-sound
//! primitive for proving a fact about dregg state under a known root. A faithful
//! Solana port of `chain/contracts/DreggMerkle.sol` (the EVM inclusion library),
//! using Solana's native `keccak` syscall.
//!
//! ## What it proves (and why it is sound with only the root)
//!
//! Given a `root`, a `leaf`, its `index`, and its `siblings` (bottom-up), this
//! returns true iff recomputing the path from the leaf yields the root. Each
//! internal node is `keccak256(left || right)` -- collision-resistant and binding
//! on BOTH children -- so a forged leaf, tampered sibling, or wrong index cannot
//! reach the same root except by a keccak collision. A program holding ONLY the
//! root can therefore soundly check inclusion; it needs neither the set nor a
//! trusted prover.
//!
//! ## Convention (fixed, matches dregg's positional `compress(left, right)`)
//!
//!   node(l, r) = keccak256(l || r)   [POSITIONAL, not sorted]
//!   walk bottom -> top; at level i, if the index bit is 0 the sibling is the
//!   RIGHT child (`node(cur, sib)`), else the LEFT (`node(sib, cur)`).
//!
//! Byte-identical to `DreggMerkle.verifyInclusion`.
//!
//! ## Honest scope (parity with the EVM ISM's fail-closed leg)
//!
//! This is a sound primitive GIVEN a root. Binding a leaf to a dregg-proven FACT
//! additionally requires that `root` be a proof-bound keccak commitment the
//! settlement recorded. Today the proof binds the dregg STATE root
//! (`packLanes`, a keccak of 8 BabyBear lanes -- NOT a keccak Merkle root over
//! leaves), so per-leaf inclusion under a dregg root awaits the apex exposing a
//! keccak-mirror sub-root as claim lanes (the named residual in
//! `DreggSettlement.sol`, identical to `DreggProofISM`'s message-root leg). The
//! `isProvenRoot` gate (`processor::assert_proven_root`) IS by-proof today.

use solana_program::keccak;

/// Domain-separated padding leaf for power-of-two completion, matching
/// `DreggMerkle.EMPTY_LEAF` (`keccak256("dregg.merkle.empty.leaf.v1")`). Exposed
/// so off-chain tree builders pad identically to the EVM.
pub fn empty_leaf() -> [u8; 32] {
    keccak::hashv(&[b"dregg.merkle.empty.leaf.v1"]).0
}

/// `node(l, r) = keccak256(l || r)` (positional, not sorted).
fn node(l: &[u8; 32], r: &[u8; 32]) -> [u8; 32] {
    keccak::hashv(&[l, r]).0
}

/// Recompute the Merkle root from `leaf` at `index` with bottom-up `siblings`.
pub fn compute_root(leaf: &[u8; 32], index: u64, siblings: &[[u8; 32]]) -> [u8; 32] {
    let mut cur = *leaf;
    let mut idx = index;
    for sib in siblings {
        cur = if idx & 1 == 0 {
            node(&cur, sib)
        } else {
            node(sib, &cur)
        };
        idx >>= 1;
    }
    cur
}

/// True iff `leaf` at `index` is included under `root` via `siblings`.
pub fn verify_inclusion(
    root: &[u8; 32],
    leaf: &[u8; 32],
    index: u64,
    siblings: &[[u8; 32]],
) -> bool {
    &compute_root(leaf, index, siblings) == root
}

#[cfg(test)]
mod tests {
    use super::*;

    // Build a 4-leaf tree and prove each leaf, mirroring DreggMerkle's positional
    // hashing so an off-chain (EVM) prover and this verifier agree.
    fn leaves() -> [[u8; 32]; 4] {
        [[1u8; 32], [2u8; 32], [3u8; 32], [4u8; 32]]
    }

    fn root4(l: &[[u8; 32]; 4]) -> [u8; 32] {
        let n01 = node(&l[0], &l[1]);
        let n23 = node(&l[2], &l[3]);
        node(&n01, &n23)
    }

    #[test]
    fn proves_every_leaf() {
        let l = leaves();
        let root = root4(&l);
        // leaf 0: siblings = [l1, node(l2,l3)], index 0
        let n23 = node(&l[2], &l[3]);
        let n01 = node(&l[0], &l[1]);
        assert!(verify_inclusion(&root, &l[0], 0, &[l[1], n23]));
        assert!(verify_inclusion(&root, &l[1], 1, &[l[0], n23]));
        assert!(verify_inclusion(&root, &l[2], 2, &[l[3], n01]));
        assert!(verify_inclusion(&root, &l[3], 3, &[l[2], n01]));
    }

    #[test]
    fn rejects_wrong_leaf_sibling_and_index() {
        let l = leaves();
        let root = root4(&l);
        let n23 = node(&l[2], &l[3]);
        // wrong leaf
        assert!(!verify_inclusion(&root, &[9u8; 32], 0, &[l[1], n23]));
        // wrong sibling
        assert!(!verify_inclusion(&root, &l[0], 0, &[[9u8; 32], n23]));
        // wrong index (0 vs 1 flips the hash order)
        assert!(!verify_inclusion(&root, &l[0], 1, &[l[1], n23]));
    }

    #[test]
    fn single_leaf_tree() {
        let leaf = [7u8; 32];
        // depth-0: root == leaf.
        assert!(verify_inclusion(&leaf, &leaf, 0, &[]));
    }
}
