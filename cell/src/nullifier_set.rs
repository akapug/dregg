//! Nullifier set: an append-only set of revealed nullifiers.
//!
//! When a note is spent, its nullifier is revealed and added to this set.
//! Double-spend detection is simply checking set membership. The set also
//! supports non-membership proofs (proving a note is NOT spent) via a
//! Merkle tree over the nullifier hashes.
//!
//! # Performance
//!
//! Uses `BTreeSet<Nullifier>` internally for O(log N) insert and lookup.
//! Previous implementation used `Vec::insert` at a binary-search position
//! which was O(N) due to element shifting on every insert.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::note::{NoteError, Nullifier};

/// A Merkle membership proof for a single nullifier in the set.
///
/// This proves that a specific nullifier exists at a given position in the
/// Merkle tree built over all nullifiers. Used as part of non-membership proofs
/// to demonstrate that neighbor elements are genuinely in the set.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MerkleMembershipProof {
    /// The nullifier whose membership is being proved.
    pub element: Nullifier,
    /// Index of the element in the sorted nullifier list.
    pub index: usize,
    /// Sibling hashes along the path from the leaf to the root (bottom-up).
    pub siblings: Vec<[u8; 32]>,
}

/// A non-membership proof: demonstrates that a nullifier is NOT in the set.
///
/// Uses adjacent-neighbor technique: shows two consecutive nullifiers in the
/// sorted set that bracket the absent value, plus Merkle membership proofs for
/// each neighbor (proving they ARE in the set).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NonMembershipProof {
    /// The nullifier being proved absent.
    pub absent: Nullifier,
    /// The nullifier just before the absent one (if any).
    pub left_neighbor: Option<Nullifier>,
    /// The nullifier just after the absent one (if any).
    pub right_neighbor: Option<Nullifier>,
    /// Merkle membership proof for the left neighbor (if present).
    pub left_membership_proof: Option<MerkleMembershipProof>,
    /// Merkle membership proof for the right neighbor (if present).
    pub right_membership_proof: Option<MerkleMembershipProof>,
    /// Root of the nullifier tree at the time of proof generation.
    pub root: [u8; 32],
}

/// Append-only set of revealed nullifiers.
/// Supports efficient membership checks and non-membership proofs.
///
/// Uses `BTreeSet` for O(log N) insert and contains operations.
/// For non-membership proofs, the set is materialized into a sorted vec
/// on demand (the BTreeSet iterator yields elements in sorted order).
#[derive(Clone, Debug)]
pub struct NullifierSet {
    /// All nullifiers ever published, kept in a BTreeSet for O(log N) operations.
    nullifiers: BTreeSet<Nullifier>,
}

impl NullifierSet {
    /// Create an empty nullifier set.
    pub fn new() -> Self {
        Self {
            nullifiers: BTreeSet::new(),
        }
    }

    /// Number of nullifiers in the set.
    pub fn len(&self) -> usize {
        self.nullifiers.len()
    }

    /// Whether the set is empty.
    pub fn is_empty(&self) -> bool {
        self.nullifiers.is_empty()
    }

    /// Add a nullifier (note is now spent). Returns error if already present (double-spend).
    ///
    /// O(log N) via BTreeSet insertion.
    pub fn insert(&mut self, nullifier: Nullifier) -> Result<(), NoteError> {
        if !self.nullifiers.insert(nullifier) {
            Err(NoteError::DoubleSpend { nullifier })
        } else {
            Ok(())
        }
    }

    /// Check if a nullifier is in the set (note is spent).
    ///
    /// O(log N) via BTreeSet contains.
    pub fn contains(&self, nullifier: &Nullifier) -> bool {
        self.nullifiers.contains(nullifier)
    }

    /// Iterate the nullifiers in sorted order (the universal-memory projection
    /// walks the set: every spent nullifier is a present `nullifiers`-domain cell).
    pub fn iter(&self) -> impl Iterator<Item = &Nullifier> {
        self.nullifiers.iter()
    }

    /// Remove a nullifier from the set.
    ///
    /// Used ONLY by the turn-journal rollback path to undo a speculative insert
    /// when a turn fails after the nullifier was recorded. Outside of rollback
    /// the set is append-only.
    ///
    /// Returns `true` if the nullifier was present and removed, `false`
    /// otherwise. O(log N) via BTreeSet remove.
    pub fn remove(&mut self, nullifier: &Nullifier) -> bool {
        self.nullifiers.remove(nullifier)
    }

    /// Get the sorted list of nullifiers (materializes from BTreeSet iterator).
    /// Used internally for Merkle tree construction and non-membership proofs.
    fn sorted_vec(&self) -> Vec<Nullifier> {
        self.nullifiers.iter().copied().collect()
    }

    /// Prove non-membership (note is NOT spent).
    /// Returns None if the nullifier IS in the set.
    pub fn prove_non_membership(&self, nullifier: &Nullifier) -> Option<NonMembershipProof> {
        if self.nullifiers.contains(nullifier) {
            return None; // It IS in the set, can't prove non-membership.
        }

        let sorted = self.sorted_vec();
        // Binary search in the sorted vec to find the adjacent neighbors.
        let idx = sorted.binary_search(nullifier).unwrap_err();

        let left_neighbor = if idx > 0 { Some(sorted[idx - 1]) } else { None };
        let right_neighbor = if idx < sorted.len() {
            Some(sorted[idx])
        } else {
            None
        };
        let left_membership_proof = if idx > 0 {
            Some(self.prove_membership_from_sorted(&sorted, idx - 1))
        } else {
            None
        };
        let right_membership_proof = if idx < sorted.len() {
            Some(self.prove_membership_from_sorted(&sorted, idx))
        } else {
            None
        };
        Some(NonMembershipProof {
            absent: *nullifier,
            left_neighbor,
            right_neighbor,
            left_membership_proof,
            right_membership_proof,
            root: self.root(),
        })
    }

    /// Generate a Merkle membership proof for the element at the given index
    /// in the sorted nullifier list.
    ///
    /// The Merkle tree is built over the sorted list of nullifier hashes as leaves.
    /// Each leaf is: BLAKE3("dregg-nullifier-leaf v1", nullifier).
    /// Internal nodes are: BLAKE3("dregg-nullifier-node v1", left || right).
    fn prove_membership_from_sorted(
        &self,
        sorted: &[Nullifier],
        index: usize,
    ) -> MerkleMembershipProof {
        let leaves: Vec<[u8; 32]> = sorted.iter().map(|n| Self::leaf_hash(&n.0)).collect();
        let siblings = Self::merkle_path(&leaves, index);
        MerkleMembershipProof {
            element: sorted[index],
            index,
            siblings,
        }
    }

    /// Hash a leaf node.
    fn leaf_hash(data: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-nullifier-leaf v1");
        hasher.update(data);
        *hasher.finalize().as_bytes()
    }

    /// Hash two children into a parent node.
    fn node_hash(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new_derive_key("dregg-nullifier-node v1");
        hasher.update(left);
        hasher.update(right);
        *hasher.finalize().as_bytes()
    }

    /// Compute the Merkle path (sibling hashes from leaf to root) for a given index.
    fn merkle_path(leaves: &[[u8; 32]], index: usize) -> Vec<[u8; 32]> {
        if leaves.len() <= 1 {
            return vec![];
        }
        let mut siblings = Vec::new();
        let mut current_level = leaves.to_vec();
        let mut idx = index;

        while current_level.len() > 1 {
            // Pad to even length with a zero hash.
            if !current_level.len().is_multiple_of(2) {
                current_level.push([0u8; 32]);
            }
            let sibling_idx = if idx.is_multiple_of(2) {
                idx + 1
            } else {
                idx - 1
            };
            siblings.push(current_level[sibling_idx]);

            // Build next level.
            let mut next_level = Vec::with_capacity(current_level.len() / 2);
            for chunk in current_level.chunks(2) {
                next_level.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current_level = next_level;
            idx /= 2;
        }
        siblings
    }

    /// Compute the Merkle root from leaves.
    fn merkle_root_from_leaves(leaves: &[[u8; 32]]) -> [u8; 32] {
        if leaves.is_empty() {
            return [0u8; 32];
        }
        let mut current_level = leaves.to_vec();
        while current_level.len() > 1 {
            if !current_level.len().is_multiple_of(2) {
                current_level.push([0u8; 32]);
            }
            let mut next_level = Vec::with_capacity(current_level.len() / 2);
            for chunk in current_level.chunks(2) {
                next_level.push(Self::node_hash(&chunk[0], &chunk[1]));
            }
            current_level = next_level;
        }
        current_level[0]
    }

    /// Verify a Merkle membership proof against a given root.
    fn verify_membership_proof(proof: &MerkleMembershipProof, root: &[u8; 32]) -> bool {
        let mut current = Self::leaf_hash(&proof.element.0);
        let mut idx = proof.index;
        for sibling in &proof.siblings {
            if idx.is_multiple_of(2) {
                current = Self::node_hash(&current, sibling);
            } else {
                current = Self::node_hash(sibling, &current);
            }
            idx /= 2;
        }
        current == *root
    }

    /// Current root of the nullifier set (Merkle tree root over all nullifier hashes).
    ///
    /// Leaves are domain-separated hashes of each nullifier (in sorted order).
    /// Internal nodes hash their two children. This produces a proper Merkle tree
    /// that supports membership proofs for non-membership verification.
    pub fn root(&self) -> [u8; 32] {
        if self.nullifiers.is_empty() {
            return [0u8; 32];
        }
        // BTreeSet iterates in sorted order, matching the old Vec behavior.
        let leaves: Vec<[u8; 32]> = self
            .nullifiers
            .iter()
            .map(|n| Self::leaf_hash(&n.0))
            .collect();
        Self::merkle_root_from_leaves(&leaves)
    }

    /// The circuit-faithful node8 leaf for a single nullifier — the EXACT
    /// [`dregg_circuit::heap_root::HeapLeaf`] the deployed rotated noteSpend
    /// grow-gate keys the nullifier accumulator on: `addr` is the folded
    /// nullifier felt (`dregg_circuit::effect_vm::fold_bytes32_to_bb`, the SAME
    /// `nullifier_to_field` fold the freshness path / `DslRevocationTree` use),
    /// `value` is `1` (the existence bit — matching the BEFORE-set leaf shape the
    /// SDK threads into `generate_rotated_note_spend_wide`, `full_turn_proof.rs`).
    ///
    /// Byte-for-byte agreement with the grow-gate is load-bearing: the committed
    /// `nullifier_root` group (rotated limb 26 lane-0 ‖ completion limbs 67..=73)
    /// is opened in-circuit against a `CanonicalHeapTree8` built from these leaves,
    /// so the executor-derived accumulator root must fold through the identical
    /// leaf encoding or the published commitment would not match the proof.
    pub fn accumulator_leaf(nullifier: &[u8; 32]) -> dregg_circuit::heap_root::HeapLeaf {
        dregg_circuit::heap_root::HeapLeaf {
            addr: dregg_circuit::effect_vm::fold_bytes32_to_bb(nullifier),
            value: dregg_circuit::field::BabyBear::ONE,
        }
    }

    /// **The faithful 8-felt (~124-bit) accumulator root of the spent-nullifier
    /// set** — the value that BELONGS in the committed rotated state's
    /// `nullifier_root` group (limb 26 lane-0 ‖ completion limbs 67..=73), so a
    /// cross-node anti-replay commitment is genuine: a node that has accepted a
    /// spend carries a DIFFERENT `root8` than one that has not.
    ///
    /// This is the native `CanonicalHeapTree8` (arity-16 sorted-Poseidon2, depth
    /// [`dregg_circuit::heap_root::HEAP_TREE_DEPTH`]) root the deployed noteSpend
    /// grow-gate opens against — built from [`Self::accumulator_leaf`] over every
    /// nullifier in the set, so it equals the BEFORE-tree root the SDK derives
    /// from `previously_spent` (`full_turn_proof::wide_commit_anchors`) lane-for-lane.
    /// The empty set folds to the native empty root
    /// (`dregg_circuit::heap_root::empty_heap_root_8`), NOT the degenerate
    /// `hash_bytes([0u8; 32])` / `[0u8; 32]` the producer path still fills — that
    /// is the vacuous 1-felt binding this replaces.
    ///
    /// UNLIKE the byte-Merkle [`Self::root`] (which serves the non-membership
    /// proof machinery), this is the FELT-domain accumulator root the rotated
    /// circuit commits to.
    pub fn root8(&self) -> dregg_circuit::Faithful8 {
        let leaves: Vec<dregg_circuit::heap_root::HeapLeaf> = self
            .nullifiers
            .iter()
            .map(|n| Self::accumulator_leaf(&n.0))
            .collect();
        dregg_circuit::heap_root::CanonicalHeapTree8::new(
            leaves,
            dregg_circuit::heap_root::HEAP_TREE_DEPTH,
        )
        .root8()
    }

    /// Verify a non-membership proof against the current root.
    ///
    /// This verifies:
    /// 1. The proof's root matches the given root.
    /// 2. The neighbors (if present) are properly ordered around the absent value.
    /// 3. The neighbors are actually IN the set (via Merkle membership proofs).
    /// 4. The neighbors are adjacent (no element between them).
    pub fn verify_non_membership(proof: &NonMembershipProof, root: &[u8; 32]) -> bool {
        if proof.root != *root {
            return false;
        }

        // Check ordering: left < absent < right.
        if let Some(left) = &proof.left_neighbor
            && left.0 >= proof.absent.0
        {
            return false;
        }
        if let Some(right) = &proof.right_neighbor
            && right.0 <= proof.absent.0
        {
            return false;
        }

        // Verify the left neighbor's Merkle membership proof.
        if let Some(left) = &proof.left_neighbor {
            match &proof.left_membership_proof {
                Some(membership_proof) => {
                    if membership_proof.element != *left {
                        return false;
                    }
                    if !Self::verify_membership_proof(membership_proof, root) {
                        return false;
                    }
                }
                None => return false, // Left neighbor claimed but no membership proof
            }
        }

        // Verify the right neighbor's Merkle membership proof.
        if let Some(right) = &proof.right_neighbor {
            match &proof.right_membership_proof {
                Some(membership_proof) => {
                    if membership_proof.element != *right {
                        return false;
                    }
                    if !Self::verify_membership_proof(membership_proof, root) {
                        return false;
                    }
                }
                None => return false, // Right neighbor claimed but no membership proof
            }
        }

        // Verify adjacency: left and right neighbors must be at consecutive indices.
        if let (Some(left_proof), Some(right_proof)) =
            (&proof.left_membership_proof, &proof.right_membership_proof)
            && right_proof.index != left_proof.index + 1
        {
            return false;
        }

        true
    }
}

impl Default for NullifierSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::note::Note;

    fn make_nullifier(seed: u8) -> Nullifier {
        let owner = {
            let mut k = [0u8; 32];
            k[0] = seed;
            k
        };
        let fields = [1u64, 100, 0, 0, 0, 0, 0, 0];
        let randomness = [seed; 32];
        let note = Note::with_randomness(owner, fields, randomness);
        let spending_key = [seed.wrapping_add(100); 32];
        note.nullifier(&spending_key)
    }

    #[test]
    fn test_nullifier_set_insert_and_contains() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);

        assert!(!set.contains(&n));
        set.insert(n).unwrap();
        assert!(set.contains(&n));
    }

    #[test]
    fn test_nullifier_set_double_spend_rejected() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);

        set.insert(n).unwrap();
        let result = set.insert(n);
        assert_eq!(result, Err(NoteError::DoubleSpend { nullifier: n }));
    }

    #[test]
    fn test_nullifier_set_multiple_inserts() {
        let mut set = NullifierSet::new();
        for i in 0..10 {
            let n = make_nullifier(i);
            set.insert(n).unwrap();
        }
        assert_eq!(set.len(), 10);

        // All should be present.
        for i in 0..10 {
            assert!(set.contains(&make_nullifier(i)));
        }
    }

    #[test]
    fn test_nullifier_set_non_membership_proof() {
        let mut set = NullifierSet::new();
        let n1 = make_nullifier(1);
        let n2 = make_nullifier(2);
        let absent = make_nullifier(3);

        set.insert(n1).unwrap();
        set.insert(n2).unwrap();

        // absent is not in the set.
        assert!(!set.contains(&absent));

        let proof = set.prove_non_membership(&absent).unwrap();
        let root = set.root();
        assert!(NullifierSet::verify_non_membership(&proof, &root));
    }

    #[test]
    fn test_nullifier_set_non_membership_present_returns_none() {
        let mut set = NullifierSet::new();
        let n = make_nullifier(1);
        set.insert(n).unwrap();

        // Can't prove non-membership for something that IS in the set.
        assert!(set.prove_non_membership(&n).is_none());
    }

    #[test]
    fn test_nullifier_set_root_changes_on_insert() {
        let mut set = NullifierSet::new();
        let root_empty = set.root();

        set.insert(make_nullifier(1)).unwrap();
        let root_one = set.root();
        assert_ne!(root_empty, root_one);

        set.insert(make_nullifier(2)).unwrap();
        let root_two = set.root();
        assert_ne!(root_one, root_two);
    }

    /// The empty set's faithful accumulator root is the NATIVE `CanonicalHeapTree8`
    /// empty root — the value a producer must fill for a no-spend accumulator, NOT
    /// the degenerate `hash_bytes([0u8; 32])` / `[0u8; 32]` the lossy producer path
    /// still uses. This is the "empty default the circuit expects" match.
    #[test]
    fn root8_empty_matches_native_empty_heap_root_8() {
        let set = NullifierSet::new();
        assert_eq!(
            set.root8(),
            dregg_circuit::heap_root::empty_heap_root_8(),
            "an empty nullifier set must fold to the native empty node8 root the \
             circuit's nullifier grow-gate defaults to"
        );
    }

    /// A non-empty accumulator fills ALL 8 lanes of the committed nullifier-root
    /// group: the completion lanes (rotated limbs 67..=73, i.e. `limbs()[1..8]`) are
    /// NON-ZERO — the vacuity the lossy 1-felt fill leaves open — and the root
    /// ADVANCES on every distinct insert (the cross-node anti-replay observable: a
    /// node that accepted a spend carries a different root).
    #[test]
    fn root8_grows_nonzero_completion_lanes_and_advances() {
        use dregg_circuit::field::BabyBear;

        let mut set = NullifierSet::new();
        let empty8 = set.root8();

        set.insert(make_nullifier(1)).unwrap();
        let one8 = set.root8();
        assert_ne!(
            empty8, one8,
            "inserting a nullifier must ADVANCE the committed accumulator root"
        );
        assert!(
            one8.limbs()[1..8].iter().any(|f| *f != BabyBear::ZERO),
            "a non-empty accumulator's completion lanes (rotated limbs 67..=73) must \
             be NON-ZERO — the whole point of the faithful 8-felt fill"
        );

        set.insert(make_nullifier(2)).unwrap();
        let two8 = set.root8();
        assert_ne!(
            one8, two8,
            "a second distinct spend must again advance the root (monotone accumulator)"
        );
    }

    /// **Encoding-match tooth (the load-bearing differential):** `root8` over the set
    /// equals a `CanonicalHeapTree8` built DIRECTLY from the deployed grow-gate's
    /// leaf encoding — `HeapLeaf { addr: fold_bytes32_to_bb(nf), value: 1 }` — so the
    /// executor-derived accumulator root is byte-identical to the BEFORE-tree root
    /// the SDK opens the committed `nullifier_root` group against
    /// (`full_turn_proof::wide_commit_anchors` → `generate_rotated_note_spend_wide`).
    /// A drift in this encoding would publish a root the in-circuit open cannot match.
    #[test]
    fn root8_matches_growgate_before_tree_encoding() {
        use dregg_circuit::field::BabyBear;
        use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};

        let nfs = [make_nullifier(7), make_nullifier(42), make_nullifier(99)];
        let mut set = NullifierSet::new();
        for n in &nfs {
            set.insert(*n).unwrap();
        }

        // The grow-gate's BEFORE-tree encoding, reconstructed independently.
        let growgate_leaves: Vec<HeapLeaf> = nfs
            .iter()
            .map(|n| HeapLeaf {
                addr: dregg_circuit::effect_vm::fold_bytes32_to_bb(&n.0),
                value: BabyBear::ONE,
            })
            .collect();
        let expected = CanonicalHeapTree8::new(growgate_leaves, HEAP_TREE_DEPTH).root8();

        assert_eq!(
            set.root8(),
            expected,
            "root8 must fold through the EXACT node8 leaf encoding the deployed \
             noteSpend grow-gate opens against"
        );
    }
}
