//! Tiered revocation system: hot Merkle set + settled polynomial accumulator.
//!
//! This module implements a two-tier revocation architecture:
//!
//! - **Hot set** (recent, small): A sorted Merkle tree ([`DslRevocationTree`]) capped at
//!   `hot_capacity` entries. Uses the same non-membership proof mechanism as the existing
//!   revocation circuit. Proofs are cheap and the tree is small.
//!
//! - **Settled set** (historical, O(1) state): The polynomial accumulator
//!   ([`AccumulatorNonRevocationAir`] via DSL). All accumulated revocations live here after
//!   settlement. Verification is O(1) in state size.
//!
//! # Settlement
//!
//! Every `CHECKPOINT_INTERVAL` (100 blocks), the hot set is absorbed into the settled
//! accumulator. The hot set is then cleared. Outstanding accumulator witnesses must refresh
//! (the accumulator value changed), but between settlements, accumulator witnesses remain
//! stable.
//!
//! # Non-revocation proof
//!
//! A holder proves non-revocation against BOTH tiers simultaneously:
//! ```text
//! full_non_revocation = prove_not_in_hot_set(hot_tree, h)
//!                     AND prove_not_in_settled_set(accumulator, alpha, h)
//! ```
//!
//! # Benefit
//!
//! With a pure accumulator, EVERY revocation invalidates ALL outstanding witnesses.
//! With tiered revocation, only settlement (every 100 blocks) invalidates accumulator
//! witnesses. Between settlements, only the small hot tree changes.

use crate::accumulator_types::{ExtElem, compute_accumulator, derive_alpha};
use crate::dsl::revocation::{DslRevocationTree, TREE_DEPTH};
use crate::field::BabyBear;

// ============================================================================
// Constants
// ============================================================================

/// Default checkpoint interval: absorb hot set into accumulator every 100 blocks.
pub const CHECKPOINT_INTERVAL: usize = 100;

/// Default hot set capacity. When the hot set reaches this many entries, it
/// auto-settles into the accumulator.
pub const DEFAULT_HOT_CAPACITY: usize = 64;

// ============================================================================
// TieredRevocationSet
// ============================================================================

/// Two-tier revocation set: small hot Merkle tree + polynomial accumulator.
///
/// The hot set contains recent revocations (at most `hot_capacity` entries).
/// The settled set contains all historical revocations absorbed via settlement.
///
/// Both the `hot_root` and `settled_accumulator` are committed state stored in
/// the node and checkpointed on the blocklace.
#[derive(Clone, Debug)]
pub struct TieredRevocationSet {
    /// Hot set: recent revocations stored as sorted Merkle tree.
    pub hot: DslRevocationTree,
    /// Raw hot entries (needed to rebuild tree on insert and to settle).
    hot_entries: Vec<BabyBear>,
    /// Settled accumulator value: product(alpha - h_i) for all settled h_i.
    pub settled_accumulator: ExtElem,
    /// Alpha challenge for the settled accumulator (derived from settled set commitment).
    pub settled_alpha: ExtElem,
    /// All hashes absorbed into the settled accumulator (needed for witness generation
    /// and alpha re-derivation on settlement).
    settled_entries: Vec<BabyBear>,
    /// Maximum entries in the hot set before auto-settlement.
    pub hot_capacity: usize,
    /// Current number of entries in the hot set.
    pub hot_count: usize,
    /// Current epoch (increments on each settlement).
    pub epoch: u64,
}

impl TieredRevocationSet {
    /// Create a new tiered revocation set with the given hot capacity.
    ///
    /// Starts with an empty hot set and an empty settled accumulator.
    pub fn new(hot_capacity: usize) -> Self {
        let hot = DslRevocationTree::new(vec![], TREE_DEPTH);
        let settled_entries: Vec<BabyBear> = vec![];
        let settled_alpha = derive_alpha(&settled_entries);
        let settled_accumulator = compute_accumulator(&settled_entries, settled_alpha);

        Self {
            hot,
            hot_entries: vec![],
            settled_accumulator,
            settled_alpha,
            settled_entries,
            hot_capacity,
            hot_count: 0,
            epoch: 0,
        }
    }

    /// Create a tiered revocation set with default capacity.
    pub fn with_default_capacity() -> Self {
        Self::new(DEFAULT_HOT_CAPACITY)
    }

    /// Revoke a hash. Adds to the hot set.
    ///
    /// If the hot set reaches capacity, automatically triggers settlement.
    pub fn revoke(&mut self, hash: BabyBear) {
        // Don't double-revoke
        if self.is_revoked(&hash) {
            return;
        }

        self.hot_entries.push(hash);
        self.hot = DslRevocationTree::new(self.hot_entries.clone(), TREE_DEPTH);
        self.hot_count += 1;

        if self.hot_count >= self.hot_capacity {
            self.settle();
        }
    }

    /// Settle: absorb all hot entries into the settled accumulator, then clear the hot set.
    ///
    /// After settlement:
    /// - The hot set is empty (new hot root).
    /// - The settled accumulator includes all previously-hot entries.
    /// - Alpha is re-derived from the full settled set.
    /// - The epoch increments.
    /// - All outstanding accumulator witnesses are invalidated and must be refreshed.
    pub fn settle(&mut self) {
        if self.hot_entries.is_empty() {
            return;
        }

        // Absorb hot entries into settled
        self.settled_entries.extend_from_slice(&self.hot_entries);

        // Re-derive alpha from the full settled set
        self.settled_alpha = derive_alpha(&self.settled_entries);

        // Recompute accumulator: product(alpha - h_i) for all settled entries
        self.settled_accumulator = compute_accumulator(&self.settled_entries, self.settled_alpha);

        // Clear hot set
        self.hot_entries.clear();
        self.hot = DslRevocationTree::new(vec![], TREE_DEPTH);
        self.hot_count = 0;

        // Increment epoch
        self.epoch += 1;
    }

    /// Check if a hash is revoked in either tier.
    pub fn is_revoked(&self, hash: &BabyBear) -> bool {
        self.is_in_hot(hash) || self.is_in_settled(hash)
    }

    /// Check if a hash is in the hot set.
    pub fn is_in_hot(&self, hash: &BabyBear) -> bool {
        self.hot.contains(hash)
    }

    /// Check if a hash is in the settled set.
    pub fn is_in_settled(&self, hash: &BabyBear) -> bool {
        self.settled_entries.contains(hash)
    }

    /// Get the current hot root (committed state).
    pub fn hot_root(&self) -> BabyBear {
        self.hot.root()
    }

    /// Get the current settled accumulator value (committed state).
    pub fn accumulator(&self) -> ExtElem {
        self.settled_accumulator
    }

    /// Get the current alpha challenge.
    pub fn alpha(&self) -> ExtElem {
        self.settled_alpha
    }

    /// Get the current epoch.
    pub fn current_epoch(&self) -> u64 {
        self.epoch
    }

    /// Number of entries in the hot set.
    pub fn hot_size(&self) -> usize {
        self.hot_count
    }

    /// Number of entries in the settled set.
    pub fn settled_size(&self) -> usize {
        self.settled_entries.len()
    }

    /// Total number of revoked entries across both tiers.
    pub fn total_revoked(&self) -> usize {
        self.hot_count + self.settled_entries.len()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: create a hash from a u32 value.
    fn test_hash(val: u32) -> BabyBear {
        // Avoid 0 and p-1 (sentinels) and ensure non-zero
        BabyBear::new(val.max(1).min(2013265919))
    }

    #[test]
    fn test_settlement_absorbs_hot_into_accumulator() {
        let mut set = TieredRevocationSet::new(10);
        let h1 = test_hash(500);
        let h2 = test_hash(600);
        set.revoke(h1);
        set.revoke(h2);

        assert_eq!(set.hot_size(), 2);
        assert_eq!(set.settled_size(), 0);

        // Settle
        set.settle();

        assert_eq!(set.hot_size(), 0);
        assert_eq!(set.settled_size(), 2);
        assert_eq!(set.current_epoch(), 1);

        // Items are still revoked (now in settled)
        assert!(set.is_revoked(&h1));
        assert!(set.is_revoked(&h2));
        assert!(set.is_in_settled(&h1));
        assert!(!set.is_in_hot(&h1));
    }

    #[test]
    fn test_auto_settle_on_capacity() {
        let capacity = 4;
        let mut set = TieredRevocationSet::new(capacity);

        // Revoke exactly capacity items
        for i in 1..=capacity {
            set.revoke(test_hash(i as u32 * 100));
        }

        // Should have auto-settled
        assert_eq!(set.hot_size(), 0);
        assert_eq!(set.settled_size(), capacity);
        assert_eq!(set.current_epoch(), 1);
    }

    #[test]
    fn test_double_revoke_is_idempotent() {
        let mut set = TieredRevocationSet::new(10);
        let h = test_hash(77);
        set.revoke(h);
        set.revoke(h); // should not increment count

        assert_eq!(set.hot_size(), 1);
    }

    #[test]
    fn test_empty_settlement_is_noop() {
        let mut set = TieredRevocationSet::new(10);
        set.settle();
        assert_eq!(set.current_epoch(), 0); // no epoch bump
        assert_eq!(set.settled_size(), 0);
    }

    #[test]
    fn test_total_revoked_across_tiers() {
        let mut set = TieredRevocationSet::new(10);
        set.revoke(test_hash(1));
        set.revoke(test_hash(2));
        set.settle();
        set.revoke(test_hash(3));

        assert_eq!(set.total_revoked(), 3);
        assert_eq!(set.settled_size(), 2);
        assert_eq!(set.hot_size(), 1);
    }
}
