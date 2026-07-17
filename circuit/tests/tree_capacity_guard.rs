//! RIG (assumption-rigging / depth-shape-params) — the deployed sorted-Merkle trees'
//! CAPACITY guard and their DEPLOYED DEPTH.
//!
//! ASSUMPTION (circuit/src/{cap_root,heap_root,openable_fields_root}.rs):
//!   The capability tree (`CAP_TREE_DEPTH=16`), heap tree (`HEAP_TREE_DEPTH=16`), and
//!   openable-fields tree (`FIELDS_TREE_DEPTH=CAP_TREE_DEPTH`) each have a hard-coded
//!   capacity of `2^depth` positions, part of which is spent on sentinels. Overflow is
//!   guarded ONLY by a bare `assert!(len <= 2^depth, "... exceeds tree capacity ...")`.
//!   The guard is depth-parameterized; the deployed depth is 16.
//!
//! WHY IT MATTERS (from the scout): these constructors are on LIVE, non-test-gated
//! paths — `cell/src/state.rs:983` rebuilds the heap tree on every heap write,
//! `turn/src/executor/authorize.rs:1192` rebuilds the cap tree over the holder's FULL
//! c-list on every action that consumes a cap. Nothing upstream bounds how many
//! entries a cell can accumulate, so the guard is the last line: it must FAIL LOUD on
//! overflow (never silently truncate/drop entries — openable's `new` `resize`s to
//! capacity, which would DROP entries if the assert were gone) and it must NOT fire
//! early (real work up to exactly capacity).
//!
//! WHY IT WAS UNRIGGED: no `#[should_panic]`, no capacity-boundary test, and no
//! depth-shape pin existed anywhere in circuit/tests or the three src `#[cfg(test)]`
//! modules (grep for `should_panic` + `capacity`/`exceeds tree capacity` returned only
//! the assert strings themselves).
//!
//! THE TEETH (each proven to bite by mutation — see the TESTQALOG entry):
//!   - Delete the `assert!` (silent truncate) -> the `*_overflow_panics` test no longer
//!     panics -> RED.
//!   - Tighten `<=` to `<` (fire one early) -> the `*_at_capacity_succeeds` test panics
//!     in a non-should_panic test -> RED.
//!   - Change the sentinel count (cap/openable use 2 sentinels, heap uses 1) -> the
//!     real-capacity boundary shifts by one -> the at-capacity/overflow split goes RED.
//!   - Bump a deployed depth -> the `deployed_tree_depths_are_sixteen` pin goes RED.
//!
//! The boundary tests run at a SMALL depth (D=4) because the guard is purely
//! depth-parameterized (`len <= 1<<depth`) — identical logic to depth 16, but a depth-16
//! tree densely materializes 65536 leaves. The deployed depth (16) is pinned separately
//! by `deployed_tree_depths_are_sixteen`, binding the small-depth logic to production.

use dregg_circuit::cap_root::{CAP_TREE_DEPTH, CanonicalCapTree, CapLeaf};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{CanonicalHeapTree8, HEAP_TREE_DEPTH, HeapLeaf};
use dregg_circuit::openable_fields_root::{FIELDS_TREE_DEPTH, FieldsLeaf, OpenableFieldsTree};

/// Small depth for the boundary tests. capacity = 2^D = 16 positions.
const D: usize = 4;
const CAPACITY: usize = 1 << D;

fn cap_leaf(key: u32) -> CapLeaf {
    // `slot_hash` is the sort key. Distinct, nonzero, well below SENTINEL_MAX
    // (=BABYBEAR_P-1) and not SENTINEL_MIN (=0), so no dedup/collision with the
    // MIN/MAX sentinels the builder brackets with.
    CapLeaf {
        slot_hash: BabyBear::new(key),
        target: BabyBear::ZERO,
        auth_tag: BabyBear::ZERO,
        mask_lo: BabyBear::ZERO,
        mask_hi: BabyBear::ZERO,
        expiry: BabyBear::ZERO,
        breadstuff: BabyBear::ZERO,
    }
}

fn cap_leaves(n: usize) -> Vec<CapLeaf> {
    (1..=n as u32).map(cap_leaf).collect()
}

fn heap_leaves(n: usize) -> Vec<HeapLeaf> {
    (1..=n as u32)
        .map(|a| HeapLeaf::entry(BabyBear::new(a), BabyBear::ZERO))
        .collect()
}

fn fields_leaves(n: usize) -> Vec<FieldsLeaf> {
    (1..=n as u32)
        .map(|k| FieldsLeaf {
            key_hash: BabyBear::new(k),
            value: BabyBear::ZERO,
        })
        .collect()
}

// ---------------------------------------------------------------------------
// DEPTH-SHAPE PIN
// ---------------------------------------------------------------------------

/// The three deployed sorted-tree depths are all exactly 16, and the openable-fields
/// depth is COUPLED to the cap depth (`FIELDS_TREE_DEPTH = CAP_TREE_DEPTH`). A silent
/// change to any of these reshapes every membership witness, root, and VK that folds
/// against `2^depth`; force it to be conscious.
#[test]
fn deployed_tree_depths_are_sixteen() {
    assert_eq!(CAP_TREE_DEPTH, 16, "capability tree depth drifted from 16");
    assert_eq!(HEAP_TREE_DEPTH, 16, "heap tree depth drifted from 16");
    assert_eq!(
        FIELDS_TREE_DEPTH, 16,
        "openable-fields tree depth drifted from 16"
    );
    assert_eq!(
        FIELDS_TREE_DEPTH, CAP_TREE_DEPTH,
        "openable-fields depth is defined as CAP_TREE_DEPTH; the coupling was broken"
    );
}

// ---------------------------------------------------------------------------
// CAP TREE — 2 sentinels (MIN/MAX) => real capacity = 2^depth - 2
// ---------------------------------------------------------------------------

/// Non-vacuity: at EXACTLY the real capacity (2^D - 2 real leaves + 2 sentinels =
/// 2^D positions) the build must succeed cleanly. If the guard fired early
/// (`<=` -> `<`), this panics -> RED.
#[test]
fn cap_tree_at_capacity_succeeds() {
    let real = CAPACITY - 2; // + MIN + MAX sentinels = CAPACITY
    let tree = CanonicalCapTree::new(cap_leaves(real), D);
    // Root is computable (no panic, no truncation): the guard admitted the full set.
    let _ = tree.root();
}

/// THE TOOTH: one real leaf past capacity (2^D - 1 real + 2 sentinels = 2^D + 1
/// positions) must FAIL LOUD, not silently truncate. If the `assert!` were removed,
/// this would not panic -> RED.
#[test]
#[should_panic(expected = "exceeds tree capacity")]
fn cap_tree_overflow_panics() {
    let real = CAPACITY - 1; // + 2 sentinels = CAPACITY + 1 > CAPACITY
    let _ = CanonicalCapTree::new(cap_leaves(real), D);
}

// ---------------------------------------------------------------------------
// HEAP TREE (8-felt, the live cell/src/state.rs path) — 1 sentinel (MIN only)
// => real capacity = 2^depth - 1
// ---------------------------------------------------------------------------

/// Non-vacuity: heap uses a SINGLE MIN sentinel (the MAX sentinel is only a terminal
/// pointer), so real capacity is 2^D - 1. At exactly that count the build succeeds.
#[test]
fn heap_tree_at_capacity_succeeds() {
    let real = CAPACITY - 1; // + 1 MIN sentinel = CAPACITY
    let tree = CanonicalHeapTree8::new(heap_leaves(real), D);
    let _ = tree.root8();
}

/// THE TOOTH: one real leaf past capacity (2^D real + 1 sentinel = 2^D + 1) panics.
#[test]
#[should_panic(expected = "exceeds tree capacity")]
fn heap_tree_overflow_panics() {
    let real = CAPACITY; // + 1 sentinel = CAPACITY + 1 > CAPACITY
    let _ = CanonicalHeapTree8::new(heap_leaves(real), D);
}

// ---------------------------------------------------------------------------
// OPENABLE-FIELDS TREE — 2 sentinels => real capacity = 2^depth - 2.
// This one DENSELY `resize`s leaf_digests to capacity, so a missing guard would
// TRUNCATE overflow entries silently (drop state) rather than merely miscount.
// ---------------------------------------------------------------------------

#[test]
fn openable_fields_tree_at_capacity_succeeds() {
    let real = CAPACITY - 2; // + 2 sentinels = CAPACITY
    let tree = OpenableFieldsTree::new(fields_leaves(real), D);
    let _ = tree.root();
}

/// THE TOOTH: overflow must panic, NOT silently `resize`-truncate the entry set.
#[test]
#[should_panic(expected = "exceeds tree capacity")]
fn openable_fields_tree_overflow_panics() {
    let real = CAPACITY - 1; // + 2 sentinels = CAPACITY + 1 > CAPACITY
    let _ = OpenableFieldsTree::new(fields_leaves(real), D);
}
