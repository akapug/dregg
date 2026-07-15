//! Rust witness builder for the emitted sorted-tree **NON-REVOCATION** descriptor
//! (`dregg-non-revocation-sorted-tree::poseidon2-v1`, authored in
//! `metatheory/Dregg2/Circuit/Emit/NonRevocationEmit.lean`).
//!
//! The non-revocation (freshness) descriptor proves a queried item `x` sits STRICTLY between two
//! ADJACENT committed sorted leaves `L < x < R`, both members of the public revocation-tree root:
//! an item strictly bracketed by two adjacent present leaves cannot itself be present — that is the
//! freshness proof. Until now the only Rust producer for it lived inside
//! `circuit-prove/tests/non_revocation_emit_gate.rs` (`consistent_row` + `trace_of`); there was NO
//! production witness builder — the analog of [`crate::membership_descriptor_4ary::membership_witness_4ary`]
//! / [`crate::adjacency_witness::adjacency_witness`] — that consumers of
//! [`crate::descriptor_by_name::descriptor_by_name`] could call. This module is that builder.
//!
//! [`non_revocation_witness`] emits the 27-column trace (a single active row repeated to a
//! power-of-two height: the queried item + the two adjacent bracketing leaves + their ordering
//! witnesses + the shared depth-2 `hash_2_to_1` Merkle path) and the 2-element public-input vector
//! `[revocation_root, queried_item]` the descriptor pins. It is purely mechanical: it computes the
//! ordering-diff wires and hashes the depth-2 path, but it does NOT itself enforce the bracket,
//! adjacency, or membership — the DESCRIPTOR's gates and 30-bit range lookups are the judge, so a
//! de-bracketed / non-adjacent / forged-root witness yields a well-formed but UNSATISFYING trace
//! that `verify_vm_descriptor2` rejects (mirroring the emit-gate canaries).
//!
//! ## The layout (`NonRevocationEmit.lean` §1; one shared depth-2 active row)
//!
//! | col   | name            | meaning                                                          |
//! |-------|-----------------|------------------------------------------------------------------|
//! | 0     | x               | the queried item (bound to PI 1)                                 |
//! | 1,2   | leaf_l, leaf_r  | the two adjacent bracketing leaves `L < x < R`                   |
//! | 3,4   | lpos, rpos      | their tree positions (adjacency forces `rpos = lpos + 1`)        |
//! | 5,6   | diff_l, diff_r  | `x − L − 1`, `R − x − 1` (the strict-ordering gap witnesses)     |
//! | 7,8   | rl, rr          | `HALF_P_MINUS_1 − diff_l/r` (range-checked to 30 bits)           |
//! | 9     | par0            | `hash_2_to_1(L, R)` (the bottom-sibling parent)                  |
//! | 10,11 | cur1, sib1      | level-1 input (`= par0`) and its sibling                         |
//! | 12    | par1            | `hash_2_to_1(par0, sib1)` = the root (bound to PI 0)             |
//! | 13..19| level-0 lanes   | the 7 witnessed permutation lanes 1..7 of the level-0 chip      |
//! | 20..26| level-1 lanes   | the 7 witnessed permutation lanes 1..7 of the level-1 chip      |

use crate::field::BabyBear;
use crate::poseidon2::hash_2_to_1;

// --- Trace column layout (must match `NonRevocationEmit.lean` §1). ---
/// The queried item `x` (bound to PI 1).
pub const X: usize = 0;
/// The left bracketing leaf `L`.
pub const LEAF_L: usize = 1;
/// The right bracketing leaf `R`.
pub const LEAF_R: usize = 2;
/// The left neighbor's tree position.
pub const LPOS: usize = 3;
/// The right neighbor's tree position (adjacency forces `rpos = lpos + 1`).
pub const RPOS: usize = 4;
/// The lower-gap witness `diff_left = x − L − 1`.
pub const DIFF_L: usize = 5;
/// The upper-gap witness `diff_right = R − x − 1`.
pub const DIFF_R: usize = 6;
/// The left range-wire `HALF_P_MINUS_1 − diff_left`.
pub const RL: usize = 7;
/// The right range-wire `HALF_P_MINUS_1 − diff_right`.
pub const RR: usize = 8;
/// Level-0 node digest `= hash_2_to_1(L, R)`.
pub const PAR0: usize = 9;
/// Level-1 path input (continuity forces `cur1 = par0`).
pub const CUR1: usize = 10;
/// Level-1 sibling.
pub const SIB1: usize = 11;
/// Level-1 node digest `= hash_2_to_1(cur1, sib1)` = the root.
pub const PAR1: usize = 12;
/// First of the level-0 chip's 7 witnessed permutation lanes 1..7.
pub const LEVEL0_LANE_BASE: usize = 13;
/// First of the level-1 chip's 7 witnessed permutation lanes 1..7.
pub const LEVEL1_LANE_BASE: usize = 20;
/// Total main-trace width: 13 base columns + 7 + 7 chip lanes.
pub const NONREV_WIDTH: usize = 27;

/// PI slot: the committed revocation-tree root (first-row `par1`).
pub const PI_ROOT: usize = 0;
/// PI slot: the queried item (first-row `x`; the no-double-spend binding "b").
pub const PI_QUERIED_ITEM: usize = 1;
/// Public-input count.
pub const NONREV_PI_COUNT: usize = 2;

/// `(p−1)/2 − 1` for BabyBear (`p = 2013265921`) — the deployed `revocation.rs::HALF_P_MINUS_1`.
/// The strict-ordering bound `diff < (p−1)/2` is enforced by range-checking `HALF_P_MINUS_1 − diff`
/// to 30 bits.
pub const HALF_P_MINUS_1: u32 = 1_006_632_959;

/// The AIR-name of the emitted descriptor this builder targets (the [`descriptor_by_name`] key).
///
/// [`descriptor_by_name`]: crate::descriptor_by_name::descriptor_by_name
pub const NON_REVOCATION_NAME: &str = "dregg-non-revocation-sorted-tree::poseidon2-v1";

/// The deployed depth-2 binary **sorted-tree** root over four leaves, under the deployed
/// `hash_2_to_1` binary-node hash: `root = hash_2_to_1(hash_2_to_1(l0,l1), hash_2_to_1(l2,l3))`. This
/// is the exact root the descriptor commits to for an adjacent bottom-left bracketing pair
/// (`leaves[0] < x < leaves[1]`, `sib1 = hash_2_to_1(leaves[2], leaves[3])`), so a witness built from
/// such a sorted set carries a BYTE-EQUAL committed root (asserted in the tests).
pub fn non_revocation_root_depth2(leaves: &[BabyBear; 4]) -> BabyBear {
    let par0 = hash_2_to_1(leaves[0], leaves[1]);
    let par1 = hash_2_to_1(leaves[2], leaves[3]);
    hash_2_to_1(par0, par1)
}

/// Build ONE fully-consistent active row for `(x, L, R, lpos, rpos, sib1)`: the two adjacent
/// bottom-sibling leaves `L, R` hashed to `par0 = hash_2_to_1(L, R)`, then
/// `root = hash_2_to_1(par0, sib1)`; the ordering witnesses `diff_left = x − L − 1`,
/// `diff_right = R − x − 1` and their range wires `HALF_P_MINUS_1 − diff` filled so every base gate
/// is satisfied BY CONSTRUCTION of the diff/range wires. The 14 chip-lane columns are left zero
/// (`prove_vm_descriptor2`'s `trace_with_chip_lanes` refills them from the genuine permutation).
///
/// Field subtraction wraps: if `x` is NOT strictly bracketed (`x ≤ L` or `x ≥ R`) the corresponding
/// range wire wraps to `≥ 2^30`, so the descriptor's 30-bit range lookup has no serving limb
/// decomposition and REJECTS — this builder does not pre-judge the bracket. Returns `(row, root)`.
fn consistent_row(
    x: BabyBear,
    l: BabyBear,
    r: BabyBear,
    lpos: u32,
    rpos: u32,
    sib1: BabyBear,
) -> (Vec<BabyBear>, BabyBear) {
    let par0 = hash_2_to_1(l, r);
    let root = hash_2_to_1(par0, sib1);
    let diff_l = x - l - BabyBear::ONE;
    let diff_r = r - x - BabyBear::ONE;
    let half = BabyBear::new(HALF_P_MINUS_1);
    let mut row = vec![BabyBear::ZERO; NONREV_WIDTH];
    row[X] = x;
    row[LEAF_L] = l;
    row[LEAF_R] = r;
    row[LPOS] = BabyBear::new(lpos);
    row[RPOS] = BabyBear::new(rpos);
    row[DIFF_L] = diff_l;
    row[DIFF_R] = diff_r;
    row[RL] = half - diff_l;
    row[RR] = half - diff_r;
    row[PAR0] = par0;
    row[CUR1] = par0; // continuity: cur1 == par0
    row[SIB1] = sib1;
    row[PAR1] = root;
    (row, root)
}

/// Build the 27-column non-revocation trace + the 2-element public-input vector
/// `[revocation_root, queried_item]` for the emitted `dregg-non-revocation-sorted-tree::poseidon2-v1`
/// descriptor.
///
/// `x` is the queried item; `leaf_lower < x < leaf_upper` are the two ADJACENT bracketing leaves (at
/// consecutive positions `lpos`, `rpos = lpos + 1`) whose parent `hash_2_to_1(L, R)` chains through
/// `level1_sibling` to the committed root. The descriptor is the representative depth-2 shape (the
/// adjacent pair as a tree's bottom siblings sharing the path to the root), so `level1_sibling` is the
/// digest of the other bottom pair. The trace is the honest active row repeated to a power-of-two
/// height (the descriptor's gates/lookups are ungated-per-row, so every row must satisfy them).
///
/// The published root (`pis[PI_ROOT]`) is `hash_2_to_1(hash_2_to_1(L,R), level1_sibling)`, the deployed
/// depth-2 sorted-tree root (see [`non_revocation_root_depth2`]); `pis[PI_QUERIED_ITEM]` is `x`. This
/// builder is purely mechanical — it does NOT enforce the strict bracket, the adjacency, or the
/// membership; the descriptor's ordering gates, 30-bit range lookups, adjacency gate, and root /
/// queried-item pins are the judge (a de-bracketed, non-adjacent, forged-leaf, forged-sibling, or
/// forged-root witness proves through this builder but `verify_vm_descriptor2` REJECTS it).
///
/// `height` must be a power of two ≥ 2 (the trace-height requirement); use [`non_revocation_witness`]
/// for the default height-4 trace.
pub fn non_revocation_witness_with_height(
    x: BabyBear,
    leaf_lower: BabyBear,
    lower_pos: u32,
    leaf_upper: BabyBear,
    upper_pos: u32,
    level1_sibling: BabyBear,
    height: usize,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    if height < 2 || !height.is_power_of_two() {
        return Err(format!(
            "non-revocation trace height {height} must be a power of two ≥ 2"
        ));
    }
    let (row, root) = consistent_row(
        x,
        leaf_lower,
        leaf_upper,
        lower_pos,
        upper_pos,
        level1_sibling,
    );
    let trace: Vec<Vec<BabyBear>> = (0..height).map(|_| row.clone()).collect();
    let pis = vec![root, x];
    Ok((trace, pis))
}

/// Build the default (height-4) non-revocation trace + public inputs `[revocation_root, queried_item]`
/// — the thin wrapper over [`non_revocation_witness_with_height`] consumers of
/// [`crate::descriptor_by_name::descriptor_by_name`] call. See that fn for the semantics.
pub fn non_revocation_witness(
    x: BabyBear,
    leaf_lower: BabyBear,
    lower_pos: u32,
    leaf_upper: BabyBear,
    upper_pos: u32,
    level1_sibling: BabyBear,
) -> Result<(Vec<Vec<BabyBear>>, Vec<BabyBear>), String> {
    non_revocation_witness_with_height(
        x,
        leaf_lower,
        lower_pos,
        leaf_upper,
        upper_pos,
        level1_sibling,
        4,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::descriptor_by_name::descriptor_by_name;
    use crate::descriptor_ir2::{
        CHIP_OUT_LANES, EffectVmDescriptor2, MemBoundaryWitness, chip_absorb_all_lanes,
        prove_vm_descriptor2, verify_vm_descriptor2,
    };
    use crate::refusal::{Outcome, classify};
    use std::panic::AssertUnwindSafe;

    /// `true` iff `(trace, pis)` is REJECTED end-to-end (prove refuses OR the produced proof fails
    /// to verify). Prove-THEN-verify is the faithful consumer-posture gate.
    fn rejects(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        match classify("rejects", || {
            let proof =
                prove_vm_descriptor2(desc, trace, pis, &MemBoundaryWitness::default(), &[])?;
            verify_vm_descriptor2(desc, &proof, pis)
        }) {
            // The p3 debug prover's DOCUMENTED unsat verdict — a real refusal.
            // `classify` REDs on any other panic (a stray unwrap, a trace-assembly
            // debug_assert), which used to land here and read as "rejected".
            Outcome::UnsatPanic(_) => true,
            Outcome::Err(_) => true,
            Outcome::Accepted(_) => false,
        }
    }

    /// The honest freshness fixture: item `x = 200` bracketed by adjacent leaves
    /// `L = 100 < 200 < 300 = R` at consecutive positions `0, 1`, with a level-1 sibling that is the
    /// digest of the other bottom pair `[400, 500]` — so `[100, 300, 400, 500]` is a real sorted set.
    fn honest_leaves() -> [BabyBear; 4] {
        [
            BabyBear::new(100),
            BabyBear::new(300),
            BabyBear::new(400),
            BabyBear::new(500),
        ]
    }
    fn honest_sibling() -> BabyBear {
        let leaves = honest_leaves();
        hash_2_to_1(leaves[2], leaves[3])
    }

    /// STEP 1 — THE ARITY-2 CHIP KAT: an arity-2 `TID_P2` absorb IS `hash_2_to_1`, the deployed
    /// binary-node hash the descriptor's chip lookups enforce. This is the hash-level byte-equality
    /// the committed-root equality builds on. Every input is load-bearing (perturbing either changes
    /// the digest AND every lane).
    #[test]
    fn arity2_chip_lookup_is_hash_2_to_1() {
        let a = BabyBear::new(123_456);
        let b = BabyBear::new(789_012);
        let lanes = chip_absorb_all_lanes(2, &[a, b]);
        assert_eq!(
            lanes[0],
            hash_2_to_1(a, b),
            "arity-2 chip out0 must equal hash_2_to_1 (the deployed binary Merkle-node hash)"
        );
        for (j, input) in [a, b].into_iter().enumerate() {
            let mut alt = [a, b];
            alt[j] = input + BabyBear::ONE;
            let alt_lanes = chip_absorb_all_lanes(2, &alt);
            for i in 0..CHIP_OUT_LANES {
                assert_ne!(
                    lanes[i], alt_lanes[i],
                    "chip lane {i} unchanged after perturbing input {j} — that input is dead"
                );
            }
        }
    }

    /// STEP 2 — THE POSITIVE POLE + the LOAD-BEARING ROOT-EQUALITY: an honest bracketed witness proves
    /// through the DISPATCHED emitted descriptor and re-verifies against `[root, queried_item]`, AND
    /// its committed root is BYTE-EQUAL to the deployed depth-2 `hash_2_to_1` sorted-tree root over the
    /// four leaves.
    #[test]
    fn honest_non_revocation_proves_and_verifies_via_dispatch() {
        let desc =
            descriptor_by_name(NON_REVOCATION_NAME).expect("non-revocation descriptor dispatches");
        let leaves = honest_leaves();
        let x = BabyBear::new(200);
        let (trace, pis) = non_revocation_witness(x, leaves[0], 0, leaves[1], 1, honest_sibling())
            .expect("witness builds");

        // THE LOAD-BEARING CLAIM: the committed root is the deployed depth-2 sorted-tree root.
        assert_eq!(
            pis[PI_ROOT],
            non_revocation_root_depth2(&leaves),
            "committed root must be BYTE-EQUAL to the deployed depth-2 hash_2_to_1 sorted-tree root"
        );
        assert_eq!(
            pis[PI_QUERIED_ITEM], x,
            "the queried item is pinned to PI 1"
        );

        let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .expect("the honest freshness witness must prove through the dispatched descriptor");
        verify_vm_descriptor2(&desc, &proof, &pis)
            .expect("the honest proof must re-verify against [root, queried_item]");
    }

    /// STEP 3a — CANARY (forged root): the honest trace, but a FORGED public root PI. The root pin
    /// (`par1 == PI[0]`) is violated → UNSAT. Non-vacuous: the honest PIs are asserted to ACCEPT.
    #[test]
    fn forged_root_refuses() {
        let desc = descriptor_by_name(NON_REVOCATION_NAME).expect("dispatch");
        let leaves = honest_leaves();
        let (trace, pis) = non_revocation_witness(
            BabyBear::new(200),
            leaves[0],
            0,
            leaves[1],
            1,
            honest_sibling(),
        )
        .expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest witness must be accepted — else the canary is vacuous"
        );
        let forged = vec![pis[PI_ROOT] + BabyBear::ONE, pis[PI_QUERIED_ITEM]];
        assert!(
            rejects(&desc, &trace, &forged),
            "a forged revocation root must be REJECTED (root pin)"
        );
    }

    /// STEP 3b — CANARY (forged queried item, the no-double-spend binding "b"): a freshness proof for
    /// item `x` handed a DIFFERENT expected item `x + 1` as `PI[1]`. The queried-item pin (`x == PI[1]`)
    /// is violated → UNSAT.
    #[test]
    fn forged_queried_item_refuses() {
        let desc = descriptor_by_name(NON_REVOCATION_NAME).expect("dispatch");
        let leaves = honest_leaves();
        let (trace, pis) = non_revocation_witness(
            BabyBear::new(200),
            leaves[0],
            0,
            leaves[1],
            1,
            honest_sibling(),
        )
        .expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepted (non-vacuity)"
        );
        let forged = vec![pis[PI_ROOT], pis[PI_QUERIED_ITEM] + BabyBear::ONE];
        assert!(
            rejects(&desc, &trace, &forged),
            "a freshness proof for one item must NOT verify against a different expected item"
        );
    }

    /// STEP 3c — CANARY (de-bracketed item, THE NON-MEMBERSHIP TOOTH): the queried item is set far
    /// above the left neighbor so `diff_left = x − L − 1` violates the strict half-field ordering bound
    /// (`RL = HALF_P_MINUS_1 − diff_left ≥ 2^30`). The 30-bit range lookup on `RL` has no serving limb
    /// decomposition → UNSAT. An item not strictly ordered just above its claimed left neighbor cannot
    /// pass as bracketed.
    #[test]
    fn de_bracketed_item_refuses_by_range() {
        let desc = descriptor_by_name(NON_REVOCATION_NAME).expect("dispatch");
        let leaves = honest_leaves();
        // non-vacuity: the honest bracketed item accepts.
        let (t_ok, pi_ok) = non_revocation_witness(
            BabyBear::new(200),
            leaves[0],
            0,
            leaves[1],
            1,
            honest_sibling(),
        )
        .expect("witness");
        assert!(
            !rejects(&desc, &t_ok, &pi_ok),
            "honest accepted (non-vacuity)"
        );

        // x = L + 1 + 1_500_000_000 ⇒ diff_left = 1_500_000_000 ⇒ RL wraps to ≥ 2^30.
        let x_bad = leaves[0] + BabyBear::ONE + BabyBear::new(1_500_000_000);
        let (trace, pis) =
            non_revocation_witness(x_bad, leaves[0], 0, leaves[1], 1, honest_sibling())
                .expect("witness");
        assert!(
            trace[0][RL].as_u32() >= (1u32 << 30),
            "the de-bracketed left range wire must exceed 2^30 for the range lookup to bite"
        );
        assert!(
            rejects(&desc, &trace, &pis),
            "a de-bracketed item (ordering-bound violated) must be REJECTED by the range lookup"
        );
    }

    /// STEP 3d — CANARY (non-adjacent neighbors): honest bracket, but the two neighbor positions are
    /// NOT consecutive (`rpos = lpos + 2`). The adjacency gate (`rpos − lpos − 1 = 0`) is violated →
    /// UNSAT — if the bracketing leaves are not adjacent, something could sit between them.
    #[test]
    fn non_adjacent_neighbors_refuses() {
        let desc = descriptor_by_name(NON_REVOCATION_NAME).expect("dispatch");
        let leaves = honest_leaves();
        let (trace, pis) = non_revocation_witness(
            BabyBear::new(200),
            leaves[0],
            0,
            leaves[1],
            2, // NOT lpos + 1
            honest_sibling(),
        )
        .expect("witness");
        assert!(
            rejects(&desc, &trace, &pis),
            "non-adjacent bracketing positions must be REJECTED (adjacency gate)"
        );
    }

    /// STEP 3e — CANARY (forged bracketing leaf / forged sibling): the left neighbor (resp. the
    /// level-1 sibling) is changed and the tree honestly recomputes to a DIFFERENT root, but the proof
    /// CLAIMS the original honest root → the root pin (`par1 == PI[0]`) is UNSAT. The bracketing leaf
    /// and the co-path are load-bearing (a fabricated neighbor / sibling is refused).
    #[test]
    fn forged_leaf_or_sibling_refuses() {
        let desc = descriptor_by_name(NON_REVOCATION_NAME).expect("dispatch");
        let leaves = honest_leaves();
        let honest_root = non_revocation_root_depth2(&leaves);

        // forged left leaf (still < x): recomputes to a different root, but claim the honest root.
        let (trace_leaf, pis_leaf) = non_revocation_witness(
            BabyBear::new(200),
            BabyBear::new(150), // was 100
            0,
            leaves[1],
            1,
            honest_sibling(),
        )
        .expect("witness");
        assert_ne!(
            pis_leaf[PI_ROOT], honest_root,
            "changing a leaf changes the root"
        );
        let claim_leaf = vec![honest_root, pis_leaf[PI_QUERIED_ITEM]];
        assert!(
            rejects(&desc, &trace_leaf, &claim_leaf),
            "a bracketing leaf not under the claimed root must be REJECTED (membership pin)"
        );

        // forged level-1 sibling: recomputes to a different root, but claim the honest root.
        let (trace_sib, pis_sib) = non_revocation_witness(
            BabyBear::new(200),
            leaves[0],
            0,
            leaves[1],
            1,
            honest_sibling() + BabyBear::ONE, // wrong co-path
        )
        .expect("witness");
        assert_ne!(
            pis_sib[PI_ROOT], honest_root,
            "changing the sibling changes the root"
        );
        let claim_sib = vec![honest_root, pis_sib[PI_QUERIED_ITEM]];
        assert!(
            rejects(&desc, &trace_sib, &claim_sib),
            "a forged sibling (wrong co-path) must be REJECTED (membership pin)"
        );
    }

    /// STEP 3f — AUDIT CANARY (tampered internal ordering-gap wire): the honest trace is proven, but
    /// the `DIFF_L` column (`x − L − 1`) is corrupted DIRECTLY in-trace (not via a PI or input), while
    /// the PIs stay honest. This attacks the ordering-gap consistency gate from the trace side — a
    /// forge that never passes through the builder's diff computation — and must be REJECTED. This is a
    /// distinct tooth from the input/PI forges above (all of which flow through `consistent_row`).
    #[test]
    fn tampered_diff_wire_refuses() {
        let desc = descriptor_by_name(NON_REVOCATION_NAME).expect("dispatch");
        let leaves = honest_leaves();
        let (trace, pis) = non_revocation_witness(
            BabyBear::new(200),
            leaves[0],
            0,
            leaves[1],
            1,
            honest_sibling(),
        )
        .expect("witness");
        assert!(
            !rejects(&desc, &trace, &pis),
            "honest accepted (non-vacuity)"
        );

        // Corrupt DIFF_L in EVERY row (ungated-per-row) so it no longer equals x − L − 1.
        let mut tampered = trace.clone();
        for row in &mut tampered {
            row[DIFF_L] = row[DIFF_L] + BabyBear::ONE;
        }
        assert_ne!(
            tampered[0][DIFF_L], trace[0][DIFF_L],
            "the tamper must actually change the wire"
        );
        assert!(
            rejects(&desc, &tampered, &pis),
            "a trace with DIFF_L != x - L - 1 must be REJECTED (ordering-gap consistency gate)"
        );
    }

    /// STEP 4 — a non-power-of-two / too-short trace height is refused at build time (the
    /// trace-height requirement).
    #[test]
    fn malformed_height_refuses() {
        let leaves = honest_leaves();
        let x = BabyBear::new(200);
        assert!(
            non_revocation_witness_with_height(x, leaves[0], 0, leaves[1], 1, honest_sibling(), 3)
                .is_err(),
            "height 3 (not a power of two) must be refused"
        );
        assert!(
            non_revocation_witness_with_height(x, leaves[0], 0, leaves[1], 1, honest_sibling(), 1)
                .is_err(),
            "height 1 (< 2) must be refused"
        );
    }

    /// Shape pins: the produced trace matches the descriptor's width/PI-count, and the witness
    /// dispatches to a well-formed descriptor carrying the expected name.
    #[test]
    fn witness_shape_matches_descriptor() {
        let desc = descriptor_by_name(NON_REVOCATION_NAME).expect("dispatch");
        assert_eq!(desc.name, NON_REVOCATION_NAME);
        assert_eq!(desc.trace_width, NONREV_WIDTH);
        assert_eq!(desc.public_input_count, NONREV_PI_COUNT);
        let leaves = honest_leaves();
        let (trace, pis) = non_revocation_witness(
            BabyBear::new(200),
            leaves[0],
            0,
            leaves[1],
            1,
            honest_sibling(),
        )
        .expect("witness");
        assert_eq!(pis.len(), NONREV_PI_COUNT);
        assert!(trace.len().is_power_of_two());
        for row in &trace {
            assert_eq!(row.len(), NONREV_WIDTH);
        }
    }
}
