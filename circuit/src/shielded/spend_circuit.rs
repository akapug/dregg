//! The shielded-spend DSL circuit: membership + nullifier, p3/uni-STARK-clean.
//!
//! This is the STARK side of an M2-a shielded transfer for ONE input note,
//! authored as a `CircuitDescriptor` (data — **zero hand-written AIR**) using
//! only the constraint forms the audited `DslP3Air` symbolic arithmetization
//! supports (`Hash`, `Transition`, `Polynomial`, `Binary`, boundary
//! `PiBinding`), so it proves through the **hiding** uni-STARK path
//! ([`crate::dsl::dsl_p3_air::prove_dsl_zk`], `HidingFriPcs`).
//!
//! # Why not reuse `dsl::note_spending` directly
//!
//! `note_spending`'s DSL trace is designed for the hand-rolled `crate::stark`
//! prover: its commitment-preimage row and power-of-two PADDING rows do not
//! satisfy the chain-continuity `Transition` under p3's `when_transition`
//! gating (which fires on row0→row1 and on interior padding rows). That is why
//! `note_spending` is `crate::stark`-only. Rather than perturb that shared
//! circuit, this lane authors a membership chain whose padding **forward-chains**
//! (`pad.current = prev.parent`, `pad.parent = hash_fact(pad.current,[0,0,0,0])`)
//! so the `Transition` holds on every checked row, and whose leaf IS the input
//! note commitment (no separate preimage row) so there is no row0→row1 break.
//!
//! # What it proves (in zero knowledge, openings blind)
//!
//! Given a published `(nullifier, merkle_root)` and a HIDDEN witness
//! `(leaf_commitment, spending_key[4], merkle path)`:
//! - **(b) membership:** the leaf commitment hashes up the 4-ary Merkle path to
//!   `merkle_root` — `parent = hash_fact(current, [sib0,sib1,sib2,position])` per
//!   level, chained by `next.current == local.parent`, last row's `current`
//!   pinned to `merkle_root`;
//! - **(c) nullifier:** `nullifier = hash_fact(leaf_commitment, key[0..4])`,
//!   bound on row 0 and pinned to the published `nullifier` PI. Reusing a note
//!   (same commitment+key) yields the same nullifier → the chain's nullifier set
//!   rejects the double-spend.
//!
//! The leaf commitment, key, and path live only in the witness; the hiding PCS
//! makes the proof's openings reveal nothing about them. *Owner/leaf is blind.*
//!
//! The note's value/asset live in the Pedersen value commitment (the other half
//! of the transfer), not here — this circuit is the membership+nullifier blind.

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::hash_fact;

/// Trace column layout (width 11), one row per Merkle level (leaf→root).
pub mod col {
    /// Current hash at this level (row 0: the leaf = input note commitment).
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    /// Child position 0..3.
    pub const POSITION: usize = 4;
    /// Parent = hash_fact(current, [sib0, sib1, sib2, position]).
    pub const PARENT: usize = 5;
    /// 1 on row 0 (the leaf row, where the nullifier is bound), 0 elsewhere.
    pub const IS_LEAF: usize = 6;
    /// The nullifier (bound on row 0 to hash_fact(current, key[0..4])).
    pub const NULLIFIER: usize = 7;
    /// Spending-key limbs key[0..4] (4 of the 8 limbs suffice for a binding
    /// nullifier here; the full 8-limb derivation lives in `note_spending`).
    pub const KEY0: usize = 8;
    pub const KEY1: usize = 9;
    pub const KEY2: usize = 10;
    pub const KEY3: usize = 11;
}

/// Trace width.
pub const WIDTH: usize = 12;

/// Public-input indices: `[nullifier, merkle_root]`.
pub mod pi {
    pub const NULLIFIER: usize = 0;
    pub const MERKLE_ROOT: usize = 1;
}

/// Number of public inputs.
pub const PUBLIC_INPUT_COUNT: usize = 2;

/// Build the shielded-spend circuit descriptor.
///
/// Constraints (all DslP3Air-supported):
/// - C1: `is_leaf` is binary.
/// - C2: position validity `pos*(pos-1)*(pos-2)*(pos-3) == 0` (degree 4).
/// - C3: Merkle hash binding `parent == hash_fact(current,[sib0,sib1,sib2,pos])`
///   (every row; padding rows satisfy it by forward-chaining).
/// - C4: nullifier binding on the leaf row (gated by `is_leaf`):
///   `nullifier == hash_fact(current,[key0,key1,key2,key3])`.
/// - C5: chain continuity `next.current == local.parent` (Transition; the
///   forward-chained padding satisfies it on every checked row).
///
/// Boundaries:
/// - Row 0: `nullifier == pi[0]`.
/// - Last row: `current == pi[1]` (merkle_root). The padding's last row carries
///   the root in `current` (= the last real level's parent), so the bound holds.
pub fn shielded_spend_descriptor() -> CircuitDescriptor {
    let p = BABYBEAR_P;
    // position validity coefficients for pos*(pos-1)*(pos-2)*(pos-3):
    //   = pos^4 - 6 pos^3 + 11 pos^2 - 6 pos
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let mut constraints = Vec::new();

    // C1: is_leaf binary.
    constraints.push(ConstraintExpr::Binary { col: col::IS_LEAF });

    // C2: position validity (degree 4).
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION],
            },
        ],
    });

    // C3: Merkle hash binding (every row).
    constraints.push(ConstraintExpr::Hash {
        output_col: col::PARENT,
        input_cols: vec![col::CURRENT, col::SIB0, col::SIB1, col::SIB2, col::POSITION],
    });

    // C4: nullifier binding on the leaf row (gated by is_leaf).
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_LEAF,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::NULLIFIER,
            input_cols: vec![col::CURRENT, col::KEY0, col::KEY1, col::KEY2, col::KEY3],
        }),
    });

    // C5: chain continuity (Transition; forward-chained padding satisfies it).
    constraints.push(ConstraintExpr::Transition {
        next_col: col::CURRENT,
        local_col: col::PARENT,
    });

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::NULLIFIER,
            pi_index: pi::NULLIFIER,
        },
        // The root is the LAST row's PARENT (the membership.rs convention): with
        // forward-chained padding the last row folds the running hash one more
        // time with zero siblings, and that final parent is the committed root.
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT,
            pi_index: pi::MERKLE_ROOT,
        },
    ];

    let columns = vec![
        ColumnDef { name: "current".into(), index: col::CURRENT, kind: ColumnKind::Hash },
        ColumnDef { name: "sib0".into(), index: col::SIB0, kind: ColumnKind::Value },
        ColumnDef { name: "sib1".into(), index: col::SIB1, kind: ColumnKind::Value },
        ColumnDef { name: "sib2".into(), index: col::SIB2, kind: ColumnKind::Value },
        ColumnDef { name: "position".into(), index: col::POSITION, kind: ColumnKind::Value },
        ColumnDef { name: "parent".into(), index: col::PARENT, kind: ColumnKind::Hash },
        ColumnDef { name: "is_leaf".into(), index: col::IS_LEAF, kind: ColumnKind::Binary },
        ColumnDef { name: "nullifier".into(), index: col::NULLIFIER, kind: ColumnKind::Hash },
        ColumnDef { name: "key0".into(), index: col::KEY0, kind: ColumnKind::Value },
        ColumnDef { name: "key1".into(), index: col::KEY1, kind: ColumnKind::Value },
        ColumnDef { name: "key2".into(), index: col::KEY2, kind: ColumnKind::Value },
        ColumnDef { name: "key3".into(), index: col::KEY3, kind: ColumnKind::Value },
    ];

    CircuitDescriptor {
        name: "dregg-shielded-spend-v1".into(),
        trace_width: WIDTH,
        max_degree: 4,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// The shielded-spend DSL circuit.
pub fn shielded_spend_circuit() -> DslCircuit {
    DslCircuit::new(shielded_spend_descriptor())
}

/// A hidden witness for one shielded spend: the leaf (input note commitment),
/// 4 spending-key limbs, and the 4-ary Merkle path to the root.
#[derive(Clone, Debug)]
pub struct ShieldedSpendWitness {
    /// The input note commitment (the Merkle leaf). Hidden.
    pub leaf_commitment: BabyBear,
    /// 4 spending-key limbs binding the nullifier. Hidden.
    pub key: [BabyBear; 4],
    /// Merkle path siblings (3 per level), leaf→root. Hidden.
    pub siblings: Vec<[BabyBear; 3]>,
    /// Merkle path positions (0..3 per level). Hidden.
    pub positions: Vec<u8>,
}

impl ShieldedSpendWitness {
    /// The nullifier this spend reveals: `hash_fact(leaf, key[0..4])`.
    pub fn nullifier(&self) -> BabyBear {
        hash_fact(self.leaf_commitment, &self.key)
    }

    /// The Merkle root this spend proves membership under — the LAST trace row's
    /// PARENT, i.e. the running hash after folding the real levels with
    /// `hash_fact(current, [sib0,sib1,sib2,position])` AND the zero-sibling
    /// padding folds the power-of-two trace appends. This is what the root
    /// boundary pins, so it must include the padding folds (the membership.rs
    /// convention). Derived from [`generate_shielded_spend_trace`] so the witness
    /// root and the trace agree by construction.
    pub fn merkle_root(&self) -> BabyBear {
        let (trace, _pis) = generate_shielded_spend_trace(self);
        trace.last().unwrap()[col::PARENT]
    }
}

/// Generate the shielded-spend trace + public inputs `[nullifier, merkle_root]`.
///
/// One row per Merkle level (leaf→root), padded to a power of two by
/// **forward-chaining** (each padding row's `current = prev.parent`,
/// `parent = hash_fact(current,[0,0,0,0])`), so the chain-continuity transition
/// holds on every checked row and the final row's `current == merkle_root`.
pub fn generate_shielded_spend_trace(
    witness: &ShieldedSpendWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = witness.siblings.len();
    assert_eq!(witness.positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2");

    let mut trace: Vec<Vec<BabyBear>> = Vec::new();
    let nullifier = witness.nullifier();

    let mut current = witness.leaf_commitment;
    for i in 0..depth {
        let pos = witness.positions[i];
        assert!(pos < 4, "position must be 0..3");
        let position = BabyBear::new(pos as u32);
        let sib = witness.siblings[i];
        let parent = hash_fact(current, &[sib[0], sib[1], sib[2], position]);

        let mut row = vec![BabyBear::ZERO; WIDTH];
        row[col::CURRENT] = current;
        row[col::SIB0] = sib[0];
        row[col::SIB1] = sib[1];
        row[col::SIB2] = sib[2];
        row[col::POSITION] = position;
        row[col::PARENT] = parent;
        if i == 0 {
            row[col::IS_LEAF] = BabyBear::ONE;
            row[col::NULLIFIER] = nullifier;
            row[col::KEY0] = witness.key[0];
            row[col::KEY1] = witness.key[1];
            row[col::KEY2] = witness.key[2];
            row[col::KEY3] = witness.key[3];
        }
        trace.push(row);
        current = parent;
    }

    // Forward-chained padding to a power of two: each padding row sets
    // `current = prev.parent` (so the chain-continuity Transition holds) and
    // `parent = hash_fact(current,[0,0,0,0])` (so the Merkle-hash constraint
    // holds with zero siblings). `is_leaf = 0` so the nullifier binding does not
    // fire and `position = 0` satisfies position validity.
    let target = depth.next_power_of_two().max(2);
    while trace.len() < target {
        let prev_parent = trace.last().unwrap()[col::PARENT];
        let pad_parent = hash_fact(
            prev_parent,
            &[BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
        );
        let mut row = vec![BabyBear::ZERO; WIDTH];
        row[col::CURRENT] = prev_parent;
        row[col::PARENT] = pad_parent;
        trace.push(row);
    }

    // The committed root is the LAST row's PARENT (membership.rs convention):
    // the running hash after the real levels AND any zero-sibling padding folds.
    // The root boundary pins exactly this cell.
    let merkle_root = trace.last().unwrap()[col::PARENT];
    let public_inputs = vec![nullifier, merkle_root];
    (trace, public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dsl::dsl_p3_air::{prove_dsl_zk, verify_dsl_zk};

    /// A bad trace makes the self-verifying prover EITHER return `Err` OR (in a
    /// debug build) panic in p3's `check_constraints` debug assertion. Either way
    /// it does NOT yield a verifying proof. This helper treats both as
    /// "rejected", which is the soundness property we test.
    fn proving_rejects(
        circuit: &DslCircuit,
        trace: &[Vec<BabyBear>],
        pis: &[BabyBear],
    ) -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_dsl_zk(circuit, trace, pis)
        }));
        match r {
            Err(_) => true,        // panicked in the debug constraint check
            Ok(Err(_)) => true,    // self-verify rejected
            Ok(Ok(_)) => false,    // produced a verifying proof — UNSOUND
        }
    }

    fn test_witness(depth: usize) -> ShieldedSpendWitness {
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            positions.push((i % 4) as u8);
            siblings.push([
                BabyBear::new((i as u32) * 5 + 1),
                BabyBear::new((i as u32) * 5 + 2),
                BabyBear::new((i as u32) * 5 + 3),
            ]);
        }
        ShieldedSpendWitness {
            leaf_commitment: BabyBear::new(0xABCDE),
            key: [
                BabyBear::new(7),
                BabyBear::new(8),
                BabyBear::new(9),
                BabyBear::new(10),
            ],
            siblings,
            positions,
        }
    }

    /// The descriptor routes through the audited `DslP3Air` symbolic
    /// arithmetization (no unsupported constraint form). If this fails, the
    /// circuit is not p3-clean.
    #[test]
    fn descriptor_is_p3_clean() {
        let dsl = shielded_spend_circuit();
        // Every constraint must be an algebraic / supported form (Hash forms
        // included); `try_from_dsl` errors on MerkleHash / Lookup / cross-row.
        crate::dsl::dsl_p3_air::DslP3Air::try_from_dsl(&dsl)
            .expect("shielded-spend descriptor must be DslP3Air-clean");
    }

    /// Both polarities at the circuit level: an honest trace proves+verifies
    /// through the hiding path; a trace whose membership is forged (a tampered
    /// sibling) cannot produce a verifying proof.
    #[test]
    fn honest_proves_forged_membership_fails() {
        let circuit = shielded_spend_circuit();

        // TRUE: honest membership+nullifier proves and verifies (blind).
        let w = test_witness(4);
        let (trace, pis) = generate_shielded_spend_trace(&w);
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("honest shielded-spend must prove through the hiding path");
        verify_dsl_zk(&circuit, &proof, &pis).expect("honest proof must verify");

        // FALSE: corrupt a Merkle sibling in the trace WITHOUT updating the
        // chained parent — the Merkle-hash constraint no longer holds, so the
        // self-verifying prover must refuse to produce a proof.
        let mut bad = trace.clone();
        bad[1][col::SIB0] = bad[1][col::SIB0] + BabyBear::ONE;
        assert!(
            proving_rejects(&circuit, &bad, &pis),
            "a forged-membership trace must NOT produce a verifying hiding proof"
        );
    }

    /// The nullifier binding bites: a trace whose row-0 nullifier disagrees with
    /// `hash_fact(leaf, key)` cannot prove.
    #[test]
    fn forged_nullifier_fails() {
        let circuit = shielded_spend_circuit();
        let w = test_witness(4);
        let (mut trace, pis) = generate_shielded_spend_trace(&w);
        // Tamper ONLY the row-0 nullifier cell (leave the PI). Now BOTH the C4
        // binding (`nullifier == hash_fact(current,key)`) AND the row-0 boundary
        // (`nullifier == pi[0]`) fail — the prover must not yield a proof.
        trace[0][col::NULLIFIER] = trace[0][col::NULLIFIER] + BabyBear::ONE;
        assert!(
            proving_rejects(&circuit, &trace, &pis),
            "a forged-nullifier trace must NOT produce a verifying hiding proof"
        );
    }
}
