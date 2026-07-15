//! Backward-compatible re-exports for Merkle AIR types, plus the AUDITED
//! Lean-emitted IR2 Merkle-Poseidon2 membership prove/verify path.
//!
//! The production DSL implementation lives in [`crate::dsl::membership`]; the
//! legacy types are in [`crate::merkle_types`].
//!
//! # Why the p3-batch membership path exists (TCB-shrinking)
//!
//! `dsl::membership::prove_membership_dsl` / `verify_membership_dsl` route the
//! 4-ary Merkle membership proof through the **bespoke** `crate::stark` prover,
//! whose hand-rolled FRI has no terminal low-degree test and never low-degree-
//! tests the trace columns. The full-turn proof's MEMBERSHIP sub-proof leg used
//! that unaudited verifier.
//!
//! This module routes the SAME membership statement through the assured IR2
//! interpreter. Its algebra is emitted by
//! `Dregg2.Circuit.Emit.MerkleMembership4aryEmit`; Rust only parses that exact
//! artifact and constructs witness rows. Poseidon2 is enforced by the emitted
//! chip lookup, with position-validity, child arrangement, hash-chain
//! continuity, and `[leaf, root]` boundary binding all Lean-authored.
//!
//! The proof carries a REAL terminal low-degree test (FRI, via the production
//! `create_config`: log_blowup=3, 38 queries, 16 PoW) and an anti-ghost tooth: a forged `root`
//! (or `leaf`) public input
//! is REJECTED by the audited verifier — see the tests.

pub use crate::merkle_types::{
    MERKLE_AIR_WIDTH, MerkleAir, MerkleLevelWitness, MerkleWitness, TREE_DEPTH,
    compute_parent_poseidon2, create_test_witness,
};

pub use membership_p3::*;

mod membership_p3 {
    use crate::descriptor_ir2::{
        DreggStarkConfig, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
        verify_vm_descriptor2,
    };
    use crate::field::BabyBear;
    use crate::membership_descriptor_4ary::{
        membership_descriptor_of_depth_4ary, membership_witness_4ary,
    };

    /// A Merkle-Poseidon2 membership proof interpreted from Lean-emitted IR2.
    pub type MembershipP3Proof = Ir2BatchProof<DreggStarkConfig>;

    /// Errors from the audited p3 Merkle-membership path.
    #[derive(Debug, Clone)]
    pub enum MembershipP3Error {
        /// The witness was malformed (depth < 2, or siblings/positions mismatch).
        InvalidWitness(String),
        /// The audited Plonky3 verifier rejected the proof.
        VerificationFailed(String),
    }

    impl core::fmt::Display for MembershipP3Error {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            match self {
                MembershipP3Error::InvalidWitness(r) => {
                    write!(f, "invalid membership witness: {r}")
                }
                MembershipP3Error::VerificationFailed(r) => {
                    write!(f, "p3 membership verification failed: {r}")
                }
            }
        }
    }

    impl std::error::Error for MembershipP3Error {}

    /// Build the public inputs `[leaf, root]` for a membership statement, exactly as
    /// the DSL path's `generate_merkle_poseidon2_trace` does (so a caller can bind
    /// them into a composed proof). The `root` is the Poseidon2 hash-chain root the
    /// `(leaf, siblings, positions)` witness recomputes.
    pub fn membership_public_inputs(
        leaf: BabyBear,
        siblings: &[[BabyBear; 3]],
        positions: &[u8],
    ) -> Result<Vec<BabyBear>, MembershipP3Error> {
        if siblings.len() < 2 {
            return Err(MembershipP3Error::InvalidWitness(
                "need at least depth 2 for STARK".into(),
            ));
        }
        if siblings.len() != positions.len() {
            return Err(MembershipP3Error::InvalidWitness(
                "siblings/positions length mismatch".into(),
            ));
        }
        let (_trace, pis) = membership_witness_4ary(leaf, siblings, positions)
            .map_err(MembershipP3Error::InvalidWitness)?;
        Ok(pis)
    }

    /// Prove 4-ary Merkle-Poseidon2 membership by interpreting the Lean-emitted
    /// IR2 descriptor through the audited Plonky3 backend.
    ///
    /// Proves that `leaf` is a member of the Poseidon2 Merkle tree whose root is
    /// recomputed from `(siblings, positions)`. The returned proof self-verifies
    /// before return (matching the other migrated AIRs), so a returned proof is one
    /// the audited verifier accepts. The public inputs are `[leaf, root]`.
    pub fn prove_membership_p3(
        leaf: BabyBear,
        siblings: &[[BabyBear; 3]],
        positions: &[u8],
    ) -> Result<MembershipP3Proof, MembershipP3Error> {
        if siblings.len() < 2 {
            return Err(MembershipP3Error::InvalidWitness(
                "need at least depth 2 for STARK".into(),
            ));
        }
        if siblings.len() != positions.len() {
            return Err(MembershipP3Error::InvalidWitness(
                "siblings/positions length mismatch".into(),
            ));
        }

        let depth = siblings.len();
        let desc = membership_descriptor_of_depth_4ary(depth);
        let (trace, pis) = membership_witness_4ary(leaf, siblings, positions)
            .map_err(MembershipP3Error::InvalidWitness)?;
        prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])
            .map_err(MembershipP3Error::VerificationFailed)
    }

    /// Verify a Merkle-Poseidon2 membership proof on the AUDITED Plonky3 verifier
    /// (`p3-batch-stark`). `public_inputs` must be `[leaf, root]`.
    ///
    /// The verifier reconstructs `CommonData` from the AIR + the proof's degree
    /// bits — it needs no witness (the genuine standalone-verifier path).
    pub fn verify_membership_p3(
        proof: &MembershipP3Proof,
        public_inputs: &[BabyBear],
    ) -> Result<(), MembershipP3Error> {
        if public_inputs.len() != 2 {
            return Err(MembershipP3Error::VerificationFailed(
                "membership public inputs must be [leaf, root]".into(),
            ));
        }
        let desc = membership_descriptor_of_depth_4ary(
            proof
                .degree_bits
                .first()
                .copied()
                .and_then(|bits| 1usize.checked_shl(bits as u32))
                .ok_or_else(|| {
                    MembershipP3Error::VerificationFailed(
                        "membership proof has no valid main-trace degree".into(),
                    )
                })?,
        );
        verify_vm_descriptor2(&desc, proof, public_inputs)
            .map_err(MembershipP3Error::VerificationFailed)
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::dsl::membership::create_test_witness as dsl_create_test_witness;

        /// Honest membership proves + verifies through the AUDITED p3 verifier, and
        /// its public inputs `[leaf, root]` match the DSL path's exactly.
        #[test]
        fn membership_p3_proves_and_verifies_honest() {
            let leaf = BabyBear::new(42424242);
            let (siblings, positions, root) = dsl_create_test_witness(leaf, 4);

            // PI parity with the DSL membership path.
            let (_dsl_trace, dsl_pis) = crate::dsl::membership::generate_merkle_poseidon2_trace(
                leaf, &siblings, &positions,
            );
            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            assert_eq!(pis, dsl_pis, "p3 membership PIs must match the DSL path");
            assert_eq!(pis[0], leaf);
            assert_eq!(pis[1], root);

            let proof = prove_membership_p3(leaf, &siblings, &positions)
                .expect("honest membership must prove+verify through audited p3");
            verify_membership_p3(&proof, &pis).expect("audited p3 verify accepts honest proof");
        }

        /// Depth-8 honest membership also round-trips.
        #[test]
        fn membership_p3_depth_8() {
            let leaf = BabyBear::new(7777);
            let (siblings, positions, _root) = dsl_create_test_witness(leaf, 8);
            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            let proof = prove_membership_p3(leaf, &siblings, &positions).expect("depth-8 proof");
            verify_membership_p3(&proof, &pis).expect("depth-8 verify");
        }

        /// ANTI-GHOST: a forged `root` public input is REJECTED by the audited
        /// verifier (the proof's bound hash-chain root is the genuine one, not the
        /// forged PI).
        #[test]
        fn membership_p3_rejects_forged_root() {
            let leaf = BabyBear::new(42424242);
            let (siblings, positions, _root) = dsl_create_test_witness(leaf, 4);
            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            let proof = prove_membership_p3(leaf, &siblings, &positions).expect("honest proof");

            let mut forged = pis.clone();
            forged[1] = forged[1] + BabyBear::new(1); // forge the root
            let res = verify_membership_p3(&proof, &forged);
            assert!(
                res.is_err(),
                "SOUNDNESS: a forged Merkle root MUST be rejected by the audited p3 verifier"
            );
        }

        /// ANTI-GHOST: a forged `leaf` public input is REJECTED (the first-row
        /// boundary pins `current == leaf`).
        #[test]
        fn membership_p3_rejects_forged_leaf() {
            let leaf = BabyBear::new(42424242);
            let (siblings, positions, _root) = dsl_create_test_witness(leaf, 4);
            let pis = membership_public_inputs(leaf, &siblings, &positions).unwrap();
            let proof = prove_membership_p3(leaf, &siblings, &positions).expect("honest proof");

            let mut forged = pis.clone();
            forged[0] = BabyBear::new(99999); // forge the leaf
            let res = verify_membership_p3(&proof, &forged);
            assert!(
                res.is_err(),
                "SOUNDNESS: a forged leaf MUST be rejected by the audited p3 verifier"
            );
        }

        /// ANTI-GHOST (forged WITNESS): a prover with a leaf that is NOT in the tree
        /// cannot produce a proof verifying against the genuine root — the recomputed
        /// hash-chain root differs, so proving (which self-verifies) fails.
        #[test]
        fn membership_p3_rejects_non_member_leaf() {
            let leaf = BabyBear::new(42424242);
            let (siblings, positions, root) = dsl_create_test_witness(leaf, 4);

            // A different leaf with the SAME siblings/positions recomputes a DIFFERENT
            // root; proving for the genuine `root` is impossible.
            let non_member = BabyBear::new(13371337);
            let res = prove_membership_p3(non_member, &siblings, &positions);
            // Proving succeeds (it proves membership for the non-member's OWN root),
            // but verifying against the genuine tree root must reject.
            if let Ok(proof) = res {
                let genuine_pis = vec![non_member, root];
                assert!(
                    verify_membership_p3(&proof, &genuine_pis).is_err(),
                    "SOUNDNESS: a non-member leaf must not verify against the genuine root"
                );
            }
        }
    }
} // mod membership_p3
