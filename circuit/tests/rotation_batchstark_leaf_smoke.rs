//! # C3 THREAD-1 SMOKE FOLD — does a rotated `Ir2BatchProof` wrap as a BatchStark leaf?
//!
//! The C3 cutover ("delete v1") drives OPTION (a): make the recursion/aggregation layer
//! ingest the rotated multi-table `Ir2BatchProof` instead of the v1 186-col uni-STARK
//! (`EffectVmDescriptorAir`) leaf. The scope verdict demands ONE smoke fold FIRST: feed a
//! single real rotated 9-table descriptor leaf (chip degree-7 S-box + LogUp buses) through
//! `build_and_prove_next_layer` as a `RecursionInput::BatchStark` leaf and observe whether
//! the recursion circuit's table-packing/constraint-profile absorbs it.
//!
//! This test produces a real `transferVmDescriptor2R24` `Ir2BatchProof` (the SAME fixture as
//! `effect_vm_rotation_flip.rs`) and hands it to
//! `dregg_circuit::ivc_turn_chain::prove_descriptor_leaf_rotated` (THREAD 1's BatchStark
//! leaf-wrap). If it folds, OPTION (a) is confirmed bounded end-to-end; if it does not, the
//! exact failure is the re-estimate signal.
//!
//! Gated on `recursion`. SLOW; run with
//! `cargo test -p dregg-circuit --features recursion batchstark_leaf_smoke -- --nocapture`.

#![cfg(feature = "recursion")]

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    ROT_WIDTH, RotatedBlockWitness, generate_rotated_effect_vm_trace, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_turn::rotation_witness as rw;

fn rotated_transfer_json() -> &'static str {
    for line in V3_STAGED_REGISTRY_TSV.lines() {
        let mut it = line.splitn(3, '\t');
        if it.next() == Some("transferVmDescriptor2R24") {
            let _name = it.next();
            return it.next().expect("json column");
        }
    }
    panic!("transferVmDescriptor2R24 not in V3_STAGED_REGISTRY_TSV");
}

fn open_permissions() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// THE SMOKE FOLD: a real rotated transfer leaf wrapped as a BatchStark recursion leaf.
#[test]
fn rotated_transfer_leaf_folds_as_batchstark() {
    let desc =
        parse_vm_descriptor2(rotated_transfer_json()).expect("rotated transfer descriptor parses");
    assert_eq!(desc.trace_width, ROT_WIDTH, "rotated width 311");
    assert_eq!(desc.public_input_count, 38, "34 v1 PIs + 4 appended");

    // -- a real transfer-out (the validated v1 reference witness). --
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let effects = vec![Effect::Transfer {
        amount,
        direction: 1,
    }];

    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance, 0);
    let after_cell = producer_cell(before_balance - amount as i64, 0);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];

    let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &receipt_log);
    let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &receipt_log);

    let bridge = |w: &rw::RotationWitness| -> RotatedBlockWitness {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("31 pre-iroot limbs")
    };
    let caveat = transfer_caveat_manifest();
    let (trace, dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &caveat,
    )
    .expect("rotated transfer trace generates");

    // The native batch proof (self-verifies before return).
    let mem_boundary = MemBoundaryWitness::default();
    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mem_boundary, &[])
        .expect("rotated transfer Ir2BatchProof proves");
    verify_vm_descriptor2(&desc, &proof, &dpis).expect("rotated transfer proof verifies natively");

    // -- THE SMOKE FOLD: attempt to wrap the multi-table batch proof as a BatchStark leaf. --
    //
    // RESULT (2026-06-13): HARD WALL. `RecursionInput::BatchStark` holds
    // `p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>` (a circuit-prover wrapper
    // under the recursion FRI config), NOT `Ir2BatchProof = p3_batch_stark::BatchProof<
    // DreggStarkConfig>` (the native production-config proof). The two `E0308` type errors
    // are documented on `prove_descriptor_leaf_rotated`; the fn returns the wall as an `Err`
    // rather than a non-compiling body so the shared library stays green for parallel lanes.
    //
    // This test is the FALSIFIABLE wall evidence: the verify-path ingredients build fine (a
    // real 5-table rotated transfer proof, 38 PIs), but the leaf-wrap is impossible without
    // a recursion-fork build (native-batch leaf-wrap entry + config unification). If a future
    // fork change makes the wrap succeed, flip this assertion to `.expect(...)` + re-verify.
    let folded = dregg_circuit::ivc_turn_chain::prove_descriptor_leaf_rotated(&desc, &proof, &dpis);
    match folded {
        Err(e) if e.contains("C3 THREAD-1 HARD WALL") => {
            eprintln!("smoke fold (expected) hit the documented wall: {e}");
        }
        Err(e) => panic!("smoke fold failed with an UNEXPECTED error (not the type wall): {e}"),
        Ok(wrapped) => {
            // The wall was lifted by a fork change — verify the wrapped root self-consistently
            // and update this test + the fn doc to reflect THREAD-1-green.
            dregg_circuit::plonky3_recursion_impl::recursive::verify_recursive_batch_proof(
                &wrapped.0,
            )
            .expect("the wrapped BatchStark leaf root proof verifies");
            panic!(
                "THREAD-1 wall appears LIFTED (the rotated leaf folded): update \
                 prove_descriptor_leaf_rotated + this test to assert green, and proceed to \
                 THREAD 2/3 (table_public_inputs propagation + PI-binding soundness)."
            );
        }
    }
}
