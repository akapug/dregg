//! # The setField VALUE8 epoch flip — the faithful per-trader-allocation gate.
//!
//! The deployed `setFieldVmDescriptor2-{slot}R24` ship the freeze-ALL wrap (`v3OfFrozen (setFieldTickFace
//! slot)`): every one of the written slot's 7 completion lanes (the high 224 bits of the 32-byte value) is
//! frozen BEFORE↔AFTER, so an honest LARGE-value `setField` is REJECTED — the R1 completeness seam proven
//! by `setfield_completion_lane_forge::honest_large_value_setfield_fails_the_deployed_freeze`. A faithful
//! per-trader settlement allocation (a real cleared amount with nonzero high bytes) therefore CANNOT prove.
//!
//! The STAGED VALUE8 epoch (`V3_SETFIELD_VALUE8_STAGED_REGISTRY_TSV`, Lean
//! `EffectVmEmitRotationV3Refused.v3RegistrySetFieldValue8`) swaps the inner freeze-ALL for freeze-EXCEPT
//! (`setFieldV3`) and pins the written slot's 7 freed completion lanes to TAIL PIs 46..52 (the VALUE8
//! weld). It is DROP-IN geometry with the deployed member (`trace_width = 1692`), +7 PIs (`piCount = 57`).
//!
//! The four teeth (all under the real `prove_vm_descriptor2` / `verify_vm_descriptor2`, `--release`):
//!   * `honest_large_value_setfield_proves_under_value8` — the seam CLOSED: an honest large write PROVES
//!     + verifies under the value8 descriptor (its high bytes ride the freed lanes, published as PIs).
//!   * `deployed_freeze_all_still_rejects_the_large_write` — the LIVE path is untouched: the SAME large
//!     write STILL fails the deployed freeze-ALL member (no regression, no live-node disruption).
//!   * `forged_completion_lane_off_the_published_pi_is_unsat` — SOUNDNESS PRESERVED: forging a completion
//!     lane while keeping the honest published PI is UNSAT (the pin binds the declared value8).
//!   * `slot_i_value8_proof_binds_uniquely` — the slot-i large-write proof verifies under descriptor-i
//!     but NOT under a sibling descriptor-j (the disjoint completion-pin columns give unique binding).

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    AFTER_BASE, empty_caveat_manifest, generate_rotated_effect_vm_trace,
    rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, fold_bytes32_to_bb};
use dregg_circuit::effect_vm_descriptors::{
    V3_SETFIELD_VALUE8_STAGED_REGISTRY_TSV, V3_STAGED_REGISTRY_TSV,
};
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

const SLOT: usize = 3;
/// The written slot's first freed completion lane, absolute trace column (`AFTER_BASE + 113 + 7·slot`) —
/// the exact column the Lean `withSetFieldCompletionPins` pins to TAIL PI 46 (per-slot base `540 + 7·slot`).
const COMPLETION_COL: usize = AFTER_BASE + 113 + 7 * SLOT;
/// The value8 PI base (the 7 completion pins ride PI 46..52; rc rides 53..56).
const VALUE8_PI_BASE: usize = 46;

fn tsv_json(tsv: &'static str, name: &str) -> &'static str {
    tsv.lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in tsv"))
}

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    Cell::with_balance(pk, [0u8; 32], balance)
}

fn bridge(w: &rw::RotationWitness) -> dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness {
    dregg_circuit::effect_vm::trace_rotated::RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
        .expect("pre-iroot limbs")
}

struct Built {
    trace: Vec<Vec<BabyBear>>,
    /// The generator's native 50-PI vector (0..45 prefix, 46..49 rc).
    gen_dpis: Vec<BabyBear>,
}

/// An honest single-effect `setField` on `SLOT` whose value has NONZERO high bytes (a real 32-byte
/// cleared amount) — the case the deployed freeze-ALL rejects.
fn build_honest_large() -> Built {
    let before: i64 = 50_000;
    let mut field_bytes = [0u8; 32];
    field_bytes[0] = 0xAB; // high byte → nonzero completion lane
    field_bytes[1] = 0xCD;
    field_bytes[28..32].copy_from_slice(&1_000u32.to_be_bytes());
    let new_value = fold_bytes32_to_bb(&field_bytes);
    let effect = Effect::SetField {
        field_idx: SLOT as u32,
        value: new_value,
    };
    // Sanity: the live routing names the deployed member for this effect.
    assert_eq!(
        rotated_descriptor_name_for_effect(&effect).expect("setField cohort member"),
        "setFieldVmDescriptor2-3R24"
    );

    let mut after_cell = producer_cell(before);
    assert!(after_cell.state.set_field(SLOT, field_bytes), "set_field");
    let st = CellState::new(before as u64, 0);
    let effects = vec![effect];
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let z8 = dregg_circuit::heap_root::empty_heap_root_8();
    let rvk = dregg_turn::rotation_witness::empty_revoked_root_8();
    let rlog = vec![[3u8; 32]];
    let before_w = rw::produce(
        &before_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );
    let after_w = rw::produce(
        &after_cell,
        &ledger,
        &z8,
        &z8,
        &rvk,
        &rlog,
        &Default::default(),
    );
    let (trace, gen_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&after_w),
        &empty_caveat_manifest(),
    )
    .expect("live rotated generator must produce a large-value setField trace + PIs");
    Built { trace, gen_dpis }
}

/// Build the 57-PI value8 dpi vector: the 46 rotated prefix, then the 7 written-slot completion lanes
/// off the last row (PI 46..52), then the 4 rc pins the generator emitted at native 46..49 (→ 53..56).
fn value8_dpis(b: &Built) -> Vec<BabyBear> {
    let last = b.trace.last().unwrap();
    let mut dpis = b.gen_dpis[..VALUE8_PI_BASE].to_vec(); // PI 0..45 (rotated prefix)
    for k in 0..7 {
        dpis.push(last[COMPLETION_COL + k]); // PI 46..52 (the declared value8 completion)
    }
    dpis.extend_from_slice(&b.gen_dpis[VALUE8_PI_BASE..]); // PI 53..56 (rc, from native 46..49)
    assert_eq!(dpis.len(), 57, "value8 dpi layout must be 57 PIs");
    dpis
}

fn value8_desc(slot: usize) -> EffectVmDescriptor2 {
    let name = format!("setFieldValue8VmDescriptor2-{slot}R24");
    parse_vm_descriptor2(tsv_json(V3_SETFIELD_VALUE8_STAGED_REGISTRY_TSV, &name))
        .expect("value8 descriptor parses")
}

fn prove_verify(desc: &EffectVmDescriptor2, trace: &[Vec<BabyBear>], dpis: &[BabyBear]) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, dpis, &MemBoundaryWitness::default(), &[])?;
        verify_vm_descriptor2(desc, &proof, dpis)
    }));
    matches!(r, Ok(Ok(())))
}

#[test]
fn honest_large_value_setfield_proves_under_value8() {
    let b = build_honest_large();
    // Non-vacuity: the large value genuinely moved a written-slot completion lane off zero.
    let any_nonzero = (0..7).any(|k| b.trace[0][COMPLETION_COL + k] != BabyBear::ZERO);
    assert!(
        any_nonzero,
        "the large value must move a completion lane off zero"
    );

    let desc = value8_desc(SLOT);
    assert_eq!(
        desc.trace_width, 1692,
        "value8 is drop-in geometry with the deployed member"
    );
    assert_eq!(desc.public_input_count, 57);
    let dpis = value8_dpis(&b);

    assert!(
        prove_verify(&desc, &b.trace, &dpis),
        "an HONEST large-value per-trader setField MUST prove + verify under the VALUE8 epoch \
         (the R1 completeness seam is CLOSED — the high 224 bits ride the freed lanes, published as PIs)"
    );
    eprintln!(
        "VALUE8: honest large-value setField proves+verifies — faithful per-trader allocation."
    );
}

#[test]
fn deployed_freeze_all_still_rejects_the_large_write() {
    // The LIVE path is byte-untouched: the SAME honest large write still FAILS the deployed
    // freeze-ALL member (the baseline the value8 epoch does NOT regress — no live-node disruption).
    let b = build_honest_large();
    let dep = parse_vm_descriptor2(tsv_json(
        V3_STAGED_REGISTRY_TSV,
        "setFieldVmDescriptor2-3R24",
    ))
    .expect("deployed descriptor parses");
    assert!(
        !prove_verify(&dep, &b.trace, &b.gen_dpis),
        "the deployed freeze-ALL setField MUST still reject the large write (the live path unchanged)"
    );
    eprintln!(
        "VALUE8: the deployed freeze-ALL member still rejects the large write — live path intact."
    );
}

#[test]
fn forged_completion_lane_off_the_published_pi_is_unsat() {
    // SOUNDNESS PRESERVED. Prove the honest baseline, then forge a completion lane in the trace while
    // keeping the honest published PI: the value8 pin (`.piBinding .last col pi`) forces after==pi, so
    // the forge is UNSAT — the high bytes are no longer an unconstrained free felt.
    let b = build_honest_large();
    let desc = value8_desc(SLOT);
    let dpis = value8_dpis(&b);
    assert!(
        prove_verify(&desc, &b.trace, &dpis),
        "honest baseline must prove"
    );

    let mut ftrace = b.trace.clone();
    // Forge completion lane 0 (col COMPLETION_COL) on the LAST row (the pin reads `.last`) to a value
    // that differs from the published PI 46 (the honest completion). dpis stay honest.
    let last = ftrace.len() - 1;
    let honest = ftrace[last][COMPLETION_COL];
    ftrace[last][COMPLETION_COL] = honest + BabyBear::new(0x9999);
    assert_ne!(
        ftrace[last][COMPLETION_COL], dpis[VALUE8_PI_BASE],
        "forge must differ from the PI"
    );

    assert!(
        !prove_verify(&desc, &ftrace, &dpis),
        "a completion lane forged OFF the published value8 PI MUST be UNSAT (the pin binds the \
         declared value — soundness preserved, not weakened)"
    );
    eprintln!(
        "VALUE8: a completion-lane forge off the published PI is UNSAT — soundness preserved."
    );
}

#[test]
fn slot_i_value8_proof_binds_uniquely() {
    // UNIQUE BINDING. The slot-3 large-write proof (its completion lanes at cols 561..567, published at
    // PI 46..52) verifies under descriptor-3 but NOT under a sibling descriptor (e.g. slot 0), which
    // pins slot-0's frozen completion lanes (cols 540..546) to the SAME PI slots — a mismatch the
    // slot-3 trace violates. This is the "selector binding ambiguous" reject the deployed freeze-ALL
    // could not give the light client.
    let b = build_honest_large();
    let dpis = value8_dpis(&b);

    assert!(
        prove_verify(&value8_desc(SLOT), &b.trace, &dpis),
        "the slot-3 proof verifies under its OWN value8 descriptor"
    );
    // A slot-3 large write moves slot-3's completion lanes off the pre-state; the sibling descriptor
    // (slot 0/1/2) pins a DIFFERENT column set, so the same (trace, dpis) must NOT verify.
    for other in [0usize, 1, 2, 4] {
        assert!(
            !prove_verify(&value8_desc(other), &b.trace, &dpis),
            "the slot-3 proof MUST NOT verify under the slot-{other} value8 descriptor (unique binding)"
        );
    }
    eprintln!(
        "VALUE8: the slot-3 proof binds UNIQUELY to descriptor-3 (disjoint completion-pin columns)."
    );
}
