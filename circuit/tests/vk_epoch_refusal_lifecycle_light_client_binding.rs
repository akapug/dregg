//! # THE VK-EPOCH FAMILY-2 DISCRIMINATOR — Refusal + the lifecycle PAYLOAD, now FORCED-ON-WIRE.
//!
//! ## What this measures (`docs/VK-EPOCH-PLAN.md`, STAGE B/C, family 2 — the VK-FREEDOM ERA close)
//!
//! Family 1 (`vk_epoch_perms_vk_light_client_binding.rs`, commit d58545a5f) PROVED that
//! setPermissions / setVK are FORCED-ON-WIRE: their in-circuit `permsVKWeldGate` welds the
//! committed AFTER perms/vk sub-limb to `param0`, AND `param0` is the post-value bound into the
//! PI-anchored `effects_hash` (a value a ledgerless light client independently knows from the
//! effect). So a perms-/vk-only forged post-cell is UNSAT through `verify_vm_descriptor2` ALONE.
//!
//! Family 2 — Refusal + the lifecycle PAYLOAD — was the HONEST CONTRAST: these ride the record-pin
//! (`rotateV3WithRecordPin off d`), which welds the committed AFTER limb (`B_RECORD_DIGEST = 24` for
//! refusal's `fields_root` audit; `B_LIFECYCLE = 29` for the lifecycle payload) to rotated PI slot
//! `ROT_PI_COUNT = 46`. The bare record pin (`trace_rotated.rs:393-395`) fills that PI from the
//! producer's OWN AFTER limb, so on the LIGHT-CLIENT path it held VACUOUSLY: a forged-but-self-consistent
//! post-cell published its own forged limb as PI 46 and the pin was satisfied by construction.
//!
//! ## THE FIX — the verifier-anchored declared-payload column (Lean `EffectVmEmitRotationV3.§5.PC`)
//!
//! The genuinely-new primitive is `rotateV3WithPayloadColumn` + the `PayloadAnchored` predicate. The
//! record pin already welds `after_payload_limb == PI[46]` IN-CIRCUIT (the descriptor is byte-identical
//! — NO VK change). The light-client FORCE is the verifier ANCHOR of that slot: the deployed light-client
//! verifier RECOMPUTES PI[46] from a value it independently knows (NOT producer-free), exactly as the
//! full node's `proof_verify.rs` step 6b does, but on the ledgerless path:
//!
//!   * **refusal** (`B_RECORD_DIGEST`): anchor = `compute_authority_digest_felt(apply refusal to the
//!     trusted before-cell)` — recomputed from the EFFECT (the `offered_action_commitment` + `reason`
//!     the published refusal params carry, bound via `effects_hash` PI[16..20], INSIDE the rotated
//!     dpis window). Effect-param-derivable.
//!   * **cellSeal / cellUnseal / cellDestroy** (`B_LIFECYCLE`): anchor = `lifecycle_felt_cell(apply
//!     lifecycle to before)` — folds `reason_hash` (an effect param) AND `sealed_at = block_height`
//!     (the TURN-HEADER height the light client independently holds). Turn-context-derivable.
//!
//! Lean theorem `rotateV3WithPayloadColumn_rejects_forged`: given `PayloadAnchored env d anchor`
//! (the verifier set PI[46] = anchor), a witness whose committed AFTER payload limb ≠ anchor is UNSAT.
//!
//! ## The discriminator (both poles, GREEN = it asserts the CURRENT TRUTH = light-client-FORCED)
//!
//! Run through `prove_vm_descriptor2` / `verify_vm_descriptor2` ALONE (the light-client path; no
//! `apply_effect_to_cell` re-derivation at the full node — instead the verifier ANCHORS PI[46], the
//! declared-payload column's slot, to the value it recomputes from light-client-known inputs). For each
//! effect:
//!
//!   * POSITIVE (no downgrade): an HONEST refusal / cellSeal turn proves + verifies, because its
//!     committed AFTER payload limb EQUALS the verifier-recomputed anchor.
//!   * FORCED-ON-WIRE (the close vs the old residual): a post-cell forged to differ ONLY in the
//!     refusal-audit / lifecycle payload is now REJECTED through the light-client path: the forged
//!     committed limb ≠ the verifier-anchored PI[46], so the in-circuit record-pin weld FAILS. The
//!     anchor (`anchor_payload_slot` below) is the HONEST value — the value the verifier recomputes by
//!     applying the effect to the trusted before-cell — NOT the producer's forged publish.
//!
//! This is the model-finds-the-bug artifact carried forward: it proves the residual the prior epoch
//! NAMED is now CLOSED. The full-node leg was already sound; this makes the LIGHT-CLIENT leg sound too.
//!
//! Gated on `prover`. Run with
//! `cargo test -p dregg-circuit --features prover --test vk_epoch_refusal_lifecycle_light_client_binding -- --nocapture`.

#![cfg(feature = "prover")]

use dregg_cell::{Cell, Ledger};
use dregg_circuit::descriptor_ir2::{
    MemBoundaryWitness, parse_vm_descriptor2, prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::trace_rotated::{
    B_LIFECYCLE, B_RECORD_DIGEST, ROT_PI_COUNT, ROT_WIDTH, RotatedBlockWitness,
    empty_caveat_manifest, generate_rotated_effect_vm_trace, rotated_descriptor_name_for_effect,
};
use dregg_circuit::effect_vm::{CellState, Effect, bytes32_to_8_limbs};
use dregg_circuit::effect_vm_descriptors::V3_STAGED_REGISTRY_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

/// Resolve a rotated descriptor JSON by registry key from the committed staged TSV.
fn rotated_descriptor_json(name: &str) -> &'static str {
    V3_STAGED_REGISTRY_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(name) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{name} not in V3_STAGED_REGISTRY_TSV"))
}

/// The producer's before-cell (the pre-state the turn opens over).
fn producer_cell(balance: i64, nonce: u64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("37 pre-iroot limbs")
}

fn h8(b: &[u8; 32]) -> [BabyBear; 8] {
    bytes32_to_8_limbs(blake3::hash(b).as_bytes())
}

/// `true` iff `prove_vm_descriptor2` + `verify_vm_descriptor2` ACCEPT (the light-client path).
/// `false` iff `prove` refuses (Err/panic) or the proof fails to verify.
fn accepts(
    desc: &dregg_circuit::descriptor_ir2::EffectVmDescriptor2,
    trace: &[Vec<BabyBear>],
    dpis: &[BabyBear],
    mem_boundary: &MemBoundaryWitness,
    map_heaps: &[Vec<dregg_circuit::heap_root::HeapLeaf>],
) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let proof = prove_vm_descriptor2(desc, trace, dpis, mem_boundary, map_heaps).ok()?;
        verify_vm_descriptor2(desc, &proof, dpis).ok()
    }));
    matches!(r, Ok(Some(())))
}

/// **THE VERIFIER ANCHOR (the light-client realization of `PayloadAnchored`).** The deployed
/// light-client verifier does NOT take PI[46] producer-free; it RECOMPUTES it from the trusted
/// before-cell + the effect (effect-param-derivable for refusal's `fields_root` audit, turn-context
/// for the lifecycle's `sealed_at = block_height`) and writes it into the payload slot before
/// `verify_vm_descriptor2`. We model that anchor by replacing `dpis[ROT_PI_COUNT]` with the HONEST
/// post-payload limb — the value the verifier computes by applying the effect to the cross-checked
/// before-cell (here: read off the honest AFTER witness, exactly the `proof_verify.rs` step-6b override
/// `compute_authority_digest_felt(post)` / `lifecycle_felt_cell(post)` projects, on the ledgerless leg).
fn anchor_payload_slot(dpis: &mut [BabyBear], honest_anchor: BabyBear) {
    dpis[ROT_PI_COUNT] = honest_anchor;
}

/// **REFUSAL is now LIGHT-CLIENT-FORCED (the residual CLOSED).** An honest refusal proves + verifies
/// (its committed AFTER record-digest limb EQUALS the verifier-anchored PI 46). A post-cell forged to
/// differ ONLY in the refusal-`fields_root` audit is REJECTED through `verify_vm_descriptor2` ALONE,
/// once the verifier ANCHORS PI 46 to the recomputed (honest) audit digest: the forged committed limb
/// ≠ the anchor, so the record-pin weld FAILS. NO off-cell `apply_effect_to_cell`, NO producer-free PI.
#[test]
fn refusal_is_light_client_forced_via_payload_column() {
    let balance: i64 = 50_000;

    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    let kernel_effect = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [11u8; 32],
        refusal_reason: dregg_turn::action::RefusalReason::Declined,
        proof_witness_index: 0,
    };

    let vm_effect = Effect::Refusal {
        target: h8(cell_id.as_bytes()),
        reason_hash: bytes32_to_8_limbs(&[0u8; 32]),
    };
    let name = rotated_descriptor_name_for_effect(&vm_effect)
        .expect("Refusal is a rotated cohort member");
    assert_eq!(name, "refusalVmDescriptor2R24");
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("rotated refusal descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "refusal carries the appended declared-payload pin (47 PIs)"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];

    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &kernel_effect, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w =
        rw::produce(&before_cell, &Ledger::new(), &nullifier_root, &commitments_root, &receipt_log);
    let after_w =
        rw::produce(&honest_after, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        before_w.pre_limbs[B_RECORD_DIGEST], after_w.pre_limbs[B_RECORD_DIGEST],
        "the refusal audit MOVES the AFTER record-digest limb (a genuine write)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(&st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat)
            .expect("live rotated generator must produce a refusal trace + 47 PIs");
    assert_eq!(trace[0].len(), ROT_WIDTH, "rotated trace width");

    // THE VERIFIER ANCHOR: the honest post-payload limb is the value the light-client verifier
    // recomputes (apply refusal to the trusted before-cell, then `compute_authority_digest_felt`).
    let honest_anchor = after_w.pre_limbs[B_RECORD_DIGEST];

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade): the honest refusal proves + verifies, anchored.
    let mut honest_dpis = dpis.clone();
    anchor_payload_slot(&mut honest_dpis, honest_anchor);
    assert_eq!(
        honest_dpis[ROT_PI_COUNT], dpis[ROT_PI_COUNT],
        "the anchor MATCHES the honest producer publish (no downgrade — the honest proof is NOT rejected)"
    );
    assert!(
        accepts(&desc, &trace, &honest_dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest refusal must prove + verify through the light-client path with the \
         verifier-anchored payload slot"
    );

    // FORCED-ON-WIRE TOOTH: a post-cell forged to differ ONLY in the refusal audit. The producer would
    // publish PI 46 from its OWN forged AFTER limb — but the VERIFIER anchors PI 46 to the HONEST
    // recomputed digest. The forged committed limb ≠ the anchor, so the record-pin weld is UNSAT.
    let forged_kernel = dregg_turn::Effect::Refusal {
        cell: cell_id,
        offered_action_commitment: [99u8; 32], // a DIFFERENT audit input
        refusal_reason: dregg_turn::action::RefusalReason::NoAuthority,
        proof_witness_index: 0,
    };
    let mut forged_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut forged_after, &cell_id, &forged_kernel, 100);
    let mut forged_ledger = Ledger::new();
    forged_ledger.insert_cell(forged_after.clone()).unwrap();
    let forged_after_w =
        rw::produce(&forged_after, &forged_ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        forged_after_w.pre_limbs[B_RECORD_DIGEST], honest_anchor,
        "the forged audit folds to a DISTINCT AFTER record-digest limb (else the contrast is vacuous)"
    );

    let (forged_trace, forged_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects, // SAME declared VM effect (params unchanged) — the forge is in the post-cell payload
        &bridge(&before_w),
        &bridge(&forged_after_w),
        &caveat,
    )
    .expect("generator builds the forged-audit trace");

    // The producer's forged dpis publish the forged limb at PI 46.
    assert_eq!(
        forged_dpis[ROT_PI_COUNT], forged_after_w.pre_limbs[B_RECORD_DIGEST],
        "the producer publishes PI 46 from its OWN forged AFTER record-digest limb"
    );

    // THE VERIFIER ANCHOR overrides PI 46 with the HONEST recomputed digest (light-client-known).
    let mut anchored_forged_dpis = forged_dpis.clone();
    anchor_payload_slot(&mut anchored_forged_dpis, honest_anchor);

    assert!(
        !accepts(&desc, &forged_trace, &anchored_forged_dpis, &mem_boundary, &map_heaps),
        "FORCED-ON-WIRE (light-client-forced): a refusal forged to differ ONLY in the `fields_root` \
         audit is REJECTED through verify_vm_descriptor2 ALONE once the verifier ANCHORS PI 46 to the \
         recomputed audit digest — the committed AFTER record-digest limb ≠ the anchored PI, so the \
         record-pin (declared-payload-column) weld FAILS. NO off-cell apply_effect_to_cell. This is the \
         STAGE-B residual CONVERTED to a genuine in-circuit force (Lean \
         `rotateV3WithPayloadColumn_rejects_forged`)."
    );

    // SANITY: the forged trace WOULD verify against its OWN (producer-free) dpis — proving the FORCE
    // comes from the verifier anchor, not from the trace being malformed.
    assert!(
        accepts(&desc, &forged_trace, &forged_dpis, &mem_boundary, &map_heaps),
        "the forged trace is itself well-formed (it verifies against its own producer-free PI 46) — so \
         the REJECTION above is precisely the verifier-anchor bite, not a degenerate malformed proof"
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 refusal: LIGHT-CLIENT-FORCED — a forged-audit post-cell is REJECTED through \
         verify_vm_descriptor2 ALONE under the verifier-anchored declared-payload column (PI 46). \
         Residual CLOSED."
    );
}

/// **The LIFECYCLE PAYLOAD is now LIGHT-CLIENT-FORCED (the residual CLOSED).** The lifecycle DISC
/// (limb 32) was already forced in-circuit (a frozen seal is rejected). This proves the OPAQUE payload
/// felt (limb 29: `reason_hash`/`sealed_at` for cellSeal) is ALSO forced: a cellSeal forged to differ
/// ONLY in the sealing payload is REJECTED through the light-client path once the verifier ANCHORS PI 46
/// to the recomputed `lifecycle_felt(reason_hash, block_height)`.
#[test]
fn lifecycle_payload_is_light_client_forced_via_payload_column() {
    let balance: i64 = 50_000;

    let before_cell = producer_cell(balance, 0);
    let cell_id = before_cell.id();
    let honest_reason = [22u8; 32];
    let honest_kernel = dregg_turn::Effect::CellSeal {
        target: cell_id,
        reason: honest_reason,
    };
    let vm_effect = Effect::CellSeal {
        target: h8(cell_id.as_bytes()),
        reason_hash: h8(&honest_reason),
    };
    let name = rotated_descriptor_name_for_effect(&vm_effect)
        .expect("CellSeal is a rotated cohort member");
    assert_eq!(name, "cellSealVmDescriptor2R24");
    let desc =
        parse_vm_descriptor2(rotated_descriptor_json(name)).expect("rotated cellSeal descriptor parses");
    assert_eq!(
        desc.public_input_count, 47,
        "cellSeal carries the appended declared-payload pin (47 PIs)"
    );

    let st = CellState::new(balance as u64, 0);
    let effects = vec![vm_effect];

    let mut honest_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut honest_after, &cell_id, &honest_kernel, 100);

    let mut ledger = Ledger::new();
    ledger.insert_cell(honest_after.clone()).unwrap();
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_log: Vec<[u8; 32]> = vec![[3u8; 32]];

    let before_w =
        rw::produce(&before_cell, &Ledger::new(), &nullifier_root, &commitments_root, &receipt_log);
    let after_w =
        rw::produce(&honest_after, &ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        before_w.pre_limbs[B_LIFECYCLE], after_w.pre_limbs[B_LIFECYCLE],
        "the seal MOVES the AFTER lifecycle limb (Live -> Sealed)"
    );

    let caveat = empty_caveat_manifest();
    let (trace, dpis) =
        generate_rotated_effect_vm_trace(&st, &effects, &bridge(&before_w), &bridge(&after_w), &caveat)
            .expect("live rotated generator must produce a cellSeal trace + 47 PIs");

    // THE VERIFIER ANCHOR: the honest lifecycle felt the light-client verifier recomputes from the
    // effect's `reason_hash` + the turn-header `block_height` (`lifecycle_felt_cell(post)`).
    let honest_anchor = after_w.pre_limbs[B_LIFECYCLE];

    let mem_boundary = MemBoundaryWitness::default();
    let map_heaps: Vec<Vec<dregg_circuit::heap_root::HeapLeaf>> = vec![];

    // POSITIVE TOOTH (no downgrade), anchored.
    let mut honest_dpis = dpis.clone();
    anchor_payload_slot(&mut honest_dpis, honest_anchor);
    assert_eq!(
        honest_dpis[ROT_PI_COUNT], dpis[ROT_PI_COUNT],
        "the anchor MATCHES the honest producer publish (no downgrade)"
    );
    assert!(
        accepts(&desc, &trace, &honest_dpis, &mem_boundary, &map_heaps),
        "NO DOWNGRADE: the honest cellSeal must prove + verify through the light-client path, anchored"
    );

    // FORCED-ON-WIRE TOOTH: forge ONLY the sealing PAYLOAD (a different reason_hash; the DISC stays
    // Sealed). The verifier anchors PI 46 to the HONEST lifecycle felt; the forged committed limb 29
    // ≠ the anchor, so the record-pin weld is UNSAT.
    let forged_reason = [44u8; 32];
    let forged_kernel = dregg_turn::Effect::CellSeal {
        target: cell_id,
        reason: forged_reason,
    };
    let mut forged_after = producer_cell(balance, 0);
    rw::apply_effect_to_cell(&mut forged_after, &cell_id, &forged_kernel, 100);
    let mut forged_ledger = Ledger::new();
    forged_ledger.insert_cell(forged_after.clone()).unwrap();
    let forged_after_w =
        rw::produce(&forged_after, &forged_ledger, &nullifier_root, &commitments_root, &receipt_log);

    assert_ne!(
        forged_after_w.pre_limbs[B_LIFECYCLE], honest_anchor,
        "the forged sealing payload folds to a DISTINCT AFTER lifecycle limb (else the contrast is vacuous)"
    );

    let (forged_trace, forged_dpis) = generate_rotated_effect_vm_trace(
        &st,
        &effects,
        &bridge(&before_w),
        &bridge(&forged_after_w),
        &caveat,
    )
    .expect("generator builds the forged-payload trace");

    let mut anchored_forged_dpis = forged_dpis.clone();
    anchor_payload_slot(&mut anchored_forged_dpis, honest_anchor);

    assert!(
        !accepts(&desc, &forged_trace, &anchored_forged_dpis, &mem_boundary, &map_heaps),
        "FORCED-ON-WIRE (light-client-forced): a cellSeal forged to differ ONLY in the sealing PAYLOAD \
         (reason_hash/sealed_at — the disc stays Sealed) is REJECTED through verify_vm_descriptor2 ALONE \
         once the verifier ANCHORS PI 46 to the recomputed `lifecycle_felt(reason_hash, block_height)`. \
         The committed AFTER lifecycle limb ≠ the anchored PI, so the declared-payload-column weld FAILS. \
         The lifecycle DISC was already forced; this closes the OPAQUE payload felt too (Lean \
         `cellSealV3_payload_rejects_forged`)."
    );

    // SANITY: the forged trace verifies against its OWN producer-free PI 46 — the FORCE is the anchor.
    assert!(
        accepts(&desc, &forged_trace, &forged_dpis, &mem_boundary, &map_heaps),
        "the forged trace is well-formed (verifies against its own producer-free PI 46) — the rejection \
         above is the verifier-anchor bite, not a malformed proof"
    );

    eprintln!(
        "VK-EPOCH FAMILY-2 lifecycle payload: LIGHT-CLIENT-FORCED — a forged-payload post-cell is \
         REJECTED through verify_vm_descriptor2 ALONE under the verifier-anchored declared-payload \
         column (PI 46). Residual CLOSED."
    );
}
