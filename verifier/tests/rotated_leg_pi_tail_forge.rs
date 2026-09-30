//! Rotated-leg public-input TAIL forge (synthesis 2026-09-30 item 1, lane 10 F1).
//!
//! A WIDE rotated leg's 8-felt before/after commit anchors are the LAST 16 PIs of its
//! accepting descriptor's `public_input_count` window, where the descriptor's carrier
//! `PiBinding`s tie them to the proof. They are "the last 16 of the shipped vector" only
//! when the shipped vector IS that window. The resolver used to verify a PREFIX
//! (`public_inputs[..public_input_count]`, guarded by `>=`) while `commit_anchors` read
//! the vector's own tail, so a genuine leg with 16 attacker-chosen felts appended
//! verified as a proof of `X -> Y`.
//!
//! `rotated_forged_tail_on_a_genuine_wide_leg_is_refused` builds that forgery CONSTRUCTIVELY from a
//! real wide leg, asserts the mutation happened (the genuine prefix is intact, the tail is
//! 16 chosen felts that differ from the genuine anchors), then asserts refusal at every
//! entry that consumes the vector.
//!
//! `wide_anchors_are_pi_bound_inside_every_accepted_rotated_window` is the layout half: for every
//! member this floor accepts as WIDE (shipped + derived welded), each of the last 16 PI
//! slots of its window carries a `PiBinding`. That is the fact that makes
//! `len == public_input_count` the right pin, rather than a layout change.
//!
//! SLOW (one real wide Plonky3 proof). Run with
//! `cargo nextest run -p dregg-verifier -E 'test(/rotated/)'`.

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
use dregg_circuit::descriptor_ir2::{VmConstraint2, parse_vm_descriptor2, prove_vm_descriptor2};
use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::trace_rotated::{
    RotatedBlockWitness, generate_rotated_effect_vm_descriptor_and_trace_wide,
    rotated_descriptor_name_for_effect, transfer_caveat_manifest,
};
use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit::effect_vm_descriptors::{WIDE_REGISTRY_STAGED_TSV, welded_wide_members};
use dregg_circuit::field::BabyBear;
use dregg_circuit::lean_descriptor_air::VmConstraint;
use dregg_commit::typed::canonical_32_to_felts_4;
use dregg_turn::rotation_witness as rw;
use dregg_turn::turn::TurnReceipt;
use dregg_verifier::rotated_replay::resolve_rotated_descriptor;
use dregg_verifier::{RotatedReplayLeg, verify_rotated_leg, verify_rotated_replay_chain};

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

fn producer_cell(balance: i64) -> Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    cell
}

fn bridge(w: &rw::RotationWitness) -> RotatedBlockWitness {
    RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot)
        .expect("pre-iroot limbs")
        .with_asset_class(w.asset_class)
}

fn produce(cell: &Cell, ledger: &Ledger) -> rw::RotationWitness {
    rw::produce(
        cell,
        ledger,
        &rw::empty_nullifier_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &rw::empty_revoked_root_8(),
        &[[1u8; 32], [2u8; 32]],
        &dregg_cell::commitment::RotationCarrierMaterial::default(),
    )
}

/// Mint ONE real WIDE transfer leg through the deployed wide dispatcher (the route the SDK's
/// `prove_cohort_run_chain` takes). Returns the leg, its genuine 8-felt anchors, and the
/// accepting descriptor's `public_input_count`.
fn mint_wide_transfer_leg() -> (RotatedReplayLeg, [BabyBear; 8], [BabyBear; 8], usize) {
    let before_balance: i64 = 100_000;
    let amount: u64 = 50;
    let st = CellState::new(before_balance as u64, 0);
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(before_balance - amount as i64);
    let mut ledger = Ledger::new();
    ledger.insert_cell(after_cell.clone()).unwrap();
    let before_w = bridge(&produce(&before_cell, &ledger));
    let after_w = bridge(&produce(&after_cell, &ledger));

    let effect = Effect::Transfer {
        amount,
        direction: 1,
    };
    let effects = vec![effect.clone()];
    let (desc, trace, mut dpis, map_heaps, mb) =
        generate_rotated_effect_vm_descriptor_and_trace_wide(
            &st,
            &effects,
            &before_w,
            &after_w,
            &transfer_caveat_manifest(),
            None,
            None,
            None,
            None,
        )
        .expect("wide dispatch");
    let pic = desc.public_input_count;
    assert_eq!(
        dpis.len(),
        pic,
        "the wide producer emits exactly the window"
    );

    let receipt = TurnReceipt {
        turn_hash: [0xB1u8; 32],
        ..Default::default()
    };
    let th = canonical_32_to_felts_4(&receipt.turn_hash);
    dpis[pi::TURN_HASH_BASE..pi::TURN_HASH_BASE + pi::TURN_HASH_LEN].copy_from_slice(&th);

    let proof = prove_vm_descriptor2(&desc, &trace, &dpis, &mb, &map_heaps)
        .unwrap_or_else(|e| panic!("wide rotated proof for {} failed: {e}", desc.name));
    let proof_bytes = postcard::to_allocvec(&proof).expect("Ir2BatchProof serializes");

    // The dispatcher resolved the WIDE row keyed by the effect's cohort name; the leg's
    // vk_hash is that row's committed-JSON fingerprint.
    let key = rotated_descriptor_name_for_effect(&effect).expect("transfer is in the cohort");
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            (it.next() == Some(key)).then(|| {
                let _ = it.next();
                it.next()
            })?
        })
        .expect("wide row for the transfer key");
    let vk_hash = *blake3::hash(json.as_bytes()).as_bytes();

    let old8: [BabyBear; 8] = dpis[pic - 16..pic - 8].try_into().unwrap();
    let new8: [BabyBear; 8] = dpis[pic - 8..pic].try_into().unwrap();
    let leg = RotatedReplayLeg {
        receipt,
        proof_bytes,
        public_inputs: dpis.iter().map(|b| b.as_u32()).collect(),
        vk_hash,
    };
    (leg, old8, new8, pic)
}

fn felts(leg: &RotatedReplayLeg) -> Vec<BabyBear> {
    leg.public_inputs
        .iter()
        .map(|&v| BabyBear::new_canonical(v))
        .collect()
}

#[test]
fn rotated_forged_tail_on_a_genuine_wide_leg_is_refused() {
    let (leg, old8, new8, pic) = mint_wide_transfer_leg();

    // Control: the genuine leg verifies against its genuine anchors.
    let ok = verify_rotated_replay_chain(std::slice::from_ref(&leg), old8, new8);
    assert!(
        ok.overall_verified,
        "the genuine wide leg must verify: {}",
        ok.summary
    );

    // The attacker's claimed transition X -> Y: 16 chosen felts.
    let x: [BabyBear; 8] = std::array::from_fn(|i| BabyBear::new(0x1000 + i as u32));
    let y: [BabyBear; 8] = std::array::from_fn(|i| BabyBear::new(0x2000 + i as u32));
    assert_ne!(
        x, old8,
        "the chosen before-anchor must differ from the genuine one"
    );
    assert_ne!(
        y, new8,
        "the chosen after-anchor must differ from the genuine one"
    );

    let mut forged = leg.clone();
    forged
        .public_inputs
        .extend(x.iter().chain(y.iter()).map(|f| f.as_u32()));

    // The mutation happened: genuine window intact, 16 chosen felts past it, and the
    // vector's own tail now reads X -> Y.
    let n = forged.public_inputs.len();
    assert_eq!(n, pic + 16);
    assert_eq!(forged.public_inputs[..pic], leg.public_inputs[..]);
    let tail_x: Vec<u32> = x.iter().map(|f| f.as_u32()).collect();
    let tail_y: Vec<u32> = y.iter().map(|f| f.as_u32()).collect();
    assert_eq!(forged.public_inputs[n - 16..n - 8], tail_x[..]);
    assert_eq!(forged.public_inputs[n - 8..n], tail_y[..]);

    // The headline: the chain verifier must not read this as a proof of X -> Y.
    let forged_xy = verify_rotated_replay_chain(std::slice::from_ref(&forged), x, y);
    assert!(
        !forged_xy.overall_verified,
        "a genuine proof of old->new was accepted as attesting X->Y: {}",
        forged_xy.summary
    );

    // Refused at the resolver (shared with cross_fed), at the leg, and at the chain against
    // the genuine endpoints too — the tail is refused, not merely ignored.
    let resolved = resolve_rotated_descriptor(&forged.proof_bytes, &felts(&forged));
    assert!(
        resolved.is_err(),
        "resolver accepted a vector {} PIs past its window: {resolved:?}",
        n - pic
    );
    assert!(
        verify_rotated_leg(&forged).is_err(),
        "verify_rotated_leg accepted the forged tail"
    );
    let forged_genuine = verify_rotated_replay_chain(std::slice::from_ref(&forged), old8, new8);
    assert!(
        !forged_genuine.overall_verified,
        "a vector longer than its window verified against the genuine anchors: {}",
        forged_genuine.summary
    );

    // One extra felt is the same defect at its smallest.
    let mut plus_one = leg.clone();
    plus_one.public_inputs.push(7);
    assert_eq!(plus_one.public_inputs.len(), pic + 1);
    assert!(
        verify_rotated_leg(&plus_one).is_err(),
        "a single trailing felt was accepted"
    );

    // And a short vector stays refused.
    let mut short = leg.clone();
    short.public_inputs.pop();
    assert_eq!(short.public_inputs.len(), pic - 1);
    assert!(
        verify_rotated_leg(&short).is_err(),
        "a truncated vector was accepted"
    );
}

#[test]
fn wide_anchors_are_pi_bound_inside_every_accepted_rotated_window() {
    let mut members: Vec<(String, dregg_circuit::descriptor_ir2::EffectVmDescriptor2)> =
        WIDE_REGISTRY_STAGED_TSV
            .lines()
            .filter_map(|line| {
                let mut it = line.splitn(3, '\t');
                let key = it.next()?;
                let _ = it.next();
                let json = it.next()?;
                Some((
                    key.to_string(),
                    parse_vm_descriptor2(json).expect("wide row parses"),
                ))
            })
            .collect();
    let shipped = members.len();
    members.extend(
        welded_wide_members()
            .into_iter()
            .map(|(k, d)| (format!("{k} (welded)"), d)),
    );
    assert!(
        shipped >= 57,
        "the wide registry is the 57-member cover, got {shipped}"
    );
    assert!(members.len() > shipped, "the welded set is non-empty");

    for (key, desc) in &members {
        let pic = desc.public_input_count;
        assert!(pic >= 16, "{key}: window {pic} cannot hold the 16 anchors");
        for slot in pic - 16..pic {
            let bound = desc.constraints.iter().any(|c| {
                matches!(
                    c,
                    VmConstraint2::Base(VmConstraint::PiBinding { pi_index, .. }) if *pi_index == slot
                )
            });
            assert!(
                bound,
                "{key}: wide anchor PI {slot} (window {pic}) carries no PiBinding — the anchor \
                 is not tied to the proof"
            );
        }
    }
}
