//! Constraint-binding weld: the OMISSION-PROOF coverage check (the soundness core
//! — `docs/deos/VK-EPOCH-CONSTRAINT-BINDING-DESIGN.md`).
//!
//! The §6 weld rungs prove a PRESENT manifest entry forces its capacity invariant;
//! these tests pin the load-bearing gap they leave — that the entry must be present
//! at all. `verify_slot_caveat_coverage` re-derives the required capacity tags from
//! the cell's COMMITTED declaration and DEMANDS each is present; paired with
//! `verify_slot_caveat_manifest` (satisfaction of present entries) the declared gate
//! is omission-proof. This is the circuit-side shadow of the Lean
//! `Dregg2.Deos.ConstraintBinding.omission_caught_under_binding` /
//! `omission_rejected` / `unsatisfied_rejected` teeth, both polarities.

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{
    SlotCaveatEntry, verify_slot_caveat_coverage, verify_slot_caveat_manifest,
};
use dregg_circuit::field::BabyBear;

const LEG_A: u8 = 3;
const LEG_B: u8 = 4;
const DEPOSITED: u32 = pi::SETTLE_ESCROW_STATUS_DEPOSITED;
const CONSUMED: u32 = pi::SETTLE_ESCROW_STATUS_CONSUMED;

fn pi_with_manifest(entries: &[SlotCaveatEntry]) -> Vec<BabyBear> {
    let mut public_inputs = vec![BabyBear::ZERO; pi::ACTIVE_BASE_COUNT];
    let count = entries.len().min(pi::MAX_SLOT_CAVEATS);
    public_inputs[pi::SLOT_CAVEAT_COUNT] = BabyBear::new(count as u32);
    for (i, entry) in entries.iter().take(count).enumerate() {
        let base = pi::SLOT_CAVEAT_MANIFEST_BASE + i * pi::SLOT_CAVEAT_ENTRY_SIZE;
        entry.write_to(&mut public_inputs[base..base + pi::SLOT_CAVEAT_ENTRY_SIZE]);
    }
    public_inputs
}

fn settle_entry() -> SlotCaveatEntry {
    SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        slot_index: LEG_A,
        params: [
            BabyBear::new(LEG_B as u32),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    }
}

fn legs(status_a: u32, status_b: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[LEG_A as usize] = BabyBear::new(status_a);
    f[LEG_B as usize] = BabyBear::new(status_b);
    f
}

// ── Accept polarity: an honest escrow turn — entry PRESENT, satisfied, covered. ──

#[test]
fn honest_escrow_turn_present_and_covered() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    let before = legs(DEPOSITED, DEPOSITED);
    let after = legs(CONSUMED, CONSUMED);
    let required = [pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW];

    // Satisfaction: the present entry's gate holds.
    assert!(verify_slot_caveat_manifest(&public_inputs, &before, &after, 0).is_ok());
    // Coverage: the required tag is present.
    assert!(
        verify_slot_caveat_coverage(&public_inputs, &required).is_ok(),
        "an honest escrow turn that declares AND publishes the SettleEscrow entry passes coverage"
    );
}

// ── THE OMISSION TOOTH: the cell DECLARES SettleEscrow, but the manifest OMITS it.
//    Satisfaction alone is vacuously OK (nothing to check) — coverage REJECTS. ──

#[test]
fn omitted_declared_entry_rejected_by_coverage() {
    // The forger publishes an EMPTY manifest (count = 0) — the omission attack.
    let public_inputs = pi_with_manifest(&[]);
    let required = [pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW];

    // Satisfaction is vacuously OK — the deployed path has nothing to reject (the gap).
    let before = legs(DEPOSITED, DEPOSITED);
    let after = legs(CONSUMED, CONSUMED);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after, 0).is_ok(),
        "satisfaction alone cannot catch an OMITTED entry — that is the soundness gap"
    );
    // Coverage CATCHES the omission (the soundness core).
    let cov = verify_slot_caveat_coverage(&public_inputs, &required);
    assert!(
        cov.is_err(),
        "a DECLARED-but-OMITTED capacity entry MUST be rejected by coverage; got {cov:?}"
    );
}

#[test]
fn wrong_tag_does_not_cover() {
    // The forger publishes a benign Monotonic entry (tag 6) instead of the declared
    // SettleEscrow (tag 17) — coverage of 17 still fails.
    let bait = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_MONOTONIC,
        slot_index: 0,
        params: [BabyBear::ZERO; 4],
    };
    let public_inputs = pi_with_manifest(&[bait]);
    let required = [pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW];
    assert!(
        verify_slot_caveat_coverage(&public_inputs, &required).is_err(),
        "a manifest with the WRONG tag does not cover the required capacity tag"
    );
}

// ── THE HOLLOW-ENTRY TOOTH: entry PRESENT (covers passes) but its gate FAILS
//    (a partial settle) — satisfaction REJECTS. Together they are omission-proof. ──

#[test]
fn present_but_partial_settle_rejected_by_satisfaction() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    let required = [pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW];
    // Coverage passes — the entry IS present.
    assert!(verify_slot_caveat_coverage(&public_inputs, &required).is_ok());
    // But the half-open trade (leg B left Deposited) fails satisfaction.
    let before = legs(DEPOSITED, DEPOSITED);
    let after = legs(CONSUMED, DEPOSITED);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &before, &after, 0).is_err(),
        "a partial settle present in the manifest fails the satisfaction gate"
    );
}

// ── Multiple declared capacities: ALL required tags must be covered. ──

#[test]
fn multiple_required_tags_all_must_be_present() {
    let public_inputs = pi_with_manifest(&[settle_entry()]);
    // The cell declares BOTH escrow and discharge; only escrow is published.
    let required = [
        pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
    ];
    assert!(
        verify_slot_caveat_coverage(&public_inputs, &required).is_err(),
        "dropping one of two declared capacity entries must be rejected by coverage"
    );
    // Publishing only escrow but requiring only escrow passes.
    assert!(
        verify_slot_caveat_coverage(&public_inputs, &[pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW]).is_ok()
    );
}

#[test]
fn empty_required_set_is_vacuously_covered() {
    // A non-capacity cell declares no capacity caveats — coverage is a no-op.
    let public_inputs = pi_with_manifest(&[]);
    assert!(verify_slot_caveat_coverage(&public_inputs, &[]).is_ok());
}
