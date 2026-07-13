//! Heap-caveat tag parity (the two just-landed `StateConstraint` atoms reach the
//! staged wire): `HeapAtom::DeltaEquals` (EXACT heap delta, tag 8 = `FIELD_DELTA`)
//! and `StateConstraint::HeapFieldLteOther` (cross-KEY heap `≤`, fresh tag 21), plus
//! the displaced `|Δ| ≤ d` bounded twin's fresh home (tag 20 = `FIELD_DELTA_BOUNDED`).
//!
//! SCOPE (honest): these are PARITY with the existing heap caveat surface — the
//! STAGED heap-plane `RotCaveatEntry` wire tag + the Lean bridge
//! (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitRotationCaveat.lean` §5/§5b) + the
//! NAMED discharge premise (`HeapCaveatRuntimeDischarge` /
//! `HeapRelCaveatRuntimeDischarge`). Heap caveats are host/scalar re-evaluated (like
//! today's `HeapField`), NOT register-live re-eval, so there is no new
//! `verify_slot_caveat_manifest` match arm — the new tags are the VK-safe additive
//! PI tags. An un-upgraded verifier rejects them as `unknown type_tag` (epoch-
//! lockstep), NOT a proving-key rotation: that is the property this file pins.
//!
//! The DeltaEquals sat/unsat fixture rides the LIVE tag-8 (`FIELD_DELTA`) re-eval,
//! whose semantics is the EXACT `new == old + delta` — precisely what the Lean twin
//! now models (`heapAdmits_deltaEquals_iff`; the prior `deltaBounded` decode was a
//! semantic mismatch, corrected). The cross-key `HeapFieldLteOther` sat/unsat lives
//! in the Lean §5b both-polarity `#guard`s (host/scalar-evaluated; no slot re-eval).

use dregg_circuit::effect_vm::pi;
use dregg_circuit::effect_vm::{SlotCaveatEntry, verify_slot_caveat_manifest};
use dregg_circuit::field::BabyBear;

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

fn fields_with(slot: usize, value: u32) -> [BabyBear; 8] {
    let mut f = [BabyBear::ZERO; 8];
    f[slot] = BabyBear::new(value);
    f
}

// ── The tag numbers: appended after VAULT_DEPOSIT=19, distinct from all prior tags. ──

#[test]
fn new_heap_caveat_tags_are_appended_and_distinct() {
    assert_eq!(pi::SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED, 20);
    assert_eq!(pi::SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER, 21);

    // Append-only: the new tags sit strictly above the prior maximum (VAULT_DEPOSIT=19),
    // so no existing tag renumbers (postcard indices / VKs untouched).
    let existing = [
        pi::SLOT_CAVEAT_TAG_FIELD_EQUALS,
        pi::SLOT_CAVEAT_TAG_FIELD_GTE,
        pi::SLOT_CAVEAT_TAG_FIELD_LTE,
        pi::SLOT_CAVEAT_TAG_WRITE_ONCE,
        pi::SLOT_CAVEAT_TAG_IMMUTABLE,
        pi::SLOT_CAVEAT_TAG_MONOTONIC,
        pi::SLOT_CAVEAT_TAG_STRICT_MONOTONIC,
        pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
        pi::SLOT_CAVEAT_TAG_MONOTONIC_SEQUENCE,
        pi::SLOT_CAVEAT_TAG_TEMPORAL_GATE,
        pi::SLOT_CAVEAT_TAG_SENDER_AUTHORIZED,
        pi::SLOT_CAVEAT_TAG_ALLOWED_TRANSITIONS,
        pi::SLOT_CAVEAT_TAG_RATE_BOUND,
        pi::SLOT_CAVEAT_TAG_UNTIL_EVENT,
        pi::SLOT_CAVEAT_TAG_SINCE_EVENT,
        pi::SLOT_CAVEAT_TAG_CHALLENGE_WINDOW,
        pi::SLOT_CAVEAT_TAG_SETTLE_ESCROW,
        pi::SLOT_CAVEAT_TAG_DISCHARGE_OBLIGATION,
        pi::SLOT_CAVEAT_TAG_VAULT_DEPOSIT,
    ];
    for t in existing {
        assert!(
            t < pi::SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED,
            "tag {t} must be below the appended new tags (append-only)"
        );
        assert_ne!(t, pi::SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED);
        assert_ne!(t, pi::SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER);
    }
    assert_ne!(
        pi::SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED,
        pi::SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER
    );
}

// ── VK-safety: an un-upgraded verifier rejects the new tags as unknown (epoch-lockstep). ──

#[test]
fn old_verifier_rejects_field_delta_bounded_tag() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA_BOUNDED, // 20 — staged, not slot-enforced
        slot_index: 0,
        params: [
            BabyBear::new(3),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(
        result.is_err(),
        "an un-upgraded slot verifier must reject the FIELD_DELTA_BOUNDED tag as unknown \
         (epoch-lockstep, not a VK rotation): {result:?}"
    );
}

#[test]
fn old_verifier_rejects_heap_field_lte_other_tag() {
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_HEAP_FIELD_LTE_OTHER, // 21 — cross-key heap, staged
        slot_index: 0,
        params: [
            BabyBear::new(131), // other_key
            BabyBear::new(2),   // delta
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = [BabyBear::ZERO; 8];
    let final_ = [BabyBear::ZERO; 8];
    let result = verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0);
    assert!(
        result.is_err(),
        "an un-upgraded slot verifier must reject the HEAP_FIELD_LTE_OTHER tag as unknown \
         (epoch-lockstep, not a VK rotation): {result:?}"
    );
}

// ── DeltaEquals sat/unsat: the EXACT-delta semantics the Lean twin now models, ──
// ── verified through the LIVE tag-8 (FIELD_DELTA) re-eval it is faithful to.    ──

#[test]
fn delta_equals_semantics_accepts_exact_delta() {
    // `HeapAtom::DeltaEquals { d }` lifts to `new == old + d` — the same relation the
    // live FIELD_DELTA (tag 8) verifier enforces. Old 10, delta 7, new 17 → EXACT.
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
        slot_index: 1,
        params: [
            BabyBear::new(7),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(1, 10);
    let final_ = fields_with(1, 17);
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0).is_ok(),
        "exact new == old + delta must pass (the DeltaEquals accept polarity)"
    );
}

#[test]
fn delta_equals_semantics_rejects_off_by_one() {
    // A neighbour a `deltaBounded 7` would ADMIT (|Δ| ≤ 7) but `deltaEquals 7` PINS the
    // precise step: old 10, delta 7, new 18 (Δ=8) → REFUSE. This is exactly why the
    // tag-8 → deltaEquals correction matters (deltaBounded would not have caught it).
    let entry = SlotCaveatEntry {
        type_tag: pi::SLOT_CAVEAT_TAG_FIELD_DELTA,
        slot_index: 1,
        params: [
            BabyBear::new(7),
            BabyBear::ZERO,
            BabyBear::ZERO,
            BabyBear::ZERO,
        ],
    };
    let public_inputs = pi_with_manifest(&[entry]);
    let initial = fields_with(1, 10);
    let final_ = fields_with(1, 18); // off-by-one from the exact delta
    assert!(
        verify_slot_caveat_manifest(&public_inputs, &initial, &final_, 0).is_err(),
        "an inexact delta must reject (the DeltaEquals refuse polarity)"
    );
}
