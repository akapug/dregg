//! state_field_truncation_regression.rs — GUARDS the state-field truncation fix and PINS the
//! documented residual (docs/FINDING-state-field-truncation.md, fix in commit 76f7a6603).
//!
//! # The bug the FINDING reported (now CLOSED)
//!
//! A cell state field holds a full 32-byte value (`FieldElement = [u8; 32]` — e.g. an
//! execution-lease's `PROVIDER_SLOT` seeded with `cell_tag(provider)`, a full cell id). The Lean
//! state producer reconstitutes each committed cell from a `WireState` whose fields are u64 lanes
//! (`lean_shadow::field_to_i128` reads only `bytes[24..32]`). Pre-fix, `wire_state_to_ledger` wrote
//! EVERY named field back through `i128_to_field` UNCONDITIONALLY (`out[24..32] = v; out[0..24] =
//! 0`), so any producer turn that merely RE-EMITTED a cell — a `GrantCapability{to: c}` moves `c`'s
//! `cap_root`, an `IncrementNonce` moves its nonce — shredded every full-width field it never
//! touched to its low 8 bytes, on the executing node only. The lease's 32-byte provider id became
//! `0000…d68064` and the rent rail silently stopped.
//!
//! The fix (76f7a6603): the reconstituted `cell` is a clone of the intact pre-state template;
//! install the produced u64 lane ONLY when it DIFFERS from the template's low-8 lane (a genuine
//! move), else keep the template's full 32 bytes. [`pinned_32byte_field_survives_a_touching_turn`]
//! is the regression guard — it FAILS on the pre-fix code (unconditional truncation) and PASSES now.
//!
//! # The residual this file also PINS (open by design, v13-scoped)
//!
//! A turn that GENUINELY `SetField`s a slot to a NEW full-width value still loses its high 24 bytes,
//! because the wire cannot carry them (`field_to_i128` is a low-8 projection; even `WireValue::Dig`
//! is a `u64`). Closing it is a wire-model + verified-kernel widening (the Lean `setField` effect
//! value is `Int`, and the committed `fields[0..7]` root is itself a `from_lossy_31bit_DANGER` fold
//! — so BOTH producers' roots agree on the lossy image and the loss is silent, not caught by the
//! `.root()` differential). That widening is sequenced WITH the v13 faithful-fields epoch, not ahead
//! of it (scholar verdict, docs/FINDING-state-field-truncation.md). [`genuine_setfield_to_a_new_
//! 32byte_value_truncates_the_residual`] PINS the boundary so it cannot move silently.
//!
//! These are PURE `wire_state_to_ledger` reconstitution tests — no Lean FFI, so they run everywhere
//! (no `lean_available()` self-skip).

use std::collections::HashMap;

use dregg_cell::{Cell, CellId, Ledger};
use dregg_exec_lean::lean_apply::wire_state_to_ledger;
use dregg_lean_ffi::marshal::{WireState, WireValue};

/// The `fields[]` slot the wire names `"target"` — the execution-lease PROVIDER slot from the
/// FINDING (`field_index_to_name(6) == "target"`).
const PROVIDER_SLOT: usize = 6;

/// The FINDING's exact 32-byte provider cell id (`934e47f2…ad7a7da327d68064`). Its high 24 bytes are
/// non-zero, so any u64-lane round-trip is OBSERVABLE as the loss of `bytes[0..24]`.
fn pinned_provider_id() -> [u8; 32] {
    [
        0x93, 0x4e, 0x47, 0xf2, 0x22, 0x21, 0x69, 0x76, 0xec, 0xab, 0xcd, 0x76, 0xf8, 0xbe, 0x42,
        0xed, 0x45, 0x9e, 0x23, 0xb1, 0x2e, 0x98, 0x8a, 0xb7, 0xad, 0x7a, 0x7d, 0xa3, 0x27, 0xd6,
        0x80, 0x64,
    ]
}

/// The low 8 bytes (big-endian) of a 32-byte value — the ONLY part the wire carries
/// (`lean_shadow::field_to_i128`).
fn low8_be(v: &[u8; 32]) -> i128 {
    let mut b = [0u8; 8];
    b.copy_from_slice(&v[24..32]);
    u64::from_be_bytes(b) as i128
}

/// A one-cell template ledger whose `PROVIDER_SLOT` carries the full 32-byte provider id — exactly
/// as `starbridge-apps/execution-lease` seeds it via `st.set_field(n, cell_tag(terms.provider))`.
/// The template is the pre-state the extractor clones; it holds the intact bytes.
fn template_with_pinned_provider() -> (Ledger, CellId, HashMap<u64, CellId>) {
    let mut pk = [0u8; 32];
    pk[0] = 1;
    pk[31] = 37;
    let mut cell = Cell::with_balance(pk, [0u8; 32], 100);
    assert!(
        cell.state.set_field(PROVIDER_SLOT, pinned_provider_id()),
        "seed the full 32-byte provider id into the PROVIDER slot"
    );
    let id = cell.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(cell).unwrap();
    let inv = HashMap::from([(0u64, id)]);
    (ledger, id, inv)
}

/// REGRESSION GUARD (fix 76f7a6603). A 32-byte field pinned in the template SURVIVES a producer
/// turn that touches the cell (bumps its nonce) but never `SetField`s that slot.
///
/// `ledger_to_wire_state` re-emits EVERY non-zero field as its low-8 lane, so the wire record
/// carries `("target", Int(low8))` even though the field did not move. The extractor sees the
/// produced lane == the template lane and keeps the template's full 32 bytes. On the PRE-FIX code
/// (`set_field(idx, i128_to_field(*i))` unconditional) this assertion FAILS — the field is shredded
/// to `0000…d68064`.
#[test]
fn pinned_32byte_field_survives_a_touching_turn() {
    let (template, id, inv) = template_with_pinned_provider();
    let full = pinned_provider_id();

    // A committed turn that TOUCHES the cell (nonce 0 -> 1) but performs NO SetField on slot 6.
    let record = WireValue::Record(vec![
        ("balance".into(), WireValue::Int(100)),
        ("nonce".into(), WireValue::Int(1)),
        ("target".into(), WireValue::Int(low8_be(&full))),
    ]);
    let ws = WireState {
        cells: vec![(0, record)],
        ..Default::default()
    };

    let out = wire_state_to_ledger(&ws, &inv, &template, &[], &[], true)
        .expect("reconstitution must succeed");
    let cell = out.get(&id).unwrap();

    assert_eq!(
        cell.state.fields[PROVIDER_SLOT], full,
        "REGRESSION (76f7a6603): a 32-byte field pinned in the template must survive a turn that \
         only bumps the nonce — the low-8 wire lane matches the template lane, so the extractor \
         keeps the full-width template field instead of shredding it to bytes[24..32]"
    );
    assert_eq!(
        cell.state.nonce(),
        1,
        "the turn really TOUCHED the cell (nonce moved), so the survival is non-vacuous"
    );
}

/// PIN of the DOCUMENTED RESIDUAL (open by design, v13-scoped). A turn that GENUINELY `SetField`s
/// slot 6 to a NEW full-width value loses its high 24 bytes: the wire carries only the low-8 lane,
/// and the extractor — seeing a genuine move (lane differs from the template) — installs the
/// truncated value. This is NOT a local extractor bug; the high bytes are already gone at the wire.
/// Closing it is the wire+kernel widening sequenced with the v13 faithful-fields epoch.
#[test]
fn genuine_setfield_to_a_new_32byte_value_truncates_the_residual() {
    let (template, id, inv) = template_with_pinned_provider();

    // The turn SetFields slot 6 to a NEW 32-byte value whose LOW 8 bytes differ from the template's
    // — so the extractor sees a genuine move and installs the (truncated) wire lane.
    let mut new_val = [0xEEu8; 32];
    new_val[24..32].copy_from_slice(&0x1122_3344_5566_7788u64.to_be_bytes());
    assert_ne!(
        low8_be(&new_val),
        low8_be(&pinned_provider_id()),
        "the new value's low-8 lane must differ so the extractor treats it as a real move"
    );

    let record = WireValue::Record(vec![
        ("balance".into(), WireValue::Int(100)),
        ("nonce".into(), WireValue::Int(1)),
        ("target".into(), WireValue::Int(low8_be(&new_val))),
    ]);
    let ws = WireState {
        cells: vec![(0, record)],
        ..Default::default()
    };

    let out = wire_state_to_ledger(&ws, &inv, &template, &[], &[], true)
        .expect("reconstitution must succeed");
    let got = out.get(&id).unwrap().state.fields[PROVIDER_SLOT];

    // The residual: only the low 8 bytes of the NEW value survive; the high 24 are zeroed.
    let mut expected_truncated = [0u8; 32];
    expected_truncated[24..32].copy_from_slice(&new_val[24..32]);
    assert_eq!(
        got, expected_truncated,
        "residual boundary MOVED: a genuine 32-byte SetField now round-trips more than its low-8 \
         lane. If the v13 wire+kernel widening landed, update docs/FINDING-state-field-truncation.md \
         and this test; otherwise the residual regressed"
    );
    assert_ne!(
        got, new_val,
        "the wire cannot carry the high 24 bytes of a genuinely-moved field — a faithful round-trip \
         is the v13-scoped widening, not a local extractor fix"
    );
}
