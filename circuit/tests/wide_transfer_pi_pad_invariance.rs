//! **THE PAD-INVARIANCE DECIDER for the wide transfer-shape PI vector.**
//!
//! The deployed `transferVmDescriptor2R24` is the availability-hardened member
//! (`dregg-effectvm-transfer-v1-avail-…`), so the production dispatcher
//! [`generate_rotated_effect_vm_descriptor_and_trace_wide`] derives `TRANSFER_AVAIL_PAD` (10) for
//! it via `avail_pad_for_descriptor_name`. Three PI-RECONSTRUCTION sites instead call the pad-0
//! wrapper `generate_rotated_transfer_shape_wide` (= `..._wide_avail(0, …)`) against that same
//! pad-10 family and keep ONLY the returned `dpis`, discarding the trace:
//!
//!   * `turn/src/executor/proof_verify.rs`   — executor-side PI reconstruction before `verify`
//!   * `sdk/src/full_turn_proof.rs`          — SDK PI reconstruction
//!   * `sdk/src/cipherclerk.rs`              — cipherclerk PI reconstruction
//!
//! That is sound IFF the PI vector is PAD-INVARIANT. The live federation verifying is EVIDENCE,
//! not proof — this file is the proof. It pins, as a measurement:
//!
//!   `dpis(pad 0) == dpis(pad 10)`, lane for lane, on an honest transfer turn.
//!
//! The structural reason: the pad only widens the v1 FACE (availability-weld witness limbs at
//! `[V1_WIDTH, V1_WIDTH + pad)`, filled from each row's OWN v1 state/param columns) and shifts
//! every appendix base by the pad; `append_wide_carriers_avail` re-absorbs the rotated limbs at
//! `BEFORE_BASE + avail_pad` / `AFTER_BASE + avail_pad` — the SAME logical limb block — so the
//! 16 wide commit carriers land on identical values. The pad moves COLUMNS, never PI VALUES.
//!
//! NOT VACUOUS: the two runs are not two spellings of one constant. `pad_10_genuinely_differs`
//! pins that the SAME pair of generator calls produces materially DIFFERENT traces — different
//! widths (`+10`), and a pad-10 v1 face whose `[AVAIL_BASE, AVAIL_BASE+10)` columns carry the
//! weld's limb/borrow witness where pad-0 carries the rotated BEFORE block. If a refactor ever
//! collapsed the two calls into the same trace, that test fails and this file stops attesting.

use dregg_circuit::CellState;
use dregg_circuit::effect_vm::Effect;
use dregg_circuit::effect_vm::trace_rotated::{
    BEFORE_BASE, RotatedBlockWitness, TRANSFER_AVAIL_PAD, V1_WIDTH, avail_pad_for_descriptor_name,
    generate_rotated_transfer_shape_wide, generate_rotated_transfer_shape_wide_avail,
    transfer_caveat_manifest,
};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_turn::rotation_witness as rw;

use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};

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

/// The registry name the deployed `transferVmDescriptor2R24` row carries.
fn deployed_transfer_name() -> String {
    for line in WIDE_REGISTRY_STAGED_TSV.lines() {
        let mut parts = line.splitn(3, '\t');
        if parts.next() == Some("transferVmDescriptor2R24") {
            return parts
                .next()
                .expect("registry line has a name column")
                .to_string();
        }
    }
    panic!("transferVmDescriptor2R24 not in WIDE_REGISTRY_STAGED_TSV");
}

/// The honest transfer turns the decider sweeps. The availability weld is about 15-bit limb
/// decomposition + the borrow/carry chains, so the sweep deliberately crosses limb boundaries and
/// runs BOTH directions — a pad that leaked into the PIs would most plausibly do it through a
/// limb/borrow-shaped value, so a single mid-range debit would be a thin measurement.
///
/// `(before_balance, after_balance, amount, direction)`; direction 1 = outgoing debit, 0 = credit.
const TRANSFER_SWEEP: &[(i64, i64, u64, u32)] = &[
    (100_000, 99_000, 1_000, 1),   // the plain mid-range debit
    (100_000, 100_000, 0, 1),      // zero amount — every borrow/carry bit closes at 0
    (100_000, 99_999, 1, 1),       // minimal debit
    (100_000, 0, 100_000, 1),      // drain to empty — the maximal borrow chain
    (32_768, 0, 32_768, 1),        // exactly 2^15: the 15-bit limb boundary
    (100_000, 67_232, 32_768, 1),  // a 2^15 debit off a non-boundary balance
    (100_000, 34_464, 65_536, 1),  // exactly 2^16 — two limbs
    (0, 1_000, 1_000, 0),          // credit onto an empty cell (the carry leg)
    (100_000, 132_768, 32_768, 0), // a limb-boundary credit
];

/// One honest transfer turn's witnesses.
fn honest_transfer_inputs_for(
    before_balance: i64,
    after_balance: i64,
    amount: u64,
    direction: u32,
) -> (
    CellState,
    Vec<Effect>,
    RotatedBlockWitness,
    RotatedBlockWitness,
    dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
) {
    let st = CellState::new(before_balance as u64, 0);
    let mut ledger = Ledger::new();
    let before_cell = producer_cell(before_balance);
    let after_cell = producer_cell(after_balance);
    ledger.insert_cell(after_cell.clone()).unwrap();
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let produce = |cell: &Cell| {
        rw::produce(
            cell,
            &ledger,
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_circuit::heap_root::empty_heap_root_8(),
            &dregg_turn::rotation_witness::empty_revoked_root_8(),
            &receipt_log,
            &Default::default(),
        )
    };
    let before_w = produce(&before_cell);
    let after_w = produce(&after_cell);
    let bridge = |w: &rw::RotationWitness| {
        RotatedBlockWitness::new(w.pre_limbs.clone(), w.iroot).expect("pre-iroot limbs")
    };
    let effects = vec![Effect::Transfer { amount, direction }];
    (
        st,
        effects,
        bridge(&before_w),
        bridge(&after_w),
        transfer_caveat_manifest(),
    )
}

/// The canonical mid-range debit, for the tests that only need one honest turn.
fn honest_transfer_inputs() -> (
    CellState,
    Vec<Effect>,
    RotatedBlockWitness,
    RotatedBlockWitness,
    dregg_circuit::effect_vm::trace_rotated::RotatedCaveatManifest,
) {
    let (b, a, amt, dir) = TRANSFER_SWEEP[0];
    honest_transfer_inputs_for(b, a, amt, dir)
}

/// The premise the three PI-reconstruction sites rest on: the DEPLOYED transfer family really is
/// the pad-10 hardened member, and the wrapper those sites call really is pad 0. If this ever
/// flips (e.g. the family goes bare), the invariance below stops being load-bearing — but it also
/// stops being a hazard, and this test says which world we are in.
#[test]
fn deployed_transfer_family_is_pad_10_while_the_shape_wrapper_is_pad_0() {
    let name = deployed_transfer_name();
    let pad = avail_pad_for_descriptor_name(&name);
    assert_eq!(
        pad, TRANSFER_AVAIL_PAD,
        "deployed transferVmDescriptor2R24 ({name}) must derive the hardened transfer pad"
    );
    assert_eq!(TRANSFER_AVAIL_PAD, 10, "the hardened transfer pad is 10");

    // `generate_rotated_transfer_shape_wide` is definitionally `..._wide_avail(0, …)`: pin it by
    // OBSERVATION (identical output to an explicit pad-0 call), not by reading the source.
    let (st, effects, before_w, after_w, caveat) = honest_transfer_inputs();
    let (t_wrapper, d_wrapper) =
        generate_rotated_transfer_shape_wide(&st, &effects, &before_w, &after_w, &caveat)
            .expect("honest transfer, shape wrapper");
    let (t_explicit0, d_explicit0) =
        generate_rotated_transfer_shape_wide_avail(0, &st, &effects, &before_w, &after_w, &caveat)
            .expect("honest transfer, explicit pad 0");
    assert_eq!(
        d_wrapper, d_explicit0,
        "the shape wrapper is the pad-0 generator"
    );
    assert_eq!(t_wrapper, t_explicit0, "…on the trace too");
}

/// **THE DECIDER.** `dpis(pad 0) == dpis(pad 10)` for the deployed transfer family, lane for lane.
///
/// This is what makes the three PI-reconstruction sites sound: they hand the pad-0 wrapper's
/// `dpis` to `verify_vm_descriptor2` against the pad-10 `transferVmDescriptor2R24` and throw the
/// (wrong-shaped) trace away. Because the PI vector does not move with the pad, the reconstructed
/// vector is the producer's vector, and Fiat–Shamir absorbs the same felts on both sides.
#[test]
fn wide_transfer_public_inputs_are_pad_invariant() {
    for &(before, after, amount, direction) in TRANSFER_SWEEP {
        let case = format!("transfer {before}→{after} amount={amount} dir={direction}");
        let (st, effects, before_w, after_w, caveat) =
            honest_transfer_inputs_for(before, after, amount, direction);

        let (_t0, dpis_pad0) = generate_rotated_transfer_shape_wide_avail(
            0, &st, &effects, &before_w, &after_w, &caveat,
        )
        .unwrap_or_else(|e| panic!("{case}: honest turn must generate at pad 0: {e}"));
        let (_t10, dpis_pad10) = generate_rotated_transfer_shape_wide_avail(
            TRANSFER_AVAIL_PAD,
            &st,
            &effects,
            &before_w,
            &after_w,
            &caveat,
        )
        .unwrap_or_else(|e| panic!("{case}: honest turn must generate at the hardened pad: {e}"));

        assert_eq!(
            dpis_pad0.len(),
            dpis_pad10.len(),
            "{case}: the pad must not change the PI COUNT (pad 0: {}, pad {}: {})",
            dpis_pad0.len(),
            TRANSFER_AVAIL_PAD,
            dpis_pad10.len()
        );

        // Lane-by-lane, so a break names the exact PI index and both felts rather than
        // "vectors differ".
        let mut differing: Vec<(usize, BabyBear, BabyBear)> = Vec::new();
        for (i, (a, b)) in dpis_pad0.iter().zip(dpis_pad10.iter()).enumerate() {
            if a != b {
                differing.push((i, *a, *b));
            }
        }
        if std::env::var("DREGG_DUMP_DPIS").is_ok() {
            eprintln!("{case}: dpis len = {}", dpis_pad0.len());
            eprintln!("  pad0  = {dpis_pad0:?}");
            eprintln!("  pad10 = {dpis_pad10:?}");
        }
        assert!(
            differing.is_empty(),
            "LIVE EXECUTOR BREAK ({case}): the wide transfer PI vector is NOT pad-invariant. The \
             three PI-reconstruction sites (turn/src/executor/proof_verify.rs, \
             sdk/src/full_turn_proof.rs, sdk/src/cipherclerk.rs) reconstruct at pad 0 and verify \
             against the pad-10 deployed transferVmDescriptor2R24. Differing lanes \
             (index, pad0, pad10): {differing:?}"
        );
    }
}

/// **THE NON-VACUITY GATE.** The equality above must not be two spellings of one constant.
///
/// The pad is a REAL, MATERIAL difference in what the generator emits — it just does not reach the
/// PIs. Pin that the exact same pair of calls whose PIs agree produce traces that genuinely
/// disagree: a `+TRANSFER_AVAIL_PAD` wider row, and a v1 face whose `[V1_WIDTH, V1_WIDTH + pad)`
/// window carries the availability weld's witness at pad 10 where pad 0 has the rotated BEFORE
/// block. If a refactor collapsed the two calls into one path, the decider would go vacuously
/// green — this test goes red instead.
#[test]
fn pad_10_genuinely_differs_so_the_invariance_is_not_vacuous() {
    let (st, effects, before_w, after_w, caveat) = honest_transfer_inputs();

    let (t0, _d0) =
        generate_rotated_transfer_shape_wide_avail(0, &st, &effects, &before_w, &after_w, &caveat)
            .expect("honest transfer at pad 0");
    let (t10, _d10) = generate_rotated_transfer_shape_wide_avail(
        TRANSFER_AVAIL_PAD,
        &st,
        &effects,
        &before_w,
        &after_w,
        &caveat,
    )
    .expect("honest transfer at the hardened transfer pad");

    assert_eq!(t0.len(), t10.len(), "same turn ⇒ same row count");
    assert_eq!(
        t10[0].len(),
        t0[0].len() + TRANSFER_AVAIL_PAD,
        "the pad-10 trace must be exactly {TRANSFER_AVAIL_PAD} columns wider — if these widths \
         agree, the two generator calls are the same call and the pad-invariance decider is vacuous"
    );

    // The v1-face window the pad occupies. At pad 10 it is the availability weld's witness (limb
    // decompositions + borrow/carry bits); at pad 0 those columns are the rotated BEFORE block
    // (`BEFORE_BASE == V1_WIDTH`). Materially different content in the same absolute columns.
    assert_eq!(
        BEFORE_BASE, V1_WIDTH,
        "the pad window opens exactly where the bare layout puts the rotated BEFORE block"
    );
    let window = V1_WIDTH..V1_WIDTH + TRANSFER_AVAIL_PAD;
    let faces_differ = t0
        .iter()
        .zip(t10.iter())
        .any(|(r0, r10)| r0[window.clone()] != r10[window.clone()]);
    assert!(
        faces_differ,
        "the pad-10 availability-weld witness window must differ from the pad-0 rotated block in \
         the same absolute columns — otherwise the pad is inert and the decider proves nothing"
    );

    // …and the traces disagree as whole objects.
    assert_ne!(t0, t10, "the pad-0 and pad-10 traces are different objects");
}
