//! # THE DEPLOYED-PATH PROVABILITY LEDGER — every effect must PROVE on the sovereign wide path.
//!
//! "No forges" (soundness) is table stakes. The system is only USABLE if every effect can produce a
//! light-client-verifiable receipt — i.e. PROVE on the deployed sovereign path
//! (`prove_effect_vm_rotated_wide`). This ledger drives each effect through that exact path and
//! asserts it mints a proof that VERIFIES against the executor-anchored wide descriptor. An effect
//! that falls through to the wrong generator (`generate_rotated_transfer_shape_wide`) is UNSAT here —
//! the test REDS until the effect is routed to its real wide generator with real map_heaps.
//!
//! Mirrors `sovereign_rotated_wide.rs` (the transfer/refusal exemplars). Requires `prover`.

#![cfg(feature = "prover")]

use dregg_cell::commitment::{V9RotationContext, compute_rotated_pre_limbs};
use dregg_cell::{Cell, CellMode, Ledger};
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2, verify_vm_descriptor2};
use dregg_circuit::effect_vm::{CellState, Effect as VmEffect};
use dregg_circuit::effect_vm_descriptors::WIDE_REGISTRY_STAGED_TSV;
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::wire_commit_8_chip;
use dregg_sdk::full_turn_proof::prove_effect_vm_rotated_wide;
use dregg_turn::rotation_witness as rw;

/// The chip-faithful 8-felt commit of a cell + turn-context (the executor's anchoring primitive).
fn cell_chip_commit8(cell: &Cell, ctx: &V9RotationContext) -> [BabyBear; 8] {
    let pre = compute_rotated_pre_limbs(cell, ctx);
    wire_commit_8_chip(&pre, ctx.iroot)
}

/// Resolve a wide descriptor JSON by its registry key.
fn wide_desc(key: &str) -> dregg_circuit::descriptor_ir2::EffectVmDescriptor2 {
    let json = WIDE_REGISTRY_STAGED_TSV
        .lines()
        .find_map(|l| {
            let mut it = l.splitn(3, '\t');
            if it.next() == Some(key) {
                let _ = it.next();
                it.next()
            } else {
                None
            }
        })
        .unwrap_or_else(|| panic!("{key} not in WIDE_REGISTRY_STAGED_TSV"));
    parse_vm_descriptor2(json).unwrap_or_else(|e| panic!("{key} wide descriptor parses: {e}"))
}

/// **createCell — the issuing sovereign cell ticks its nonce; the accounts set grows.** The new cell's
/// commitment is `create_hash`. The issuing cell's balance is unchanged (createCell does not move
/// value); the deployed apply ticks the issuer nonce, so the AFTER 8-felt commit binds it.
fn sovereign_issuer_cells(balance: i64, domain: &[u8]) -> (Cell, Cell) {
    let token_id = *blake3::hash(domain).as_bytes();
    let mut before = Cell::with_balance([7u8; 32], token_id, balance);
    before.mode = CellMode::Sovereign;
    let mut after = before.clone();
    let _ = after.state.increment_nonce();
    (before, after)
}

/// **THE createCell PROVE-THROUGH (deployed wide path).** An honest createCell turn MUST prove on
/// `prove_effect_vm_rotated_wide` and VERIFY against the executor-anchored wide createCell descriptor.
/// BEFORE routing: createCell falls through to `generate_rotated_transfer_shape_wide` (a transfer
/// trace) → UNSAT vs `createCellVmDescriptor2R24`. AFTER routing it to `generate_rotated_create_cell_wide`
/// (the accounts-set grow-gate): it proves + verifies.
#[test]
fn create_cell_proves_on_deployed_wide_path() {
    let balance: i64 = 100_000;
    let (before_cell, after_cell) = sovereign_issuer_cells(balance, b"ledger-create-cell-domain");

    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = vec![];
    let mut ctx_ledger = Ledger::new();
    let _ = ctx_ledger.insert_cell(before_cell.clone());

    let before_w = rw::produce(
        &before_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
    );
    let after_w = rw::produce(
        &after_cell,
        &ctx_ledger,
        &nullifier_root,
        &commitments_root,
        &receipt_hashes,
    );

    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let effects = vec![VmEffect::CreateCell {
        create_hash: dregg_circuit::effect_vm::bytes32_to_8_limbs(
            blake3::hash(b"the-new-cell-commitment").as_bytes(),
        ),
    }];
    let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();

    // -- PRODUCER LEG: mint a wide createCell proof on the DEPLOYED path. --
    let (proof, producer_dpis) = prove_effect_vm_rotated_wide(
        &initial_vm_state,
        &effects,
        &before_w,
        &after_w,
        &caveat,
        None,
        None,
    )
    .expect(
        "DEPLOYED createCell PROVE-THROUGH: createCell MUST prove on the wide path (routed to \
         generate_rotated_create_cell_wide — the accounts-set grow-gate); the transfer-shape \
         fallthrough is UNSAT vs createCellVmDescriptor2R24",
    );

    let desc = wide_desc("createCellVmDescriptor2R24");
    assert_eq!(producer_dpis.len(), desc.public_input_count, "wide createCell PI count");

    // -- VERIFY LEG (the deployed light-client verifier): the minted proof VERIFIES against its
    //    published wide PIs. This is the prove-through: a light client running nothing but
    //    `verify_vm_descriptor2` ACCEPTS an honest createCell turn's receipt. The published commitment
    //    binds the GROWN accounts root (the empty BEFORE tree with `create_hash` inserted via the
    //    limb-0 `.write` map-op), so the createCell-specific grow-gate PI is satisfied — exactly what
    //    the transfer-shape fallthrough could NOT produce. (Anchoring to a trusted RECONSTRUCTED
    //    accounts tree is a deeper soundness check, separate from this liveness pole.) --
    verify_vm_descriptor2(&desc, &proof, &producer_dpis)
        .expect("the honest wide createCell proof VERIFIES against its published wide PIs");

    // Non-vacuity: the AFTER accounts-root limb genuinely advanced (the new cell was inserted) —
    // the grow is real, not a frozen passthrough. The before/after 8-felt commits differ.
    let wide_base = desc.public_input_count - 16;
    let before8 = &producer_dpis[wide_base..wide_base + 8];
    let after8 = &producer_dpis[wide_base + 8..wide_base + 16];
    assert_ne!(
        before8, after8,
        "the createCell grow-gate MOVES the committed state (BEFORE != AFTER 8-felt commit) — the \
         new cell's insertion is genuinely bound, not a frozen passthrough"
    );

    eprintln!(
        "DEPLOYED createCell PROVE-THROUGH GREEN: createCell proves + verifies on the wide path \
         (routed to the accounts-set grow-gate; the AFTER commit binds the grown accounts root)."
    );
}

/// Drive an honest single-effect sovereign turn through the DEPLOYED wide path and return its
/// `(proof, dpis)`. The issuer cell ticks its nonce (the deployed apply for a birth/field write); the
/// `before_w`/`after_w` are produced over a single-cell ledger snapshot, exactly as the createCell
/// prove-through above. This is the shared spine for the per-effect prove-throughs below.
fn prove_through_deployed(
    domain: &[u8],
    effects: &[VmEffect],
) -> (
    dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    Vec<BabyBear>,
) {
    let balance: i64 = 100_000;
    let (before_cell, after_cell) = sovereign_issuer_cells(balance, domain);
    let nullifier_root = [0u8; 32];
    let commitments_root = [0u8; 32];
    let receipt_hashes: Vec<[u8; 32]> = vec![];
    let mut ledger = Ledger::new();
    let _ = ledger.insert_cell(before_cell.clone());
    let before_w =
        rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &receipt_hashes);
    let after_w =
        rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &receipt_hashes);
    let initial_vm_state = CellState::with_capability_root_and_record_digest(
        balance as u64,
        before_cell.state.nonce() as u32,
        dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
        dregg_cell::compute_authority_digest_felt(&before_cell),
    );
    let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
    prove_effect_vm_rotated_wide(
        &initial_vm_state, effects, &before_w, &after_w, &caveat, None, None,
    )
    .unwrap_or_else(|e| {
        panic!("DEPLOYED PROVE-THROUGH ({domain:?}) must prove on the wide path: {e}")
    })
}

/// Assert the minted wide proof VERIFIES (the deployed light-client verifier) against its published
/// wide PIs, the PI count matches the descriptor, AND the AFTER 8-felt commit genuinely MOVED off the
/// BEFORE commit (non-vacuity: the effect's genuine write is bound, not a frozen passthrough).
fn assert_verifies_and_nonvacuous(
    key: &str,
    proof: &dregg_circuit::descriptor_ir2::Ir2BatchProof<dregg_circuit::descriptor_ir2::DreggStarkConfig>,
    dpis: &[BabyBear],
) {
    let desc = wide_desc(key);
    assert_eq!(dpis.len(), desc.public_input_count, "{key} wide PI count matches descriptor");
    verify_vm_descriptor2(&desc, proof, dpis)
        .unwrap_or_else(|e| panic!("the honest wide {key} proof VERIFIES against its published PIs: {e}"));
    let wide_base = desc.public_input_count - 16;
    let before8 = &dpis[wide_base..wide_base + 8];
    let after8 = &dpis[wide_base + 8..wide_base + 16];
    assert_ne!(
        before8, after8,
        "{key}: the AFTER 8-felt commit MOVED off the BEFORE commit — the effect's genuine write \
         (the grown accounts root / the dyn field) is bound, not a frozen passthrough"
    );
}

/// **THE createCellFromFactory PROVE-THROUGH (deployed wide path).** An honest factory-birth turn MUST
/// prove on `prove_effect_vm_rotated_wide` + VERIFY against `factoryVmDescriptor2R24`. BEFORE routing:
/// createCellFromFactory fell through to `generate_rotated_transfer_shape_wide` → UNSAT (PI-count
/// mismatch vs the factory grow-gate descriptor). AFTER routing it to
/// `generate_rotated_create_from_factory_wide` (the accounts-set grow-gate, child key on param1): it
/// proves + verifies, and the AFTER commit binds the grown accounts root (the born child inserted).
#[test]
fn create_cell_from_factory_proves_on_deployed_wide_path() {
    // The child VK (param1, the new-cell key) MUST be non-zero (an all-zero key collides with the
    // empty-tree sentinel and the `.absent` no-collision op refuses — a witness artifact, not a gap).
    let effects = vec![VmEffect::CreateCellFromFactory {
        factory_vk: BabyBear::new(0xFAC0),
        child_vk_derived: BabyBear::new(0xC417),
    }];
    let (proof, dpis) = prove_through_deployed(b"ledger-factory-domain", &effects);
    assert_verifies_and_nonvacuous("factoryVmDescriptor2R24", &proof, &dpis);
    eprintln!(
        "DEPLOYED createCellFromFactory PROVE-THROUGH GREEN: proves + verifies on the wide path \
         (routed to the factory accounts-set grow-gate; the AFTER commit binds the grown accounts root)."
    );
}

/// **THE spawn PROVE-THROUGH (deployed wide path).** An honest spawn-birth turn MUST prove on
/// `prove_effect_vm_rotated_wide` + VERIFY against `spawnVmDescriptor2R24` for the accounts-birth
/// column. BEFORE: spawn fell through to the transfer-shape producer → UNSAT vs the spawn grow-gate
/// descriptor. AFTER routing it to `generate_rotated_spawn_wide` (the accounts-set grow-gate, born
/// child key on param0): it proves + verifies; the AFTER commit binds the grown accounts root. (The
/// parent→child cap-handoff is the SEPARATE cap-open path's job — not the wide accounts-birth column.)
#[test]
fn spawn_proves_on_deployed_wide_path() {
    // The born child's key (param0 = spawn_hash[0]) MUST be non-zero (empty-tree sentinel collision).
    let spawn_id = BabyBear::new(0x5BA1);
    let effects = vec![VmEffect::SpawnWithDelegation { spawn_hash: [spawn_id; 8] }];
    let (proof, dpis) = prove_through_deployed(b"ledger-spawn-domain", &effects);
    assert_verifies_and_nonvacuous("spawnVmDescriptor2R24", &proof, &dpis);
    eprintln!(
        "DEPLOYED spawn PROVE-THROUGH GREEN: the accounts-birth leg proves + verifies on the wide path \
         (routed to the spawn accounts-set grow-gate; the AFTER commit binds the grown accounts root)."
    );
}

/// **THE setFieldDyn PROVE-THROUGH (deployed wide path).** An honest dynamic overflow-field write
/// (`SetField { field_idx >= 8 }`) MUST prove on `prove_effect_vm_rotated_wide` + VERIFY against
/// `setFieldDynVmDescriptor2R24` (the 581-wide V1Face / 789-wide member). BEFORE: setFieldDyn fell
/// through to the transfer-shape producer → UNSAT vs the distinct dyn geometry. AFTER routing it to
/// `generate_rotated_set_field_dyn_wide` (the Blum linear-memory write→read transport, witnessed by a
/// `MemBoundaryWitness` threaded to `prove_vm_descriptor2` — NOT a `map_heaps`): it proves + verifies,
/// and the AFTER commit binds the dyn-field write (the AFTER fields_root limb forced to the slot).
#[test]
fn set_field_dyn_proves_on_deployed_wide_path() {
    // field_idx 11 (>= 8) is the OVERFLOW write → setFieldDynVmDescriptor2R24; the in-circuit slot is
    // 11 % 8 = 3 (the 8-cell Blum overflow memory address).
    let effects = vec![VmEffect::SetField { field_idx: 11, value: BabyBear::new(0x5E7F) }];
    let (proof, dpis) = prove_through_deployed(b"ledger-setfielddyn-domain", &effects);
    assert_verifies_and_nonvacuous("setFieldDynVmDescriptor2R24", &proof, &dpis);
    eprintln!(
        "DEPLOYED setFieldDyn PROVE-THROUGH GREEN: the dynamic overflow-field write proves + verifies \
         on the wide path (routed to the Blum linear-memory transport; the AFTER commit binds the dyn \
         field — the MemBoundaryWitness, not map_heaps, is the gate's witness)."
    );
}

/// **THE PROVABILITY SCOREBOARD (diagnostic).** Drive each effect through the DEPLOYED wide path and
/// report SAT/UNSAT. An effect that cannot prove cannot produce a light-client receipt — i.e. is not
/// USABLE. This is the ground-truth completeness worklist (run with `--nocapture`). The control
/// effects (Transfer, CreateCell) MUST prove; the rest are reported so the routing burndown is
/// visible. As each effect is routed to its real wide generator, its line flips to PROVABLE.
#[test]
fn provability_scoreboard_deployed_wide_path() {
    let probe = |label: &str, effects: Vec<VmEffect>| -> Result<(), String> {
        let (before_cell, after_cell) = sovereign_issuer_cells(100_000, label.as_bytes());
        let nullifier_root = [0u8; 32];
        let commitments_root = [0u8; 32];
        let mut ledger = Ledger::new();
        let _ = ledger.insert_cell(before_cell.clone());
        let before_w = rw::produce(&before_cell, &ledger, &nullifier_root, &commitments_root, &[]);
        let after_w = rw::produce(&after_cell, &ledger, &nullifier_root, &commitments_root, &[]);
        let initial = CellState::with_capability_root_and_record_digest(
            100_000u64,
            before_cell.state.nonce() as u32,
            dregg_cell::compute_canonical_capability_root_felt(&before_cell.capabilities),
            dregg_cell::compute_authority_digest_felt(&before_cell),
        );
        let caveat = dregg_circuit::effect_vm::trace_rotated::empty_caveat_manifest();
        match prove_effect_vm_rotated_wide(
            &initial, &effects, &before_w, &after_w, &caveat, None, None,
        ) {
            Ok(_) => {
                eprintln!("  [PROVABLE]   {label}");
                Ok(())
            }
            Err(e) => {
                eprintln!("  [UNPROVABLE] {label}: {e}");
                Err(format!("{label}: {e}"))
            }
        }
    };

    eprintln!("=== DEPLOYED-PATH PROVABILITY SCOREBOARD (prove_effect_vm_rotated_wide) ===");
    let z8 = [BabyBear::new(0); 8];
    // A real (non-sentinel) new-cell commitment — an all-zero key collides with the empty-tree
    // sentinel and the `.absent` no-collision op refuses (a witness artifact, not a routing gap).
    let create_hash =
        dregg_circuit::effect_vm::bytes32_to_8_limbs(blake3::hash(b"scoreboard-new-cell").as_bytes());
    let cases: Vec<(&str, Vec<VmEffect>)> = vec![
        ("transfer", vec![VmEffect::Transfer { amount: 100, direction: 1 }]),
        ("createCell", vec![VmEffect::CreateCell { create_hash }]),
        ("incrementNonce", vec![VmEffect::IncrementNonce]),
        ("makeSovereign", vec![VmEffect::MakeSovereign]),
        // The born child's key (param0 = spawn_hash[0]) must be non-zero — an all-zero key collides
        // with the empty-tree sentinel and the `.absent` op refuses (witness artifact, not a gap).
        (
            "spawnWithDelegation",
            vec![VmEffect::SpawnWithDelegation { spawn_hash: [BabyBear::new(0x5BA1); 8] }],
        ),
        ("exerciseViaCapability", vec![VmEffect::ExerciseViaCapability { exercise_hash: z8 }]),
        ("pipelinedSend", vec![VmEffect::PipelinedSend { send_hash: z8 }]),
        (
            "createCellFromFactory",
            vec![VmEffect::CreateCellFromFactory {
                factory_vk: BabyBear::new(7),
                child_vk_derived: BabyBear::new(11),
            }],
        ),
        (
            "setFieldDyn",
            vec![VmEffect::SetField { field_idx: 11, value: BabyBear::new(0x5E7F) }],
        ),
    ];
    let mut provable = Vec::new();
    let mut unprovable = Vec::new();
    for (label, effects) in cases {
        match probe(label, effects) {
            Ok(()) => provable.push(label),
            Err(_) => unprovable.push(label),
        }
    }
    eprintln!("PROVABLE  ({}): {provable:?}", provable.len());
    eprintln!("UNPROVABLE({}): {unprovable:?}", unprovable.len());

    // The routed effects MUST be provable (regression guard); the rest are the burndown worklist.
    assert!(provable.contains(&"transfer"), "transfer must prove on the deployed wide path");
    assert!(provable.contains(&"createCell"), "createCell must prove (routed a prior session)");
    assert!(
        provable.contains(&"createCellFromFactory"),
        "createCellFromFactory must prove (routed to the factory accounts-set grow-gate this session)"
    );
    assert!(
        provable.contains(&"spawnWithDelegation"),
        "spawn (accounts-birth leg) must prove (routed to the spawn accounts-set grow-gate this session)"
    );
    assert!(
        provable.contains(&"setFieldDyn"),
        "setFieldDyn must prove (routed to the Blum linear-memory transport this session)"
    );
}
