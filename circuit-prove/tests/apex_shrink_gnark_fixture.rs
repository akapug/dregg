//! THE WRAP FIXTURE EXPORT: serialize a REAL shrink proof's FRI layer +
//! transcript prefix into the gnark fixture
//! `chain/gnark/fixtures/apex_shrink_fri_real.json`.
//!
//! Same real objects as `apex_shrink_bn254_tooth.rs` (a 2-turn rotated
//! chain → `ir2_leaf_wrap` apex → BN254-native shrink proof) — except the
//! turn BODY is `IncrementNonce`, not the tooth's `Transfer` (see
//! [`make_turn`] for why), plus:
//!
//! 1. the shrink proof is CACHED (postcard, under `target/`) so re-exports
//!    skip the ~20-minute fold+shrink when a verified cache exists;
//! 2. `export_real_shrink_fri_fixture` mirrors the batch verifier's pre-FRI
//!    transcript and re-runs the FRI core host-side with real p3 components —
//!    the export FAILS unless the real `pcs.verify` accepts from the mirrored
//!    transcript state AND every fold chain reaches the final polynomial
//!    (see the module doc of `apex_shrink_gnark_export` for the argument);
//! 3. the fixture JSON is written for the gnark tests
//!    (`chain/gnark/apex_shrink_real_fixture_test.go`) to load.
//!
//! Run:
//!   cargo test -p dregg-circuit-prove --release --test apex_shrink_gnark_fixture -- --ignored --nocapture

use std::path::PathBuf;
use std::time::Instant;

use dregg_circuit::effect_vm::{CellState, Effect};
use dregg_circuit_prove::apex_shrink::{shrink_apex_to_outer, verify_shrink_proof};
use dregg_circuit_prove::apex_shrink_gnark_export::export_real_shrink_fri_fixture;
use dregg_circuit_prove::dregg_outer_config::{DreggOuterConfig, create_outer_config};
use dregg_circuit_prove::ivc_turn_chain::{
    FinalizedTurn, ir2_leaf_wrap_config, prove_turn_chain_recursive,
};
use dregg_circuit_prove::joint_turn_aggregation::DescriptorParticipant;
use dregg_circuit_prove::plonky3_recursion_impl::recursive::verify_recursive_batch_proof_with_config;
use dregg_turn::rotation_witness::mint_rotated_participant_leg;
use p3_circuit_prover::BatchStarkProof;

/// OPEN permissions (the audited Bucket-F mint fixture, as in the tooth).
fn open_permissions() -> dregg_cell::Permissions {
    use dregg_cell::AuthRequired;
    dregg_cell::Permissions {
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

fn producer_cell(balance: i64, nonce: u64) -> dregg_cell::Cell {
    let mut pk = [0u8; 32];
    pk[0] = 7;
    let mut cell = dregg_cell::Cell::with_balance(pk, [0u8; 32], balance);
    cell.permissions = open_permissions();
    for _ in 0..nonce {
        let _ = cell.state.increment_nonce();
    }
    cell
}

/// One `IncrementNonce` turn (the `apex_shrink_blowup_sweep.rs` fixture).
///
/// HONEST LABEL: the tooth's fixture uses `Effect::Transfer`, but the working
/// tree currently carries a mid-flight sibling flag-day (GAP #4 wide-registry
/// cutover — the v3-staged registry's transfer display name is
/// `dregg-effectvm-transfer-v1-avail-…` while the wide registry the mint reads
/// still says `dregg-effectvm-transfer-v1-…`), so a transfer leg fails host
/// admission (`not a known R=24 cohort member`). `IncrementNonce`'s rows AGREE
/// across both registries, and the export doesn't care WHICH effect the apex
/// folds — only that the apex is real. The transfer-bodied version of this
/// fixture runs unchanged once the sibling regenerates the wide registry.
fn make_turn(balance: u64, nonce: u32) -> FinalizedTurn {
    let state = CellState::new(balance, nonce);
    let effects = vec![Effect::IncrementNonce];
    let before_cell = producer_cell(balance as i64, nonce as u64);
    let after_cell = producer_cell(balance as i64, nonce as u64);
    let receipt_log: Vec<[u8; 32]> = vec![[1u8; 32], [2u8; 32]];
    let leg = mint_rotated_participant_leg(
        &state,
        &effects,
        &before_cell,
        &after_cell,
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &dregg_circuit::heap_root::empty_heap_root_8(),
        &receipt_log,
        None,
    )
    .expect("rotated leg mints");
    FinalizedTurn::new(DescriptorParticipant::rotated(leg))
}

/// The fixed 2-turn chain (`recursion_vk_determinism.rs`'s fixture shape,
/// `IncrementNonce`-bodied — see [`make_turn`]; the same chain
/// `apex_shrink_blowup_sweep.rs` folds).
fn the_chain() -> Vec<FinalizedTurn> {
    vec![make_turn(1000, 0), make_turn(1000, 1)]
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("circuit-prove has a parent")
        .to_path_buf()
}

fn cache_path() -> PathBuf {
    repo_root().join("target/apex_shrink_proof_cache.postcard")
}

fn fixture_path() -> PathBuf {
    repo_root().join("chain/gnark/fixtures/apex_shrink_fri_real.json")
}

/// Load a cached shrink proof if present AND it still verifies; otherwise
/// regenerate from the real 2-turn chain and cache it.
fn real_shrink_proof(outer_config: &DreggOuterConfig) -> BatchStarkProof<DreggOuterConfig> {
    let cache = cache_path();
    if let Ok(bytes) = std::fs::read(&cache) {
        if let Ok(proof) = postcard::from_bytes::<BatchStarkProof<DreggOuterConfig>>(&bytes) {
            if verify_shrink_proof(&proof, outer_config).is_ok() {
                println!("using cached shrink proof: {}", cache.display());
                return proof;
            }
            println!("cached shrink proof no longer verifies — regenerating");
        } else {
            println!("cached shrink proof no longer deserializes — regenerating");
        }
    }

    // ---- the REAL apex (same flow as apex_shrink_bn254_tooth.rs) ----------
    let t0 = Instant::now();
    let whole = prove_turn_chain_recursive(&the_chain()).expect("the fixed 2-turn chain folds");
    println!("apex fold time     : {:?}", t0.elapsed());

    let inner_config = ir2_leaf_wrap_config();
    verify_recursive_batch_proof_with_config(&whole.root.0, &inner_config)
        .expect("the real apex verifies under ir2_leaf_wrap_config");

    let t1 = Instant::now();
    let shrink = shrink_apex_to_outer(&whole.root, &inner_config, outer_config)
        .expect("the real apex shrinks under DreggOuterConfig");
    println!("shrink prove time  : {:?}", t1.elapsed());

    verify_shrink_proof(&shrink.proof, outer_config)
        .expect("the BN254-native shrink proof verifies");

    let bytes = postcard::to_allocvec(&shrink.proof).expect("shrink proof postcard-serializes");
    if let Some(dir) = cache.parent() {
        let _ = std::fs::create_dir_all(dir);
    }
    std::fs::write(&cache, &bytes).expect("write shrink proof cache");
    println!(
        "cached shrink proof ({} bytes): {}",
        bytes.len(),
        cache.display()
    );
    shrink.proof
}

#[test]
#[ignore = "SLOW unless the shrink-proof cache exists (one real 2-turn fold + BN254-native shrink \
            prove, ~20 min); run with --ignored — emits chain/gnark/fixtures/apex_shrink_fri_real.json"]
fn export_real_shrink_fri_fixture_for_gnark() {
    let outer_config = create_outer_config();
    let proof = real_shrink_proof(&outer_config);

    // The export self-checks: real pcs.verify from the mirrored transcript
    // state + full host-side FRI-core re-verification (fold chains, Merkle
    // openings, PoW, final poly) over exactly the data being exported.
    let t = Instant::now();
    let fixture = export_real_shrink_fri_fixture(&proof, &outer_config)
        .expect("fixture export (with host-side self-checks) succeeds");
    println!("export+selfcheck   : {:?}", t.elapsed());

    let json = serde_json::to_string(&fixture).expect("fixture serializes");
    let path = fixture_path();
    std::fs::write(&path, &json).expect("write gnark fixture");

    println!("=== REAL SHRINK FRI FIXTURE ===");
    println!("path               : {}", path.display());
    println!("bytes              : {}", json.len());
    println!("degree_bits        : {:?}", fixture.degree_bits);
    println!(
        "rounds/queries     : {} / {}",
        fixture.fri.rounds,
        fixture.queries.len()
    );
    println!("log_max_height     : {}", fixture.fri.log_global_max_height);
    println!("roll_in_rounds     : {:?}", fixture.roll_in_rounds);
    println!("prefix events      : {}", fixture.prefix_events.len());

    // Shape sanity the gnark loader will re-assert.
    assert_eq!(fixture.fri.rounds, fixture.commit_roots.len());
    assert_eq!(fixture.queries.len(), fixture.fri.num_queries);
    for q in &fixture.queries {
        assert_eq!(q.siblings.len(), fixture.fri.rounds);
        assert_eq!(q.roll_ins.len(), fixture.roll_in_rounds.len());
        for (r, path) in q.merkle_paths.iter().enumerate() {
            assert_eq!(path.len(), fixture.fri.log_global_max_height - r - 1);
        }
    }
}
