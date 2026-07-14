//! # Shielded-deposit bridge PoC — the tractable first brick of
//! `docs/deos/SHIELDED-DEPOSIT-BRIDGE.md`.
//!
//! This exercises the REAL shielded-pool primitives for the middle of the
//! deposit→shield→private-clear→settle pipeline, end to end, in one run:
//!
//!   (a) DEPOSIT   — a LOCAL STAND-IN for an LC-attested lock. We do NOT run the
//!                   eth-lightclient here; a `(asset, value)` pair stands in for a
//!                   `ProvenErc20Holding{trust=ConsensusProven}` locked in the
//!                   bridge escrow. THIS SIDE IS LABELLED A STAND-IN (the real
//!                   attestation is `eth-lightclient::verify_holding`, cited in the
//!                   doc; the note-mint below is what consumes it).
//!   (b) MINT      — REAL Poseidon2 note-mint: the PQ value-binding
//!                   `value_binding = hash_fact(value, [asset, randomness, 0])`
//!                   (the spend circuit's C7 / `RealCrypto §1.3`, binding
//!                   `(value, asset)` under Poseidon2 collision-resistance), the
//!                   note leaf commitment `hash_fact(value,[asset,owner,rand])`,
//!                   and the nullifier `hash_fact(leaf, key)`. No-double-mint and
//!                   no-hidden-inflation (range) gates enforced against a live set.
//!   (c) PRIVATE   — a REAL reveal-nothing hiding-STARK: the note proves it is
//!       CLEAR      solvent (`attr >= 1`) over its hidden committed value through
//!                   the production `HidingFriPcs` path (`prove_dsl_zk`), the SAME
//!                   zero-knowledge machinery the shielded clearing runs the
//!                   membership/nullifier leg through. The verifier learns only the
//!                   commitment + the predicate truth — never the value.
//!   (d) SETTLE     — the nullifier is consumed; a replay of the same nullifier is
//!                   refused (the double-spend gate that lets the cleared result
//!                   settle exactly once).
//!
//! Both polarities are exercised at every soundness-relevant seam (a valid deposit
//! mints + attests + settles; a double-mint, an out-of-range/inflating deposit, a
//! zero-value note that cannot attest solvency, and a double-spend are each
//! REFUSED).
//!
//! The NUMERIC private clearing + the Cert-F optimality certificate (stage (c)/(d)
//! settle-cert) run in the REAL fhEgg engine (`fhegg-solver`, the `fhegg-e2e`
//! binary: clear → allocate → PDHG solve → CertF → check, both polarities). That
//! crate is deliberately isolated (no protocol deps), so it is cited from its own
//! real run in the doc rather than linked here. The SEAM this PoC does not cross —
//! turning minted pool notes into the sealed orders the engine folds — is the
//! exact MISSING wire named in the doc.

use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_zk, verify_dsl_zk};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit_prove::shielded::{
    AttestWitness, Predicate, attest_circuit, generate_attest_trace,
};

/// The honest no-inflation window (matches `shielded::attest::RANGE_BITS`): a
/// note value must lie in `[0, 2^30)`, strictly below BabyBear's negative reps, so
/// a "wrapped negative" (hidden inflation) has no valid decomposition.
const RANGE_BITS: u32 = 30;

/// A deposited, minted shielded note over REAL Poseidon2 commitments.
#[derive(Clone, Debug)]
struct MintedNote {
    /// The note's leaf commitment `hash_fact(value, [asset, owner, randomness])`.
    leaf: BabyBear,
    /// The PQ value-binding `hash_fact(value, [asset, randomness, 0])` — binds
    /// `(value, asset)` under Poseidon2 CR (`RealCrypto §1.3`, spend circuit C7).
    value_binding: BabyBear,
    /// The spend nullifier `hash_fact(leaf, key[0..4])`.
    nullifier: BabyBear,
    /// The hidden value (lives only in the witness; never published).
    value: u64,
    /// The asset class (issuer cell id, dregg3 `AssetId`).
    asset: u64,
}

/// The shielded pool's live sets (the executor's `commitments` + `nullifiers`).
#[derive(Default)]
struct Pool {
    commitments: Vec<BabyBear>,
    nullifiers: Vec<BabyBear>,
}

fn felt(v: u64) -> BabyBear {
    BabyBear::new((v % (dregg_circuit::field::BABYBEAR_P as u64)) as u32)
}

/// Compute the REAL note commitments for a deposit `(asset, value)` blinded by
/// `(owner, randomness)` and keyed by `key` — the exact Poseidon2 facts the
/// shielded spend circuit binds in-witness.
fn compute_note(asset: u64, value: u64, owner: u64, randomness: u64, key: u64) -> MintedNote {
    let v = felt(value);
    let a = felt(asset);
    let o = felt(owner);
    let r = felt(randomness);
    // Leaf commitment (C6): hash_fact(value, [asset, owner, randomness]).
    let leaf = hash_fact(v, &[a, o, r]);
    // PQ value-binding (C7 / RealCrypto §1.3): hash_fact(value, [asset, rand, 0]).
    let value_binding = hash_fact(v, &[a, r, BabyBear::ZERO]);
    // Nullifier: hash_fact(leaf_commitment, key[0..4]).
    let nullifier = hash_fact(
        leaf,
        &[felt(key), BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    );
    MintedNote {
        leaf,
        value_binding,
        nullifier,
        value,
        asset,
    }
}

/// STAGE (b) MINT — insert the note IFF it is fresh (no-double-mint) and its value
/// is range-valid (no hidden inflation at creation). Fail-closed, mirroring the
/// Lean `shieldK` freshness gate + `noteCreateBound_in_range`.
fn try_mint(pool: &mut Pool, note: &MintedNote) -> Result<(), &'static str> {
    if note.value >= (1u64 << RANGE_BITS) {
        return Err("hidden inflation: value outside [0, 2^30) has no range witness");
    }
    if pool.commitments.contains(&note.leaf) {
        return Err("double-mint: this note commitment is already in the pool");
    }
    if pool.nullifiers.contains(&note.nullifier) {
        return Err("double-mint: this note's nullifier is already consumed");
    }
    pool.commitments.push(note.leaf);
    Ok(())
}

/// STAGE (d) SETTLE — consume the nullifier IFF unconsumed (fail-closed on
/// double-spend), the gate that lets the cleared result settle exactly once.
fn try_settle(pool: &mut Pool, note: &MintedNote) -> Result<(), &'static str> {
    if pool.nullifiers.contains(&note.nullifier) {
        return Err("double-spend: nullifier already consumed");
    }
    pool.nullifiers.push(note.nullifier);
    Ok(())
}

/// STAGE (c) PRIVATE CLEAR — the note proves it is solvent (`value >= 1`) through
/// the REAL production hiding STARK, over a Poseidon2 commitment to its hidden
/// value, disclosing nothing but the commitment. Returns Ok iff an accepting proof
/// is produced AND verifies. `proving_rejects` is the negative-polarity oracle
/// (no verifying proof for an insolvent note).
fn note_attests_solvent(value: u64, salt: u64) -> bool {
    let pred = Predicate::Positive; // attr >= 1
    let circuit = attest_circuit(&pred);
    let w = AttestWitness {
        attr: felt(value),
        salt: felt(salt),
    };
    let (trace, pis) = generate_attest_trace(&w, &pred);
    match prove_dsl_zk(&circuit, &trace, &pis) {
        Ok(proof) => verify_dsl_zk(&circuit, &proof, &pis).is_ok(),
        Err(_) => false,
    }
}

/// Treat "prover errors" and "debug constraint panic" alike as rejection — the
/// soundness property is "no verifying proof is produced" (mirrors attest.rs).
fn proving_rejects_solvency(value: u64, salt: u64) -> bool {
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        note_attests_solvent(value, salt)
    }));
    match r {
        Err(_) => true,    // panic in the debug constraint checker
        Ok(false) => true, // prover/verifier refused
        Ok(true) => false, // an accepting proof was produced (NOT rejected)
    }
}

#[test]
fn shielded_deposit_bridge_end_to_end() {
    println!(
        "\n=== SHIELDED-DEPOSIT BRIDGE PoC — real Poseidon2 note-mint + reveal-nothing STARK ===\n"
    );

    let mut pool = Pool::default();

    // ---------------------------------------------------------------------
    // (a) DEPOSIT — LOCAL STAND-IN for an LC-attested lock (LABELLED).
    //     In production: eth-lightclient::verify_holding proves a real WETH
    //     holding = ConsensusProven; the bridge escrow locks it. Here a fixed
    //     (asset, value) stands in for that attested lock.
    // ---------------------------------------------------------------------
    let asset: u64 = 1; // a stand-in asset class (issuer cell id)
    let deposit_value: u64 = 1_000; // stand-in attested locked amount
    println!("(a) DEPOSIT  [STAND-IN]: attested lock of {deposit_value} units of asset {asset}");
    println!(
        "             (production: eth-lightclient verify_holding → ConsensusProven → escrow lock)\n"
    );

    // ---------------------------------------------------------------------
    // (b) MINT — REAL Poseidon2 shielded note.
    // ---------------------------------------------------------------------
    let note = compute_note(asset, deposit_value, 0xA11CE, 0x5EED, 0x7);
    println!(
        "(b) MINT: REAL Poseidon2 note over the attested deposit (asset {})",
        note.asset
    );
    println!("      leaf commitment  = {:?}", note.leaf);
    println!(
        "      value_binding    = {:?}  (binds (value,asset) under HashCR)",
        note.value_binding
    );
    println!("      nullifier        = {:?}", note.nullifier);

    try_mint(&mut pool, &note).expect("a fresh, range-valid deposit must mint");
    assert!(
        pool.commitments.contains(&note.leaf),
        "the note commitment must be in the pool"
    );
    println!("      MINTED (commitment inserted into the pool set)\n");

    // NEGATIVE: DOUBLE-MINT — a second note for the SAME deposit (same commitment)
    // is refused (no minting two notes from one locked deposit).
    let dup = note.clone();
    assert!(
        try_mint(&mut pool, &dup).is_err(),
        "double-mint of the same commitment must be REFUSED"
    );
    println!("      [neg] double-mint (same commitment) REFUSED");

    // NEGATIVE: HIDDEN INFLATION — a deposit whose value is outside [0,2^30) has no
    // range witness; the mint is refused (no wrapped-negative inflation).
    let inflating = compute_note(asset, (1u64 << RANGE_BITS) + 5, 0xBAD, 0xBAD, 0x9);
    assert!(
        try_mint(&mut pool, &inflating).is_err(),
        "an out-of-range (inflating) deposit must be REFUSED at mint"
    );
    println!("      [neg] hidden-inflation (value >= 2^30) REFUSED");

    // The value-binding is BINDING: re-opening the commitment to a DIFFERENT value
    // yields a different Poseidon2 hash — a hidden mint forces a HashCR collision.
    let other = compute_note(asset, deposit_value + 1, 0xA11CE, 0x5EED, 0x7);
    assert_ne!(
        note.value_binding, other.value_binding,
        "distinct values MUST give distinct value-bindings (binding under HashCR)"
    );
    println!("      [neg] value_binding re-open to value+1 gives a DIFFERENT hash (binding)\n");

    // ---------------------------------------------------------------------
    // (c) PRIVATE CLEAR — the note enters the clear by a REAL reveal-nothing STARK:
    //     it proves it is solvent (value >= 1) disclosing nothing but the commitment.
    // ---------------------------------------------------------------------
    println!("(c) PRIVATE CLEAR: reveal-nothing hiding STARK (attr >= 1 over the hidden value)");
    assert!(
        note_attests_solvent(note.value, 0x5EED),
        "a solvent note (value {}) must produce a verifying reveal-nothing proof",
        note.value
    );
    println!(
        "      solvency proof over value={} VERIFIES (value stays hidden)",
        note.value
    );

    // NEGATIVE: a zero-value note cannot attest solvency — it cannot enter the clear.
    assert!(
        proving_rejects_solvency(0, 0xDEAD),
        "a zero-value note must NOT be able to forge a solvency proof"
    );
    println!("      [neg] zero-value note CANNOT attest solvency (no verifying proof)\n");

    // ---------------------------------------------------------------------
    // (d) SETTLE — the cleared note settles exactly once (nullifier consumed).
    // ---------------------------------------------------------------------
    println!("(d) SETTLE: consume the nullifier (the cleared result settles once)");
    try_settle(&mut pool, &note).expect("the first settle must consume the nullifier");
    println!("      SETTLED (nullifier consumed: {:?})", note.nullifier);

    // NEGATIVE: DOUBLE-SPEND — replaying the same nullifier is refused.
    assert!(
        try_settle(&mut pool, &note).is_err(),
        "a double-spend (replayed nullifier) must be REFUSED"
    );
    println!("      [neg] double-spend (replayed nullifier) REFUSED\n");

    println!(
        "=== PoC COMPLETE — deposit(stand-in) → REAL mint → REAL reveal-nothing clear → settle ==="
    );
    println!(
        "    real primitives exercised: Poseidon2 hash_fact value-binding/commitment/nullifier,"
    );
    println!(
        "    the production HidingFriPcs reveal-nothing STARK, no-double-mint / no-inflation /"
    );
    println!(
        "    no-double-spend gates. Numeric clear + Cert-F: fhegg-solver `fhegg-e2e` (cited in doc)."
    );
}
