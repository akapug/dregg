//! verifier-stark — the firmament's verified-compute heart organ.
//!
//! Where the M1 verifier PD (`../verifier/`) runs a no_std *structural* check,
//! this PD runs a **real cryptographic STARK** inside seL4: Reed-Solomon trace
//! encoding, BLAKE3 Merkle commitments, FRI low-degree testing, Fiat-Shamir
//! non-interactivity — the verbatim `dregg-circuit` custom STARK, carried to
//! no_std (`stark_core/`). It proves a small AIR, verifies the proof, then
//! tampers the trace and shows verification REJECTS it — the anti-ghost tooth
//! at the cryptographic (not structural) level, executing on the microkernel.
//!
//! `prove()` is fully deterministic (Fiat-Shamir; no RNG, no clock), so the PD
//! needs no `getrandom`/entropy source — it both proves and verifies a real
//! STARK on-device. This is a concrete firmament organ: a booting seL4 PD that
//! does genuine proof-checking, no Lean required (docs/FIRMAMENT.md §6).
//!
//! Capability partition (the firmament's verifier trust boundary): this PD is
//! pure compute over bytes. It holds NO prover authority over dregg state, NO
//! storage cap, NO NIC cap — the seL4-enforced form of "a verifier runs with
//! no callback into a prover" (verifier/src/lib.rs).

#![no_std]
#![no_main]

extern crate alloc;

mod stark_core;

use alloc::vec;
use alloc::vec::Vec;

use stark_core::field::BabyBear;
use stark_core::stark::{
    prove, proof_from_bytes, proof_to_bytes, verify, BoundaryConstraint, StarkAir,
};

use sel4_microkit::{debug_println, protection_domain, Handler, Infallible};

/// A minimal but real AIR: a 2-column trace with the transition constraint
/// `col0' = col0 + 1` and the algebraic boundary `col1 = col0^2`. Small enough
/// to prove on-device in a heartbeat, real enough that the FRI + Merkle +
/// Fiat-Shamir machinery all run.
struct CounterSquareAir;

impl StarkAir for CounterSquareAir {
    fn width(&self) -> usize {
        2
    }
    fn constraint_degree(&self) -> usize {
        2
    }
    fn air_name(&self) -> &'static str {
        "dregg-firmament-counter-square-v1"
    }
    fn has_chain_continuity(&self) -> bool {
        false
    }
    fn eval_constraints(
        &self,
        local: &[BabyBear],
        next: &[BabyBear],
        _public_inputs: &[BabyBear],
        alpha: BabyBear,
    ) -> BabyBear {
        // transition: next col0 = local col0 + 1
        let c1 = next[0] - local[0] - BabyBear::ONE;
        // algebraic: col1 = col0^2 (a real degree-2 constraint, not linear)
        let c2 = local[1] - local[0] * local[0];
        c1 + alpha * c2
    }

    fn boundary_constraints(
        &self,
        public_inputs: &[BabyBear],
        _trace_len: usize,
    ) -> Vec<BoundaryConstraint> {
        // Bind row 0 col 0 to the public input: the trace cannot be re-aimed at
        // a different starting value without breaking the proof.
        if public_inputs.is_empty() {
            return vec![];
        }
        vec![BoundaryConstraint {
            row: 0,
            col: 0,
            value: public_inputs[0],
        }]
    }
}

/// Build the valid 4-row trace for `col0 = 0,1,2,3` and `col1 = col0^2`.
fn good_trace() -> Vec<Vec<BabyBear>> {
    (0u32..4)
        .map(|i| vec![BabyBear::new(i), BabyBear::new(i * i)])
        .collect()
}

#[protection_domain(heap_size = 0x100000)]
fn init() -> HandlerImpl {
    debug_println!("[stark] dregg verifier-stark PD booted — REAL STARK (BabyBear+BLAKE3+FRI) on seL4");

    let air = CounterSquareAir;
    let pi = vec![BabyBear::new(0)]; // public input: row0 col0 == 0
    let trace = good_trace();

    // 1. Prove a valid trace — real Reed-Solomon + Merkle + FRI + Fiat-Shamir.
    let proof = prove(&air, &trace, &pi);
    let bytes = proof_to_bytes(&proof);
    debug_println!("[stark] proved 4-row AIR  -> proof {} bytes", bytes.len());

    // 2. Verify the proof — the genuine cryptographic check.
    match verify(&air, &proof, &pi) {
        Ok(()) => debug_println!("[stark] verify(good proof) -> ACCEPT  (STARK verified ✓)"),
        Err(e) => debug_println!("[stark] verify(good proof) -> REJECT  UNEXPECTED: {}", e),
    }

    // 3. Serialization roundtrip — the wire form a peer would ship in.
    match proof_from_bytes(&bytes) {
        Ok(p2) => match verify(&air, &p2, &pi) {
            Ok(()) => debug_println!("[stark] verify(roundtripped proof) -> ACCEPT  (wire form OK ✓)"),
            Err(e) => debug_println!("[stark] verify(roundtripped proof) -> REJECT  UNEXPECTED: {}", e),
        },
        Err(e) => debug_println!("[stark] proof_from_bytes -> Err UNEXPECTED: {}", e),
    }

    // 4. Anti-ghost: TAMPER the serialized proof (flip a byte in the FRI/commit
    //    payload) and show verification REJECTS it. (A constraint-violating
    //    TRACE is caught at prove time — the prover refuses to forge a proof —
    //    so the verify-side tooth is exercised by tampering the proof bytes a
    //    cheater would actually ship.)
    let mut tampered = bytes.clone();
    let mid = tampered.len() / 2;
    tampered[mid] ^= 0xff; // corrupt one byte deep in the proof
    match proof_from_bytes(&tampered) {
        Ok(tp) => match verify(&air, &tp, &pi) {
            Err(e) => debug_println!("[stark] verify(tampered proof) -> REJECT  (anti-ghost ✓): {}", e),
            Ok(()) => debug_println!("[stark] verify(tampered proof) -> ACCEPT  UNSOUND!! the tooth failed"),
        },
        Err(e) => debug_println!("[stark] tampered proof rejected at decode -> (anti-ghost ✓): {}", e),
    }

    // 5. Anti-ghost #2: verify the HONEST proof against a DIFFERENT public input
    //    (claim row0 col0 == 1, but the trace starts at 0). The boundary
    //    constraint binds the trace to the PI, so verification must reject.
    let wrong_pi = vec![BabyBear::new(1)];
    match verify(&air, &proof, &wrong_pi) {
        Err(e) => debug_println!("[stark] verify(good proof, wrong PI) -> REJECT  (boundary tooth ✓): {}", e),
        Ok(()) => debug_println!("[stark] verify(good proof, wrong PI) -> ACCEPT  UNSOUND!! boundary failed"),
    }

    debug_println!("[stark] real STARK proof-checking is LIVE on the microkernel — the firmament has a verified heart organ");
    HandlerImpl
}

struct HandlerImpl;

impl Handler for HandlerImpl {
    type Error = Infallible;
}
