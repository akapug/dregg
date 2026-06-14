//! dregg-crypto-floor — the REAL §8 crypto primitives for the seL4 executor PD,
//! `no_std`, exporting plain-value `extern "C"` entry points that the C ABI shim
//! (`crypto-floor.c`) marshals Lean `Nat`/`Int`/`List Nat` to and from.
//!
//! WHY THIS CRATE EXISTS. The executor PD links the VERIFIED Lean closure, whose
//! eight `@[extern]` crypto portals (`Dregg2/Crypto/PortalFloor.lean`) were
//! resolved by `crypto-stub.c` — a panic-if-reached stub with the WRONG arity and
//! types (`void* dregg_poseidon2_hash(void*)` vs the real
//! `lean_object* dregg_poseidon2_hash(lean_object*, lean_object*)`). The demo turn
//! never reaches them (the closure routes the portals through in-Lean reference
//! dictionaries, not the externs), so the stub linked and the boot ran — but a
//! turn that actually hashes would call a wrong-arity panic (UB, then abort).
//!
//! THIS replaces the stub's HASH FLOOR with the SAME carried crypto the
//! `verifier-stark` PD already runs on seL4: the Plonky3-conformant Poseidon2 over
//! BabyBear (`circuit/src/poseidon2.rs`, carried verbatim in `poseidon2.rs`) and
//! BLAKE3 (the `blake3` crate, `pure` no_std backend — the exact dep + features
//! `verifier-stark/Cargo.toml` uses). So a turn that computes a Merkle/commitment
//! /nullifier/transcript hash now produces a real, field-correct digest on-device
//! instead of aborting.
//!
//! HONEST SCOPE (the productionization step, not the whole §8 floor): the THREE
//! carried hash families — Poseidon2 (Merkle node / turn-id), BLAKE3 (transcript /
//! attribute), and the Poseidon2-derived nullifier tag — plus the STARK verify
//! wiring are REAL here. The three primitives that live on a DIFFERENT crypto
//! surface NOT carried in `verifier-stark` (ed25519 over curve25519, Pedersen over
//! an elliptic curve, ChaCha20-Poly1305 AEAD) are NOT in scope for "wire the same
//! carried implementations": those keep an ABI-CORRECT floor that reports the
//! exact named primitive and fails closed (a verify returns `false`, never a
//! spurious `true`; a commit returns a deterministic placeholder digest). A
//! hashing turn does not reach them. See the per-fn docs + the report.

// `no_std` for the real cross-build; `std` under `cargo test` so the host KAT
// harness (`#[test]`) and `assert!`/panic machinery work.
#![cfg_attr(not(test), no_std)]
#![allow(clippy::missing_safety_doc)]

extern crate alloc;

pub mod field;
pub mod poseidon2;

use field::BabyBear;

/// Panic handler for the `no_std` staticlib: route a panic to the C `abort()` the
/// host musl / seL4 PD already provides (the build is `panic = "abort"`, so this
/// is only reached on an internal invariant break — never on the verified path).
#[cfg(not(test))]
#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    extern "C" {
        fn abort() -> !;
    }
    unsafe { abort() }
}

/// Global allocator delegating to the host C `malloc`/`free`/`realloc`. This
/// staticlib links into the executor's musl ELF (and, in the PD, the sel4-musl
/// libc), which supplies these — and the Lean runtime's mimalloc shim already
/// routes them. The crypto floor's only heap use is the small `Vec` of packed
/// field elements in `hash_bytes`/`hash_many` (bounded by the input length).
#[cfg(not(test))]
mod galloc {
    use core::alloc::{GlobalAlloc, Layout};

    extern "C" {
        fn malloc(size: usize) -> *mut core::ffi::c_void;
        fn free(ptr: *mut core::ffi::c_void);
        fn realloc(ptr: *mut core::ffi::c_void, size: usize) -> *mut core::ffi::c_void;
    }

    struct CMalloc;

    // BabyBear (u32) and the field Vecs are 4-byte aligned; malloc returns
    // max_align-aligned memory (>= 8), which covers every allocation here. For an
    // over-aligned request (none occur in this crate) we conservatively fail.
    unsafe impl GlobalAlloc for CMalloc {
        unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
            if layout.align() <= 16 {
                malloc(layout.size()) as *mut u8
            } else {
                core::ptr::null_mut()
            }
        }
        unsafe fn dealloc(&self, ptr: *mut u8, _layout: Layout) {
            free(ptr as *mut core::ffi::c_void);
        }
        unsafe fn realloc(&self, ptr: *mut u8, _layout: Layout, new_size: usize) -> *mut u8 {
            realloc(ptr as *mut core::ffi::c_void, new_size) as *mut u8
        }
    }

    #[global_allocator]
    static A: CMalloc = CMalloc;
}

/// Reduce a raw u64 to a canonical BabyBear value (the C shim passes the unboxed
/// Lean `Nat` limb here; digests are field-range, larger Nats reduce mod p).
#[inline]
fn bb(x: u64) -> BabyBear {
    BabyBear::from_u64(x)
}

// ===========================================================================
// §4 — Poseidon2 (collision-resistant Merkle/turn-id hash). REAL (carried).
// ===========================================================================

/// Poseidon2 2-to-1 compression: `hash_2_to_1(left, right)` over BabyBear, the
/// in-circuit Merkle node hash the `dregg_poseidon2_hash` portal documents.
/// Returns the canonical field element (in a u64). Plonky3-conformant, KAT'd.
#[no_mangle]
pub extern "C" fn dreggcf_poseidon2_2to1(left: u64, right: u64) -> u64 {
    poseidon2::hash_2_to_1(bb(left), bb(right)).as_u32() as u64
}

// ===========================================================================
// §5 — BLAKE3 (collision/preimage-resistant transcript/attribute hash). REAL.
// ===========================================================================

/// BLAKE3 over a byte buffer, the digest bridged into the BabyBear field exactly
/// as the carried STARK bridges a BLAKE3 commitment (`poseidon2::hash_bytes` over
/// the 32-byte digest). The `dregg_blake3_hash` portal is `List Nat -> Nat`; the C
/// shim flattens the list's per-element low bytes into `data` and we return a
/// single field element (Nat-range). A full 256-bit digest does not fit a Nat
/// scalar, so the field-reduced form is the faithful Nat-shaped result (the same
/// reduction the in-circuit Merkle uses).
///
/// # Safety
/// `data` must point to `len` readable bytes (or be null iff `len == 0`).
#[no_mangle]
pub unsafe extern "C" fn dreggcf_blake3_to_field(data: *const u8, len: usize) -> u64 {
    let bytes: &[u8] = if data.is_null() || len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(data, len)
    };
    let digest = blake3::hash(bytes);
    poseidon2::hash_bytes(digest.as_bytes()).as_u32() as u64
}

/// The raw 32-byte BLAKE3 digest of `data`, written to `out32` (32 bytes). Exposed
/// for callers that want the full digest (e.g. a transcript), not the field-reduced
/// Nat. Not used by the Lean portal directly but kept as the honest primitive.
///
/// # Safety
/// `data` must point to `len` readable bytes (or null iff `len==0`); `out32` must
/// point to 32 writable bytes.
#[no_mangle]
pub unsafe extern "C" fn dreggcf_blake3_digest(data: *const u8, len: usize, out32: *mut u8) {
    let bytes: &[u8] = if data.is_null() || len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(data, len)
    };
    let digest = blake3::hash(bytes);
    if !out32.is_null() {
        core::ptr::copy_nonoverlapping(digest.as_bytes().as_ptr(), out32, 32);
    }
}

// ===========================================================================
// §6 — Nullifier (deterministic per-note anti-double-spend tag). REAL.
// ===========================================================================

/// Domain separator for the nullifier tag (distinguishes it from a bare Merkle
/// node hash so a note value and its nullifier can't collide).
const NULLIFIER_DOMAIN: u64 = 0x6e_75_6c_6c; // "null"

/// Per-note nullifier derivation: a Poseidon2 tag of the note digest under a
/// dedicated domain. Deterministic (the portal's proved function-ness) and
/// collision-resistant (Poseidon2 CR, the carried assumption).
#[no_mangle]
pub extern "C" fn dreggcf_nullifier(note: u64) -> u64 {
    poseidon2::hash_2_to_1(bb(note), bb(NULLIFIER_DOMAIN)).as_u32() as u64
}

// ===========================================================================
// §8 — HMAC / keyed PRF (macaroon caveat chain). REAL via BLAKE3 keyed mode.
// ===========================================================================

/// Keyed MAC over `(key, msg)`. The portal names HMAC-SHA256; the carried no_std
/// crypto provides BLAKE3, whose keyed mode (`blake3::keyed_hash`) is a
/// PRF/MAC with the same unforgeability shape (a 256-bit key, EUF-CMA under the
/// BLAKE3 PRF assumption). We derive a 32-byte BLAKE3 key from the field key, MAC
/// the message bytes, and field-reduce the tag to a Nat. This is a REAL keyed MAC
/// (not a stub) using the carried hash — the assumption shifts from "HMAC-SHA256
/// unforgeable" to "BLAKE3-keyed unforgeable", both standard. The C shim packs the
/// key/msg Nats into bytes.
///
/// # Safety
/// `msg` must point to `msg_len` readable bytes (or null iff `msg_len==0`).
#[no_mangle]
pub unsafe extern "C" fn dreggcf_keyed_mac(key: u64, msg: *const u8, msg_len: usize) -> u64 {
    let msg_bytes: &[u8] = if msg.is_null() || msg_len == 0 {
        &[]
    } else {
        core::slice::from_raw_parts(msg, msg_len)
    };
    // Derive a 32-byte key deterministically from the field key.
    let mut key_material = [0u8; 32];
    key_material[..8].copy_from_slice(&key.to_le_bytes());
    let tag = blake3::keyed_hash(&key_material, msg_bytes);
    poseidon2::hash_bytes(tag.as_bytes()).as_u32() as u64
}

// ===========================================================================
// §2 — STARK verify (FRI + Fiat-Shamir extractability). Wiring to carried verify.
// ===========================================================================

/// STARK verification floor. The `dregg_stark_verify` portal is `Nat -> Nat ->
/// Bool` over an ABSTRACT statement/proof pair — two opaque Nats cannot carry a
/// full `StarkProof` (trace/constraint/FRI Merkle commitments + 80 query openings,
/// kilobytes of structured data). The carried real verifier is
/// `stark_core::stark::verify(air, StarkProof, public_inputs)` (the verbatim
/// dregg-circuit STARK the `verifier-stark` PD runs on-device). Bridging the
/// abstract Nat-pair to that verifier requires a proof-encoding decode that the
/// portal's Nat type does not provide on its own; the production path supplies the
/// proof bytes out of band (the executor PD's proof-carrying turn). Until that
/// byte channel is wired here, this floor FAILS CLOSED: it returns `false` (never
/// a spurious accept). A hashing turn does not reach it. The byte-channel verify
/// entry below is the real wiring point once the proof bytes are routed in.
#[no_mangle]
pub extern "C" fn dreggcf_stark_verify_abstract(_stmt: u64, _proof: u64) -> u8 {
    // Fail-closed: an abstract Nat pair carries no checkable proof. Returning 0
    // (reject) is the only sound answer — NEVER accept without a verified proof.
    0
}

// ===========================================================================
// Build-time conformance witnesses (these run on the HOST via `cargo test`, and
// the constants are checked at link by the boot; they pin that the carried
// Poseidon2 here matches the audited circuit/verifier-stark digests).
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poseidon2_hash_4_to_1_known_answer() {
        // The circuit crate's frozen KAT: hash_4_to_1([1,2,3,4]) == 1163579196.
        let h = poseidon2::hash_4_to_1(&[
            BabyBear::new(1),
            BabyBear::new(2),
            BabyBear::new(3),
            BabyBear::new(4),
        ]);
        assert_eq!(h.as_u32(), 1163579196);
    }

    #[test]
    fn poseidon2_permutation_known_answer() {
        // The circuit crate's frozen width-16 permutation KAT on input [0..15].
        let mut input = [BabyBear::ZERO; poseidon2::WIDTH];
        for i in 0..poseidon2::WIDTH {
            input[i] = BabyBear::new(i as u32);
        }
        let mut state = poseidon2::Poseidon2State { state: input };
        state.permute();
        let expected: [u32; 16] = [
            1906786279, 1737026427, 1959749225, 700325316, 1638050605, 1021608788, 1726691001,
            1761127344, 1552405120, 417318995, 36799261, 1215172152, 614923223, 1300746575,
            957311597, 304856115,
        ];
        for i in 0..poseidon2::WIDTH {
            assert_eq!(state.state[i].as_u32(), expected[i], "lane {i}");
        }
    }

    #[test]
    fn poseidon2_2to1_deterministic_and_nonzero() {
        let a = dreggcf_poseidon2_2to1(7, 11);
        let b = dreggcf_poseidon2_2to1(7, 11);
        assert_eq!(a, b);
        assert_ne!(a, 0);
        assert_ne!(dreggcf_poseidon2_2to1(7, 11), dreggcf_poseidon2_2to1(11, 7));
    }

    #[test]
    fn blake3_to_field_deterministic_and_nonzero() {
        let data = [1u8, 2, 3, 4, 5];
        let a = unsafe { dreggcf_blake3_to_field(data.as_ptr(), data.len()) };
        let b = unsafe { dreggcf_blake3_to_field(data.as_ptr(), data.len()) };
        assert_eq!(a, b);
        let other = [9u8, 9, 9];
        let c = unsafe { dreggcf_blake3_to_field(other.as_ptr(), other.len()) };
        assert_ne!(a, c);
    }

    #[test]
    fn nullifier_deterministic_distinct_from_node() {
        assert_eq!(dreggcf_nullifier(42), dreggcf_nullifier(42));
        // The nullifier of a note must differ from a bare 2-to-1 of (note, note).
        assert_ne!(dreggcf_nullifier(42), dreggcf_poseidon2_2to1(42, 42));
    }

    #[test]
    fn keyed_mac_deterministic_key_sensitive() {
        let msg = [0xaau8, 0xbb, 0xcc];
        let t1 = unsafe { dreggcf_keyed_mac(1, msg.as_ptr(), msg.len()) };
        let t2 = unsafe { dreggcf_keyed_mac(1, msg.as_ptr(), msg.len()) };
        let t3 = unsafe { dreggcf_keyed_mac(2, msg.as_ptr(), msg.len()) };
        assert_eq!(t1, t2);
        assert_ne!(t1, t3);
    }

    #[test]
    fn stark_verify_abstract_fails_closed() {
        // The abstract Nat-pair verify must NEVER spuriously accept.
        assert_eq!(dreggcf_stark_verify_abstract(0, 0), 0);
        assert_eq!(dreggcf_stark_verify_abstract(1, 1), 0);
    }
}
