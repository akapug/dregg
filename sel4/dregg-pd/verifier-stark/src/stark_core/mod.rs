//! The no_std STARK core carried to the seL4 verifier-stark PD.
//!
//! `field` + `stark` are the verbatim `dregg-circuit` `src/field.rs` +
//! `src/stark.rs` (the custom BabyBear+BLAKE3+FRI STARK), ported `std → core`/
//! `alloc` with the `#[cfg(test)]` modules dropped. This is the REAL
//! cryptographic STARK — Reed-Solomon trace encoding, BLAKE3 Merkle
//! commitments, FRI low-degree testing, Fiat-Shamir non-interactivity — not a
//! structural stand-in. A tampered trace fails verification.

pub mod field;
pub mod stark;
