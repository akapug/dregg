//! REAL no-viewer — the n-of-n collective threshold-decrypt with PROVEN smudging (the keystone).
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §1. This file is OWNED by the `threshold`
//! swarm lane. Anchor: fhe.rs `mbfv` (`DecryptionShare`/`PublicKeyShare`/`CommonRandomPoly`) is the crypto
//! oracle; the smudging bound is proven in `metatheory/Bfv/Smudging.lean` — NOT fhe.rs mbfv's fresh-noise TODO.
#![allow(dead_code, unused_variables)]

use crate::bfv_lean::LeanCiphertext;

pub type Result<T> = std::result::Result<T, ThresholdError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ThresholdError {
    QuorumTooSmall { have: usize, need: usize },
    ParamMismatch,
    SmudgeTooSmall,
}

/// One party's share of the collective secret key (no dealer ever holds the whole key).
pub struct KeyShare;
/// One party's SMUDGED partial decryption of the folded aggregate.
pub struct DecryptShare;
/// The collective public key everyone encrypts to.
pub struct CollectivePublicKey;
/// BFV parameter handle (degree/moduli/t) — the fold set for this prototype.
pub struct BfvParams;

/// n-of-n collective keygen (each party contributes; NO dealer). Anchored to mbfv PublicKeyShare + CommonRandomPoly.
pub fn collective_keygen(n: usize, params: &BfvParams) -> (CollectivePublicKey, Vec<KeyShare>) {
    todo!("threshold lane: mbfv-anchored collective keygen")
}
/// One party's SMUDGED partial decrypt; smudge_bits ≥ the Bfv/Smudging.lean bound or it is unsound.
pub fn partial_decrypt(share: &KeyShare, ct: &LeanCiphertext, smudge_bits: u32) -> DecryptShare {
    todo!("threshold lane: smudged partial decrypt")
}
/// Combine n partial decrypts → plaintext. Refuses < n shares or param disagreement.
pub fn combine(shares: &[DecryptShare], params: &BfvParams) -> Result<Vec<u64>> {
    todo!("threshold lane: combine shares")
}
