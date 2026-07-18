//! BFV ct×ct MULTIPLY — the MULTIPLICATIVE stone, differentially anchored to
//! `fhe.rs` as the ORACLE.
//!
//! WHY THIS EXISTS: the additive fold (`bfv_lean.rs` / `additive.rs`) is cheap
//! precisely BECAUSE it never multiplies two ciphertexts — no NTT tensor, no
//! relinearization, no keyswitch material. But genuine private×private
//! products — quadratic objectives (xᵀQx), option payoffs, AMM invariants
//! (x·y = k), any product of two secret quantities — NEED BFV ct×ct multiply
//! + relinearization. This module is the first working, oracle-validated
//! stone on that path.
//!
//! WHAT THIS STONE IS (scoped honestly):
//! * a thin, WRAP-GUARDED engine over fhe.rs's own `Multiplicator` +
//!   `RelinearizationKey` (`fhe-0.1.1/src/bfv/ops/mul.rs`,
//!   `bfv/keys/relinearization_key.rs`). The multiply arithmetic here IS
//!   fhe.rs — that is deliberate: for multiplication the real library is the
//!   anchor, and the oracle tests (`tests/bfv_mul_oracle.rs`) close the loop
//!   encrypt(fhe.rs) → multiply(here) → decrypt(fhe.rs) == product mod t.
//! * the multiplicative WRAP DISCIPLINE: slot products ≥ t wrap SILENTLY
//!   (mod t), exactly like the additive class-(C) hazard, but the budget is
//!   MUCH tighter — with the deployed t = 1032193 (~2^20), full-range u16
//!   inputs ALREADY wrap (65535² ≫ t); the safe per-operand bound for a
//!   single square is 1015 (1015² = 1030225 < t < 1016² = 1032256). Every
//!   [`BoundedCiphertext`] carries a declared inclusive slot bound and
//!   [`MulEngine::multiply`] refuses when `bound_a · bound_b ≥ t`.
//! * a bounded PRODUCT-SUM fold `Σᵢ aᵢ·bᵢ` ([`MulEngine::product_sum`]) —
//!   the quadratic-objective / dot-product shape — with the summed wrap
//!   guard `Σ (bound_aᵢ·bound_bᵢ) < t`.
//!
//! NAMED NEXT STONES (not attempted here — the honesty ledger):
//! * FROM-SCRATCH tensor+relin: unlike the fold-add (trivial RNS add, done
//!   from scratch in `bfv_lean.rs`), ct×ct multiply needs RNS basis extension
//!   (`Scaler`), the negacyclic NTT, and t/q down-scaling — the whole
//!   `fhe-math` machinery. Rebuilding that Lean-first is the real next stone.
//! * THE GPU HOT PATH: the multiply cost is the negacyclic polynomial
//!   multiplication in the EXTENDED RNS basis — (I)NTT + pointwise mul. That
//!   is the NTT the convex engine will hammer; `bfv_gpu.rs` today only does
//!   the fold-ADD rows — wiring an NTT kernel into it is named, not built.
//! * NOISE THEORY: multiply noise growth is measured here (oracle test
//!   `noise_growth_measured`), not proven. The Lean noise model
//!   (`metatheory/Bfv/Noise.lean`) covers ADDITION only; the multiplicative
//!   noise lemma (the t·n·(e_a+e_b)-shape bound) belongs to the mult-noise
//!   Lean lane. Coordinate there before claiming any depth budget.
//! * KEY MANAGEMENT: `RelinearizationKey` here is generated next to the
//!   secret key in tests. Threshold/n-of-n relin-key generation (who holds
//!   sk²-material in a no-viewer deployment?) is an OPEN design point — the
//!   additive-only no-viewer story does NOT carry over for free.
//! * DEPTH: this stone validates depth-1 (one multiply, then adds). Depth-2
//!   is exercised in the oracle tests to MEASURE where the 3-moduli
//!   (~109-bit q) budget actually dies — see the test for the measured verdict.

use std::fmt;
use std::sync::Arc;

use fhe::bfv::{BfvParameters, Ciphertext, Multiplicator, RelinearizationKey};

/// Errors — every refusal is loud and NAMES what was refused.
#[derive(Debug)]
pub enum BfvMulError {
    /// Multiplicative wrap refusal: the declared slot bounds multiply past
    /// t-1, so a slot product could wrap mod t SILENTLY (a well-formed WRONG
    /// number, not an error state). Refused before touching the ciphertexts.
    WrapRefused {
        bound_product: u128,
        plaintext_modulus: u64,
    },
    /// Additive wrap refusal inside `product_sum`: the per-pair product
    /// bounds SUM past t-1.
    SumWrapRefused {
        bound_sum: u128,
        plaintext_modulus: u64,
    },
    /// `product_sum` over an empty list has no ciphertext to return.
    EmptyProductSum,
    /// `product_sum` was given mismatched operand lists.
    LengthMismatch { lhs: usize, rhs: usize },
    /// An underlying fhe.rs operation failed (its error text carried through).
    Fhe(String),
}

impl fmt::Display for BfvMulError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrapRefused {
                bound_product,
                plaintext_modulus,
            } => write!(
                f,
                "plaintext wrap refused: declared slot bounds multiply to {bound_product} >= t = \
                 {plaintext_modulus}; a slot product could wrap mod t silently"
            ),
            Self::SumWrapRefused {
                bound_sum,
                plaintext_modulus,
            } => write!(
                f,
                "plaintext wrap refused: per-pair product bounds sum to {bound_sum} >= t = \
                 {plaintext_modulus}; the product-sum could wrap mod t silently"
            ),
            Self::EmptyProductSum => write!(f, "product_sum over an empty list refused"),
            Self::LengthMismatch { lhs, rhs } => {
                write!(f, "product_sum operand lists differ: {lhs} vs {rhs}")
            }
            Self::Fhe(e) => write!(f, "fhe.rs operation failed: {e}"),
        }
    }
}

impl std::error::Error for BfvMulError {}

/// A ciphertext carrying a caller-DECLARED inclusive upper bound on every
/// plaintext slot. The bound is declared, not proven — binding it
/// cryptographically (range proof at ingest) is the same named later stone as
/// in `bfv_lean.rs`; today it is enforceable at the ingest boundary.
#[derive(Debug, Clone)]
pub struct BoundedCiphertext {
    pub ct: Ciphertext,
    /// Inclusive upper bound on every plaintext slot value.
    pub plain_bound: u64,
}

impl BoundedCiphertext {
    pub fn new(ct: Ciphertext, plain_bound: u64) -> Self {
        Self { ct, plain_bound }
    }
}

/// The wrap-guarded ct×ct multiply engine. Wraps fhe.rs's default
/// multiplication strategy (extended-basis tensor, t/q down-scale,
/// relinearization back to a 2-element ciphertext).
pub struct MulEngine {
    mult: Multiplicator,
    t: u64,
}

impl MulEngine {
    /// Build the engine from a relinearization key. Uses fhe.rs's
    /// `Multiplicator::default` strategy (the 2016-style extended-basis
    /// multiply with relinearization enabled).
    pub fn new(rk: &RelinearizationKey, params: &Arc<BfvParameters>) -> Result<Self, BfvMulError> {
        let mult = Multiplicator::default(rk).map_err(|e| BfvMulError::Fhe(e.to_string()))?;
        Ok(Self {
            mult,
            t: params.plaintext(),
        })
    }

    /// The plaintext modulus the wrap guard enforces against.
    pub fn plaintext_modulus(&self) -> u64 {
        self.t
    }

    /// ct×ct multiply + relinearize, wrap-guarded: refuses unless
    /// `bound_a · bound_b < t`, so every slot product is the EXACT integer
    /// product (no silent mod-t wrap). The result carries the product bound.
    pub fn multiply(
        &self,
        a: &BoundedCiphertext,
        b: &BoundedCiphertext,
    ) -> Result<BoundedCiphertext, BfvMulError> {
        let bound_product = (a.plain_bound as u128) * (b.plain_bound as u128);
        if bound_product >= self.t as u128 {
            return Err(BfvMulError::WrapRefused {
                bound_product,
                plaintext_modulus: self.t,
            });
        }
        let ct = self
            .mult
            .multiply(&a.ct, &b.ct)
            .map_err(|e| BfvMulError::Fhe(e.to_string()))?;
        Ok(BoundedCiphertext {
            ct,
            // bound_product < t <= u64::MAX, so the cast is exact.
            plain_bound: bound_product as u64,
        })
    }

    /// The quadratic-objective / dot-product shape: `Σᵢ aᵢ·bᵢ` over pairs of
    /// encrypted operands, each pair multiplied+relinearized, the products
    /// folded by homomorphic ADDITION. Wrap-guarded twice: each pair through
    /// [`Self::multiply`], and the SUM of product bounds against t.
    pub fn product_sum(
        &self,
        lhs: &[BoundedCiphertext],
        rhs: &[BoundedCiphertext],
    ) -> Result<BoundedCiphertext, BfvMulError> {
        if lhs.len() != rhs.len() {
            return Err(BfvMulError::LengthMismatch {
                lhs: lhs.len(),
                rhs: rhs.len(),
            });
        }
        if lhs.is_empty() {
            return Err(BfvMulError::EmptyProductSum);
        }
        let bound_sum: u128 = lhs
            .iter()
            .zip(rhs.iter())
            .map(|(a, b)| (a.plain_bound as u128) * (b.plain_bound as u128))
            .sum();
        if bound_sum >= self.t as u128 {
            return Err(BfvMulError::SumWrapRefused {
                bound_sum,
                plaintext_modulus: self.t,
            });
        }
        let mut acc: Option<BoundedCiphertext> = None;
        for (a, b) in lhs.iter().zip(rhs.iter()) {
            let prod = self.multiply(a, b)?;
            acc = Some(match acc {
                None => prod,
                Some(sum) => BoundedCiphertext {
                    ct: &sum.ct + &prod.ct,
                    plain_bound: sum.plain_bound + prod.plain_bound,
                },
            });
        }
        Ok(acc.expect("non-empty by check above"))
    }
}

/// The largest per-operand bound safe for a single square at plaintext
/// modulus `t`: `floor(sqrt(t-1))`. For the deployed t = 1032193 this is
/// 1015 — NOT u16::MAX; full-range u16 inputs already wrap under multiply.
pub fn square_safe_bound(t: u64) -> u64 {
    let mut lo = 0u64;
    let mut hi = 1u64 << 32;
    while lo < hi {
        let mid = lo + (hi - lo).div_ceil(2);
        if (mid as u128) * (mid as u128) <= (t as u128) - 1 {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lo
}

#[cfg(test)]
mod tests {
    use super::square_safe_bound;

    #[test]
    fn square_safe_bound_is_tight() {
        // Deployed t: 1015² = 1030225 < 1032193 <= 1016² = 1032256.
        assert_eq!(square_safe_bound(1032193), 1015);
        assert_eq!(square_safe_bound(2), 1);
        assert_eq!(square_safe_bound(5), 2);
        // Tightness generally: bound² < t <= (bound+1)².
        for t in [2u64, 3, 4, 5, 100, 65537, 1032193, 1 << 40] {
            let b = square_safe_bound(t);
            assert!((b as u128) * (b as u128) < t as u128);
            assert!(((b + 1) as u128) * ((b + 1) as u128) >= t as u128);
        }
    }
}
