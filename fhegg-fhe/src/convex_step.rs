//! PRIVATE CONVEX ENGINE — stone 1: ONE iteration of `x ← prox(x − τ·A·x)`
//! over ENCRYPTED state, in the purely ADDITIVE homomorphic regime.
//!
//! This is the first laid stone of the `FHEGG-MATHEMATICAL-BRIEF.md` §5
//! generalization: fhEgg's auction fold is the `T = 1` special case of a
//! first-order convex solver whose iteration is `x ← prox(x − τ·A·x)`.
//!
//! ## THE KEY INSIGHT (load-bearing, stated out loud)
//!
//! **The N-dependent linear step never needs a ct×ct multiply.** `A` is a
//! PUBLIC matrix, so `A·x` over encrypted `x` is scalar multiplication by
//! public constants — and scalar multiplication by a public integer `c` IS
//! `c` repeated homomorphic additions (proven by execution in
//! `tests/convex_step_oracle.rs`: our scale-by-5 is byte-identical to
//! fhe.rs's own `ct+ct+ct+ct+ct`). No relinearization, no key material, no
//! noise blow-up beyond the linear factor. The whole matrix-vector step
//! stays in the same cheap additive regime as the auction fold; the ONLY
//! nonlinearity in the iteration is the prox (here: one box clamp), and in
//! this stone the prox is applied AT THE DECRYPT BOUNDARY — exactly where
//! fhEgg's crossing lives (`mpc.rs`'s output-boundary posture).
//!
//! ## What one iteration computes, exactly
//!
//! Fix a public `d×d` integer matrix `A`, a public rational step
//! `τ = tau_num / tau_den`, and a box `[lo, hi]` (the prox of the indicator
//! of a box = clamp; with `A ⪰ 0` this iteration is projected gradient
//! descent on `min ½xᵀAx  s.t. x ∈ [lo,hi]^d`). Over the encrypted state we
//! compute the SCALED linear step
//!
//! ```text
//!     w_i  =  tau_den·x_i  −  tau_num·Σ_j A_ij·x_j      (= tau_den·(x − τAx)_i)
//! ```
//!
//! entirely homomorphically (scalar mul by public constants + adds + neg).
//! At the boundary, decrypt, decode CENTERED mod t (signed values live in
//! `[−(t−1)/2, (t−1)/2]`), and apply the prox in the SCALED domain:
//! `clamp(w, tau_den·lo, tau_den·hi) = tau_den·clamp(w/tau_den, lo, hi)` —
//! clamp commutes with positive scaling, so the scaled comparison is EXACT
//! (no rounding anywhere; BFV is an exact scheme and every value here is an
//! integer).
//!
//! Because each of the 4096 SIMD slots is an independent plaintext, `d`
//! ciphertexts carry 4096 INDEPENDENT d-dimensional problem instances at
//! once — the differential test checks all of them against a cleartext
//! reference.
//!
//! ## The signed layer (why `bfv_lean::fold_add` is not reused directly)
//!
//! Convex iterates go negative; plaintexts are residues mod t. We adopt the
//! standard centered encoding (`v ↦ v mod t`, decode `m > t/2 ↦ m − t`) and
//! carry a DECLARED signed interval `[lo, hi]` per ciphertext — the signed
//! generalization of `bfv_lean`'s `plain_bound`. Every operation here does
//! interval arithmetic and REFUSES (loudly, named) any op whose interval
//! could leave the centered window `[−(t−1)/2, (t−1)/2]`: outside it,
//! centered decode silently misreads a large positive as a negative (proven
//! real by execution in the oracle tests — the signed twin of the class-(C)
//! wrap). The unsigned `fold_add` gate types sums in `[0, t)`, so it cannot
//! type this window; the raw residue add is restated here (5 lines) and the
//! oracle byte-differentials (`&a + &b`, `&a − &b`, `−&a` under fhe.rs)
//! keep all three primitive ops honest. Deliberate fail-closed coupling:
//! a `SignedCt`'s inner `LeanCiphertext` carries `plain_bound = t − 1`, so
//! feeding it back to the UNSIGNED `fold_add` gate refuses — the two
//! encodings cannot be silently mixed.
//!
//! ## NAMED residuals (what this stone does NOT do)
//!
//! * **T > 1 composition:** the output is scaled by `tau_den`; iterating
//!   again needs division by `tau_den` (rescale), which exact BFV does not
//!   offer homomorphically. Paths: `tau_den = 1` (integer τ·A only),
//!   boundary-assisted re-encryption each iteration (decrypt-prox-reencrypt,
//!   the posture this stone already has), or CKKS with native rescale —
//!   CKKS is NOT in our dependency set (tfhe-rs has no CKKS; fhe.rs 0.1.1
//!   ships BFV only). Named, not attempted.
//! * **Noise across T:** one iteration multiplies fresh noise by at most
//!   `tau_den + tau_num·max_i Σ_j |A_ij|` (scalar mul by c scales noise by
//!   ≤ c, adds sum it). Staying encrypted for T iterations compounds this
//!   geometrically — the budget theorem is `metatheory/Bfv/Noise.lean`'s
//!   margin meter, which today covers the additive fold only; extending
//!   `marginHolds` to the scalar-mul factor is the mult-noise-lean
//!   coordination point.
//! * **prox under encryption:** clamp is a comparison; keeping it encrypted
//!   needs the crossing/threshold machinery (output-boundary MPC as in
//!   `mpc.rs`, or TFHE PBS) — not scalar arithmetic. This stone decrypts
//!   first (the auction's own posture for its single crossing).
//! * **Declared, not proven, intervals:** like `plain_bound`, the signed
//!   interval is a caller declaration; binding it cryptographically (range
//!   proof at ingest) is the same named later stone as in `bfv_lean`.

use crate::bfv_lean::{LeanCiphertext, RnsPoly};
use std::fmt;

/// Errors — every refusal is loud and NAMES what was refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvexStepError {
    /// A declared/derived signed interval could leave the centered window
    /// `[−(t−1)/2, (t−1)/2]`; centered decode would silently misread.
    WindowExceeded { lo: i128, hi: i128, half: u64 },
    /// The two operands disagree on moduli/degree/level/poly-count.
    Incompatible(&'static str),
    /// State vector and matrix dimensions disagree, or the state is empty.
    Dimension(&'static str),
    /// A step constant (`tau_num·A_ij` or `tau_den`) does not fit the scalar
    /// range this stone supports.
    ConstantOverflow(&'static str),
    /// `tau_den` must be ≥ 1.
    ZeroDenominator,
}

impl fmt::Display for ConvexStepError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WindowExceeded { lo, hi, half } => write!(
                f,
                "signed window exceeded: interval [{lo}, {hi}] leaves \
                 [-(t-1)/2, (t-1)/2] = [-{half}, {half}]; centered decode would \
                 silently alias"
            ),
            Self::Incompatible(what) => write!(f, "incompatible operands: {what}"),
            Self::Dimension(what) => write!(f, "dimension mismatch: {what}"),
            Self::ConstantOverflow(what) => write!(f, "step constant overflow: {what}"),
            Self::ZeroDenominator => write!(f, "tau_den must be >= 1"),
        }
    }
}

impl std::error::Error for ConvexStepError {}

type Result<T> = std::result::Result<T, ConvexStepError>;

/// The centered-window radius: signed values must satisfy `|v| ≤ (t−1)/2`.
pub const fn centered_window(t: u64) -> u64 {
    (t - 1) / 2
}

/// Encode a signed value as a residue mod t (the centered encoding's inverse
/// is [`center`]). Callers must keep `|v| ≤ (t−1)/2` for the round-trip to
/// hold — that is exactly what the window gate enforces on ciphertexts.
pub fn encode_signed(v: i64, t: u64) -> u64 {
    (i128::from(v)).rem_euclid(i128::from(t)) as u64
}

/// Centered decode of a decrypted slot: residues above t/2 are negatives.
pub fn center(m: u64, t: u64) -> i64 {
    debug_assert!(m < t);
    if m > t / 2 {
        (i128::from(m) - i128::from(t)) as i64
    } else {
        m as i64
    }
}

/// An encrypted signed value: a parsed BFV ciphertext plus a DECLARED
/// inclusive interval `[lo, hi]` bounding the true (unwrapped) value of every
/// slot. The interval is the signed twin of `bfv_lean`'s `plain_bound`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedCt {
    ct: LeanCiphertext,
    lo: i64,
    hi: i64,
}

fn check_window(lo: i128, hi: i128, t: u64) -> Result<()> {
    let half = i128::from(centered_window(t));
    if lo > hi {
        return Err(ConvexStepError::Dimension("interval lo > hi"));
    }
    if lo < -half || hi > half {
        return Err(ConvexStepError::WindowExceeded {
            lo,
            hi,
            half: centered_window(t),
        });
    }
    Ok(())
}

fn check_compatible(a: &LeanCiphertext, b: &LeanCiphertext) -> Result<()> {
    if a.moduli != b.moduli {
        return Err(ConvexStepError::Incompatible("RNS moduli differ"));
    }
    if a.degree != b.degree {
        return Err(ConvexStepError::Incompatible("degree differs"));
    }
    if a.level != b.level {
        return Err(ConvexStepError::Incompatible("level differs"));
    }
    if a.polys.len() != 2 || b.polys.len() != 2 {
        return Err(ConvexStepError::Incompatible("poly count is not 2"));
    }
    Ok(())
}

/// Map every residue through `f(coeff, q)`, preserving metadata. The inner
/// `plain_bound` is pinned to `t−1` == "unsigned gate refuses" (fail-closed:
/// a signed ciphertext cannot silently re-enter the unsigned fold).
fn map_rows(ct: &LeanCiphertext, t: u64, f: impl Fn(u64, u64) -> u64) -> LeanCiphertext {
    LeanCiphertext {
        moduli: ct.moduli.clone(),
        degree: ct.degree,
        level: ct.level,
        variable_time: ct.variable_time,
        polys: ct
            .polys
            .iter()
            .map(|p| RnsPoly {
                rows: p
                    .rows
                    .iter()
                    .zip(ct.moduli.iter())
                    .map(|(row, &q)| row.iter().map(|&c| f(c, q)).collect())
                    .collect(),
            })
            .collect(),
        plain_bound: t - 1,
    }
}

impl SignedCt {
    /// Wrap a parsed ciphertext with its declared signed interval. Refuses an
    /// interval outside the centered window. The inner `plain_bound` is
    /// overwritten to `t−1` (see module docs: fail-closed vs the unsigned gate).
    pub fn new(ct: LeanCiphertext, lo: i64, hi: i64, t: u64) -> Result<Self> {
        check_window(i128::from(lo), i128::from(hi), t)?;
        if ct.polys.len() != 2 {
            return Err(ConvexStepError::Incompatible("poly count is not 2"));
        }
        let ct = map_rows(&ct, t, |c, _| c); // clone with plain_bound = t−1
        Ok(Self { ct, lo, hi })
    }

    pub fn interval(&self) -> (i64, i64) {
        (self.lo, self.hi)
    }

    pub fn ciphertext(&self) -> &LeanCiphertext {
        &self.ct
    }

    pub fn into_ciphertext(self) -> LeanCiphertext {
        self.ct
    }
}

/// Homomorphic negation: residue-wise `q − c` (i.e. scalar mul by −1). The
/// plaintext maps `v ↦ −v`; the interval flips.
pub fn signed_neg(x: &SignedCt, t: u64) -> Result<SignedCt> {
    let (lo, hi) = (-i128::from(x.hi), -i128::from(x.lo));
    check_window(lo, hi, t)?;
    Ok(SignedCt {
        ct: map_rows(&x.ct, t, |c, q| if c == 0 { 0 } else { q - c }),
        lo: lo as i64,
        hi: hi as i64,
    })
}

/// Homomorphic addition of two signed ciphertexts, gated on the SIGNED
/// window (the centered twin of `fold_add`'s wrap gate).
pub fn signed_add(a: &SignedCt, b: &SignedCt, t: u64) -> Result<SignedCt> {
    check_compatible(&a.ct, &b.ct)?;
    let (lo, hi) = (
        i128::from(a.lo) + i128::from(b.lo),
        i128::from(a.hi) + i128::from(b.hi),
    );
    check_window(lo, hi, t)?;
    let polys =
        a.ct.polys
            .iter()
            .zip(b.ct.polys.iter())
            .map(|(pa, pb)| RnsPoly {
                rows: pa
                    .rows
                    .iter()
                    .zip(pb.rows.iter())
                    .zip(a.ct.moduli.iter())
                    .map(|((ra, rb), &q)| {
                        ra.iter()
                            .zip(rb.iter())
                            .map(|(&x, &y)| {
                                let s = x + y; // both canonical (< q < 2^38): no overflow
                                if s >= q {
                                    s - q
                                } else {
                                    s
                                }
                            })
                            .collect()
                    })
                    .collect(),
            })
            .collect();
    Ok(SignedCt {
        ct: LeanCiphertext {
            moduli: a.ct.moduli.clone(),
            degree: a.ct.degree,
            level: a.ct.level,
            variable_time: a.ct.variable_time | b.ct.variable_time,
            polys,
            plain_bound: t - 1,
        },
        lo: lo as i64,
        hi: hi as i64,
    })
}

/// Homomorphic scalar multiplication by a PUBLIC signed constant `c`:
/// residue-wise `coeff·|c| mod q`, negated if `c < 0`. Semantically this IS
/// `|c|` repeated additions (byte-equal to fhe.rs's own repeated `+` — the
/// oracle test proves it), evaluated in one pass. This is the whole trick
/// that keeps the public-matrix step additive: NO ct×ct, NO relinearization.
pub fn signed_scale(x: &SignedCt, c: i64, t: u64) -> Result<SignedCt> {
    let p1 = i128::from(x.lo) * i128::from(c);
    let p2 = i128::from(x.hi) * i128::from(c);
    let (lo, hi) = (p1.min(p2), p1.max(p2));
    check_window(lo, hi, t)?;
    let cm = c.unsigned_abs();
    let mag = map_rows(&x.ct, t, |co, q| {
        ((u128::from(co) * u128::from(cm)) % u128::from(q)) as u64
    });
    let ct = if c >= 0 {
        mag
    } else {
        // residues carry |c|·v; negate residue-wise to get c·v = −|c|·v.
        map_rows(&mag, t, |co, q| if co == 0 { 0 } else { q - co })
    };
    Ok(SignedCt {
        ct,
        lo: lo as i64,
        hi: hi as i64,
    })
}

/// The public data of one first-order iteration `x ← prox(x − τ·A·x)`:
/// a PUBLIC `d×d` integer matrix and a public rational step
/// `τ = tau_num / tau_den`. Nothing here is secret — that is the point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PublicLinearStep {
    pub a: Vec<Vec<i64>>,
    pub tau_num: u64,
    pub tau_den: u64,
}

/// ONE homomorphic linear step: `w_i = tau_den·x_i − tau_num·Σ_j A_ij·x_j`
/// (the τ_den-scaled gradient step), computed entirely with public-constant
/// scalar muls + adds + neg over the encrypted state. Refuses loudly on
/// dimension mismatch, constant overflow, or any window violation.
pub fn convex_linear_step(
    x: &[SignedCt],
    step: &PublicLinearStep,
    t: u64,
) -> Result<Vec<SignedCt>> {
    let d = x.len();
    if d == 0 {
        return Err(ConvexStepError::Dimension("empty state vector"));
    }
    if step.tau_den == 0 {
        return Err(ConvexStepError::ZeroDenominator);
    }
    if step.a.len() != d || step.a.iter().any(|row| row.len() != d) {
        return Err(ConvexStepError::Dimension("A is not d×d for the state"));
    }
    let den = i64::try_from(step.tau_den)
        .map_err(|_| ConvexStepError::ConstantOverflow("tau_den > i64::MAX"))?;
    let mut out = Vec::with_capacity(d);
    for i in 0..d {
        // acc = tau_den · x_i
        let mut acc = signed_scale(&x[i], den, t)?;
        for (j, xj) in x.iter().enumerate() {
            let c = -i128::from(step.tau_num) * i128::from(step.a[i][j]);
            if c == 0 {
                continue;
            }
            let c = i64::try_from(c)
                .map_err(|_| ConvexStepError::ConstantOverflow("tau_num·A_ij overflows i64"))?;
            let term = signed_scale(xj, c, t)?;
            acc = signed_add(&acc, &term, t)?;
        }
        out.push(acc);
    }
    Ok(out)
}

/// The prox box `[lo, hi]` (original, UNSCALED units).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClampBox {
    pub lo: i64,
    pub hi: i64,
}

/// THE PROX, applied at the decrypt boundary in the SCALED domain:
/// `clamp(w, tau_den·lo, tau_den·hi)` = `tau_den · clamp(w/tau_den, lo, hi)`
/// exactly (clamp commutes with positive scaling; everything is an integer).
pub fn prox_clamp_scaled(w: i64, bx: &ClampBox, tau_den: u64) -> i128 {
    let lo = i128::from(bx.lo) * i128::from(tau_den);
    let hi = i128::from(bx.hi) * i128::from(tau_den);
    i128::from(w).clamp(lo, hi)
}

/// CLEARTEXT REFERENCE, linear part: exact integer `w = tau_den·x − tau_num·A·x`
/// for ONE instance (one slot across the d coordinates). The differential
/// test runs this for every one of the 4096 slot-instances.
pub fn reference_linear_scaled(x: &[i64], step: &PublicLinearStep) -> Vec<i128> {
    let d = x.len();
    (0..d)
        .map(|i| {
            let ax: i128 = (0..d)
                .map(|j| i128::from(step.a[i][j]) * i128::from(x[j]))
                .sum();
            i128::from(step.tau_den) * i128::from(x[i]) - i128::from(step.tau_num) * ax
        })
        .collect()
}

/// CLEARTEXT REFERENCE, full iteration (scaled domain): `tau_den·prox(x − τAx)`.
pub fn reference_step_scaled(x: &[i64], step: &PublicLinearStep, bx: &ClampBox) -> Vec<i128> {
    reference_linear_scaled(x, step)
        .into_iter()
        .map(|w| {
            let lo = i128::from(bx.lo) * i128::from(step.tau_den);
            let hi = i128::from(bx.hi) * i128::from(step.tau_den);
            w.clamp(lo, hi)
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const T: u64 = 1_032_193; // the deployed fold plaintext modulus (asserted against fhe.rs in the oracle tests)

    #[test]
    fn encode_center_roundtrip_edges() {
        let half = centered_window(T) as i64;
        for v in [0i64, 1, -1, 17, -17, half, -half] {
            assert_eq!(
                center(encode_signed(v, T), T),
                v,
                "roundtrip failed for {v}"
            );
        }
    }

    #[test]
    fn centered_aliasing_is_the_named_hazard() {
        // One past the window: encode/decode silently misreads sign — this is
        // exactly what the window gate refuses to let a ciphertext reach.
        let half = centered_window(T) as i64;
        let v = half + 1;
        assert_eq!(
            center(encode_signed(v, T), T),
            -half,
            "aliasing shape changed"
        );
    }

    #[test]
    fn window_check_refuses_out_of_range() {
        let half = centered_window(T);
        assert!(check_window(-(half as i128), half as i128, T).is_ok());
        assert_eq!(
            check_window(0, half as i128 + 1, T),
            Err(ConvexStepError::WindowExceeded {
                lo: 0,
                hi: half as i128 + 1,
                half
            })
        );
        assert!(matches!(
            check_window(5, 4, T),
            Err(ConvexStepError::Dimension(_))
        ));
    }

    #[test]
    fn reference_step_hand_computed_instance() {
        // d = 2, A = [[2,1],[1,3]], τ = 1/4, x = (10, −8), box [0, 6].
        // A·x = (2·10 + 1·(−8), 1·10 + 3·(−8)) = (12, −14)
        // w   = 4·x − 1·A·x = (40 − 12, −32 + 14) = (28, −18)
        // prox scaled to [0·4, 6·4] = [0, 24]: (24, 0)   → x⁺ = (6, 0)
        let step = PublicLinearStep {
            a: vec![vec![2, 1], vec![1, 3]],
            tau_num: 1,
            tau_den: 4,
        };
        let bx = ClampBox { lo: 0, hi: 6 };
        assert_eq!(reference_linear_scaled(&[10, -8], &step), vec![28, -18]);
        assert_eq!(reference_step_scaled(&[10, -8], &step, &bx), vec![24, 0]);
        // and the boundary helper agrees with the reference's clamp
        assert_eq!(prox_clamp_scaled(28, &bx, 4), 24);
        assert_eq!(prox_clamp_scaled(-18, &bx, 4), 0);
    }

    #[test]
    fn prox_clamp_interior_is_identity() {
        let bx = ClampBox { lo: -5, hi: 5 };
        assert_eq!(prox_clamp_scaled(7, &bx, 2), 7); // 7 ∈ [−10, 10]
        assert_eq!(prox_clamp_scaled(-11, &bx, 2), -10);
        assert_eq!(prox_clamp_scaled(11, &bx, 2), 10);
    }
}
