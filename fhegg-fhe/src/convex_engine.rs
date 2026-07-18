//! The Private Convex Engine at T>1 — iterated `x ← prox(x − τ·A·x)` with a proven noise budget.
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §2. OWNED by the `convex_engine` lane.
//! Consumes `convex_step::{SignedCt, PublicLinearStep, convex_linear_step}` (T=1, already built + tested).
//! Depends on `metatheory/Bfv/Noise.lean`'s T-composition bound for `max_iterations_for_params`.
//!
//! ## How T>1 composes WITHOUT a rescale (the scaled-domain trick)
//!
//! `convex_step` computes ONE iteration in the `tau_den`-scaled domain:
//! `w = tau_den·x − tau_num·A·x = tau_den·(x − τAx)`. Exact BFV has no homomorphic
//! division, so we never descale: the linear map is HOMOGENEOUS, so feeding the
//! scaled state straight back in yields `tau_den^k · x_k` after `k` iterations —
//! exact integers all the way (BFV is exact; no rounding exists anywhere in this
//! loop). The caller decrypts `tau_den^T · x_T` and divides once, in the clear.
//! The price is geometric growth `tau_den^k`, paid out of the centered window
//! `[−(t−1)/2, (t−1)/2]` — and every op in the loop rides `convex_step`'s window
//! gate, so exhausting the window REFUSES (`WindowExceeded`), never aliases.
//!
//! ## The prox at T>1: a CERTIFIED IDENTITY, or a refusal (stated out loud)
//!
//! The box clamp is a comparison; additive BFV cannot compare under encryption,
//! and this signature carries no key material, so an ACTIVE clamp mid-loop is
//! impossible in this regime (the same fact `convex_step`'s module doc names —
//! its T=1 prox runs at the decrypt boundary; the encrypted-comparison machinery
//! is `mpc.rs`/threshold territory, a NAMED residual, not silently faked here).
//! What CAN be done soundly: per iteration, the engine checks the propagated
//! signed interval of every coordinate against the (scale-matched) box
//! `[tau_den^k·prox_lo, tau_den^k·prox_hi]`. If the interval is inside, the
//! clamp is PROVABLY the identity on every one of the 4096 slot-instances —
//! applying it is exact, and the iterate equals the true PDHG iterate. If the
//! interval sticks out, the clamp might bind and cannot be computed: the engine
//! REFUSES (`ProxNotCertifiedIdentity`, naming the iteration + coordinate),
//! never returns a silently-unclamped trajectory. So `convex_solve` solves the
//! class of programs whose box is certifiably inactive along the trajectory
//! (interval arithmetic is the certificate) and fails CLOSED outside it.
//!
//! ## The fused evaluation (why the loop does not call `convex_linear_step` verbatim)
//!
//! `convex_linear_step` evaluates `tau_den·x_i` and `−tau_num·A_ii·x_i` as two
//! separate terms, so its interval bookkeeping treats them as INDEPENDENT and
//! loses the diagonal correlation (for the demo program: `[−36, 90]` where the
//! true row bound is `[6, 48]`) — coarse enough to kill every T>1 certificate.
//! The loop here evaluates the SAME linear map with fused coefficients
//! `C = tau_den·I − tau_num·A` over the same `convex_step` primitives
//! (`signed_scale` + `signed_add`): mod-q the residues are IDENTICAL
//! (`c₁·x + c₂·x = (c₁+c₂)·x` exactly, in canonical form), and a tooth proves
//! the fused step BYTE-EQUAL to `convex_linear_step`'s ciphertexts — only the
//! declared-interval metadata is tighter (per-row exact interval arithmetic).
//!
//! ## The noise ceiling (the Bfv/Noise.lean T-composition coordination point)
//!
//! One linear step multiplies the per-coefficient noise bound by at most
//! `G = ‖tau_den·I − tau_num·A‖_∞` (the max row abs sum of the ACTUAL fused
//! coefficient matrix; scalar mul by public `c` is `|c|` repeated adds ⇒ noise
//! scales by ≤ `|c|`; adds sum — both exact in `Bfv.Noise`'s phase model via
//! `noiseAt_add`). T composed steps: `B_T = G^T · B_fresh`.
//! Decrypt stays exact while `SafeNoise` holds (`Bfv.Noise.decrypt_exact`):
//! `2t·B_T + 2(t−1)·r < q`. `max_iterations_for_params` returns the largest such
//! T for the DEPLOYED modulus (`q = 0xffffee001·0xffffc4001·0x1ffffe0001`, the
//! set every oracle test pins) with `B_fresh = 2^20` (the named fresh-noise
//! ASSUMPTION from `Bfv/Noise.lean`'s module doc — an input to the theorem, not
//! derived). COORDINATION CONSTANT for the noise-t-lean lane: `noise_after_T`
//! should prove exactly this recurrence shape (`B_{k+1} ≤ G·B_k`, closed form
//! `G^T·B_0`), and `T_gt_ceiling_fails` its failing side; the Rust formula here
//! is the emitted twin. `convex_solve` refuses `iterations > ceiling` BEFORE
//! touching any ciphertext (`NoiseBudgetExceeded`, fail-closed).
//!
//! ## NAMED residuals
//! * ACTIVE prox under encryption (a binding clamp) — needs comparison machinery
//!   (output-boundary MPC / threshold / PBS); refused, not approximated.
//! * The interval certificate is conservative: a program whose TRUE trajectory
//!   never touches the box can still be refused if interval arithmetic cannot
//!   prove it. Fail-closed by design.
//! * `noise_after_T` in Lean does not exist yet (noise-t-lean lane); the formula
//!   above is the coordinated constant, recorded in TESTQALOG for that lane.

use crate::convex_step::{signed_add, signed_scale, ConvexStepError, PublicLinearStep, SignedCt};
use std::fmt;

pub type Result<T> = std::result::Result<T, ConvexEngineError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConvexEngineError {
    NoiseBudgetExceeded {
        requested: u32,
        ceiling: u32,
    },
    DimMismatch,
    /// `prox_lo > prox_hi`.
    InvalidProxBox,
    /// The propagated interval of a coordinate leaves the scale-matched prox box:
    /// the clamp might BIND, and a binding clamp cannot be computed under
    /// additive encryption — refused, never silently skipped.
    ProxNotCertifiedIdentity {
        iteration: u32,
        coord: usize,
        lo: i64,
        hi: i64,
        box_lo: i128,
        box_hi: i128,
    },
    /// `tau_den^k` or the scaled box left i128 — the scaled domain is exhausted.
    ScaleOverflow,
    /// A refusal from the underlying `convex_step` op (window/compat/overflow).
    Step(ConvexStepError),
}

impl fmt::Display for ConvexEngineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoiseBudgetExceeded { requested, ceiling } => write!(
                f,
                "noise budget exceeded: T={requested} requested, proven-safe ceiling is {ceiling} \
                 (G^T·B_fresh would cross the Bfv/Noise.lean SafeNoise margin)"
            ),
            Self::DimMismatch => write!(f, "state/matrix dimension mismatch"),
            Self::InvalidProxBox => write!(f, "prox box has lo > hi"),
            Self::ProxNotCertifiedIdentity {
                iteration,
                coord,
                lo,
                hi,
                box_lo,
                box_hi,
            } => write!(
                f,
                "prox not certified identity at iteration {iteration}, coord {coord}: \
                 interval [{lo}, {hi}] is not inside the scaled box [{box_lo}, {box_hi}]; \
                 a binding clamp cannot be computed under additive encryption"
            ),
            Self::ScaleOverflow => write!(f, "tau_den^k overflowed the scaled domain"),
            Self::Step(e) => write!(f, "convex_step refused: {e}"),
        }
    }
}

impl std::error::Error for ConvexEngineError {}

/// The deployed ciphertext modulus `q = 0xffffee001 · 0xffffc4001 · 0x1ffffe0001`
/// (109 bits — the exact fhe.rs degree-4096 set `Bfv/Params.lean` pins as
/// `q4096`; a test asserts it equals the product of `bfv_lean::FOLD_MODULI`).
pub const Q4096: u128 = 0xffffee001 * 0xffffc4001 * 0x1ffffe0001;

/// The fresh-noise bound `B_fresh = 2^20` — the named ASSUMPTION from
/// `Bfv/Noise.lean`'s module doc (public-key fresh encryption; an input to the
/// margin theorems, not derived). The coordination constant with noise-t-lean.
pub const B_FRESH: u128 = 1 << 20;

/// The fused coefficient of state coordinate `j` in output row `i`:
/// `C_ij = tau_den·[i=j] − tau_num·A_ij` — the coefficient the loop actually
/// applies (see the module doc's fused-evaluation section). `None` if it does
/// not fit i128 intermediate arithmetic.
fn fused_coeff(step: &PublicLinearStep, i: usize, j: usize) -> Option<i128> {
    let diag: i128 = if i == j { i128::from(step.tau_den) } else { 0 };
    let prod = i128::from(step.tau_num).checked_mul(i128::from(step.a[i][j]))?;
    diag.checked_sub(prod)
}

/// The per-iteration noise growth factor `G = ‖tau_den·I − tau_num·A‖_∞`
/// (max row abs sum of the ACTUAL fused coefficient matrix — the coordination
/// constant with Bfv/Noise.lean's `noise_after_T`).
/// `None` on arithmetic overflow or a degenerate step (`tau_den = 0`).
fn growth_factor(step: &PublicLinearStep) -> Option<u128> {
    if step.tau_den == 0 {
        return None;
    }
    let d = step.a.len();
    let mut max_row: u128 = 0;
    for i in 0..d {
        if step.a[i].len() != d {
            return None;
        }
        let mut row_sum: u128 = 0;
        for j in 0..d {
            row_sum = row_sum.checked_add(fused_coeff(step, i, j)?.unsigned_abs())?;
        }
        max_row = max_row.max(row_sum);
    }
    // d = 0 (or A = tau_den·I/tau_num exactly): G could be 0; noise then cannot
    // grow, treat as the G ≤ 1 identity-class in the ceiling.
    Some(max_row)
}

/// `SafeNoise` from `Bfv/Noise.lean`, on the deployed modulus: `2t·B + 2(t−1)·r < q`,
/// with `r = q mod t`. Checked arithmetic; overflow counts as UNSAFE (fail closed).
fn safe_noise(t: u64, b: u128) -> bool {
    if t < 2 {
        return false;
    }
    let t = u128::from(t);
    let r = Q4096 % t;
    let lhs = (|| {
        let noise_term = 2u128.checked_mul(t)?.checked_mul(b)?;
        let residue_term = 2u128.checked_mul(t - 1)?.checked_mul(r)?;
        noise_term.checked_add(residue_term)
    })();
    matches!(lhs, Some(s) if s < Q4096)
}

/// The proven-safe iteration ceiling for these params: the largest `T` with
/// `SafeNoise(G^T · B_fresh)` on the deployed modulus (the `Bfv/Noise.lean`
/// T-composition bound, Rust-side twin — see the module doc's coordination
/// constant). Degenerate params (t < 2, tau_den = 0, overflowing G) → 0.
pub fn max_iterations_for_params(step: &PublicLinearStep, t: u64) -> u32 {
    let Some(g) = growth_factor(step) else {
        return 0;
    };
    if !safe_noise(t, B_FRESH) {
        return 0;
    }
    if g <= 1 {
        // G ≤ 1 ⇔ every row of C = tau_den·I − tau_num·A has abs sum ≤ 1 (the
        // identity map and its sub-cases): noise does not grow, no T is unsafe.
        return u32::MAX;
    }
    let mut b = B_FRESH;
    let mut ceiling: u32 = 0;
    while ceiling < u32::MAX {
        let Some(nb) = b.checked_mul(g) else { break };
        if !safe_noise(t, nb) {
            break;
        }
        b = nb;
        ceiling += 1;
    }
    ceiling
}

/// The domain scale after `iterations` steps: `tau_den^iterations` (the factor
/// the caller divides out at the decrypt boundary). `None` if it leaves i128.
/// Helper, not part of the frozen contract surface.
pub fn solve_scale(step: &PublicLinearStep, iterations: u32) -> Option<i128> {
    let mut s: i128 = 1;
    for _ in 0..iterations {
        s = s.checked_mul(i128::from(step.tau_den))?;
    }
    Some(s)
}

/// ONE homomorphic linear step `w = (tau_den·I − tau_num·A)·x`, evaluated with
/// FUSED per-row coefficients over the `convex_step` primitives. Mod-q this is
/// the SAME map `convex_linear_step` computes (byte-equal — proven by the
/// `fused_step_byte_equals_convex_linear_step` tooth); the difference is the
/// interval metadata: one scalar mul per state coordinate per row, so the
/// declared interval is the exact per-row interval-arithmetic bound, keeping
/// the diagonal correlation `convex_linear_step`'s two-term evaluation loses.
fn fused_linear_step(x: &[SignedCt], step: &PublicLinearStep, t: u64) -> Result<Vec<SignedCt>> {
    if step.tau_den == 0 {
        return Err(ConvexEngineError::Step(ConvexStepError::ZeroDenominator));
    }
    let d = x.len();
    let wrap = |e: ConvexStepError| match e {
        ConvexStepError::Dimension(_) => ConvexEngineError::DimMismatch,
        other => ConvexEngineError::Step(other),
    };
    let mut out = Vec::with_capacity(d);
    for i in 0..d {
        let coeff = |j: usize| -> Result<i64> {
            let c = fused_coeff(step, i, j).ok_or(ConvexEngineError::Step(
                ConvexStepError::ConstantOverflow("tau_num·A_ij overflows i128"),
            ))?;
            i64::try_from(c).map_err(|_| {
                ConvexEngineError::Step(ConvexStepError::ConstantOverflow(
                    "fused coefficient tau_den·[i=j] − tau_num·A_ij overflows i64",
                ))
            })
        };
        // acc = C_ii·x_i (the fused diagonal — the whole point).
        let mut acc = signed_scale(&x[i], coeff(i)?, t).map_err(wrap)?;
        for (j, xj) in x.iter().enumerate() {
            if j == i {
                continue;
            }
            let c = coeff(j)?;
            if c == 0 {
                continue;
            }
            let term = signed_scale(xj, c, t).map_err(wrap)?;
            acc = signed_add(&acc, &term, t).map_err(wrap)?;
        }
        out.push(acc);
    }
    Ok(out)
}

/// T iterations of x ← prox(x − τ·A·x). Refuses fail-closed when T exceeds the proven-safe ceiling.
///
/// Returns the state in the `tau_den^T`-scaled domain (see the module doc): decrypt,
/// center, and divide by [`solve_scale`] to read `x_T`. The prox is applied per
/// iteration as a CERTIFIED identity (interval ⊆ scale-matched box) — a clamp
/// that could bind is a refusal, never a silent skip.
pub fn convex_solve(
    x0: &[SignedCt],
    step: &PublicLinearStep,
    prox_lo: i64,
    prox_hi: i64,
    iterations: u32,
    t: u64,
) -> Result<Vec<SignedCt>> {
    // 1. The noise-budget gate, BEFORE any ciphertext work (fail-closed).
    let ceiling = max_iterations_for_params(step, t);
    if iterations > ceiling {
        return Err(ConvexEngineError::NoiseBudgetExceeded {
            requested: iterations,
            ceiling,
        });
    }
    if prox_lo > prox_hi {
        return Err(ConvexEngineError::InvalidProxBox);
    }
    let d = x0.len();
    if d == 0 || step.a.len() != d || step.a.iter().any(|row| row.len() != d) {
        return Err(ConvexEngineError::DimMismatch);
    }

    let mut x: Vec<SignedCt> = x0.to_vec();
    let mut scale: i128 = 1; // tau_den^k after k iterations
    for k in 0..iterations {
        // 2. The homomorphic linear step (public-constant scalar muls + adds only;
        //    every op window-gated by convex_step — exhaustion refuses, never aliases).
        let w = fused_linear_step(&x, step, t)?;
        scale = scale
            .checked_mul(i128::from(step.tau_den))
            .ok_or(ConvexEngineError::ScaleOverflow)?;

        // 3. The prox, as a certified identity in the scaled domain.
        let box_lo = i128::from(prox_lo)
            .checked_mul(scale)
            .ok_or(ConvexEngineError::ScaleOverflow)?;
        let box_hi = i128::from(prox_hi)
            .checked_mul(scale)
            .ok_or(ConvexEngineError::ScaleOverflow)?;
        for (i, wi) in w.iter().enumerate() {
            let (lo, hi) = wi.interval();
            if i128::from(lo) < box_lo || i128::from(hi) > box_hi {
                return Err(ConvexEngineError::ProxNotCertifiedIdentity {
                    iteration: k + 1,
                    coord: i,
                    lo,
                    hi,
                    box_lo,
                    box_hi,
                });
            }
        }
        x = w;
    }
    Ok(x)
}

/// CLEARTEXT REFERENCE for the FULL T-iteration solve, in the scaled domain:
/// the exact plaintext PDHG the differential tooth compares against. Applies
/// the box clamp per iteration (scale-matched), exactly as the true iteration
/// does. One instance (one slot across the d coordinates), exact i128 integers.
pub fn reference_solve_scaled(
    x0: &[i64],
    step: &PublicLinearStep,
    prox_lo: i64,
    prox_hi: i64,
    iterations: u32,
) -> Vec<i128> {
    let d = x0.len();
    let mut x: Vec<i128> = x0.iter().map(|&v| i128::from(v)).collect();
    let mut scale: i128 = 1;
    for _ in 0..iterations {
        scale *= i128::from(step.tau_den);
        let w: Vec<i128> = (0..d)
            .map(|i| {
                let ax: i128 = (0..d).map(|j| i128::from(step.a[i][j]) * x[j]).sum();
                i128::from(step.tau_den) * x[i] - i128::from(step.tau_num) * ax
            })
            .collect();
        let (blo, bhi) = (i128::from(prox_lo) * scale, i128::from(prox_hi) * scale);
        x = w.into_iter().map(|v| v.clamp(blo, bhi)).collect();
    }
    x
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::additive::pick_params;
    use crate::bfv_lean::{LeanCiphertext, FOLD_DEGREE, FOLD_MODULI};
    use crate::convex_step::{center, encode_signed};
    use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
    use fhe_traits::{
        DeserializeParametrized, FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize,
    };
    use rand_09::rngs::StdRng;
    use rand_09::{Rng, SeedableRng};
    use std::sync::Arc;

    /// The demo convex program (a REAL 2-asset portfolio rebalance, expressed as
    /// the homogeneous augmented system — see the differential test's doc):
    /// state (x₁, x₂, s) with s the constant-1 coordinate,
    /// objective ½(x−p)ᵀQ(x−p) + ½λ(1ᵀx − B)², Q = [[2,1],[1,2]], λ = 1,
    /// target p = (6, 8), budget B = 14 ⇒ minimizer x* = p (interior).
    /// τ = 1/4; L(Q + λ11ᵀ) = 5 < 2/τ = 8 ⇒ contraction.
    fn demo_step() -> PublicLinearStep {
        // M = Q + λ·11ᵀ = [[3,2],[2,3]]; c = Qp + λB·1 = (34, 36).
        // Augmented rows: [M | −c]; the s row is zero (s just rides the scale).
        PublicLinearStep {
            a: vec![vec![3, 2, -34], vec![2, 3, -36], vec![0, 0, 0]],
            tau_num: 1,
            tau_den: 4,
        }
    }
    const DEMO_TARGET: [i64; 2] = [6, 8];
    const DEMO_BOX: (i64, i64) = (-4, 16); // contains the trajectory AND s = 1

    struct Fixture {
        params: Arc<BfvParameters>,
        sk: SecretKey,
        pk: PublicKey,
        rng: StdRng,
        t: u64,
    }

    fn fixture(seed: u64) -> Fixture {
        let params = pick_params(20);
        assert_eq!(params.degree(), FOLD_DEGREE, "degree drifted");
        assert_eq!(params.moduli(), &FOLD_MODULI, "RNS moduli drifted");
        let t = params.plaintext();
        let mut rng = StdRng::seed_from_u64(seed);
        let sk = SecretKey::random(&params, &mut rng);
        let pk = PublicKey::new(&sk, &mut rng);
        Fixture {
            params,
            sk,
            pk,
            rng,
            t,
        }
    }

    fn encrypt_signed(fx: &mut Fixture, vals: &[i64], lo: i64, hi: i64) -> SignedCt {
        let t = fx.t;
        let slots: Vec<u64> = vals.iter().map(|&v| encode_signed(v, t)).collect();
        let pt = Plaintext::try_encode(&slots, Encoding::simd(), &fx.params).expect("simd encode");
        let ct = fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt");
        let lean = LeanCiphertext::from_fhe_bytes(
            &ct.to_bytes(),
            fx.params.moduli(),
            fx.params.degree(),
            0,
        )
        .expect("parse fhe.rs ciphertext");
        SignedCt::new(lean, lo, hi, t).expect("interval inside the window")
    }

    fn decrypt_centered(fx: &Fixture, s: &SignedCt, k: usize) -> Vec<i64> {
        let ct = Ciphertext::from_bytes(&s.ciphertext().to_fhe_bytes(), &fx.params)
            .expect("fhe.rs accepts our bytes");
        let pt = fx.sk.try_decrypt(&ct).expect("fhe.rs decrypt");
        let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode");
        v[..k].iter().map(|&m| center(m, fx.t)).collect()
    }

    /// The deployed-modulus constant is the REAL one: Q4096 == Π FOLD_MODULI,
    /// tying the noise ceiling to the exact set every oracle test pins.
    #[test]
    fn q4096_is_the_product_of_the_deployed_moduli() {
        let prod: u128 = FOLD_MODULI.iter().map(|&m| u128::from(m)).product();
        assert_eq!(Q4096, prod);
        assert_eq!(
            Q4096 % 1_032_193,
            843_789,
            "r drifted from Bfv/Params.lean's pin"
        );
    }

    /// The ceiling is exactly the largest T with SafeNoise(G^T·B_fresh) —
    /// re-derived here from first principles (independent pow loop), and both
    /// sides of the boundary are checked: safe AT the ceiling, unsafe ONE past.
    #[test]
    fn ceiling_matches_first_principles_on_both_sides() {
        let step = demo_step();
        let t: u64 = 1_032_193;
        // C = 4I − A = [[1,−2,34],[−2,1,36],[0,0,4]]: row abs sums (37, 39, 4) ⇒ G = 39.
        let g: u128 = 39;
        let ceiling = max_iterations_for_params(&step, t);
        assert!(
            ceiling > 0,
            "deployed params must admit at least one iteration"
        );
        let b_at = |tt: u32| -> u128 { B_FRESH * g.pow(tt) };
        let safe = |b: u128| {
            let r = Q4096 % u128::from(t);
            2 * u128::from(t) * b + 2 * (u128::from(t) - 1) * r < Q4096
        };
        assert!(safe(b_at(ceiling)), "must be safe AT the ceiling");
        assert!(
            !safe(b_at(ceiling + 1)),
            "must be unsafe ONE past the ceiling"
        );
    }

    /// G = 1 (identity map): noise never grows, no T is unsafe.
    #[test]
    fn identity_map_has_unbounded_ceiling_and_degenerates_refuse() {
        let ident = PublicLinearStep {
            a: vec![vec![0]],
            tau_num: 1,
            tau_den: 1,
        };
        assert_eq!(max_iterations_for_params(&ident, 1_032_193), u32::MAX);
        // degenerate params fail closed
        let bad = PublicLinearStep {
            a: vec![vec![1]],
            tau_num: 1,
            tau_den: 0,
        };
        assert_eq!(max_iterations_for_params(&bad, 1_032_193), 0);
        assert_eq!(max_iterations_for_params(&demo_step(), 1), 0);
    }

    /// THE FUSION-IS-NOT-A-FORK TOOTH: the fused-coefficient step is BYTE-EQUAL
    /// to the already-oracle-anchored `convex_linear_step` (same mod-q map,
    /// same serialization), so the T=1 fhe.rs anchor carries over to this loop
    /// verbatim — and the fused interval is strictly TIGHTER (⊆), which is the
    /// entire reason the fused evaluation exists.
    #[test]
    fn fused_step_byte_equals_convex_linear_step() {
        use crate::convex_step::convex_linear_step;
        let mut fx = fixture(0xCE05);
        let t = fx.t;
        let step = demo_step();
        let state = vec![
            encrypt_signed(&mut fx, &[12, 3, 0, 14], 0, 14),
            encrypt_signed(&mut fx, &[2, 11, 14, 0], 0, 14),
            encrypt_signed(&mut fx, &[1, 1, 1, 1], 1, 1),
        ];
        let fused = fused_linear_step(&state, &step, t).expect("fused step in window");
        let theirs = convex_linear_step(&state, &step, t).expect("reference step in window");
        assert_eq!(fused.len(), theirs.len());
        for (i, (f, th)) in fused.iter().zip(theirs.iter()).enumerate() {
            assert_eq!(
                f.ciphertext().to_fhe_bytes(),
                th.ciphertext().to_fhe_bytes(),
                "fused evaluation FORKED the ciphertext at coord {i}"
            );
            let (fl, fh) = f.interval();
            let (tl, th_) = th.interval();
            assert!(
                fl >= tl && fh <= th_,
                "fused interval not tighter at coord {i}"
            );
        }
        // and strictly tighter somewhere, or the fusion is pointless:
        assert!(
            fused
                .iter()
                .zip(theirs.iter())
                .any(|(f, th)| f.interval() != th.interval()),
            "fusion gained nothing — the coarse path would have certified too"
        );
        // decrypt differential on top: both decrypt to the same values (the map is the map)
        let df = decrypt_centered(&fx, &fused[0], 4);
        let dt = decrypt_centered(&fx, &theirs[0], 4);
        assert_eq!(df, dt);
    }

    /// THE LOAD-BEARING TOOTH — the FULL T=5 solve under FHE, differentially
    /// vs the plaintext PDHG on a REAL convex program: a 2-asset portfolio
    /// rebalance min ½(x−p)ᵀQ(x−p) + ½λ(1ᵀx−B)² over the box, target p=(6,8),
    /// run on 4096 INDEPENDENT slot-instances at once (random holdings each).
    /// The FHE x_T must decrypt EXACTLY (BFV is exact — no tolerance) to the
    /// cleartext same-iteration trajectory, and must have CONVERGED toward the
    /// target (squared-ℓ2 deviation strictly shrinks) — i.e. a real convex
    /// solve happened under encryption, not an identity shuffle.
    #[test]
    fn differential_portfolio_rebalance_vs_plaintext_pdhg_all_4096_instances() {
        let mut fx = fixture(0xCE01);
        let t = fx.t;
        let step = demo_step();
        let (blo, bhi) = DEMO_BOX;
        let iterations: u32 = 5;
        let n = FOLD_DEGREE;

        // random initial holdings x0 ∈ [0, 14]² per slot; s = 1 in every slot.
        let mut gen = StdRng::seed_from_u64(0x9EBA1A);
        let coords: Vec<Vec<i64>> = (0..2)
            .map(|_| (0..n).map(|_| gen.random_range(0..=14)).collect())
            .collect();
        let ones: Vec<i64> = vec![1; n];

        let state = vec![
            encrypt_signed(&mut fx, &coords[0], 0, 14),
            encrypt_signed(&mut fx, &coords[1], 0, 14),
            encrypt_signed(&mut fx, &ones, 1, 1),
        ];

        let out = convex_solve(&state, &step, blo, bhi, iterations, t)
            .expect("T=5 is inside the ceiling and the box is certified");
        assert_eq!(out.len(), 3);

        let scale = solve_scale(&step, iterations).expect("scale fits");
        assert_eq!(scale, 1024); // 4^5

        let dec: Vec<Vec<i64>> = out.iter().map(|s| decrypt_centered(&fx, s, n)).collect();

        let mut moved = 0usize;
        for s in 0..n {
            let x0 = [coords[0][s], coords[1][s], 1];
            let want = reference_solve_scaled(&x0, &step, blo, bhi, iterations);
            for i in 0..3 {
                assert_eq!(
                    i128::from(dec[i][s]),
                    want[i],
                    "FHE x_T diverged from plaintext PDHG at instance {s}, coord {i}"
                );
            }
            // the s coordinate must ride the scale exactly: s_T = tau_den^T
            assert_eq!(i128::from(dec[2][s]), scale);
            // convergence toward the target (scaled squared ℓ2): a real solve.
            let dev_t: i128 = (0..2)
                .map(|i| {
                    let d = i128::from(dec[i][s]) - scale * i128::from(DEMO_TARGET[i]);
                    d * d
                })
                .sum();
            let dev_0: i128 = (0..2)
                .map(|i| {
                    let d = scale * (i128::from(x0[i]) - i128::from(DEMO_TARGET[i]));
                    d * d
                })
                .sum();
            assert!(dev_t <= dev_0, "instance {s} moved AWAY from the target");
            if dev_0 > 0 {
                assert!(
                    dev_t < dev_0,
                    "instance {s} with off-target start did not converge"
                );
                moved += 1;
            }
        }
        assert!(
            moved > 4000,
            "almost every random instance starts off-target"
        );
    }

    /// THE REFUSAL TOOTH (mutation target): one past the ceiling is refused
    /// LOUDLY, with the ceiling named, BEFORE any ciphertext work — and the
    /// refusal is not over-broad (the same call one below the boundary gets
    /// past the noise gate; on this program it then hits the WINDOW gate, a
    /// different named refusal, proving the two budgets are independent teeth).
    #[test]
    fn over_ceiling_t_is_refused_fail_closed() {
        let mut fx = fixture(0xCE02);
        let t = fx.t;
        let step = demo_step();
        let ceiling = max_iterations_for_params(&step, t);
        assert_eq!(ceiling, 12, "G=45 on the deployed set: ceiling drifted");

        let state = vec![
            encrypt_signed(&mut fx, &[12], 0, 14),
            encrypt_signed(&mut fx, &[2], 0, 14),
            encrypt_signed(&mut fx, &[1], 1, 1),
        ];
        match convex_solve(&state, &step, DEMO_BOX.0, DEMO_BOX.1, ceiling + 1, t) {
            Err(ConvexEngineError::NoiseBudgetExceeded {
                requested,
                ceiling: c,
            }) => {
                assert_eq!(requested, ceiling + 1);
                assert_eq!(c, ceiling);
            }
            other => panic!("expected NoiseBudgetExceeded, got {other:?}"),
        }
        // At T = 8 the noise gate passes (8 ≤ 12) but tau_den^8·x exhausts the
        // centered window: convex_step refuses (WindowExceeded) — fail-closed
        // composition, no silent aliasing. Independent gates, both biting.
        match convex_solve(&state, &step, DEMO_BOX.0, DEMO_BOX.1, 8, t) {
            Err(ConvexEngineError::Step(ConvexStepError::WindowExceeded { .. })) => {}
            other => panic!("expected Step(WindowExceeded) at T=8, got {other:?}"),
        }
        // and T = 5 (the differential test's depth) is inside BOTH budgets.
        assert!(convex_solve(&state, &step, DEMO_BOX.0, DEMO_BOX.1, 5, t).is_ok());
    }

    /// THE PROX-REFUSAL TOOTH: a box the interval cannot be certified inside
    /// is REFUSED (named, with the iteration + coordinate), not silently
    /// unclamped — the engine never returns a trajectory whose clamp might
    /// have needed to bind.
    #[test]
    fn prox_that_could_bind_is_refused_not_skipped() {
        let mut fx = fixture(0xCE03);
        let t = fx.t;
        let step = demo_step();
        let state = vec![
            encrypt_signed(&mut fx, &[12], 0, 14),
            encrypt_signed(&mut fx, &[2], 0, 14),
            encrypt_signed(&mut fx, &[1], 1, 1),
        ];
        // Box [0, 10]: after one step w₁'s interval is [6, 48] ⊄ 4·[0, 10].
        match convex_solve(&state, &step, 0, 10, 3, t) {
            Err(ConvexEngineError::ProxNotCertifiedIdentity {
                iteration, coord, ..
            }) => {
                assert_eq!(iteration, 1);
                assert_eq!(coord, 0);
            }
            other => panic!("expected ProxNotCertifiedIdentity, got {other:?}"),
        }
        // Not over-broad: the demo box certifies the same program (T=1).
        assert!(convex_solve(&state, &step, DEMO_BOX.0, DEMO_BOX.1, 1, t).is_ok());
        // And the reference oracle CONFIRMS the refusal was load-bearing: the
        // plaintext trajectory under box [0,10] genuinely clamps (differs from
        // the unclamped one), so skipping the clamp would have been WRONG.
        let unclamped = reference_solve_scaled(&[12, 2, 1], &step, DEMO_BOX.0, DEMO_BOX.1, 1);
        let clamped = reference_solve_scaled(&[12, 2, 1], &step, 0, 10, 1);
        assert_ne!(
            unclamped, clamped,
            "the refused clamp would have been a no-op — toothless case"
        );
    }

    /// Shape/validation refusals: empty state, non-square A, inverted box, T=0.
    #[test]
    fn validation_refusals_and_t0_identity() {
        let mut fx = fixture(0xCE04);
        let t = fx.t;
        let step = demo_step();
        let x1 = encrypt_signed(&mut fx, &[3], 0, 14);
        assert_eq!(
            convex_solve(&[], &step, -4, 16, 1, t),
            Err(ConvexEngineError::DimMismatch)
        );
        assert_eq!(
            convex_solve(&[x1.clone()], &step, -4, 16, 1, t),
            Err(ConvexEngineError::DimMismatch),
            "d=1 state against the 3x3 demo matrix must refuse"
        );
        assert_eq!(
            convex_solve(&[x1.clone()], &step, 16, -4, 1, t),
            Err(ConvexEngineError::InvalidProxBox)
        );
        // T = 0: the solve is the identity (returns x0's ciphertexts unchanged).
        let ident = PublicLinearStep {
            a: vec![vec![0]],
            tau_num: 1,
            tau_den: 1,
        };
        let out = convex_solve(&[x1.clone()], &ident, -4, 16, 0, t).expect("T=0 is trivial");
        assert_eq!(out[0], x1);
    }
}
