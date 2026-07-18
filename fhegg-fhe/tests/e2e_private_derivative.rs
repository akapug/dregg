//! E2E INTEGRATION PROOF — one REAL private derivative, end to end.
//! Contract: `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §5 (this file is the north-star test).
//! OWNED by the `e2e` lane. Codes against the FROZEN signatures of §1 (threshold),
//! §2 (convex_engine), §4 (fhir). While those modules are `todo!()` stubs, the
//! integration test PANICS at the first unimplemented call — expected; it goes
//! green as the lanes land. The PLAINTEXT REFERENCE is a standalone passing
//! test TODAY (see `reference_*` below), so the ground truth is verified before
//! the FHE path exists.
//!
//! # The derivative: a 2-asset portfolio rebalance (a real small convex program)
//!
//! Holdings `h`, target weights `w*` (both sum to the budget). Rebalance =
//!
//! ```text
//!   minimize   ½‖x − w*‖²  +  (ρ/2)·(1ᵀx − budget)²      (tracking error + budget penalty)
//!   subject to x within position limits (a box)
//! ```
//!
//! The frozen `PublicLinearStep` carries ONLY a matrix `A` (no affine term), so
//! we solve in the SHIFTED variable `y = x − w*` (public shift; `1ᵀw* = budget`):
//!
//! ```text
//!   ∇f(y) = y + ρ·1(1ᵀy) = (I + ρ·11ᵀ)·y  =  A·y        — purely linear!
//!   A = I + ρ·11ᵀ  =  [[2,1],[1,2]]  for d = 2, ρ = 1
//! ```
//!
//! and iterate the contract's kernel `y ← prox(y − τ·A·y)` with `prox` the box
//! clamp `[LO, HI] = [−15, 15]` (position limit: |x_i − w*_i| ≤ 15). Constants:
//!
//! * `τ = TAU_NUM/TAU_DEN = 1/4` — eigenvalues of A are {1, 3}; τ < 2/3 converges.
//! * start `h = (84, 16)`, target `w* = (60, 40)` ⇒ `y0 = (24, −24)`, along the
//!   eigenvector `(1,−1)` (eigenvalue 1 ⇒ exact contraction 1 − τ = 3/4 per step),
//!   and OUTSIDE the box, so the prox genuinely clamps at iteration 1. The whole
//!   trajectory is hand-computable and asserted exactly (see the hand-check test).
//!
//! # The scaling convention (pinned here for the convex_engine lane)
//!
//! Division is impossible under FHE, so iterate k carries the state at scale
//! `TAU_DEN^k` and every step is EXACT integer arithmetic:
//!
//! ```text
//!   s_0 = y_0                                       (scale 1)
//!   s_{k+1} = clamp(TAU_DEN·s_k − TAU_NUM·A·s_k,    (scale TAU_DEN^{k+1})
//!                   LO·TAU_DEN^{k+1}, HI·TAU_DEN^{k+1})
//! ```
//!
//! `s_T / TAU_DEN^T` IS the rational PDHG iterate `y_T`, exactly — no rounding
//! anywhere. The FHE path must decrypt to `s_T` bit-for-bit (`convex_step`'s
//! T=1 oracle test already pins this convention for one step; `prox_lo/prox_hi`
//! in `convex_solve` are therefore UNSCALED original units, the engine scales
//! the clamp bounds internally per iteration).
//!
//! T_E2E = 6 is chosen so every intermediate fits the signed centered window of
//! t = 1_032_193 (proved by `reference_window_feasibility_for_t` below).

use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::convex_engine::{self, ConvexEngineError};
use fhegg_fhe::convex_step::{center, centered_window, PublicLinearStep, SignedCt};
use fhegg_fhe::fhir::{self, Program, Tier};
use fhegg_fhe::threshold::{self, BfvParams, CollectivePublicKey, ThresholdError};

// ---------------------------------------------------------------------------
// The rebalance instance (shared by the reference tests and the FHE e2e).
// ---------------------------------------------------------------------------

/// The deployed fold plaintext modulus (asserted against fhe.rs in the oracle tests).
const PLAINTEXT_MODULUS: u64 = 1_032_193;
/// d = 2 assets. A = I + ρ·11ᵀ, ρ = 1: tracking error + budget penalty (see module docs).
const A_REBALANCE: [[i64; 2]; 2] = [[2, 1], [1, 2]];
/// τ = 1/4.
const TAU_NUM: u64 = 1;
const TAU_DEN: u64 = 4;
/// Position-limit box on y = x − w*: |x_i − w*_i| ≤ 15.
const BOX_LO: i64 = -15;
const BOX_HI: i64 = 15;
/// Target weights and starting holdings (budget 100).
const TARGET: [i64; 2] = [60, 40];
const HOLDINGS: [i64; 2] = [84, 16];
/// y0 = holdings − target = (24, −24).
const Y0: [i64; 2] = [24, -24];
/// FHE iteration depth — chosen to fit the signed window (feasibility test below).
const T_E2E: u32 = 6;
/// n-of-n quorum size for the collective key.
const QUORUM_N: usize = 3;
/// Smudging noise bits for partial decrypts. PLACEHOLDER pending the exported
/// bound from `metatheory/Bfv/Smudging.lean` (§1b) — the REAL value must be the
/// proven bound for these params, not this constant. Named in TESTQALOG.
const SMUDGE_BITS: u32 = 64;

fn rebalance_step() -> PublicLinearStep {
    PublicLinearStep {
        a: A_REBALANCE.iter().map(|r| r.to_vec()).collect(),
        tau_num: TAU_NUM,
        tau_den: TAU_DEN,
    }
}

// ---------------------------------------------------------------------------
// THE PLAINTEXT REFERENCE — exact scaled-integer PDHG, verified standalone NOW.
// ---------------------------------------------------------------------------

/// T iterations of `y ← clamp(y − τ·A·y, lo, hi)` carried EXACTLY at scale
/// `tau_den^k` (see module docs). Returns `s_T`; `s_T / tau_den^T == y_T` as
/// rationals, with zero rounding. This is the ground truth the FHE `convex_solve`
/// result must decrypt to bit-for-bit.
fn reference_solve_scaled(
    y0: &[i64],
    step: &PublicLinearStep,
    lo: i64,
    hi: i64,
    iterations: u32,
) -> Vec<i128> {
    let d = y0.len();
    assert!(d > 0 && step.a.len() == d && step.a.iter().all(|r| r.len() == d));
    let mut s: Vec<i128> = y0.iter().map(|&v| i128::from(v)).collect();
    let mut scale: i128 = 1;
    for _ in 0..iterations {
        // w = tau_den·s − tau_num·A·s   (exact; scale becomes scale·tau_den)
        let w: Vec<i128> = (0..d)
            .map(|i| {
                let ax: i128 = (0..d).map(|j| i128::from(step.a[i][j]) * s[j]).sum();
                i128::from(step.tau_den) * s[i] - i128::from(step.tau_num) * ax
            })
            .collect();
        scale = scale
            .checked_mul(i128::from(step.tau_den))
            .expect("scale overflow: T too deep for the i128 reference");
        let (blo, bhi) = (i128::from(lo) * scale, i128::from(hi) * scale);
        s = w.into_iter().map(|wi| wi.clamp(blo, bhi)).collect();
    }
    s
}

/// The reference trajectory's PRE-clamp interval bound at each iteration —
/// used to prove the chosen (t, T) pair fits `SignedCt`'s centered window.
/// Input interval [−B, B] ⇒ step output bound (tau_den + tau_num·max_row_abs_sum)·B.
fn preclamp_bound(b: i128, step: &PublicLinearStep) -> i128 {
    let row_sum: i128 = step
        .a
        .iter()
        .map(|r| r.iter().map(|&c| i128::from(c.unsigned_abs() as u64)).sum())
        .max()
        .unwrap();
    (i128::from(step.tau_den) + i128::from(step.tau_num) * row_sum) * b
}

// ---------------------------------------------------------------------------
// STANDALONE PASSING TESTS — the reference is verified before the FHE path.
// ---------------------------------------------------------------------------

/// The trajectory, hand-computed (module docs): y0 = 24·(1,−1) is an eigenvector
/// of A with eigenvalue 1, so the unclamped step is exactly ×3 in scaled units
/// (4c − 1·c = 3c) while the scale grows ×4 — contraction 3/4. Iteration 1
/// CLAMPS (72 > 60 = 15·4). Every value below is derived by hand, so this test
/// fails on ANY error in A, τ, the clamp, or the scaling convention:
///   k=1: w=72·(1,−1), box ±60      → s1 = ( 60, −60)   [PROX BITES]
///   k=2: w=180, box ±240 (inactive) → s2 = (180, −180)
///   k=3: 540 · k=4: 1620 · k=5: 4860 · k=6: s6 = (14580, −14580), scale 4096
///   (y6 = 14580/4096 = 3645/1024 ≈ 3.56 → x6 ≈ (63.56, 36.44), en route to (60,40))
#[test]
fn reference_hand_checked_trajectory() {
    let step = rebalance_step();
    // The shift is the load-bearing trick (module docs): y0 = holdings − target,
    // and the budget-penalty gradient is linear ONLY because 1ᵀ·target = budget.
    for i in 0..2 {
        assert_eq!(Y0[i], HOLDINGS[i] - TARGET[i]);
    }
    assert_eq!(HOLDINGS.iter().sum::<i64>(), TARGET.iter().sum::<i64>());
    assert_eq!(
        reference_solve_scaled(&Y0, &step, BOX_LO, BOX_HI, 1),
        vec![60, -60],
        "iteration 1 must CLAMP 72 → 60 (the prox is active)"
    );
    assert_eq!(
        reference_solve_scaled(&Y0, &step, BOX_LO, BOX_HI, T_E2E),
        vec![14580, -14580],
        "hand-computed s6 at scale 4^6 = 4096"
    );
    // The prox tooth, in-test: with the box removed the same step does NOT clamp,
    // so the trajectories genuinely differ — the clamp is doing real work.
    assert_eq!(
        reference_solve_scaled(&Y0, &step, i64::MIN / 4, i64::MAX / 4, 1),
        vec![72, -72],
        "unclamped iteration 1 is 72 — differs from the clamped 60"
    );
}

/// Convergence: the rebalance actually REBALANCES. After T = 20 iterations
/// |y_T| = 15·(3/4)^19 ≈ 0.063 < 0.1, i.e. the allocation is within 0.1 units
/// of the target (60, 40) — asserted exactly in scaled integers (10·|s| < scale).
#[test]
fn reference_converges_to_target_allocation() {
    let step = rebalance_step();
    let t_iters = 20u32;
    let s = reference_solve_scaled(&Y0, &step, BOX_LO, BOX_HI, t_iters);
    let scale = i128::from(TAU_DEN).pow(t_iters);
    for (i, &si) in s.iter().enumerate() {
        assert!(
            10 * si.abs() < scale,
            "asset {i}: |y_T| = {si}/{scale} not within 0.1 of target"
        );
    }
    // And it moved: y0 was 24 units off target, y_T is < 0.1 off.
    assert!(s[0].abs() * 240 < scale * i128::from(Y0[0].abs()));
}

/// The budget penalty works: from a budget-VIOLATING start (1ᵀy0 = 16 ≠ 0),
/// 1ᵀA = 3·1ᵀ (column sums 3) makes the scaled sum an exact invariant of the
/// unclamped step (4·Σs − 1·3·Σs = Σs) while the scale grows ×4 — so the
/// unscaled budget violation decays ×1/4 per iteration, to < 0.001 by k = 8.
#[test]
fn reference_budget_penalty_restores_budget() {
    let step = rebalance_step();
    let y0 = [10i64, 6]; // inside the box; clamp stays inactive (checked below)
    for k in 1..=8u32 {
        let s = reference_solve_scaled(&y0, &step, BOX_LO, BOX_HI, k);
        let sum: i128 = s.iter().sum();
        assert_eq!(sum, 16, "scaled budget-violation invariant broke at k={k}");
        // clamp inactive on this trajectory: the unbounded run is identical
        assert_eq!(
            s,
            reference_solve_scaled(&y0, &step, i64::MIN / 4, i64::MAX / 4, k)
        );
    }
    // violation after 8 iters = 16/4^8 < 0.001 of the budget — restored.
    assert!(16 * 1000 < i128::from(TAU_DEN).pow(8));
}

/// Feasibility of the FHE run this file's e2e performs: every PRE-clamp
/// intermediate of the T_E2E = 6 trajectory fits the signed centered window of
/// t = 1_032_193, so `SignedCt`'s window gate cannot refuse the real run.
/// (Interval algebra mirrors `convex_step`'s: [−B,B] → ±(τden + τnum·Σ|A_i·|)·B.)
#[test]
fn reference_window_feasibility_for_t() {
    let step = rebalance_step();
    let window = i128::from(centered_window(PLAINTEXT_MODULUS));
    // B_0 = max|y0| = 24; after each clamp B_{k} = HI·TAU_DEN^k.
    let mut b: i128 = Y0.iter().map(|v| i128::from(v.abs())).max().unwrap();
    for k in 0..T_E2E {
        let pre = preclamp_bound(b, &step);
        assert!(
            pre <= window,
            "iteration {} pre-clamp bound {pre} exceeds window {window}",
            k + 1
        );
        b = i128::from(BOX_HI) * i128::from(TAU_DEN).pow(k + 1);
    }
}

// ---------------------------------------------------------------------------
// CONTRACT-GAP SHIMS — named precisely; each panics with its gap until the
// owning lane / supervisor closes it. (TESTQALOG 2026-07-18 proto/e2e names all
// three for the supervisor.) NO fake fallback paths: the e2e is honest-red.
// ---------------------------------------------------------------------------

/// GAP 1 (fhir lane, expected): the frozen contract fixes `admissible`/`compile`
/// but `Program`'s AST shape is lane-defined and today has no constructors. The
/// program to express here: 2-asset CONVEX rebalance — objective ½yᵀ[[2,1],[1,2]]y
/// (tracking error + budget penalty, committed visibility, clear phase), box
/// constraint y ∈ [−15,15]², i.e. Tier0-dark FHE-tractable. Replace this body
/// with the real AST construction when fhir lands.
fn express_rebalance_in_fhir() -> Program {
    unimplemented!(
        "e2e GAP 1: fhir::Program has no constructors yet (AST is fhir-lane-defined); \
         build the 2-asset convex rebalance AST here when fhir lands"
    )
}

/// GAP 2 (contract, NAMED for the supervisor): `threshold::BfvParams` has no
/// constructor in the frozen interface — the e2e cannot instantiate the fold
/// parameter set (degree 4096 / fold moduli / t = 1_032_193). Needs e.g.
/// `BfvParams::fold_default()` in threshold.rs.
fn fold_params() -> BfvParams {
    unimplemented!(
        "e2e GAP 2: no BfvParams constructor in the frozen contract \
         (need threshold::BfvParams::fold_default() or equivalent)"
    )
}

/// GAP 3 (contract, NAMED for the supervisor): the frozen interface has keygen /
/// partial_decrypt / combine but NO encrypt-under-the-collective-key, so state
/// cannot enter the system. Needs e.g.
/// `threshold::encrypt_collective(&CollectivePublicKey, &[u64], &BfvParams) -> LeanCiphertext`
/// (all 4096 slots of one coordinate carry the same centered-encoded value here).
fn encrypt_to_collective(
    _pk: &CollectivePublicKey,
    _params: &BfvParams,
    _slot_value: u64,
) -> LeanCiphertext {
    unimplemented!(
        "e2e GAP 3: no encrypt-under-CollectivePublicKey signature in the frozen contract"
    )
}

// ---------------------------------------------------------------------------
// THE INTEGRATION PROOF — fhir → collective key → convex_solve → threshold.
// ---------------------------------------------------------------------------

/// The end-to-end private derivative: express the rebalance in fhir, compile to
/// a ClearingSpec, encrypt y0 to a 3-party collective key, run T_E2E convex
/// iterations at Tier 0 over the encrypted state, threshold-combine the n
/// partial decrypts, and assert the cleared allocation equals the plaintext
/// reference EXACTLY (bit-for-bit in the scaled domain, every slot).
///
/// Ignored until threshold + convex_engine + fhir land (their bodies are
/// `todo!()` stubs today, and gaps 1–3 above are open): run un-ignored, it
/// panics at the first unimplemented call — that red is honest and expected.
#[test]
#[ignore = "waits on threshold/convex_engine/fhir lanes + contract gaps 1-3 (no Program ctor, no BfvParams ctor, no collective encrypt); reference path is verified by the passing tests above"]
fn e2e_private_rebalance_matches_plaintext_reference() {
    // 1. Express the derivative in fhir and compile it. [waits: fhir lane, GAP 1]
    let program = express_rebalance_in_fhir();
    let tier = fhir::admissible(&program).expect("the convex rebalance must be admissible");
    assert_eq!(
        tier,
        Tier::Tier0Dark,
        "a convex program over committed state is Tier 0"
    );
    let spec = fhir::compile(&program).expect("the admissible program must compile");
    assert_eq!(spec.tier, tier);
    assert_eq!(
        spec.a,
        A_REBALANCE.iter().map(|r| r.to_vec()).collect::<Vec<_>>(),
        "the compiled public matrix must be I + ρ·11ᵀ"
    );

    // 2. n-of-n collective keygen — no party ever holds sk. [waits: threshold lane]
    let params = fold_params(); // [GAP 2]
    let (cpk, key_shares) = threshold::collective_keygen(QUORUM_N, &params);
    assert_eq!(key_shares.len(), QUORUM_N);

    // 3. Encrypt the SHIFTED state y0 = holdings − target to the collective key,
    //    centered-encoded, one ciphertext per coordinate. [GAP 3]
    let x0: Vec<SignedCt> = Y0
        .iter()
        .map(|&y| {
            let ct = encrypt_to_collective(
                &cpk,
                &params,
                fhegg_fhe::convex_step::encode_signed(y, PLAINTEXT_MODULUS),
            );
            SignedCt::new(ct, -Y0[0].abs(), Y0[0].abs(), PLAINTEXT_MODULUS)
                .expect("y0 fits the centered window")
        })
        .collect();

    // 4. The convex engine at T > 1, using the COMPILED matrix. [waits: convex_engine lane]
    let step = PublicLinearStep {
        a: spec.a.clone(),
        tau_num: TAU_NUM,
        tau_den: TAU_DEN,
    };
    let ceiling = convex_engine::max_iterations_for_params(&step, PLAINTEXT_MODULUS);
    assert!(
        ceiling >= T_E2E,
        "the proven-safe ceiling ({ceiling}) must admit T_E2E = {T_E2E} \
         (window feasibility is proven by reference_window_feasibility_for_t)"
    );
    // Fail-closed tooth: one past the ceiling must REFUSE, never silently mis-clear.
    assert!(
        matches!(
            convex_engine::convex_solve(&x0, &step, BOX_LO, BOX_HI, ceiling + 1, PLAINTEXT_MODULUS),
            Err(ConvexEngineError::NoiseBudgetExceeded { .. })
        ),
        "T = ceiling+1 must fail CLOSED with NoiseBudgetExceeded"
    );
    let x_t = convex_engine::convex_solve(&x0, &step, BOX_LO, BOX_HI, T_E2E, PLAINTEXT_MODULUS)
        .expect("T_E2E is within the proven ceiling");
    assert_eq!(x_t.len(), Y0.len());

    // 5. Threshold decrypt: all n parties partial-decrypt, combine, decode.
    let expected = reference_solve_scaled(&Y0, &step, BOX_LO, BOX_HI, T_E2E); // (14580, −14580)·(scale 4096)
    for (i, ct) in x_t.iter().enumerate() {
        let shares: Vec<_> = key_shares
            .iter()
            .map(|ks| threshold::partial_decrypt(ks, ct.ciphertext(), SMUDGE_BITS))
            .collect();

        // Quorum tooth: k < n shares must REFUSE — no sub-quorum ever clears.
        assert!(
            matches!(
                threshold::combine(&shares[..QUORUM_N - 1], &params),
                Err(ThresholdError::QuorumTooSmall { .. })
            ),
            "combine with n−1 shares must refuse"
        );

        let slots = threshold::combine(&shares, &params).expect("full quorum decrypts");
        assert!(!slots.is_empty());
        for &m in &slots {
            assert_eq!(
                i128::from(center(m, PLAINTEXT_MODULUS)),
                expected[i],
                "coordinate {i}: FHE scaled result must equal the plaintext reference bit-for-bit"
            );
        }
    }

    // 6. The cleared allocation: x_T = target + s_T/scale ≈ (63.56, 36.44),
    //    within the position limits, budget preserved (Σ s_T = 0 exactly).
    let scale = i128::from(TAU_DEN).pow(T_E2E);
    assert_eq!(expected.iter().sum::<i128>(), 0, "budget-neutral rebalance");
    for (i, &si) in expected.iter().enumerate() {
        let dev = si.abs();
        assert!(
            dev <= i128::from(BOX_HI) * scale,
            "asset {i} within position limits"
        );
    }
}
