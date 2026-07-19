//! The REAL no-viewer smudge tooth — the fix for the opus finding
//! `ThresholdNoViewerToothVacuous`.
//!
//! ## What was vacuous (verified in `src/threshold.rs` before writing this)
//!
//! The in-src statistical tooth (`no_viewer_partial_aggregate_is_plaintext_and_smudge_independent`)
//! measures the (n-1)-share coalition aggregate, whose shape is the MISSING party's RLWE key term
//! `s_j·c1` — a ~2^109-scale near-uniform mask. That term drowns the 2^80 smudge completely: the
//! aggregate histogram is uniform whether the smudge is 2^80, 2^15, or ZERO. The assertion
//! `TV(b=80, b=82) < 0.15` therefore passes at zero smudge — it never exercised the property
//! Smudging.lean proves. (Demonstrated by mutation below: under a sampler that smudges at 2^15
//! while stamping 80 — fhe.rs mbfv's exact TODO failure mode — the old tooth stays GREEN.)
//!
//! ## What this tooth does instead: ISOLATE the smudge
//!
//! Craft a meter ciphertext with `c1 = 0` (LeanCiphertext fields are public). Then the published
//! partial-decrypt share is `h = s·c1 + e = e` — the smudge ALONE, key term held identically at
//! zero. `h` is the protocol's WIRE object (what a coalition actually observes), read here through
//! the derived `Debug` (the minimal clean accessor threshold.rs should add is named in TESTQALOG).
//!
//! Against those isolated samples we pin the EXACT distribution `metatheory/Bfv/Smudging.lean`
//! proves about — uniform on the integer interval `[-2^b, 2^b]`, `smudgeBits = 80` ("the theorems
//! are about that distribution and no other"; "the smudge distribution must be UNIFORM on [-S,S]
//! ... the fail-closed sampler gate"):
//!
//! * **width/shape quantiles** — `P(|u| > 2^79) = 1/2`, `P(|u| > 3·2^78) = 1/4`, `max|u| ≤ 2^80`
//!   (the correctness-jaw radius of `deployed_smudged_decrypt_exact`). 4096 iid coefficient
//!   samples, binomial σ ≈ 0.008, bands ±0.05 ≈ 6σ. RED at zero smudge, at 2^15, at b=79, at
//!   b≥82, and for a non-uniform (e.g. Gaussian) sampler of the right max.
//! * **the sd mirror** — Smudging.lean's exact formula `sd = min(|Δc|, 2S+1)/(2S+1)` between two
//!   candidate secret noises inside the deployed envelope: `e₁ = 0`, `e₂ = 2^32 = deployedCtNoise`
//!   (the very pair of `deployed_smudge_floor_leaks`). The optimal distinguisher for two shifted
//!   uniforms is the threshold test at a point between the centers (`smudge_too_small_distinguishes`
//!   is its pointwise form): adv = |P(e₁+u ≥ D) − P(e₂+u ≥ D)| at D = 2^31. At S = 2^80 the true
//!   advantage is ≈ 2^-49 (`deployed_smudge_hides` proves ≤ 2^-48); we assert it below the 4096-
//!   sample noise floor (0.05 ≈ 2^-4.3 — the execution check is honest about its resolution; the
//!   2^-48 tail is Lean's, not a statistical test's). At S = 2^15 (or zero) the advantage is
//!   EXACTLY 1 — sd's cliff, and this test goes RED.
//! * **the public-path bridge** — the smudge must be live through the REAL `combine` → fhe.rs
//!   decrypt, not just present in the share object: put the single meter coefficient at a known
//!   distance d = 2^79 below the t/q rounding cliff, so the decoded output flips iff `u ≥ 2^79`
//!   (p = 1/4 for the Lean distribution). Any smudge with `b ≤ 79` — including ZERO — produces
//!   0 flips: deterministic RED.
//!
//! Bite proven by mutation (break → RED → restore; reds recorded in TESTQALOG 2026-07-18
//! par/threshold-tooth): (M1) sampler smudges at 2^15 while stamping smudge_bits=80; (M2) sampler
//! smudges ZERO. Both leave the OLD in-src tooth green and turn every test in this file RED.

use fhegg_fhe::bfv_lean::{LeanCiphertext, RnsPoly};
use fhegg_fhe::threshold::{
    collective_keygen, combine, partial_decrypt, BfvParams, DecryptShare, MIN_SMUDGE_BITS,
};

// ---------------------------------------------------------------------------
// the meter ciphertext: c1 = 0 kills the key term; c0 is ours to craft
// ---------------------------------------------------------------------------

/// A fold-shaped ciphertext with `c1 = 0` and `c0` zero except coefficient 0 = `c00`
/// (as RNS residues). With `c1 = 0` the partial-decrypt share is the smudge alone.
fn meter_ct(params: &BfvParams, c00: u128) -> LeanCiphertext {
    let degree = params.degree();
    let zero_rows: Vec<Vec<u64>> = params.moduli().iter().map(|_| vec![0u64; degree]).collect();
    let mut c0_rows = zero_rows.clone();
    for (row, &m) in c0_rows.iter_mut().zip(params.moduli().iter()) {
        row[0] = (c00 % m as u128) as u64;
    }
    LeanCiphertext {
        moduli: params.moduli().to_vec(),
        degree,
        level: 0,
        variable_time: false,
        polys: vec![RnsPoly { rows: c0_rows }, RnsPoly { rows: zero_rows }],
        plain_bound: 1,
    }
}

fn q_product(params: &BfvParams) -> u128 {
    params.moduli().iter().map(|&m| m as u128).product()
}

// ---------------------------------------------------------------------------
// reading the coalition's view: the share h (the wire object) via Debug
// ---------------------------------------------------------------------------
// DecryptShare's `h` is exactly what a party PUBLISHES in the protocol — the
// coalition sees it by construction. The field is module-private in Rust, so
// this test reads it through the derived `Debug` representation (loud parse
// failures, never silent). The clean accessor is named in TESTQALOG.

fn h_rows_of(share: &DecryptShare, n_rows: usize, degree: usize) -> Vec<Vec<u64>> {
    let s = format!("{share:?}");
    let start = s.find("h: [[").expect("Debug shape changed: no `h: [[`") + 5;
    let end = s[start..]
        .find("]], ct:")
        .expect("Debug shape changed: no `]], ct:` terminator")
        + start;
    let rows: Vec<Vec<u64>> = s[start..end]
        .split("], [")
        .map(|row| {
            row.split(", ")
                .map(|n| {
                    n.trim()
                        .parse::<u64>()
                        .expect("h coefficient parses as u64")
                })
                .collect()
        })
        .collect();
    assert_eq!(rows.len(), n_rows, "h must have one row per RNS modulus");
    for r in &rows {
        assert_eq!(
            r.len(),
            degree,
            "each h row must have `degree` coefficients"
        );
    }
    rows
}

// ---------------------------------------------------------------------------
// CRT reconstruction (test-side, pinned against known values below)
// ---------------------------------------------------------------------------

struct Crt {
    q: u128,
    c: Vec<u128>, // c_i = M_i · (M_i^{-1} mod q_i), M_i = q/q_i
}

impl Crt {
    fn new(moduli: &[u64]) -> Self {
        let q: u128 = moduli.iter().map(|&m| m as u128).product();
        let c = moduli
            .iter()
            .map(|&m| {
                let big_m = q / m as u128;
                let inv = modpow_u64((big_m % m as u128) as u64, m - 2, m); // q_i prime
                mulmod_u128(big_m, inv, q)
            })
            .collect();
        Self { q, c }
    }

    fn combine(&self, residues: &[u64]) -> u128 {
        let mut acc = 0u128;
        for (&r, &c) in residues.iter().zip(self.c.iter()) {
            acc = (acc + mulmod_u128(c, r, self.q)) % self.q;
        }
        acc
    }

    /// Centered representative in `(-q/2, q/2]`.
    fn centered(&self, residues: &[u64]) -> i128 {
        let x = self.combine(residues);
        if x > self.q / 2 {
            x as i128 - self.q as i128
        } else {
            x as i128
        }
    }
}

fn modpow_u64(b: u64, mut e: u64, m: u64) -> u64 {
    let mut acc: u128 = 1;
    let mut bb: u128 = b as u128 % m as u128;
    while e > 0 {
        if e & 1 == 1 {
            acc = acc * bb % m as u128;
        }
        bb = bb * bb % m as u128;
        e >>= 1;
    }
    acc as u64
}

/// `a·b mod q` for a,q < 2^110, b < 2^64 — shift-add (the full product overflows u128).
fn mulmod_u128(mut a: u128, mut b: u64, q: u128) -> u128 {
    let mut acc = 0u128;
    a %= q;
    while b > 0 {
        if b & 1 == 1 {
            acc = (acc + a) % q;
        }
        a = (a + a) % q;
        b >>= 1;
    }
    acc
}

/// Extract the 4096 isolated smudge samples (centered integers) from one share over a
/// `c1 = 0` meter ciphertext: `h = s·0 + e = e`, CRT-reconstructed per coefficient.
fn smudge_samples(share: &DecryptShare, params: &BfvParams, crt: &Crt) -> Vec<i128> {
    let rows = h_rows_of(share, params.moduli().len(), params.degree());
    (0..params.degree())
        .map(|j| {
            let residues: Vec<u64> = rows.iter().map(|r| r[j]).collect();
            crt.centered(&residues)
        })
        .collect()
}

fn frac(samples: &[i128], pred: impl Fn(i128) -> bool) -> f64 {
    samples.iter().filter(|&&x| pred(x)).count() as f64 / samples.len() as f64
}

// ---------------------------------------------------------------------------
// the teeth
// ---------------------------------------------------------------------------

/// TOOTH 1 — the sampler IS the Lean distribution (width + shape + the sd mirror).
///
/// RED at zero smudge (all quantiles collapse to 0, sd-mirror advantage = 1), at 2^15
/// (same), at b = 79 (the >2^79 quantile reads 0), at b ≥ 82 (max|u| breaches the
/// correctness-jaw radius), and for a non-uniform sampler of the right range.
#[test]
fn smudge_is_the_exact_lean_distribution() {
    let params = BfvParams::fold_set();
    assert_eq!(
        MIN_SMUDGE_BITS, 80,
        "this tooth pins Bfv.Smudging.smudgeBits = 80; re-derive the bands if the export moves"
    );
    let crt = Crt::new(params.moduli());

    // CRT pin: a small positive and a small negative value reconstruct exactly.
    {
        let v = 123_456_789u64;
        let residues: Vec<u64> = params.moduli().iter().map(|&m| v % m).collect();
        assert_eq!(crt.centered(&residues), v as i128, "CRT positive pin");
        let neg: Vec<u64> = params.moduli().iter().map(|&m| m - 5).collect(); // ≡ -5 (mod q)
        assert_eq!(crt.centered(&neg), -5, "CRT negative/centering pin");
    }

    let (_cpk, key_shares) = collective_keygen(1, &params);
    let ct = meter_ct(&params, 0);
    let share = partial_decrypt(&key_shares[0], &ct, MIN_SMUDGE_BITS);
    let u = smudge_samples(&share, &params, &crt);
    assert_eq!(u.len(), 4096);

    let s: i128 = 1 << 80; // the Lean radius S = 2^smudgeBits

    // Correctness jaw (deployed_smudged_decrypt_exact's per-party radius): NEVER above 2^80.
    // Catches an over-smudging sampler (b ≥ 81), which would break the proven decrypt margin.
    let max_abs = u.iter().map(|x| x.abs()).max().unwrap();
    assert!(
        max_abs <= s,
        "smudge sample exceeds the proven per-party radius 2^80: max|u| = 2^{:.2}",
        (max_abs as f64).log2()
    );

    // Hiding-jaw width/shape: uniform on [-2^80, 2^80] has P(|u| > 2^79) = 1/2 and
    // P(|u| > 3·2^78) = 1/4. Any b ≤ 79 (including ZERO) reads 0 on the first quantile — RED.
    let q_half = frac(&u, |x| x.abs() > (1i128 << 79));
    let q_quarter = frac(&u, |x| x.abs() > 3 * (1i128 << 78));
    assert!(
        (0.45..=0.55).contains(&q_half),
        "smudge width is not the Lean 2^80 uniform: P(|u| > 2^79) = {q_half} (expect 0.5; \
         0 here means the smudge is ABSENT or below the Smudging.lean bound)"
    );
    assert!(
        (0.20..=0.30).contains(&q_quarter),
        "smudge shape is not uniform on [-2^80, 2^80]: P(|u| > 3·2^78) = {q_quarter} (expect 0.25)"
    );

    // THE sd MIRROR — Smudging.lean: sd = min(|Δc|, 2S+1)/(2S+1). Candidate secrets
    // e₁ = 0, e₂ = 2^32 = deployedCtNoise (the deployed_smudge_floor_leaks pair). The optimal
    // distinguisher between two shifted uniforms is the threshold test at D between the centers
    // (smudge_too_small_distinguishes is its pointwise form). At S = 2^80 the true advantage is
    // min(2^32, 2^81+1)/(2^81+1) ≈ 2^-49 (deployed_smudge_hides: ≤ 2^-48); at S = 2^15 or S = 0
    // it is EXACTLY 1 — the same statistic, both sides of the cliff.
    let d: i128 = 1 << 31;
    let b_env: i128 = 1 << 32;
    let p_e1 = frac(&u, |x| x >= d); // P(e₁ + u ≥ D), e₁ = 0
    let p_e2 = frac(&u, |x| x >= d - b_env); // P(e₂ + u ≥ D) = P(u ≥ D − 2^32)
    assert!(
        (0.45..=0.55).contains(&p_e1),
        "distinguisher threshold does not straddle the smudge support: P(u ≥ 2^31) = {p_e1} \
         (expect ≈ 0.5; 0 means the smudge is too small to reach the candidate gap at all)"
    );
    let adv = (p_e1 - p_e2).abs();
    assert!(
        adv <= 0.05,
        "coalition distinguishes the two in-envelope secrets: threshold advantage = {adv} \
         (Smudging.lean proves sd ≤ 2^-48 at S = 2^80; a sub-bound smudge makes this EXACTLY 1)"
    );
}

/// TOOTH 2 — the smudge is LIVE through the real public path (`combine` → fhe.rs decrypt),
/// with the meter coefficient a known d = 2^79 below the t/q rounding cliff: the decoded
/// output flips iff `u ≥ 2^79`, p = 1/4 under the Lean distribution.
///
/// RED (0 flips, deterministically) for ANY smudge with b ≤ 79 — including ZERO.
#[test]
fn smudge_moves_the_public_combine_output_at_the_cliff() {
    let params = BfvParams::fold_set();
    let q = q_product(&params);
    let t = params.plaintext_modulus() as u128;
    // Smallest phase that rounds to plaintext 1: cliff = ceil(q / (2t)) (round-nearest t/q
    // scaling; ±1 slop is irrelevant against d = 2^79).
    let cliff = (q + 2 * t - 1) / (2 * t);
    let d: u128 = 1 << 79;
    assert!(
        cliff > d && cliff + (1 << 80) < q / 2,
        "meter placement sanity"
    );

    let (_cpk, key_shares) = collective_keygen(1, &params);
    let ct = meter_ct(&params, cliff - d);

    let runs = 32usize;
    let mut flips = 0usize;
    for _ in 0..runs {
        let share = partial_decrypt(&key_shares[0], &ct, MIN_SMUDGE_BITS);
        let slots = combine(&[share], &params).expect("1-of-1 combine over the meter ciphertext");
        // A single power-basis meter coefficient decodes to a CONSTANT slot vector (the
        // plaintext poly is b·X^0), so the flip bit is domain-robustly readable from any slot.
        let b0 = slots[0];
        assert!(
            slots.iter().all(|&x| x == b0),
            "meter ciphertext must decode to a constant slot vector"
        );
        assert!(b0 <= 1, "meter must decode to 0 or 1, got {b0}");
        flips += b0 as usize;
    }

    // p = P(u ≥ 2^79) = (2^80 − 2^79 + 1)/(2^81 + 1) ≈ 1/4 → E[flips] = 8 of 32.
    // Band [1, 28]: false-RED ≈ 0.75^32 ≈ 1e-4. A smudge with b ≤ 79 (or zero, or fhe.rs's
    // fresh-noise TODO scale) can NEVER reach the cliff: flips = 0, deterministic RED.
    assert!(
        flips >= 1,
        "the smudge never crossed a 2^79 rounding gap in {runs} runs: the sampled smudge is \
         absent or below the Smudging.lean bound (expected ≈ {} crossings)",
        runs / 4
    );
    assert!(
        flips <= 28,
        "flip rate {flips}/{runs} is far above the uniform-2^80 rate (≈ 1/4): smudge much too wide"
    );
}
