//! ORACLE TEETH for `convex_step` — fhe.rs is the authority. Every primitive
//! op (neg / sub / public-scalar mul) is byte-differentialed against fhe.rs's
//! OWN operators, and the full iteration `prox(x − τ·A·x)` is differentially
//! validated against a cleartext reference across ALL 4096 SIMD
//! slot-instances at once. If any of our arithmetic is wrong in any bit,
//! fhe.rs decrypts a different value (or the bytes diverge) and the test is
//! RED — agreement with a real BFV library cannot be faked.
//!
//! Params: the same deployed fold set the whole lane is anchored to
//! (degree-4096, RNS moduli {0xffffee001, 0xffffc4001, 0x1ffffe0001},
//! t ≈ 2^20), asserted not assumed.

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{
    DeserializeParametrized, FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize,
};
use rand_09::rngs::StdRng;
use rand_09::{Rng, SeedableRng};
use std::sync::Arc;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::bfv_lean::{fold_add, BfvLeanError, LeanCiphertext, FOLD_DEGREE, FOLD_MODULI};
use fhegg_fhe::convex_step::{
    center, centered_window, convex_linear_step, encode_signed, prox_clamp_scaled,
    reference_linear_scaled, reference_step_scaled, signed_add, signed_neg, signed_scale, ClampBox,
    ConvexStepError, PublicLinearStep, SignedCt,
};

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
    assert!(
        (1 << 19) < t && t < (1 << 21),
        "plaintext modulus t={t} is not ~2^20"
    );
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

fn encrypt_slots(fx: &mut Fixture, slots: &[u64]) -> Ciphertext {
    let pt = Plaintext::try_encode(slots, Encoding::simd(), &fx.params).expect("simd encode");
    fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt")
}

/// Encrypt a vector of SIGNED slot values under the centered encoding and
/// wrap it as a SignedCt with the declared interval [lo, hi].
fn encrypt_signed(fx: &mut Fixture, vals: &[i64], lo: i64, hi: i64) -> (Ciphertext, SignedCt) {
    let t = fx.t;
    let slots: Vec<u64> = vals.iter().map(|&v| encode_signed(v, t)).collect();
    let ct = encrypt_slots(fx, &slots);
    let lean =
        LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), fx.params.moduli(), fx.params.degree(), 0)
            .expect("parse fhe.rs ciphertext");
    let signed = SignedCt::new(lean, lo, hi, t).expect("interval inside the window");
    (ct, signed)
}

fn decrypt_slots(fx: &Fixture, lean: &LeanCiphertext, k: usize) -> Vec<u64> {
    let ct = Ciphertext::from_bytes(&lean.to_fhe_bytes(), &fx.params)
        .expect("fhe.rs accepts our re-serialized bytes");
    let pt = fx.sk.try_decrypt(&ct).expect("fhe.rs decrypt");
    let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode");
    v[..k].to_vec()
}

/// PRIMITIVE TOOTH 1 — negation: byte-identical to fhe.rs's own `−&ct`, and
/// fhe.rs decrypts it to the centered negative.
#[test]
fn oracle_neg_matches_fhers_and_decrypts_to_minus() {
    let mut fx = fixture(0xC1);
    let vals: Vec<i64> = vec![0, 1, -1, 42, -37, 500, -499];
    let (ct, signed) = encrypt_signed(&mut fx, &vals, -499, 500);

    let ours = signed_neg(&signed, fx.t).expect("neg in window");
    assert_eq!(ours.interval(), (-500, 499), "interval must flip");

    // byte differential vs fhe.rs's OWN Neg
    let theirs = -&ct;
    assert_eq!(
        ours.ciphertext().to_fhe_bytes(),
        theirs.to_bytes(),
        "byte-level divergence from fhe.rs's own neg"
    );

    // decrypt differential: every slot reads −v under centered decode
    let got = decrypt_slots(&fx, ours.ciphertext(), vals.len());
    let t = fx.t;
    let read: Vec<i64> = got.iter().map(|&m| center(m, t)).collect();
    let want: Vec<i64> = vals.iter().map(|&v| -v).collect();
    assert_eq!(read, want, "neg decrypted to something other than −v");
}

/// PRIMITIVE TOOTH 2 — THE ADD-ONLY-COMPOSABLE CLAIM, proven by execution:
/// our one-pass scalar mul by 5 is byte-identical to fhe.rs's own
/// `ct+ct+ct+ct+ct` (scalar mul by a public constant IS repeated addition),
/// and decrypts to 5·v.
#[test]
fn oracle_scalar_mul_is_repeated_adds_byte_identical() {
    let mut fx = fixture(0xC2);
    let vals: Vec<i64> = vec![7, -3, 0, 100, -100, 1];
    let (ct, signed) = encrypt_signed(&mut fx, &vals, -100, 100);

    let ours = signed_scale(&signed, 5, fx.t).expect("scale in window");
    assert_eq!(ours.interval(), (-500, 500));

    let theirs = &(&(&(&ct + &ct) + &ct) + &ct) + &ct; // 5 = 1+1+1+1+1
    assert_eq!(
        ours.ciphertext().to_fhe_bytes(),
        theirs.to_bytes(),
        "scalar mul by 5 diverged from fhe.rs's own 5 repeated adds"
    );

    let t = fx.t;
    let read: Vec<i64> = decrypt_slots(&fx, ours.ciphertext(), vals.len())
        .iter()
        .map(|&m| center(m, t))
        .collect();
    let want: Vec<i64> = vals.iter().map(|&v| 5 * v).collect();
    assert_eq!(read, want, "5·v decrypt mismatch");
}

/// PRIMITIVE TOOTH 3 — subtraction as add∘neg: byte-identical to fhe.rs's
/// own `&a − &b`.
#[test]
fn oracle_sub_matches_fhers_sub() {
    let mut fx = fixture(0xC3);
    let va: Vec<i64> = vec![10, 20, -30, 40];
    let vb: Vec<i64> = vec![3, -7, 11, -19];
    let (ca, sa) = encrypt_signed(&mut fx, &va, -30, 40);
    let (cb, sb) = encrypt_signed(&mut fx, &vb, -19, 11);

    let ours = signed_add(&sa, &signed_neg(&sb, fx.t).unwrap(), fx.t).expect("sub in window");
    let theirs = &ca - &cb;
    assert_eq!(
        ours.ciphertext().to_fhe_bytes(),
        theirs.to_bytes(),
        "a + (−b) diverged from fhe.rs's own sub"
    );
    let t = fx.t;
    let read: Vec<i64> = decrypt_slots(&fx, ours.ciphertext(), va.len())
        .iter()
        .map(|&m| center(m, t))
        .collect();
    let want: Vec<i64> = va.iter().zip(vb.iter()).map(|(&x, &y)| x - y).collect();
    assert_eq!(read, want);
}

/// THE LOAD-BEARING TOOTH — one FULL convex iteration under FHE, checked
/// against the cleartext reference on ALL 4096 independent slot-instances:
/// d = 3, A = [[4,1,0],[1,3,1],[0,1,5]] (public, PSD), τ = 1/8,
/// prox = clamp to [0, 40]. The FHE path computes the SCALED linear step
/// w = 8·x − 1·A·x homomorphically (public-constant scalar muls + adds
/// ONLY — no ct×ct, no relinearization), decrypts, centers, and applies the
/// prox at the boundary in the scaled domain; the reference computes the
/// same iteration in exact cleartext integers. Every one of the 3×4096
/// values must agree EXACTLY (BFV is exact — no tolerance).
#[test]
fn oracle_one_convex_iteration_matches_reference_on_all_4096_instances() {
    let mut fx = fixture(0xC4);
    let t = fx.t;
    let d = 3;
    let n = FOLD_DEGREE; // 4096 independent instances, one per SIMD slot
    let step = PublicLinearStep {
        a: vec![vec![4, 1, 0], vec![1, 3, 1], vec![0, 1, 5]],
        tau_num: 1,
        tau_den: 8,
    };
    let bx = ClampBox { lo: 0, hi: 40 };

    // deterministic pseudorandom instances, x ∈ [−50, 50]^3 per slot
    let mut gen = StdRng::seed_from_u64(0xC0117E);
    let coords: Vec<Vec<i64>> = (0..d)
        .map(|_| (0..n).map(|_| gen.random_range(-50..=50)).collect())
        .collect();

    // encrypt each coordinate (4096 instances ride each ciphertext)
    let state: Vec<SignedCt> = coords
        .iter()
        .map(|c| encrypt_signed(&mut fx, c, -50, 50).1)
        .collect();

    // FHE path: the homomorphic linear step
    let w = convex_linear_step(&state, &step, t).expect("step stays in the window");

    // interval bookkeeping sanity: |w| ≤ 8·50 + (max row sum 6)·50 = 700
    for wi in &w {
        let (lo, hi) = wi.interval();
        assert!(
            lo >= -700 && hi <= 700,
            "interval propagated wrong: [{lo},{hi}]"
        );
    }

    // boundary: decrypt + center + prox, vs the cleartext reference
    let mut clamped_count = 0usize;
    let mut interior_count = 0usize;
    let decrypted: Vec<Vec<i64>> = w
        .iter()
        .map(|wi| {
            decrypt_slots(&fx, wi.ciphertext(), n)
                .iter()
                .map(|&m| center(m, t))
                .collect()
        })
        .collect();
    for s in 0..n {
        let x_inst: Vec<i64> = (0..d).map(|i| coords[i][s]).collect();
        let want_linear = reference_linear_scaled(&x_inst, &step);
        let want_full = reference_step_scaled(&x_inst, &step, &bx);
        for i in 0..d {
            let got_linear = i128::from(decrypted[i][s]);
            assert_eq!(
                got_linear, want_linear[i],
                "linear step mismatch at instance {s}, coord {i}"
            );
            let got_full = prox_clamp_scaled(decrypted[i][s], &bx, step.tau_den);
            assert_eq!(
                got_full, want_full[i],
                "full prox(x − τAx) mismatch at instance {s}, coord {i}"
            );
            if got_full == got_linear {
                interior_count += 1;
            } else {
                clamped_count += 1;
            }
        }
    }
    // the prox must BITE on this data (and not be constant): both kinds occur
    assert!(
        clamped_count > 0,
        "prox never clamped — test data is toothless"
    );
    assert!(
        interior_count > 0,
        "prox clamped everything — clamp check vacuous"
    );
}

/// WINDOW TOOTH — (1) CONTROL: one past the centered window, the aliasing is
/// REAL and SILENT through a genuine fhe.rs encrypt/decrypt round trip;
/// (2) the gate REFUSES intervals that could reach it; (3) not over-broad:
/// the exact window edge passes.
#[test]
fn window_aliasing_is_real_and_the_gate_refuses_it() {
    let mut fx = fixture(0xC5);
    let t = fx.t;
    let half = centered_window(t);

    // (1) CONTROL: encrypt v = half+1. fhe.rs decrypts the residue fine —
    // but centered decode reads it as NEGATIVE. Silent, well-formed, wrong.
    let ct = encrypt_slots(&mut fx, &[encode_signed(half as i64 + 1, t)]);
    let lean =
        LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), fx.params.moduli(), fx.params.degree(), 0)
            .expect("parse");
    let m = decrypt_slots(&fx, &lean, 1)[0];
    assert_eq!(
        center(m, t),
        -(half as i64),
        "expected silent sign aliasing at half+1"
    );

    // (2) the gate refuses the declaration that could reach it…
    match SignedCt::new(lean.clone(), 0, half as i64 + 1, t) {
        Err(ConvexStepError::WindowExceeded { hi, .. }) => {
            assert_eq!(hi, i128::from(half) + 1)
        }
        other => panic!("expected WindowExceeded, got {other:?}"),
    }
    // …and refuses an op that would leave the window even from safe inputs:
    let safe = SignedCt::new(lean, 0, half as i64, t).expect("edge interval is legal");
    assert!(matches!(
        signed_scale(&safe, 2, t),
        Err(ConvexStepError::WindowExceeded { .. })
    ));

    // (3) not over-broad: scale by 1 at the edge stays legal.
    assert!(signed_scale(&safe, 1, t).is_ok());
}

/// FAIL-CLOSED COUPLING TOOTH — a SignedCt's inner ciphertext carries
/// `plain_bound = t−1`, so feeding it back into the UNSIGNED fold gate
/// refuses: the signed and unsigned regimes cannot be silently mixed.
#[test]
fn signed_ciphertext_refused_by_unsigned_fold_gate() {
    let mut fx = fixture(0xC6);
    let (_, s1) = encrypt_signed(&mut fx, &[1, -2, 3], -2, 3);
    let (_, s2) = encrypt_signed(&mut fx, &[4, 5, -6], -6, 5);
    assert!(matches!(
        fold_add(s1.ciphertext(), s2.ciphertext(), fx.t),
        Err(BfvLeanError::WrapRefused { .. })
    ));
}
