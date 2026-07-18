//! THE ORACLE TEETH for `bfv_mul` — fhe.rs is the authority. Every test
//! encrypts with REAL fhe.rs, multiplies through our wrap-guarded engine (or
//! raw fhe.rs, for the wrap witness), and decrypts with REAL fhe.rs. If the
//! multiply is wrong in any way, fhe.rs decrypts the wrong product and the
//! test is RED — agreement with a real BFV library cannot be faked.
//!
//! Params (asserted, not assumed): degree-4096, RNS moduli
//! {0xffffee001, 0xffffc4001, 0x1ffffe0001} (~109-bit q), t = 1032193 (~2^20)
//! — the exact set the additive fold lane is anchored to.

use fhe::bfv::{
    BfvParameters, Ciphertext, Encoding, Multiplicator, Plaintext, PublicKey, RelinearizationKey,
    SecretKey,
};
use fhe_traits::{FheDecoder, FheDecrypter, FheEncoder, FheEncrypter};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;
use std::sync::Arc;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::bfv_lean::{FOLD_DEGREE, FOLD_MODULI};
use fhegg_fhe::bfv_mul::{square_safe_bound, BfvMulError, BoundedCiphertext, MulEngine};

struct Fixture {
    params: Arc<BfvParameters>,
    sk: SecretKey,
    pk: PublicKey,
    rk: RelinearizationKey,
    rng: StdRng,
    t: u64,
}

fn fixture(seed: u64) -> Fixture {
    let params = pick_params(20);
    // Pin the parameter facts. If fhe.rs's default set ever drifts, this
    // fails LOUDLY instead of testing a different scheme.
    assert_eq!(params.degree(), FOLD_DEGREE, "degree drifted");
    assert_eq!(params.moduli(), &FOLD_MODULI, "RNS moduli drifted");
    let t = params.plaintext();
    assert_eq!(t, 1_032_193, "plaintext modulus drifted");
    let mut rng = StdRng::seed_from_u64(seed);
    let sk = SecretKey::random(&params, &mut rng);
    let pk = PublicKey::new(&sk, &mut rng);
    let rk = RelinearizationKey::new(&sk, &mut rng).expect("relin key");
    Fixture {
        params,
        sk,
        pk,
        rk,
        rng,
        t,
    }
}

fn encrypt(fx: &mut Fixture, slots: &[u64]) -> Ciphertext {
    let pt = Plaintext::try_encode(slots, Encoding::simd(), &fx.params).expect("simd encode");
    fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt")
}

fn decrypt_slots(fx: &Fixture, ct: &Ciphertext, k: usize) -> Vec<u64> {
    let pt = fx.sk.try_decrypt(ct).expect("fhe.rs decrypt");
    let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode");
    v[..k].to_vec()
}

fn engine(fx: &Fixture) -> MulEngine {
    MulEngine::new(&fx.rk, &fx.params).expect("mul engine")
}

/// THE LOAD-BEARING TOOTH: two encrypted secret scalars, multiplied through
/// the engine, decrypt to their exact integer product (in-bound, so mod t is
/// the identity). The product of two secrets neither party revealed.
#[test]
fn oracle_scalar_product_decrypts_to_plaintext_product() {
    let mut fx = fixture(0x341);
    let a_val = 41u64;
    let b_val = 7u64;
    let ct_a = encrypt(&mut fx, &[a_val]);
    let ct_b = encrypt(&mut fx, &[b_val]);

    let eng = engine(&fx);
    let prod = eng
        .multiply(
            &BoundedCiphertext::new(ct_a, a_val),
            &BoundedCiphertext::new(ct_b, b_val),
        )
        .expect("in-bound multiply");

    assert_eq!(prod.plain_bound, a_val * b_val, "bound must propagate");
    let got = decrypt_slots(&fx, &prod.ct, 1);
    assert_eq!(got, vec![287], "fhe.rs decrypted a different product");
}

/// SIMD vector tooth: slot-wise products of two encrypted vectors (the shape
/// of a batched elementwise private×private product), oracle-checked on
/// every live slot, at the tight square-safe bound.
#[test]
fn oracle_simd_vector_product() {
    let mut fx = fixture(0x342);
    let k = 32;
    let bound = square_safe_bound(fx.t); // 1015 at deployed t
    assert_eq!(bound, 1015);
    // Deterministic in-bound vectors including the extremes 0 and bound.
    let v1: Vec<u64> = (0..k as u64).map(|i| (i * 131) % (bound + 1)).collect();
    let mut v2: Vec<u64> = (0..k as u64).map(|i| (i * 977 + 3) % (bound + 1)).collect();
    v2[0] = bound;
    let mut v1 = v1;
    v1[0] = bound; // slot 0 exercises the exact corner bound²  < t
    v1[1] = 0;

    let ct1 = encrypt(&mut fx, &v1);
    let ct2 = encrypt(&mut fx, &v2);
    let eng = engine(&fx);
    let prod = eng
        .multiply(
            &BoundedCiphertext::new(ct1, bound),
            &BoundedCiphertext::new(ct2, bound),
        )
        .expect("in-bound multiply");

    let got = decrypt_slots(&fx, &prod.ct, k);
    let want: Vec<u64> = v1.iter().zip(v2.iter()).map(|(x, y)| x * y).collect();
    assert!(want.iter().all(|&w| w < fx.t), "test data must be in-bound");
    assert_eq!(got, want, "slot-wise products disagree with plaintext");
}

/// THE WRAP IS REAL (failing-side witness) AND THE GUARD REFUSES IT:
/// (a) raw fhe.rs multiply of 1016×1016 decrypts to 1032256 mod t = 63 — a
///     well-formed WRONG number, proven by the oracle itself;
/// (b) our engine REFUSES the same bounds before touching the ciphertexts.
#[test]
fn wrap_is_real_and_refused() {
    let mut fx = fixture(0x343);
    let v = 1016u64; // 1016² = 1032256 >= t = 1032193
    let ct1 = encrypt(&mut fx, &[v]);
    let ct2 = encrypt(&mut fx, &[v]);

    // (a) the silent wrap, witnessed through raw fhe.rs (no guard in the way).
    let raw = Multiplicator::default(&fx.rk).expect("multiplicator");
    let wrapped = raw.multiply(&ct1, &ct2).expect("raw multiply");
    let got = decrypt_slots(&fx, &wrapped, 1);
    assert_eq!(
        got,
        vec![(v * v) % fx.t],
        "expected the silent mod-t wrap value"
    );
    assert_eq!(got, vec![63], "1032256 mod 1032193 = 63, a plausible lie");

    // (b) the guard refuses exactly this.
    let eng = engine(&fx);
    let err = eng
        .multiply(
            &BoundedCiphertext::new(ct1, v),
            &BoundedCiphertext::new(ct2, v),
        )
        .expect_err("bounds 1016*1016 >= t must be refused");
    match err {
        BfvMulError::WrapRefused {
            bound_product,
            plaintext_modulus,
        } => {
            assert_eq!(bound_product, (v as u128) * (v as u128));
            assert_eq!(plaintext_modulus, fx.t);
        }
        other => panic!("wrong refusal: {other}"),
    }
}

/// The quadratic-objective shape: Σ aᵢ·bᵢ over four pairs of encrypted
/// scalars (multiply each pair, fold the products additively), decrypting to
/// the exact inner product. Plus the summed wrap guard's failing side.
#[test]
fn oracle_product_sum_dot() {
    let mut fx = fixture(0x344);
    let a_vals = [3u64, 700, 0, 999];
    let b_vals = [500u64, 800, 1015, 1];
    let want: u64 = a_vals.iter().zip(b_vals.iter()).map(|(a, b)| a * b).sum();
    assert!(want < fx.t, "test data must be in-bound: {want}");

    let lhs: Vec<BoundedCiphertext> = a_vals
        .iter()
        .map(|&v| BoundedCiphertext::new(encrypt(&mut fx, &[v]), v.max(1)))
        .collect();
    let rhs: Vec<BoundedCiphertext> = b_vals
        .iter()
        .map(|&v| BoundedCiphertext::new(encrypt(&mut fx, &[v]), v.max(1)))
        .collect();

    let eng = engine(&fx);
    let dot = eng.product_sum(&lhs, &rhs).expect("in-bound product-sum");
    let got = decrypt_slots(&fx, &dot.ct, 1);
    assert_eq!(got, vec![want], "inner product disagrees with plaintext");

    // Failing side of the SUM guard: each pair in-bound for multiply, but the
    // bounds sum past t. 3 pairs of 600×600 = 3·360000 = 1080000 >= t.
    let six: Vec<BoundedCiphertext> = (0..3)
        .map(|_| BoundedCiphertext::new(encrypt(&mut fx, &[600]), 600))
        .collect();
    let err = eng
        .product_sum(&six, &six.clone())
        .expect_err("summed bounds must be refused");
    assert!(
        matches!(
            err,
            BfvMulError::SumWrapRefused {
                bound_sum: 1_080_000,
                ..
            }
        ),
        "wrong refusal: {err}"
    );
}

/// NOISE GROWTH, MEASURED (not asserted from folklore): fresh vs add vs
/// multiply+relin, in bits of centered noise (fhe.rs `measure_noise`), on the
/// deployed degree-4096 / 3-moduli (~109-bit q) / t≈2^20 set. The test's
/// teeth: multiply noise must strictly exceed add noise (the whole reason the
/// additive fold is cheap), and one multiply must stay under budget.
#[test]
fn noise_growth_measured() {
    let mut fx = fixture(0x345);
    let v = square_safe_bound(fx.t);
    let ct1 = encrypt(&mut fx, &[v]);
    let ct2 = encrypt(&mut fx, &[v]);

    let n_fresh1 = unsafe { fx.sk.measure_noise(&ct1) }.expect("noise fresh1");
    let n_fresh2 = unsafe { fx.sk.measure_noise(&ct2) }.expect("noise fresh2");

    let added = &ct1 + &ct2;
    let n_add = unsafe { fx.sk.measure_noise(&added) }.expect("noise add");

    let eng = engine(&fx);
    let prod = eng
        .multiply(
            &BoundedCiphertext::new(ct1.clone(), 1),
            &BoundedCiphertext::new(ct2.clone(), v),
        )
        .expect("multiply");
    let n_mul = unsafe { fx.sk.measure_noise(&prod.ct) }.expect("noise mul");

    // q is 109.4 bits; decrypt fails around noise ≈ log2(q/(2t)) ≈ 88 bits.
    let budget_bits = 88usize;
    println!(
        "MEASURED noise (bits, centered, deployed 4096/3-moduli/t=2^20 set): \
         fresh={n_fresh1}/{n_fresh2}, add={n_add}, mul+relin={n_mul}, budget≈{budget_bits}"
    );

    // Teeth (each can fail): addition grows noise by at most ~1 bit; multiply
    // is a step change strictly above add; one multiply stays under budget.
    assert!(
        n_add <= n_fresh1.max(n_fresh2) + 1,
        "add should cost ~1 bit: fresh {n_fresh1}/{n_fresh2} -> add {n_add}"
    );
    assert!(
        n_mul > n_add + 8,
        "multiply must be a step change over add: add={n_add}, mul={n_mul}"
    );
    assert!(
        n_mul < budget_bits,
        "one multiply must stay under the ~{budget_bits}-bit budget, got {n_mul}"
    );
}

/// DEPTH-2 PROBE: (a·b)·c — measures whether the 3-moduli set survives a
/// second multiply. This is a MEASUREMENT with correctness teeth: whatever
/// the noise reading, the decrypt must still equal a·b·c (in-bound) — if the
/// budget dies at depth 2, this test goes RED and the honest answer changes
/// to a failing-side pin.
#[test]
fn oracle_depth_two_product() {
    let mut fx = fixture(0x346);
    // 90·11·1013 = 1_002_870 < t = 1_032_193; every intermediate in-bound.
    let (a, b, c) = (90u64, 11u64, 1013u64);
    let ct_a = encrypt(&mut fx, &[a]);
    let ct_b = encrypt(&mut fx, &[b]);
    let ct_c = encrypt(&mut fx, &[c]);

    let eng = engine(&fx);
    let ab = eng
        .multiply(
            &BoundedCiphertext::new(ct_a, a),
            &BoundedCiphertext::new(ct_b, b),
        )
        .expect("depth-1");
    let abc = eng
        .multiply(&ab, &BoundedCiphertext::new(ct_c, c))
        .expect("depth-2 multiply (same level, relinearized)");

    let n_ab = unsafe { fx.sk.measure_noise(&ab.ct) }.expect("noise ab");
    let n_abc = unsafe { fx.sk.measure_noise(&abc.ct) }.expect("noise abc");
    println!("MEASURED depth noise (bits): depth1={n_ab}, depth2={n_abc}");

    let got = decrypt_slots(&fx, &abc.ct, 1);
    assert_eq!(got, vec![a * b * c], "depth-2 product decrypted wrong");
}
