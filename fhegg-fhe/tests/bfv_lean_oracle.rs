//! THE ORACLE TEETH for `bfv_lean` — fhe.rs is the authority, not our own
//! reconstruction. Every test encrypts and/or decrypts with REAL fhe.rs; the
//! from-scratch RNS add sits in the middle. If our add is wrong in any bit,
//! fhe.rs decrypts the wrong sum (or refuses the bytes) and the test is RED —
//! agreement with a real BFV library cannot be faked.
//!
//! Params (asserted, not assumed): degree-4096, RNS moduli
//! {0xffffee001, 0xffffc4001, 0x1ffffe0001}, t ≈ 2^20 — the exact set
//! `additive.rs` uses for the fold envelope.

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, Plaintext, PublicKey, SecretKey};
use fhe_traits::{
    DeserializeParametrized, FheDecoder, FheDecrypter, FheEncoder, FheEncrypter, Serialize,
};
use rand_09::rngs::StdRng;
use rand_09::SeedableRng;
use std::sync::Arc;

use fhegg_fhe::additive::pick_params;
use fhegg_fhe::bfv_lean::{
    fold, fold_add, rns_add_wrap_control, BfvLeanError, LeanCiphertext, FOLD_DEGREE, FOLD_MODULI,
};
use fhegg_fhe::{order_increment, Order, Side};

struct Fixture {
    params: Arc<BfvParameters>,
    sk: SecretKey,
    pk: PublicKey,
    rng: StdRng,
    t: u64,
}

fn fixture(seed: u64) -> Fixture {
    let params = pick_params(20);
    // Pin the parameter facts the whole lane is anchored to. If fhe.rs's
    // default set ever drifts, this fails LOUDLY instead of testing a
    // different scheme.
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

fn encrypt(fx: &mut Fixture, slots: &[u64]) -> Ciphertext {
    let pt = Plaintext::try_encode(slots, Encoding::simd(), &fx.params).expect("simd encode");
    fx.pk.try_encrypt(&pt, &mut fx.rng).expect("pk encrypt")
}

fn parse(fx: &Fixture, ct: &Ciphertext, plain_bound: u64) -> LeanCiphertext {
    LeanCiphertext::from_fhe_bytes(
        &ct.to_bytes(),
        fx.params.moduli(),
        fx.params.degree(),
        plain_bound,
    )
    .expect("parse fhe.rs ciphertext")
}

fn decrypt_slots(fx: &Fixture, lean: &LeanCiphertext, k: usize) -> Vec<u64> {
    let ct = Ciphertext::from_bytes(&lean.to_fhe_bytes(), &fx.params)
        .expect("fhe.rs accepts our re-serialized bytes");
    let pt = fx.sk.try_decrypt(&ct).expect("fhe.rs decrypt");
    let v = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("simd decode");
    v[..k].to_vec()
}

/// THE LOAD-BEARING TOOTH: fhe.rs encrypts two bucket-increment vectors, OUR
/// RNS add sums them, fhe.rs decrypts — result must equal the plaintext sum.
#[test]
fn oracle_single_add_decrypts_to_plaintext_sum() {
    let mut fx = fixture(0xB1F);
    let k = 16;
    // Two REAL bucket-increment vectors (a bid and another bid, so the sums land
    // in the same demand curve), exactly the fold's data shape.
    let o1 = Order {
        side: Side::Bid,
        limit: 8,
        qty: 7,
    };
    let o2 = Order {
        side: Side::Bid,
        limit: 12,
        qty: 41,
    };
    let v1: Vec<u64> = order_increment(&o1, k).iter().map(|&q| q as u64).collect();
    let v2: Vec<u64> = order_increment(&o2, k).iter().map(|&q| q as u64).collect();
    let ct1 = encrypt(&mut fx, &v1);
    let ct2 = encrypt(&mut fx, &v2);

    let a = parse(&fx, &ct1, 7);
    let b = parse(&fx, &ct2, 41);
    let sum = fold_add(&a, &b, fx.t).expect("in-budget add");

    let got = decrypt_slots(&fx, &sum, k);
    let want: Vec<u64> = v1.iter().zip(v2.iter()).map(|(x, y)| x + y).collect();
    assert_eq!(got, want, "fhe.rs decrypted a different sum than plaintext");
}

/// Byte differential: our add must produce EXACTLY the bytes fhe.rs's own
/// `&ct1 + &ct2` serializes to — not just something that decrypts right.
#[test]
fn oracle_bytes_match_fhers_own_add() {
    let mut fx = fixture(0xB2F);
    let k = 16;
    let v1: Vec<u64> = (0..k as u64).map(|i| i * 3 + 1).collect();
    let v2: Vec<u64> = (0..k as u64).map(|i| 1000 - i * 7).collect();
    let ct1 = encrypt(&mut fx, &v1);
    let ct2 = encrypt(&mut fx, &v2);

    let ours = fold_add(&parse(&fx, &ct1, 46), &parse(&fx, &ct2, 1000), fx.t)
        .expect("in-budget add")
        .to_fhe_bytes();
    let theirs = (&ct1 + &ct2).to_bytes();
    assert_eq!(ours, theirs, "byte-level divergence from fhe.rs's own add");
}

/// Parse → re-serialize with NO operation must be byte-identical (the codec
/// itself is oracle-anchored, not just the add).
#[test]
fn reencode_roundtrip_is_byte_identical() {
    let mut fx = fixture(0xB3F);
    let ct = encrypt(&mut fx, &[5u64, 4, 3, 2, 1]);
    let bytes = ct.to_bytes();
    let lean = LeanCiphertext::from_fhe_bytes(&bytes, fx.params.moduli(), fx.params.degree(), 5)
        .expect("parse");
    assert_eq!(lean.to_fhe_bytes(), bytes);
}

/// A REAL fold: N orders' packed increments folded by OUR add chain, checked
/// against (a) the plaintext reference curves and (b) fhe.rs's own fold.
#[test]
fn oracle_fold_of_book_matches_plaintext_reference_and_fhers_fold() {
    let mut fx = fixture(0xB4F);
    let k = 16;
    let n = 32;
    // Deterministic book, same shape the envelope benches use.
    let orders: Vec<Order> = (0..n)
        .map(|i| Order {
            side: if i % 2 == 0 { Side::Bid } else { Side::Ask },
            limit: (i * 5 + 3) % k,
            qty: ((i * 37 + 11) % 97 + 1) as u16,
        })
        .collect();

    for side in [Side::Bid, Side::Ask] {
        let mut cts: Vec<Ciphertext> = Vec::new();
        let mut leans: Vec<LeanCiphertext> = Vec::new();
        let mut reference = vec![0u64; k];
        for o in orders.iter().filter(|o| {
            matches!(
                (o.side, side),
                (Side::Bid, Side::Bid) | (Side::Ask, Side::Ask)
            )
        }) {
            let inc: Vec<u64> = order_increment(o, k).iter().map(|&q| q as u64).collect();
            for (r, i) in reference.iter_mut().zip(inc.iter()) {
                *r += i;
            }
            let ct = encrypt(&mut fx, &inc);
            leans.push(parse(&fx, &ct, o.qty as u64));
            cts.push(ct);
        }
        // (a) our fold vs the plaintext reference, through fhe.rs decrypt
        let folded = fold(&leans, fx.t).expect("in-budget fold");
        let got = decrypt_slots(&fx, &folded, k);
        assert_eq!(got, reference, "fold diverged from plaintext reference");
        // (b) our fold vs fhe.rs's own fold, at the byte level
        let mut fhe_acc = cts[0].clone();
        for ct in &cts[1..] {
            fhe_acc = &fhe_acc + ct;
        }
        assert_eq!(
            folded.to_fhe_bytes(),
            fhe_acc.to_bytes(),
            "fold diverged from fhe.rs's own fold at the byte level"
        );
    }
}

/// Class-(C) WRAP TOOTH, both directions:
/// (1) the CONTROL proves the danger is real — without the gate, (t-1) + 2
///     silently decrypts to 1 under fhe.rs (wrapped mod t, no error anywhere);
/// (2) the gate REFUSES that add (named `WrapRefused`), and
/// (3) the gate is not over-broad: bounds summing to exactly t-1 pass and
///     decrypt to the true sum.
#[test]
fn wrap_is_real_and_refused_not_silently_wrapped() {
    let mut fx = fixture(0xB5F);
    let t = fx.t;
    let hot = encrypt(&mut fx, &[t - 1]);
    let two = encrypt(&mut fx, &[2u64]);
    let a = parse(&fx, &hot, t - 1);
    let b = parse(&fx, &two, 2);

    // (1) CONTROL: the wrap is real and SILENT — fhe.rs decrypts (t+1) mod t.
    let wrapped = rns_add_wrap_control(&a, &b).expect("control add");
    let got = decrypt_slots(&fx, &wrapped, 1);
    assert_eq!(
        got[0], 1,
        "expected silent wrap to (t+1) mod t = 1; fhe.rs gave {}",
        got[0]
    );
    assert_ne!(got[0], (t - 1) + 2, "true sum is unrepresentable mod t");

    // (2) the gate refuses exactly this.
    match fold_add(&a, &b, t) {
        Err(BfvLeanError::WrapRefused {
            bound_sum,
            plaintext_modulus,
        }) => {
            assert_eq!(bound_sum, u128::from(t) + 1);
            assert_eq!(plaintext_modulus, t);
        }
        other => panic!("expected WrapRefused, got {other:?}"),
    }

    // (3) not over-broad: bounds t-3 and 2 sum to t-1 < t → allowed + correct.
    let cold = encrypt(&mut fx, &[t - 3]);
    let c = parse(&fx, &cold, t - 3);
    let ok = fold_add(&c, &b, t).expect("bounds summing to t-1 must pass");
    assert_eq!(decrypt_slots(&fx, &ok, 1)[0], t - 1);
}

/// Seeded (secret-key-encrypted) ciphertexts are a NAMED later stone — the
/// parser must refuse them loudly, not guess at ChaCha8 seed expansion.
#[test]
fn seeded_ciphertext_refused_loudly() {
    let mut fx = fixture(0xB6F);
    let pt = Plaintext::try_encode(&[1u64, 2, 3], Encoding::simd(), &fx.params).expect("encode");
    let ct: Ciphertext = fx.sk.try_encrypt(&pt, &mut fx.rng).expect("sk encrypt");
    let err =
        LeanCiphertext::from_fhe_bytes(&ct.to_bytes(), fx.params.moduli(), fx.params.degree(), 3)
            .unwrap_err();
    assert_eq!(err, BfvLeanError::SeededCiphertext);
}

/// Mismatched operands are refused, and an empty fold is refused.
#[test]
fn incompatible_and_empty_folds_refused() {
    let mut fx = fixture(0xB7F);
    let ct = encrypt(&mut fx, &[1u64]);
    let a = parse(&fx, &ct, 1);
    let mut b = a.clone();
    b.level = 1;
    assert!(matches!(
        fold_add(&a, &b, fx.t),
        Err(BfvLeanError::Incompatible("level differs"))
    ));
    assert!(matches!(fold(&[], fx.t), Err(BfvLeanError::EmptyFold)));
}
