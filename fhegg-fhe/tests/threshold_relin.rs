//! Multiparty relinearization-key custody teeth.
//!
//! The load-bearing test uses the exact party shares that formed a real
//! collective fhe.rs public key, runs the two-round mbfv relinearization
//! ceremony, performs an actual encrypted ciphertext×ciphertext multiply, and
//! opens only the product through fhEgg's Lean-pinned smudged threshold
//! decrypt.  No joint `SecretKey` is constructed anywhere in this test.

use std::time::Duration;

use fhe::bfv::{Encoding, Plaintext};
use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};
use fhegg_fhe::bfv_lean::LeanCiphertext;
use fhegg_fhe::bfv_mul::{BoundedCiphertext, MulEngine};
use fhegg_fhe::dark_amm::DarkPool;
use fhegg_fhe::threshold::relin::{generate_relinearization_key, RelinError, RelinKeySession};
use fhegg_fhe::threshold::{
    combine, BfvParams, CollectivePublicKey, KeygenCoordinator, KeygenSession, ThresholdParty,
    MIN_SMUDGE_BITS,
};

fn collective_keygen(
    n: usize,
    params: &BfvParams,
) -> (KeygenSession, CollectivePublicKey, Vec<ThresholdParty>) {
    let session = KeygenSession::random(n).expect("keygen session");
    let mut coordinator = KeygenCoordinator::new(session.clone(), params.clone());
    let mut parties = Vec::with_capacity(n);
    for party_index in 0..n {
        let (party, contribution) =
            ThresholdParty::join(&session, party_index, params).expect("party keygen");
        coordinator
            .accept(contribution)
            .expect("public contribution");
        parties.push(party);
    }
    let collective = coordinator.finish().expect("collective public key");
    (session, collective, parties)
}

#[test]
fn party_owned_relin_drives_hidden_amount_dark_amm_and_threshold_decrypts() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (keygen, collective, parties) = collective_keygen(N, &params);
    let session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0x52; 32],
        Duration::from_secs(90),
    )
    .expect("relin session");

    let relin = generate_relinearization_key(&session, &params, &collective, &parties)
        .expect("n-of-n relin ceremony");

    let a = 41u64;
    let b = 7u64;
    let plaintext_a =
        Plaintext::try_encode(&[a], Encoding::simd(), params.arc()).expect("encode a");
    let plaintext_b =
        Plaintext::try_encode(&[b], Encoding::simd(), params.arc()).expect("encode b");
    let mut rng = rand_09::rng();
    let ciphertext_a = collective
        .pk
        .try_encrypt(&plaintext_a, &mut rng)
        .expect("collective encrypt a");
    let ciphertext_b = collective
        .pk
        .try_encrypt(&plaintext_b, &mut rng)
        .expect("collective encrypt b");

    let engine = MulEngine::new(&relin, params.arc()).expect("multiplication engine");
    let product = engine
        .multiply(
            &BoundedCiphertext::new(ciphertext_a, a),
            &BoundedCiphertext::new(ciphertext_b, b),
        )
        .expect("exact in-bound ciphertext product");
    assert_eq!(product.plain_bound, a * b);

    let product = LeanCiphertext::from_fhe_bytes(
        &product.ct.to_bytes(),
        params.moduli(),
        params.degree(),
        a * b,
    )
    .expect("product crosses the strict Lean ciphertext boundary");
    let shares = parties
        .iter()
        .map(|party| {
            party
                .partial_decrypt(&product, MIN_SMUDGE_BITS)
                .expect("Lean-pinned smudged product share")
        })
        .collect::<Vec<_>>();
    let opened = combine(&shares, &params).expect("full threshold product opening");
    assert_eq!(opened[0], a * b, "real collective BFV product is exact");

    // Feed the same collectively generated relin key into the actual Dark AMM
    // state machine.  The invariant and post-state are opened here only as a
    // differential test; every opening still uses the n-of-n smudged path.
    let mut pool_rng = rand_09::rng();
    let mut pool = DarkPool::init(
        params.arc(),
        &collective.pk,
        &relin,
        60,
        70,
        80,
        80,
        &mut pool_rng,
    )
    .expect("collective-key Dark AMM pool");
    pool.strip_lp_view();
    let encrypted_dx = BoundedCiphertext::new(
        collective
            .pk
            .try_encrypt(
                &Plaintext::try_encode(&[10u64], Encoding::simd(), params.arc())
                    .expect("encode hidden dx"),
                &mut pool_rng,
            )
            .expect("encrypt hidden dx"),
        10,
    );
    let encrypted_dy = BoundedCiphertext::new(
        collective
            .pk
            .try_encrypt(
                &Plaintext::try_encode(&[10u64], Encoding::simd(), params.arc())
                    .expect("encode hidden dy"),
                &mut pool_rng,
            )
            .expect("encrypt hidden dy"),
        10,
    );
    let candidate = pool
        .try_private_swap_proposed(&encrypted_dx, &encrypted_dy)
        .expect("encrypted-amount constant-product transition");
    let invariant = LeanCiphertext::from_fhe_bytes(
        &candidate.invariant.ct.to_bytes(),
        params.moduli(),
        params.degree(),
        candidate.invariant.plain_bound,
    )
    .expect("Dark AMM invariant boundary");
    let invariant_shares = parties
        .iter()
        .map(|party| {
            party
                .partial_decrypt(&invariant, MIN_SMUDGE_BITS)
                .expect("invariant decrypt share")
        })
        .collect::<Vec<_>>();
    let invariant_opened = combine(&invariant_shares, &params).expect("threshold invariant open");
    assert_eq!(invariant_opened[0], 4_200);
    pool.commit_private(candidate, invariant_opened[0])
        .expect("atomic hidden-amount Dark AMM commit");

    for (reserve, expected) in [
        (&pool.reserve_cts().ct_x, 70u64),
        (&pool.reserve_cts().ct_y, 60u64),
    ] {
        let ciphertext = LeanCiphertext::from_fhe_bytes(
            &reserve.ct.to_bytes(),
            params.moduli(),
            params.degree(),
            reserve.plain_bound,
        )
        .expect("post-state reserve boundary");
        let shares = parties
            .iter()
            .map(|party| {
                party
                    .partial_decrypt(&ciphertext, MIN_SMUDGE_BITS)
                    .expect("post-state decrypt share")
            })
            .collect::<Vec<_>>();
        assert_eq!(
            combine(&shares, &params).expect("threshold post-state open")[0],
            expected
        );
    }
}

#[test]
fn ceremony_refuses_missing_duplicate_wrong_session_and_wrong_public_key() {
    const N: usize = 3;
    let params = BfvParams::fold_set();
    let (keygen, collective, parties) = collective_keygen(N, &params);
    let session = RelinKeySession::from_public_entropy(
        &keygen,
        &collective,
        [0x91; 32],
        Duration::from_secs(30),
    )
    .expect("relin session");

    assert_eq!(
        generate_relinearization_key(&session, &params, &collective, &parties[..N - 1])
            .expect_err("n-1 must fail"),
        RelinError::QuorumTooSmall {
            have: N - 1,
            need: N,
        }
    );

    let (duplicate_zero, _) =
        ThresholdParty::join(&keygen, 0, &params).expect("duplicate zero joins");
    let (duplicate_zero_again, _) =
        ThresholdParty::join(&keygen, 0, &params).expect("second duplicate zero joins");
    let (party_two, _) = ThresholdParty::join(&keygen, 2, &params).expect("party two joins");
    let duplicate_roster = vec![duplicate_zero, duplicate_zero_again, party_two];
    assert_eq!(
        generate_relinearization_key(&session, &params, &collective, &duplicate_roster)
            .expect_err("duplicate party must fail"),
        RelinError::DuplicateParty { party: 0 }
    );

    let wrong_keygen = KeygenSession::random(N).expect("other keygen session");
    let mut wrong_parties = Vec::with_capacity(N);
    for party_index in 0..N {
        wrong_parties.push(
            ThresholdParty::join(&wrong_keygen, party_index, &params)
                .expect("other party joins")
                .0,
        );
    }
    assert_eq!(
        generate_relinearization_key(&session, &params, &collective, &wrong_parties)
            .expect_err("cross-session share replay must fail"),
        RelinError::SessionMismatch { party: 0 }
    );

    // A second collective key can use the same public keygen CRP while being
    // formed from different secret shares.  The relin session binds the exact
    // resulting public key, not merely the public CRP/session label.
    let mut other_coordinator = KeygenCoordinator::new(keygen.clone(), params.clone());
    for party_index in 0..N {
        let (_, contribution) =
            ThresholdParty::join(&keygen, party_index, &params).expect("other collective party");
        other_coordinator
            .accept(contribution)
            .expect("other public contribution");
    }
    let other_collective = other_coordinator.finish().expect("other collective key");
    assert_eq!(
        generate_relinearization_key(&session, &params, &other_collective, &parties)
            .expect_err("public-key substitution must fail"),
        RelinError::PublicKeyMismatch
    );

    assert_eq!(
        RelinKeySession::from_public_entropy(&keygen, &collective, [0x91; 32], Duration::ZERO,)
            .expect_err("zero timeout must fail"),
        RelinError::ZeroTimeout
    );
}
