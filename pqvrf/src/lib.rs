//! A readable reference implementation of the one-time LB-VRF of Esgin et al.
//!
//! # Construction and concrete parameters
//!
//! This crate implements Set I from M. F. Esgin, V. Kuchta, A. Sakzad,
//! R. Steinfeld, Z. Zhang, S. Sun, and S. Chu, *Practical Post-Quantum
//! Few-Time Verifiable Random Function with Applications to Algorand*, FC
//! 2021, full version [IACR ePrint 2020/1222](https://eprint.iacr.org/2020/1222).
//! The paper reports this set as one-time, with a 4.94 KB compressed proof,
//! an 84-byte VRF value, a 3.32 KB public key, and root-Hermite factor about
//! 1.0045. Later literature classifies it as NIST security level II.
//!
//! The exact algebraic parameters used here are [`DEGREE`] = 256,
//! [`MODULUS_Q`] = 100,679,681, [`MODULUS_P`] = 2,097,169, MSIS rank
//! [`MSIS_RANK`] = 4, secret width [`SECRET_WIDTH`] = 9, sparse challenge
//! weight [`CHALLENGE_WEIGHT`] = 39, and masking bound [`MASK_BOUND`] =
//! 89,856. The main ring is `R_q = Z_q[x]/(x^256+1)`. Values live in
//! `Rbar_p = Z_p[x]/(x^32+852368)`, the paper's factor-ring representation.
//! The secret is ternary and the public key is exactly `t = A*s`.
//!
//! Evaluation derives `b = G(A,t,input)`, returns `v = <b,s>` and proves the
//! two short relations with Fiat--Shamir-with-aborts:
//!
//! ```text
//! z = y + c*s
//! A*z = w1 + c*t                         over R_q
//! <b,z> = w2 + c*v                       over Rbar_p
//! c = H(A,t,input,w1,w2,v)
//! ||z||_infinity <= beta-kappa
//! ```
//!
//! BLAKE3, with separate domain strings, realizes `G`, `H`, deterministic
//! masking, and expansion of the fixed public matrix. Polynomial products are
//! deliberately schoolbook products: this is a reviewable reference, not an
//! optimized NTT implementation. The fixed matrix is generated from the
//! versioned [`PARAMETER_ID`]; changing that string changes the scheme.
//!
//! # Rust to Lean map
//!
//! The abstract object in `metatheory/Dregg2/Crypto/VRF.lean` maps as follows:
//!
//! - [`SecretKey`], [`PublicKey`], `&[u8]`, [`Output`], and [`Proof`] realize
//!   its `SK`, `PK`, `Input`, `Output`, and `Proof` carriers.
//! - [`keygen`] plus [`SecretKey::public_key`] realize `VRF.pkOf`; [`eval`]
//!   realizes `VRF.eval`; [`verify`] realizes `VRF.verify`.
//! - The honest round trip tested by `honest_evaluation_verifies` is the
//!   executable counterpart of `Correct` / `provability`.
//! - Rejecting every tested second value in `uniqueness_no_second_output_verifies`
//!   exercises the `UniqueOutputs` / `uniqueness_at_most_one` boundary.
//! - [`PublicKey::t`] is `t = A*s`, the key shape used by
//!   `Dregg2.Crypto.HermineMSIS`.
//! - The verifier's `A*z = w1 + c*t` check is the concrete
//!   `latticeVerify` relation. Two accepting transcripts subtract to the short
//!   augmented-kernel vector used by `lattice_vrf_uniqueness_reduces_to_msis`
//!   and `lattice_vrf_unique_under_msis`.
//!
//! There is an important refinement boundary: the Lean lattice skeleton names
//! the scalar in `A*z = w + y*t` as `y`; in the complete paper construction
//! that scalar is the Fiat--Shamir challenge `c`, while the externally returned
//! VRF value is `v` and is bound by the second relation. Thus the Lean theorem
//! proves the load-bearing MSIS extraction shape, but it is not by itself a
//! machine-checked end-to-end refinement theorem for this Rust program.
//!
//! # Assurance boundary
//!
//! Computational uniqueness is grounded in Module-SIS through the short
//! accepting relations, matching the proved Lean reduction shape. Output
//! pseudorandomness is an MLWE-based assumption and remains the undischarged
//! `Pseudorandom` obligation in Lean. Set I is **one-time**: [`eval`] consumes
//! the only evaluation in a [`SecretKey`] and returns
//! [`EvalError::EvaluationLimitExceeded`] thereafter. Applications must also
//! prevent cloning, rollback, or restoring old secret-key state at the storage
//! layer; an in-memory counter cannot solve rollback.
//!
//! This crate has no compressed/canonical wire codec, constant-time audit,
//! secret zeroization, fault hardening, or independent cryptographic audit. It
//! is not production cryptography. In particular, its in-memory structs do not
//! have the compressed sizes quoted by the paper.

#![forbid(unsafe_code)]

mod polynomial;

use polynomial::{
    OutputPoly, inner_product_output, matrix_vector_product, mul_output, mul_q_signed,
    reduce_to_output, sub_output, sub_q,
};
use std::fmt;
use std::sync::OnceLock;

/// Degree of the paper's main negacyclic ring `R_q`.
pub const DEGREE: usize = 256;
/// Prime modulus of `R_q` in Set I.
pub const MODULUS_Q: u32 = 100_679_681;
/// Degree of the paper's output quotient ring.
pub const OUTPUT_DEGREE: usize = 32;
/// Prime modulus of the output quotient ring.
pub const MODULUS_P: u32 = 2_097_169;
/// Constant term of `x^32 + 852368`, the output-ring modulus polynomial.
pub const OUTPUT_POLYNOMIAL_CONSTANT: u32 = 852_368;
/// Module-SIS row rank (`n` in the paper).
pub const MSIS_RANK: usize = 4;
/// Width `n + ell + k = 4 + 4 + 1` of the public matrix and secret.
pub const SECRET_WIDTH: usize = 9;
/// Hamming weight `kappa` of a Fiat--Shamir challenge.
pub const CHALLENGE_WEIGHT: usize = 39;
/// Coefficient bound `beta` for masking randomness.
pub const MASK_BOUND: i32 = 89_856;
/// Verification bound `beta - kappa` on every response coefficient.
pub const RESPONSE_BOUND: i32 = MASK_BOUND - CHALLENGE_WEIGHT as i32;
/// Set I's number of permitted evaluations per key.
pub const MAX_EVALUATIONS: u64 = 1;
/// Versioned identifier from which the global public matrix is expanded.
pub const PARAMETER_ID: &[u8] = b"dregg.pqvrf.lb-vrf.fc2021.set-i.blake3.v1";

const MAX_MASK_ATTEMPTS: u32 = 128;

type Matrix = [[[u32; DEGREE]; SECRET_WIDTH]; MSIS_RANK];

static PUBLIC_MATRIX: OnceLock<Matrix> = OnceLock::new();

/// One canonical polynomial in `R_q`, used for each public-key component.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicPolynomial {
    /// Coefficients in the canonical interval `[0,q)`.
    pub coefficients: [u32; DEGREE],
}

/// LB-VRF public key `t = A*s`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PublicKey {
    /// The four `R_q` components of `t`.
    pub t: [PublicPolynomial; MSIS_RANK],
}

/// Stateful, one-time LB-VRF secret key.
///
/// Deliberately does not implement `Clone`: duplicating it would duplicate the
/// local usage counter. Rollback protection still belongs to persistent state.
pub struct SecretKey {
    secret: [[i8; DEGREE]; SECRET_WIDTH],
    public_key: PublicKey,
    evaluations: u64,
}

impl fmt::Debug for SecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SecretKey")
            .field("secret", &"REDACTED")
            .field("public_key", &self.public_key)
            .field("evaluations", &self.evaluations)
            .finish()
    }
}

impl SecretKey {
    /// Returns the corresponding public key (`VRF.pkOf` in the Lean model).
    #[must_use]
    pub fn public_key(&self) -> &PublicKey {
        &self.public_key
    }

    /// Number of successful evaluations already consumed.
    #[must_use]
    pub fn evaluations_used(&self) -> u64 {
        self.evaluations
    }

    /// Number of evaluations still available in this key epoch.
    #[must_use]
    pub fn evaluations_remaining(&self) -> u64 {
        MAX_EVALUATIONS.saturating_sub(self.evaluations)
    }
}

/// A canonical value in `Z_p[x]/(x^32+852368)`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Output {
    /// Coefficients in the canonical interval `[0,p)`.
    pub coefficients: [u32; OUTPUT_DEGREE],
}

/// A signed response polynomial. These are untrusted proof inputs to `verify`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResponsePolynomial {
    /// Centered coefficients, each required to have magnitude at most
    /// [`RESPONSE_BOUND`].
    pub coefficients: [i32; DEGREE],
}

/// Sparse ternary Fiat--Shamir challenge.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ChallengePolynomial {
    /// Exactly [`CHALLENGE_WEIGHT`] entries must be `-1` or `1`; all others
    /// must be zero.
    pub coefficients: [i8; DEGREE],
}

/// Paper proof `(z,c)`; the output `v` is passed separately to [`verify`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proof {
    /// Short response vector `z`.
    pub response: [ResponsePolynomial; SECRET_WIDTH],
    /// Fiat--Shamir challenge `c`.
    pub challenge: ChallengePolynomial,
}

/// Errors returned by stateful evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EvalError {
    /// Set I permits only one successful evaluation per key epoch.
    EvaluationLimitExceeded,
    /// Rejection sampling failed far beyond its paper-estimated expectation.
    SamplingFailure,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EvaluationLimitExceeded => {
                f.write_str("the one-time LB-VRF evaluation budget is exhausted")
            }
            Self::SamplingFailure => f.write_str("Fiat-Shamir-with-aborts sampling failed"),
        }
    }
}

impl std::error::Error for EvalError {}

/// Deterministically derives a Set I keypair from a 32-byte seed.
///
/// Production integration should supply a seed from an approved operating
/// system CSPRNG and protect both the seed and returned secret state.
#[must_use]
pub fn keygen(seed: &[u8; 32]) -> (PublicKey, SecretKey) {
    let mut reader = xof(&[b"pqvrf.keygen.v1", PARAMETER_ID, seed]);
    let mut secret = [[0_i8; DEGREE]; SECRET_WIDTH];
    for polynomial in &mut secret {
        for coefficient in polynomial {
            *coefficient = sample_ternary(&mut reader);
        }
    }

    let signed_secret = secret.map(|poly| poly.map(i32::from));
    let t = matrix_vector_product(public_matrix(), &signed_secret)
        .map(|coefficients| PublicPolynomial { coefficients });
    let public_key = PublicKey { t };
    let secret_key = SecretKey {
        secret,
        public_key: public_key.clone(),
        evaluations: 0,
    };
    (public_key, secret_key)
}

/// Evaluates the one-time VRF and returns `(output, proof)` (`VRF.eval`).
///
/// The output is deterministic for a fixed key and input. The proof masking is
/// also derived deterministically, avoiding reliance on fresh prover entropy.
/// A successful call consumes the key's sole Set I evaluation.
pub fn eval(secret_key: &mut SecretKey, input: &[u8]) -> Result<(Output, Proof), EvalError> {
    if secret_key.evaluations >= MAX_EVALUATIONS {
        return Err(EvalError::EvaluationLimitExceeded);
    }

    let context = context_hash(&secret_key.public_key, input);
    let basis = hash_to_basis(&context);
    let secret_output = secret_key.secret.map(reduce_to_output);
    let output_coefficients = inner_product_output(&basis, &secret_output);
    let output = Output {
        coefficients: output_coefficients,
    };

    for attempt in 0..MAX_MASK_ATTEMPTS {
        let masking = sample_mask(&secret_key.secret, &context, attempt);
        let w1 = matrix_vector_product(public_matrix(), &masking);
        let masking_output = masking.map(reduce_to_output);
        let w2 = inner_product_output(&basis, &masking_output);
        let challenge = hash_to_challenge(&context, &w1, &w2, &output);
        let mut response = masking;

        for (response_polynomial, secret_polynomial) in response.iter_mut().zip(&secret_key.secret)
        {
            let challenge_times_secret = negacyclic_sparse_product(&challenge, secret_polynomial);
            for (coefficient, delta) in response_polynomial.iter_mut().zip(challenge_times_secret) {
                *coefficient += delta;
            }
        }

        if response_is_short(&response) {
            secret_key.evaluations += 1;
            return Ok((
                output,
                Proof {
                    response: response.map(|coefficients| ResponsePolynomial { coefficients }),
                    challenge: ChallengePolynomial {
                        coefficients: challenge,
                    },
                },
            ));
        }
    }

    Err(EvalError::SamplingFailure)
}

/// Verifies an `(output, proof)` pair (`VRF.verify` in the Lean model).
///
/// This function treats every public field as adversarial: it checks canonical
/// encodings, exact challenge weight, challenge coefficient range, and the
/// response infinity norm before performing either accepting relation.
#[must_use]
pub fn verify(public_key: &PublicKey, input: &[u8], output: &Output, proof: &Proof) -> bool {
    if !public_key_is_canonical(public_key)
        || output.coefficients.iter().any(|&x| x >= MODULUS_P)
        || !challenge_is_valid(&proof.challenge.coefficients)
    {
        return false;
    }

    let response = proof.response.clone().map(|poly| poly.coefficients);
    if !response_is_short(&response) {
        return false;
    }

    let context = context_hash(public_key, input);
    let basis = hash_to_basis(&context);
    let az = matrix_vector_product(public_matrix(), &response);
    let challenge = &proof.challenge.coefficients;

    let mut w1 = [[0_u32; DEGREE]; MSIS_RANK];
    for row in 0..MSIS_RANK {
        let ct = mul_q_signed(&public_key.t[row].coefficients, &challenge.map(i32::from));
        w1[row] = sub_q(&az[row], &ct);
    }

    let response_output = response.map(reduce_to_output);
    let bz = inner_product_output(&basis, &response_output);
    let challenge_output = reduce_to_output(challenge.map(i32::from));
    let cv = mul_output(&challenge_output, &output.coefficients);
    let w2 = sub_output(&bz, &cv);
    let expected = hash_to_challenge(&context, &w1, &w2, output);
    expected == *challenge
}

fn public_matrix() -> &'static Matrix {
    PUBLIC_MATRIX.get_or_init(|| {
        let mut reader = xof(&[b"pqvrf.public-matrix.v1", PARAMETER_ID]);
        let mut matrix = [[[0_u32; DEGREE]; SECRET_WIDTH]; MSIS_RANK];
        for row in &mut matrix {
            for polynomial in row {
                for coefficient in polynomial {
                    *coefficient = sample_mod(&mut reader, MODULUS_Q);
                }
            }
        }
        matrix
    })
}

fn context_hash(public_key: &PublicKey, input: &[u8]) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pqvrf.input-context.v1");
    hasher.update(PARAMETER_ID);
    for polynomial in &public_key.t {
        for coefficient in polynomial.coefficients {
            hasher.update(&coefficient.to_le_bytes());
        }
    }
    hasher.update(&(input.len() as u64).to_le_bytes());
    hasher.update(input);
    *hasher.finalize().as_bytes()
}

fn hash_to_basis(context: &[u8; 32]) -> [OutputPoly; SECRET_WIDTH] {
    let mut reader = xof(&[b"pqvrf.hash-to-basis.v1", context]);
    let mut basis = [[0_u32; OUTPUT_DEGREE]; SECRET_WIDTH];
    for polynomial in &mut basis {
        for coefficient in polynomial {
            *coefficient = sample_mod(&mut reader, MODULUS_P);
        }
    }
    basis
}

fn hash_to_challenge(
    context: &[u8; 32],
    w1: &[[u32; DEGREE]; MSIS_RANK],
    w2: &OutputPoly,
    output: &Output,
) -> [i8; DEGREE] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"pqvrf.fiat-shamir-challenge.v1");
    hasher.update(context);
    for polynomial in w1 {
        for coefficient in polynomial {
            hasher.update(&coefficient.to_le_bytes());
        }
    }
    for coefficient in w2 {
        hasher.update(&coefficient.to_le_bytes());
    }
    for coefficient in output.coefficients {
        hasher.update(&coefficient.to_le_bytes());
    }
    let mut reader = hasher.finalize_xof();
    let mut challenge = [0_i8; DEGREE];
    let mut selected = 0;
    while selected < CHALLENGE_WEIGHT {
        let mut bytes = [0_u8; 2];
        reader.fill(&mut bytes);
        let position = usize::from(bytes[0]);
        if challenge[position] == 0 {
            challenge[position] = if bytes[1] & 1 == 0 { -1 } else { 1 };
            selected += 1;
        }
    }
    challenge
}

fn sample_mask(
    secret: &[[i8; DEGREE]; SECRET_WIDTH],
    context: &[u8; 32],
    attempt: u32,
) -> [[i32; DEGREE]; SECRET_WIDTH] {
    let mut key_deriver =
        blake3::Hasher::new_derive_key("dregg pqvrf deterministic masking key v1");
    for polynomial in secret {
        for &coefficient in polynomial {
            key_deriver.update(&coefficient.to_le_bytes());
        }
    }
    let masking_key = *key_deriver.finalize().as_bytes();
    let mut hasher = blake3::Hasher::new_keyed(&masking_key);
    hasher.update(PARAMETER_ID);
    hasher.update(context);
    hasher.update(&attempt.to_le_bytes());
    let mut reader = hasher.finalize_xof();
    let width = (2 * MASK_BOUND + 1) as u32;
    let mut masking = [[0_i32; DEGREE]; SECRET_WIDTH];
    for polynomial in &mut masking {
        for coefficient in polynomial {
            *coefficient = sample_mod(&mut reader, width) as i32 - MASK_BOUND;
        }
    }
    masking
}

fn negacyclic_sparse_product(challenge: &[i8; DEGREE], secret: &[i8; DEGREE]) -> [i32; DEGREE] {
    let mut result = [0_i32; DEGREE];
    for (i, &c) in challenge.iter().enumerate() {
        if c == 0 {
            continue;
        }
        for (j, &s) in secret.iter().enumerate() {
            let product = i32::from(c) * i32::from(s);
            if i + j < DEGREE {
                result[i + j] += product;
            } else {
                result[i + j - DEGREE] -= product;
            }
        }
    }
    result
}

fn response_is_short(response: &[[i32; DEGREE]; SECRET_WIDTH]) -> bool {
    response
        .iter()
        .flatten()
        .all(|&coefficient| (-RESPONSE_BOUND..=RESPONSE_BOUND).contains(&coefficient))
}

fn challenge_is_valid(challenge: &[i8; DEGREE]) -> bool {
    let mut weight = 0;
    for &coefficient in challenge {
        match coefficient {
            -1 | 1 => weight += 1,
            0 => {}
            _ => return false,
        }
    }
    weight == CHALLENGE_WEIGHT
}

fn public_key_is_canonical(public_key: &PublicKey) -> bool {
    public_key
        .t
        .iter()
        .flat_map(|poly| poly.coefficients)
        .all(|coefficient| coefficient < MODULUS_Q)
}

fn xof(parts: &[&[u8]]) -> blake3::OutputReader {
    let mut hasher = blake3::Hasher::new();
    for part in parts {
        hasher.update(&(part.len() as u64).to_le_bytes());
        hasher.update(part);
    }
    hasher.finalize_xof()
}

fn sample_mod(reader: &mut blake3::OutputReader, modulus: u32) -> u32 {
    let modulus = u64::from(modulus);
    let zone = (1_u64 << 32) / modulus * modulus;
    loop {
        let mut bytes = [0_u8; 4];
        reader.fill(&mut bytes);
        let sample = u64::from(u32::from_le_bytes(bytes));
        if sample < zone {
            return (sample % modulus) as u32;
        }
    }
}

fn sample_ternary(reader: &mut blake3::OutputReader) -> i8 {
    loop {
        let mut byte = [0_u8; 1];
        reader.fill(&mut byte);
        if byte[0] < 255 {
            return (byte[0] % 3) as i8 - 1;
        }
    }
}

/// The Module-SIS uniqueness reduction, exhibited in code.
///
/// This module makes the load-bearing Lean leg concrete. `verify`'s first
/// accepting relation is `A*z = w1 + c*t` — the exact `latticeVerify` relation
/// of `metatheory/Dregg2/Crypto/VRF.lean`. The theorem
/// `lattice_vrf_uniqueness_reduces_to_msis` there says: two accepting
/// transcripts `(z1,c1)`, `(z2,c2)` on the *same* commitment `w1` with `c1 != c2`
/// subtract to `(z1 - z2, -(c1 - c2))`, a short nonzero kernel vector of the
/// augmented map `[A | t]` — a genuine `IsMSISSolution`. Uniqueness therefore
/// rests on Module-SIS: no party without the secret can produce that pair.
///
/// A malicious *holder* could produce two transcripts sharing a commitment (via
/// mask reuse across two challenges), and this test does exactly that to exhibit
/// the extracted vector — precisely why doing so *is* an MSIS solution, and why
/// an outsider cannot. The two accepting-relation identities and the augmented
/// kernel identity are checked symbolically against the ring arithmetic.
#[cfg(test)]
mod msis_reduction {
    use super::polynomial::{add_q, matrix_vector_product, mul_q_signed, sub_q};
    use super::*;

    /// Builds `z = y + c*s` (over the integers, negacyclic in `x^256+1`), the
    /// short response the honest prover would emit for mask `y`, challenge `c`.
    fn response_for(
        secret: &[[i8; DEGREE]; SECRET_WIDTH],
        mask: &[[i32; DEGREE]; SECRET_WIDTH],
        challenge: &[i8; DEGREE],
    ) -> [[i32; DEGREE]; SECRET_WIDTH] {
        let mut z = *mask;
        for (z_j, s_j) in z.iter_mut().zip(secret) {
            let cs = negacyclic_sparse_product(challenge, s_j);
            for (coefficient, delta) in z_j.iter_mut().zip(cs) {
                *coefficient += delta;
            }
        }
        z
    }

    /// A valid sparse ternary challenge of weight `CHALLENGE_WEIGHT`, placing
    /// `+1` at the given contiguous offset (two distinct offsets => `c1 != c2`).
    fn sparse_challenge(offset: usize) -> [i8; DEGREE] {
        let mut c = [0_i8; DEGREE];
        for i in 0..CHALLENGE_WEIGHT {
            c[offset + i] = 1;
        }
        c
    }

    #[test]
    fn two_transcripts_share_commitment_yield_short_augmented_kernel_vector() {
        let seed = [0x42_u8; 32];
        let (public_key, secret_key) = keygen(&seed);
        let secret = secret_key.secret;
        let t: [[u32; DEGREE]; MSIS_RANK] = std::array::from_fn(|r| public_key.t[r].coefficients);

        // One shared commitment w1 = A*y from a single mask y.
        let context = context_hash(&public_key, b"msis-reduction-demo");
        let mask = sample_mask(&secret, &context, 0);
        let w1 = matrix_vector_product(public_matrix(), &mask);

        // Two DISTINCT valid challenges over the SAME commitment.
        let c1 = sparse_challenge(0);
        let c2 = sparse_challenge(1);
        assert_ne!(c1, c2);
        assert!(challenge_is_valid(&c1) && challenge_is_valid(&c2));

        let z1 = response_for(&secret, &mask, &c1);
        let z2 = response_for(&secret, &mask, &c2);

        let c1_i32 = c1.map(i32::from);
        let c2_i32 = c2.map(i32::from);

        // Each transcript satisfies the first accepting relation A*z = w1 + c*t.
        let az1 = matrix_vector_product(public_matrix(), &z1);
        let az2 = matrix_vector_product(public_matrix(), &z2);
        for r in 0..MSIS_RANK {
            assert_eq!(az1[r], add_q(&w1[r], &mul_q_signed(&t[r], &c1_i32)));
            assert_eq!(az2[r], add_q(&w1[r], &mul_q_signed(&t[r], &c2_i32)));
        }

        // The extracted augmented-kernel vector (z1 - z2, -(c1 - c2)).
        let mut dz = [[0_i32; DEGREE]; SECRET_WIDTH];
        for j in 0..SECRET_WIDTH {
            for i in 0..DEGREE {
                dz[j][i] = z1[j][i] - z2[j][i];
            }
        }
        let dc: [i32; DEGREE] = std::array::from_fn(|i| c1_i32[i] - c2_i32[i]);

        // NONZERO — from the challenge (output) coordinate: c1 != c2.
        assert!(dc.iter().any(|&x| x != 0));
        assert!(dz.iter().flatten().any(|&x| x != 0));

        // SHORT — dz = (c1 - c2)*s is bounded by 2*CHALLENGE_WEIGHT (each output
        // coefficient sums at most 2*kappa ternary terms), well under q.
        let dz_bound = 2 * CHALLENGE_WEIGHT as i32;
        assert!(dz.iter().flatten().all(|&x| x.abs() <= dz_bound));

        // KERNEL of the augmented map [A | t]: A*(z1 - z2) - (c1 - c2)*t = 0
        // (mod q). This is `augmented A t (dz, -dc) = 0` — an IsMSISSolution.
        let a_dz = matrix_vector_product(public_matrix(), &dz);
        for r in 0..MSIS_RANK {
            let dc_t = mul_q_signed(&t[r], &dc);
            let residual = sub_q(&a_dz[r], &dc_t);
            assert!(
                residual.iter().all(|&x| x == 0),
                "augmented kernel identity A*(z1-z2) = (c1-c2)*t must hold mod q",
            );
        }
    }
}
