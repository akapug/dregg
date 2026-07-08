//! Trusted-dealer Shamir keygen over `R_q` and the single-ceremony threshold
//! signing helper — the Lean `hermine_cert_verifies_under_group_key` algebra,
//! executably. Structural mirror of `federation/src/frost.rs`'s
//! `FrostTestDealer` / `frost_sign`, over a module instead of a prime-order
//! group.
//!
//! # Production-signing boundary (read before even THINKING about wiring)
//!
//! Everything here is fit for tests and differentials against the Lean spec,
//! and for NOTHING else:
//! * the dealer transiently knows the group secret (no DKG);
//! * masks are sampled uniformly from a toy PRNG — real Raccoon/Hermine masks
//!   carry the noise-flooding distribution that makes Fiat–Shamir-without-
//!   aborts zero-knowledge, absent here;
//! * the challenge is a toy non-cryptographic hash into all of `R_q` — the
//!   deployed scheme uses a short challenge set with unit differences;
//! * no RFC-style per-signer binding factors (concurrent-session attacks
//!   apply), no constant-time arithmetic, toy parameters.

use crate::linalg::{Matrix, PolyVec};
use crate::ring::{inv_mod_q, Poly, N, Q};
use crate::verify;

// =============================================================================
// Toy deterministic sampling (splitmix64) — reference-only, NOT cryptographic
// =============================================================================

/// splitmix64 step — the toy PRNG behind deterministic dealing and masking.
fn splitmix64(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
}

/// A uniform-ish (mod-biased; irrelevant for a reference) element of `R_q`.
fn sample_poly(state: &mut u64) -> Poly {
    let mut coeffs = [0u64; N];
    for c in coeffs.iter_mut() {
        *c = splitmix64(state) % Q;
    }
    Poly { coeffs }
}

/// A vector of `len` sampled ring elements.
fn sample_vec(state: &mut u64, len: usize) -> PolyVec {
    PolyVec((0..len).map(|_| sample_poly(state)).collect())
}

/// The toy Fiat–Shamir challenge `c = H(w ‖ t ‖ message)` into `R_q`.
///
/// Domain-separated FNV-1a absorb, splitmix64 squeeze. NON-cryptographic:
/// its only job in the reference is to be a deterministic function of the
/// commitment, the public key, and the message (so honest verification and
/// the two-message forking test are both exact).
fn challenge(w: &PolyVec, group_key: &PolyVec, message: &[u8]) -> Poly {
    let mut h: u64 = 0xcbf29ce484222325;
    let mut absorb = |byte: u64| {
        h ^= byte;
        h = h.wrapping_mul(0x100000001b3);
    };
    absorb(w.len() as u64);
    for p in &w.0 {
        for &c in &p.coeffs {
            absorb(c);
        }
    }
    absorb(group_key.len() as u64);
    for p in &group_key.0 {
        for &c in &p.coeffs {
            absorb(c);
        }
    }
    absorb(message.len() as u64);
    for &b in message {
        absorb(b as u64);
    }
    let mut state = h;
    sample_poly(&mut state)
}

// =============================================================================
// Trusted-dealer Shamir keygen over R_q
// =============================================================================

/// One member's Shamir share of the group secret, dealt by
/// [`HermineTestDealer`] — the Lean `shares i : M`.
#[derive(Clone)]
pub struct HermineShare {
    /// 1-based Shamir evaluation index (x-coordinate; 0 is the group secret).
    pub index: u64,
    /// The share vector `f(index) ∈ R_q^ℓ`.
    share: PolyVec,
}

impl HermineShare {
    /// This member's share verification key `A·(λ_i·s_i)` for a given signing
    /// subset — the key share the Lean
    /// `hermine_share_is_valid_under_key_share` verifies partials against
    /// (the basis of non-interactive identifiable abort).
    pub fn key_share(&self, a: &Matrix, parts: &[u64]) -> PolyVec {
        let lam = Poly::constant(lagrange_at_zero(self.index, parts));
        a.mul_vec(&self.share.scale(&lam))
    }
}

/// Trusted-dealer Shamir keygen over `R_q^ℓ`, and the sampled public matrix.
///
/// The dealer transiently knows the group secret — exactly what a production
/// DKG removes. Mirror of `frost.rs`'s `FrostTestDealer`, with the Shamir
/// polynomial's coefficients living in the module `R_q^ℓ` and evaluation
/// points the constant polynomials `1..=n` (whose pairwise differences are
/// units in `R_q` since `q` is prime and `n < q` — the "everywhere-short"
/// linear reconstruction's invertibility, minus the shortness, which is the
/// norm carrier and out of scope here).
pub struct HermineTestDealer {
    /// The public matrix `A : R_q^ℓ → R_q^k`.
    pub a: Matrix,
    /// The group public key `t = A·s` (the Lean `A s`).
    pub group_key: PolyVec,
    /// The signing threshold `t` (shares needed to reconstruct at 0).
    pub threshold: u64,
    /// All dealt shares, index `i+1` at position `i`.
    pub shares: Vec<HermineShare>,
    /// The group secret `s = f(0)` — retained ONLY so tests can witness the
    /// reconstruction identity and the extractor's recovered secret. A real
    /// dealer must destroy this; a real scheme never materializes it.
    #[cfg_attr(not(test), allow(dead_code))]
    group_secret: PolyVec,
}

impl HermineTestDealer {
    /// Deal an `n`-member committee with threshold `t`, public matrix
    /// `rows × cols`, deterministically from `seed`.
    pub fn deal(rows: usize, cols: usize, n: u64, t: u64, seed: u64) -> Option<Self> {
        if t == 0 || t > n || n >= Q || rows == 0 || cols == 0 {
            return None;
        }
        let mut state = seed;
        let a = Matrix::from_fn(rows, cols, |_, _| sample_poly(&mut state));
        // f(x) = a_0 + a_1·x + … + a_{t-1}·x^{t-1}, coefficients in R_q^ℓ.
        let coeffs: Vec<PolyVec> = (0..t).map(|_| sample_vec(&mut state, cols)).collect();
        let eval = |x: &Poly| -> PolyVec {
            // Horner over the module.
            coeffs
                .iter()
                .rev()
                .fold(PolyVec::zero(cols), |acc, c| acc.scale(x).add(c))
        };
        let group_secret = coeffs[0].clone();
        let group_key = a.mul_vec(&group_secret);
        let shares = (1..=n)
            .map(|i| HermineShare {
                index: i,
                share: eval(&Poly::constant(i)),
            })
            .collect();
        Some(Self {
            a,
            group_key,
            threshold: t,
            shares,
            group_secret,
        })
    }

    /// Lagrange-reconstruct `Σ λ_i • s_i` over a share subset — the Lean
    /// `hrecon` right-hand side. Equals the group secret iff the subset
    /// carries ≥ threshold genuine shares.
    pub fn reconstruct(shares: &[&HermineShare]) -> PolyVec {
        let parts: Vec<u64> = shares.iter().map(|s| s.index).collect();
        shares
            .iter()
            .map(|s| {
                s.share
                    .scale(&Poly::constant(lagrange_at_zero(s.index, &parts)))
            })
            .reduce(|acc, v| acc.add(&v))
            .expect("reconstruct requires a nonempty subset")
    }

    /// Test-only witness of the dealt secret (see the field doc).
    #[cfg(test)]
    pub(crate) fn group_secret(&self) -> &PolyVec {
        &self.group_secret
    }
}

/// The Lagrange coefficient at 0 for participant `i` over the index set
/// `parts`, computed in `ℤ_q` (evaluation points are constants, so the
/// coefficient embeds into `R_q` as a constant — the Lean `lam i : R`).
fn lagrange_at_zero(i: u64, parts: &[u64]) -> u64 {
    let mut num = 1u64;
    let mut den = 1u64;
    for &j in parts {
        if j == i {
            continue;
        }
        num = num * (j % Q) % Q;
        den = den * ((j % Q + Q - i % Q) % Q) % Q;
    }
    num * inv_mod_q(den).expect("distinct indices < q have unit differences") % Q
}

// =============================================================================
// Single-ceremony threshold signing — the Lean theorem's algebra
// =============================================================================

/// A Hermine signature/transcript `(w, c, z)`: commitment, challenge,
/// combined response. [`verify`] accepts it iff `A·z = w + c·t`.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct HermineSignature {
    /// The combined commitment `w = A·(Σ y_i)` (the Lean `A (∑ masks i)`).
    pub w: PolyVec,
    /// The challenge `c = H(w ‖ t ‖ message)` (a ring element, Lean `c : R`).
    pub c: Poly,
    /// The combined response `z = Σ z_i = Σ (y_i + c·(λ_i·s_i))`.
    pub z: PolyVec,
}

/// Produce a Hermine threshold signature from a signing subset — the Lean
/// `hermine_cert_verifies_under_group_key` algebra, executably.
///
/// Each participant `i ∈ parts` contributes mask `y_i` (derived from
/// `mask_seed` and its index, NOT from the message — so re-signing a
/// different message under the same seed forks the transcript at the
/// challenge, exactly the extractor's hypothesis); the ceremony forms
/// `w = A·(Σ y_i)`, the challenge `c = H(w ‖ t ‖ M)`, partial responses
/// `z_i = y_i + c·(λ_i·s_i)`, and the certificate `(w, c, z = Σ z_i)`.
///
/// SINGLE-CEREMONY, TOY-SAMPLING ONLY — see the module boundary doc.
/// `mask_seed` must be fresh per ceremony (mask reuse across two DIFFERENT
/// challenges hands out the secret — that leak IS the extractor identity
/// this crate's tests witness).
pub fn hermine_sign(
    a: &Matrix,
    group_key: &PolyVec,
    signers: &[&HermineShare],
    mask_seed: u64,
    message: &[u8],
) -> Option<HermineSignature> {
    if signers.is_empty() {
        return None;
    }
    let parts: Vec<u64> = signers.iter().map(|s| s.index).collect();
    // Distinct indices only (a duplicated signer is a caller bug, not a quorum).
    {
        let mut seen = std::collections::HashSet::new();
        if !parts.iter().all(|i| seen.insert(*i)) {
            return None;
        }
    }

    // Round 1: masks + combined commitment.
    let masks: Vec<PolyVec> = signers
        .iter()
        .map(|s| {
            let mut state = mask_seed ^ s.index.wrapping_mul(0x9e3779b97f4a7c15);
            sample_vec(&mut state, a.cols)
        })
        .collect();
    let y_sum = masks
        .iter()
        .fold(PolyVec::zero(a.cols), |acc, y| acc.add(y));
    let w = a.mul_vec(&y_sum);

    // Challenge under the GROUP key.
    let c = challenge(&w, group_key, message);

    // Round 2: Lagrange-weighted partials z_i = y_i + c·(λ_i·s_i), summed.
    let z = signers
        .iter()
        .zip(masks.iter())
        .map(|(s, y)| partial_response(s, &parts, y, &c))
        .reduce(|acc, zi| acc.add(&zi))
        .expect("nonempty signer set");

    Some(HermineSignature { w, c, z })
}

/// Signer `i`'s partial response `z_i = y_i + c·(λ_i·s_i)` — the Lean
/// `masks i + c • (lam i • shares i)`, one summand of the certificate.
/// Exposed so tests can witness `hermine_share_is_valid_under_key_share`.
pub fn partial_response(signer: &HermineShare, parts: &[u64], mask: &PolyVec, c: &Poly) -> PolyVec {
    let lam = Poly::constant(lagrange_at_zero(signer.index, parts));
    mask.add(&signer.share.scale(&lam).scale(c))
}

/// Verify a Hermine signature against the group key: recompute the challenge
/// from `(w, t, message)` and check the Lean relation `A·z = w + c·t`.
pub fn verify_hermine(
    a: &Matrix,
    group_key: &PolyVec,
    message: &[u8],
    sig: &HermineSignature,
) -> bool {
    sig.c == challenge(&sig.w, group_key, message) && verify(a, group_key, &sig.w, &sig.c, &sig.z)
}

// =============================================================================
// The special-soundness extractor (HermineExtractor.lean)
// =============================================================================

/// The extracted lattice relation from two forked transcripts sharing a
/// commitment: returns `(A·(z − z'), (c − c')·t)` — the two sides of the Lean
/// `hermine_special_soundness_extracts_relation` conclusion
/// `A (z - z') = (c - c') • t`. Both accepting transcripts make them equal;
/// the SHORTNESS of `z − z'` (what makes it an MSIS break) is the norm
/// carrier, out of scope.
pub fn extracted_relation(
    a: &Matrix,
    group_key: &PolyVec,
    fork1: &HermineSignature,
    fork2: &HermineSignature,
) -> (PolyVec, PolyVec) {
    let lhs = a.mul_vec(&fork1.z.sub(&fork2.z));
    let rhs = group_key.scale(&fork1.c.sub(&fork2.c));
    (lhs, rhs)
}

/// The Lean `extractPreimage c c' z z' = (c - c')⁻¹ • (z - z')`, realized on
/// the constant-unit subring (this reference's stand-in for the deployed
/// challenge set's unit-difference property; the Lean `FieldModel` takes a
/// field). `None` if `c − c'` is not a constant unit.
pub fn extract_preimage(
    c: &Poly,
    c_prime: &Poly,
    z: &PolyVec,
    z_prime: &PolyVec,
) -> Option<PolyVec> {
    let inv = c.sub(c_prime).inverse_constant()?;
    Some(z.sub(z_prime).scale(&inv))
}

// =============================================================================
// Tests — the Lean spec's identities, witnessed on concrete R_q
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    /// k=2, ℓ=3, n=5 members, threshold t=3, deterministic seed.
    fn dealer_5_of_3() -> HermineTestDealer {
        HermineTestDealer::deal(2, 3, 5, 3, 0xd7e6_6001).unwrap()
    }

    // -- (a) correctness: hermine_cert_verifies_under_group_key ------------

    #[test]
    fn honest_threshold_signature_verifies() {
        let d = dealer_5_of_3();
        let message = b"dregg-federation-vote-v1:hermine";
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &signers, 0xAA11, message).unwrap();
        assert!(verify_hermine(&d.a, &d.group_key, message, &sig));
        // And the raw Lean relation directly, not just via the wrapper.
        assert!(verify(&d.a, &d.group_key, &sig.w, &sig.c, &sig.z));
    }

    #[test]
    fn any_t_subset_verifies_no_dependence_on_which_subset() {
        // The Lean theorem has NO dependence on t, n, or which subset signed.
        let d = dealer_5_of_3();
        let message = b"subset independence";
        for subset in [[0usize, 1, 2], [0, 2, 4], [1, 3, 4]] {
            let signers: Vec<&HermineShare> = subset.iter().map(|&i| &d.shares[i]).collect();
            let sig = hermine_sign(
                &d.a,
                &d.group_key,
                &signers,
                0xBB00 + subset[0] as u64,
                message,
            )
            .unwrap();
            assert!(verify_hermine(&d.a, &d.group_key, message, &sig));
        }
        // Supra-threshold subsets verify too (linear reconstruction is exact).
        let all: Vec<&HermineShare> = d.shares.iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &all, 0xCC00, message).unwrap();
        assert!(verify_hermine(&d.a, &d.group_key, message, &sig));
    }

    #[test]
    fn wrong_message_fails() {
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &signers, 0xDD00, b"correct").unwrap();
        assert!(!verify_hermine(&d.a, &d.group_key, b"wrong", &sig));
    }

    #[test]
    fn tampered_response_fails_the_relation() {
        let d = dealer_5_of_3();
        let message = b"tamper";
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let mut sig = hermine_sign(&d.a, &d.group_key, &signers, 0xEE00, message).unwrap();
        sig.z.0[0] = sig.z.0[0].add(&Poly::constant(1));
        assert!(!verify_hermine(&d.a, &d.group_key, message, &sig));
    }

    // -- hermine_share_is_valid_under_key_share (identifiable abort) -------

    #[test]
    fn partial_is_valid_signature_under_its_key_share() {
        // z_i = y_i + c·(λ_i·s_i) verifies under key share A·(λ_i·s_i) with
        // commitment A·y_i — so a bad share is caught by verifying it alone.
        let d = dealer_5_of_3();
        let parts = [1u64, 2, 3];
        let c = Poly::constant(7).add(&Poly {
            coeffs: [0, 5, 0, 0, 11, 0, 0, 2],
        });
        for signer in &d.shares[0..3] {
            let mut state = 0x51_6E45 ^ signer.index;
            let mask = super::sample_vec(&mut state, d.a.cols);
            let z_i = partial_response(signer, &parts, &mask, &c);
            let key_share = signer.key_share(&d.a, &parts);
            let w_i = d.a.mul_vec(&mask);
            assert!(verify(&d.a, &key_share, &w_i, &c, &z_i));
        }
    }

    // -- (b) the extractor identity: HermineExtractor.lean -----------------

    #[test]
    fn forked_transcripts_satisfy_the_extractor_relation() {
        // Same mask seed, two different messages → same commitment w,
        // different challenges — the forking-lemma transcript pair. The Lean
        // hermine_special_soundness_extracts_relation:
        //   A·(z − z') = (c − c')·t.
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[1..4].iter().collect();
        let seed = 0xF0F0;
        let sig1 = hermine_sign(&d.a, &d.group_key, &signers, seed, b"fork-msg-1").unwrap();
        let sig2 = hermine_sign(&d.a, &d.group_key, &signers, seed, b"fork-msg-2").unwrap();
        // Both accept; shared commitment; distinct challenges.
        assert!(verify_hermine(&d.a, &d.group_key, b"fork-msg-1", &sig1));
        assert!(verify_hermine(&d.a, &d.group_key, b"fork-msg-2", &sig2));
        assert_eq!(sig1.w, sig2.w);
        assert_ne!(sig1.c, sig2.c);
        // The extracted relation holds.
        let (lhs, rhs) = extracted_relation(&d.a, &d.group_key, &sig1, &sig2);
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn extractor_recovers_the_secret_on_constant_challenge_forks() {
        // The Lean FieldModel extractor_recovers_secret: with a unit
        // difference, extractPreimage on honest responses computes s itself.
        // Constant challenges make c − c' a constant unit in R_q.
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[0..3].iter().collect();
        let parts: Vec<u64> = signers.iter().map(|s| s.index).collect();
        let c1 = Poly::constant(19);
        let c2 = Poly::constant(1001);
        let mut masks = Vec::new();
        for s in &signers {
            let mut state = 0xE47_AC7 ^ s.index;
            masks.push(super::sample_vec(&mut state, d.a.cols));
        }
        let respond = |c: &Poly| -> PolyVec {
            signers
                .iter()
                .zip(masks.iter())
                .map(|(s, y)| partial_response(s, &parts, y, c))
                .reduce(|a, b| a.add(&b))
                .unwrap()
        };
        let (z1, z2) = (respond(&c1), respond(&c2));
        let recovered = extract_preimage(&c1, &c2, &z1, &z2).unwrap();
        // The recovered witness IS the group secret, and it maps to t.
        assert_eq!(&recovered, d.group_secret());
        assert_eq!(d.a.mul_vec(&recovered), d.group_key);
    }

    // -- (c) sub-threshold cannot reconstruct or forge ----------------------

    #[test]
    fn sub_threshold_subset_cannot_forge() {
        // 2 shares of a t=3 sharing Lagrange-interpolate a DIFFERENT degree-1
        // polynomial's value at 0, not the group secret: the cert must fail.
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = d.shares[0..2].iter().collect();
        let sig = hermine_sign(&d.a, &d.group_key, &signers, 0x5B00, b"m").unwrap();
        assert!(!verify_hermine(&d.a, &d.group_key, b"m", &sig));
        assert!(!verify(&d.a, &d.group_key, &sig.w, &sig.c, &sig.z));
    }

    #[test]
    fn shamir_reconstruction_threshold_boundary() {
        // Any t-subset reconstructs s exactly (the Lean hrecon hypothesis is
        // REAL, not assumed); any (t−1)-subset reconstructs something else.
        let d = dealer_5_of_3();
        for subset in [[0usize, 1, 2], [0, 2, 4], [2, 3, 4]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &d.shares[i]).collect();
            assert_eq!(&HermineTestDealer::reconstruct(&shares), d.group_secret());
        }
        for subset in [[0usize, 1], [1, 4], [2, 3]] {
            let shares: Vec<&HermineShare> = subset.iter().map(|&i| &d.shares[i]).collect();
            assert_ne!(&HermineTestDealer::reconstruct(&shares), d.group_secret());
        }
    }

    // -- harness hygiene (mirroring frost.rs's refusals) ---------------------

    #[test]
    fn duplicate_signer_is_refused() {
        let d = dealer_5_of_3();
        let signers: Vec<&HermineShare> = vec![&d.shares[0], &d.shares[0], &d.shares[1]];
        assert!(hermine_sign(&d.a, &d.group_key, &signers, 0x1111, b"m").is_none());
    }

    #[test]
    fn empty_signer_set_is_refused() {
        let d = dealer_5_of_3();
        assert!(hermine_sign(&d.a, &d.group_key, &[], 0x2222, b"m").is_none());
    }

    #[test]
    fn degenerate_dealer_parameters_are_refused() {
        assert!(HermineTestDealer::deal(2, 3, 5, 0, 1).is_none()); // t = 0
        assert!(HermineTestDealer::deal(2, 3, 3, 4, 1).is_none()); // t > n
        assert!(HermineTestDealer::deal(0, 3, 5, 3, 1).is_none()); // no rows
        assert!(HermineTestDealer::deal(2, 0, 5, 3, 1).is_none()); // no cols
        assert!(HermineTestDealer::deal(2, 3, Q, 2, 1).is_none()); // n ≥ q
    }
}
