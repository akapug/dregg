//! REAL no-viewer — the n-of-n collective threshold-decrypt with PROVEN smudging (the keystone).
//!
//! Interface fixed in `docs/deos/FHEGG-PROTOTYPE-INTERFACES.md` §1. This file is OWNED by the `threshold`
//! swarm lane. Anchor: fhe.rs `mbfv` (`DecryptionShare`/`PublicKeyShare`/`CommonRandomPoly`) is the crypto
//! oracle; the smudging bound is proven in `metatheory/Bfv/Smudging.lean` — NOT fhe.rs mbfv's fresh-noise TODO.
//!
//! ## What is anchored where (read before touching)
//!
//! * **Collective keygen** rides fhe.rs `mbfv` DIRECTLY: `CommonRandomPoly` + one `PublicKeyShare`
//!   per party, aggregated into a real fhe.rs `PublicKey` ("Protocol 1: EncKeyGen" of
//!   [Mouchet et al. 2020](https://eprint.iacr.org/2020/304.pdf)). No dealer: each party samples its
//!   own ternary secret share; the collective secret key `s = Σ sᵢ` never exists anywhere.
//! * **Partial decryption is OURS**, because fhe.rs `mbfv::DecryptionShare` samples its share error at
//!   the FRESH-noise variance with the literal source comment "TODO this should be exponential in
//!   ciphertext noise!" (`fhe-0.1.1/src/mbfv/secret_key_switch.rs`) — the exact hole this module exists
//!   to close — and its `h_share` is `pub(crate)`, so the error cannot be topped up from outside. We
//!   compute the share `hᵢ = sᵢ·c1 + eᵢ` ourselves over the parsed [`LeanCiphertext`] RNS rows
//!   (negacyclic ternary convolution, the same power-basis representation `bfv_lean` folds in), with
//!   `eᵢ` a SMUDGING noise sampled uniformly from `[-2^b, 2^b]`, `b ≥` [`MIN_SMUDGE_BITS`].
//! * **Combine** sums the shares into `c0' = c0 + Σ hᵢ` (our RNS arithmetic) and then delegates the
//!   rounding/scale step to fhe.rs itself: a ciphertext `(c0', c1)` decrypted under the ALL-ZERO
//!   secret key is exactly the final step of fhe.rs's own `Aggregate<DecryptionShare> for Plaintext`
//!   (`c0 + c1·0`, scale by `t/q`, round). Any error in our share arithmetic that survives this path
//!   is a wrong plaintext under a REAL library — agreement cannot be faked. The tests additionally
//!   pin our combine against (a) the joint-key `s = Σ sᵢ` fhe.rs decrypt and (b) fhe.rs mbfv's own
//!   `DecryptionShare` aggregation over the same key shares.
//!
//! ## The smudging bound (the coordinate with `metatheory/Bfv/Smudging.lean`)
//!
//! The share of an honest party leaks `eᵢ + (ciphertext noise contribution)` to a coalition of the
//! other `n-1` parties (who can subtract everything else they know). Smudging hides that leak
//! statistically: `SD(e_ct + e_smudge, e_smudge) ≤ B_ct / 2^b` for `e_smudge` uniform on `[-2^b, 2^b]`,
//! so `b ≥ log2(B_ct) + λ` gives statistical distance `≤ 2^-λ`.
//!
//! Deployed numbers, PINNED to `metatheory/Bfv/Smudging.lean`'s export (lane 1b, landed mid-swarm):
//! `Bfv.Smudging.smudgeBits = 80` — the smudge is uniform on `[-2^80, 2^80]` (the EXACT distribution
//! [`partial_decrypt`] samples; the theorems are about that distribution and no other). Both jaws are
//! proved on the real degree-4096 parameters:
//! * hiding (`deployed_smudge_hides`): against the deployed fold envelope's ciphertext noise
//!   `≤ 2^32` (4096 orders × `B_fresh ≈ 2^20`), a `2^80` smudge hides the secret term to
//!   statistical distance `≤ 2^-48`;
//! * correctness (`deployed_smudged_decrypt_exact`): 16 parties' worth of `2^80` smudge
//!   (`≤ 2^84` total) plus the `2^32` fold noise still decrypts EXACTLY (margin `≈ 2^88`);
//! * failing side (`deployed_smudge_floor_leaks`): a `2^15` smudge on the same envelope leaks
//!   TOTALLY (sd = 1) — the bound is a real cliff, not a safety margin.

use std::sync::Arc;

use fhe::bfv::{BfvParameters, Ciphertext, Encoding, PublicKey, SecretKey};
use fhe::mbfv::{Aggregate, CommonRandomPoly, PublicKeyShare};
use fhe_traits::{DeserializeParametrized, FheDecoder, FheDecrypter};
use rand_09::Rng;

use crate::additive::pick_params;
use crate::bfv_lean::{LeanCiphertext, RnsPoly};

pub type Result<T> = std::result::Result<T, ThresholdError>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ThresholdError {
    QuorumTooSmall { have: usize, need: usize },
    ParamMismatch,
    SmudgeTooSmall,
}

/// SMUDGE-BOUND-PIN: minimum admissible smudging bit-width `b` (noise uniform on `[-2^b, 2^b]`),
/// pinned to `Bfv.Smudging.smudgeBits = 80` (`metatheory/Bfv/Smudging.lean`, the deployed export):
/// hides the secret term to statistical distance `≤ 2^-48` against the `2^32` fold envelope
/// (`deployed_smudge_hides`), while `deployed_smudge_floor_leaks` proves a sub-bound smudge leaks.
pub const MIN_SMUDGE_BITS: u32 = 80;

/// Correctness ceiling: `Bfv.Smudging.deployed_smudged_decrypt_exact` proves the decrypt margin
/// holds for TOTAL smudge `≤ 2^84` (= 16 parties × `2^80`) plus the `2^32` fold envelope.
/// [`partial_decrypt`] enforces the per-party form `smudge_bits + ceil(log2(n)) ≤ 84`.
pub const MAX_SMUDGE_BITS_TOTAL: u32 = 84;

/// One party's share of the collective secret key (no dealer ever holds the whole key).
///
/// `coeffs` (ternary, self-sampled) is the secret; it is deliberately private to this module.
/// NAMED GAP: no zeroize-on-drop (the crate has no `zeroize` dep and lanes may not add deps).
pub struct KeyShare {
    coeffs: Vec<i64>,
    /// This party's index in `0..n_parties`.
    pub party: usize,
    /// The quorum size n fixed at keygen (n-of-n: all shares are needed).
    pub n_parties: usize,
}

/// One party's SMUDGED partial decryption of the folded aggregate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecryptShare {
    /// `hᵢ = sᵢ·c1 + eᵢ` as RNS rows (one row per ciphertext modulus, power-basis order).
    h: Vec<Vec<u64>>,
    /// The ciphertext this share decrypts (mirrors mbfv's `SecretKeySwitchShare::ct`); combine
    /// refuses shares over different ciphertexts.
    ct: LeanCiphertext,
    party: usize,
    n_parties: usize,
    smudge_bits: u32,
}

/// The collective public key everyone encrypts to — a REAL fhe.rs `PublicKey`, aggregated from
/// per-party mbfv `PublicKeyShare`s.
pub struct CollectivePublicKey {
    /// Use with `fhe_traits::FheEncrypter` exactly like a single-party key.
    pub pk: PublicKey,
}

/// BFV parameter handle (degree/moduli/t) — the fold set for this prototype.
#[derive(Clone)]
pub struct BfvParams {
    arc: Arc<BfvParameters>,
}

impl BfvParams {
    /// The pinned fold parameter set (degree-4096, 128-bit HE-standard moduli, t ≈ 2^20) — the
    /// same set `bfv_lean`'s oracle tests assert against.
    pub fn fold_set() -> Self {
        let arc = pick_params(20);
        Self { arc }
    }

    pub fn arc(&self) -> &Arc<BfvParameters> {
        &self.arc
    }
    pub fn degree(&self) -> usize {
        self.arc.degree()
    }
    pub fn moduli(&self) -> &[u64] {
        self.arc.moduli()
    }
    pub fn plaintext_modulus(&self) -> u64 {
        self.arc.plaintext()
    }
}

// ---------------------------------------------------------------------------
// SecretKey construction through fhe.rs's own PUBLIC serialization API
// ---------------------------------------------------------------------------
// fhe.rs's `SecretKey::new` is pub(crate); the PUBLIC way to build a key from chosen coefficients
// is its proto codec: `message SecretKey { repeated sint64 coeffs = 1 }` (zigzag, packed) via
// `DeserializeParametrized::from_bytes`. We encode that message ourselves (same from-scratch
// proto3 discipline as `bfv_lean`).

fn push_varint(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            out.push(byte);
            return;
        }
        out.push(byte | 0x80);
    }
}

fn zigzag(v: i64) -> u64 {
    ((v << 1) ^ (v >> 63)) as u64
}

/// Build a real fhe.rs `SecretKey` with the given coefficients, through the public proto codec.
fn sk_from_coeffs(coeffs: &[i64], par: &Arc<BfvParameters>) -> SecretKey {
    let mut payload = Vec::with_capacity(coeffs.len() * 2);
    for &c in coeffs {
        push_varint(&mut payload, zigzag(c));
    }
    let mut bytes = Vec::with_capacity(payload.len() + 4);
    bytes.push(0x0a); // field 1, wire type 2 (packed sint64)
    push_varint(&mut bytes, payload.len() as u64);
    bytes.extend_from_slice(&payload);
    SecretKey::from_bytes(&bytes, par).expect("fhe.rs accepts our packed-sint64 SecretKey proto")
}

// ---------------------------------------------------------------------------
// RNS helpers (same representation bfv_lean owns: power-basis residue rows)
// ---------------------------------------------------------------------------

#[inline]
fn add_mod(a: u64, b: u64, q: u64) -> u64 {
    let s = a + b; // both < q < 2^38: no overflow
    if s >= q {
        s - q
    } else {
        s
    }
}

#[inline]
fn sub_mod(a: u64, b: u64, q: u64) -> u64 {
    if a >= b {
        a - b
    } else {
        a + q - b
    }
}

/// Negacyclic (mod `X^n + 1`) product `s · c` for a TERNARY `s` (coeffs in {-1,0,1}), one RNS row.
/// Multiplication-free: each nonzero `s[a]` adds/subtracts a rotated copy of `c`, with the
/// wrap-around sign flip of the negacyclic ring.
fn ternary_negacyclic_mul(s: &[i64], c: &[u64], q: u64) -> Vec<u64> {
    let n = s.len();
    debug_assert_eq!(n, c.len());
    let mut acc = vec![0u64; n];
    for (a, &sa) in s.iter().enumerate() {
        if sa == 0 {
            continue;
        }
        debug_assert!(sa == 1 || sa == -1, "key share must be ternary");
        let positive = sa == 1;
        for (b, &cb) in c.iter().enumerate() {
            let j = a + b;
            // X^{a+b} = -X^{a+b-n} when a+b >= n
            let (idx, add) = if j < n {
                (j, positive)
            } else {
                (j - n, !positive)
            };
            acc[idx] = if add {
                add_mod(acc[idx], cb, q)
            } else {
                sub_mod(acc[idx], cb, q)
            };
        }
    }
    acc
}

// ---------------------------------------------------------------------------
// the protocol
// ---------------------------------------------------------------------------

/// n-of-n collective keygen (each party contributes; NO dealer). Anchored to mbfv PublicKeyShare + CommonRandomPoly.
pub fn collective_keygen(n: usize, params: &BfvParams) -> (CollectivePublicKey, Vec<KeyShare>) {
    assert!(n >= 1, "collective keygen needs at least one party");
    let mut rng = rand_09::rng();
    let par = params.arc.clone();
    let degree = par.degree();

    // Each party samples its own uniform-ternary secret share (HE-standard secret distribution;
    // ternary is what keeps the share convolution in partial_decrypt multiplication-free).
    let key_shares: Vec<KeyShare> = (0..n)
        .map(|party| KeyShare {
            coeffs: (0..degree).map(|_| rng.random_range(-1i64..=1)).collect(),
            party,
            n_parties: n,
        })
        .collect();

    // Protocol 1 (EncKeyGen) over REAL fhe.rs mbfv: shared CRP, one PublicKeyShare per party,
    // aggregated into the collective PublicKey.
    let crp = CommonRandomPoly::new(&par, &mut rng).expect("CRP sampling");
    let pk_shares: Vec<PublicKeyShare> = key_shares
        .iter()
        .map(|ks| {
            let sk = sk_from_coeffs(&ks.coeffs, &par);
            PublicKeyShare::new(&sk, crp.clone(), &mut rng).expect("mbfv PublicKeyShare")
        })
        .collect();
    let pk = PublicKey::from_shares(pk_shares).expect("mbfv public key aggregation");

    (CollectivePublicKey { pk }, key_shares)
}

/// One party's SMUDGED partial decrypt; smudge_bits ≥ the Bfv/Smudging.lean bound or it is unsound.
///
/// Computes `hᵢ = sᵢ·c1 + eᵢ` with `eᵢ` uniform on `[-2^smudge_bits, 2^smudge_bits]` — the SAME
/// integer noise element reduced into every RNS row (one ring element, not per-row noise).
///
/// A sub-bound `smudge_bits` is accepted HERE (a single honest party cannot know what the others
/// sampled) and refused at [`combine`], which is the enforcement point ([`ThresholdError::SmudgeTooSmall`]).
/// Widths whose n-party TOTAL would breach the proven `2^84` decrypt-margin budget
/// (`Bfv.Smudging.deployed_smudged_decrypt_exact`) panic loudly instead of silently mis-clearing.
pub fn partial_decrypt(share: &KeyShare, ct: &LeanCiphertext, smudge_bits: u32) -> DecryptShare {
    let log2_n = usize::BITS - share.n_parties.next_power_of_two().leading_zeros() - 1;
    assert!(
        smudge_bits + log2_n <= MAX_SMUDGE_BITS_TOTAL,
        "smudge_bits {smudge_bits} with n={} parties exceeds the proven 2^{MAX_SMUDGE_BITS_TOTAL} \
         total-smudge decrypt-margin budget",
        share.n_parties
    );
    assert_eq!(
        ct.polys.len(),
        2,
        "fold-path ciphertexts have exactly 2 polys"
    );
    assert_eq!(ct.degree, share.coeffs.len(), "degree mismatch");
    assert_eq!(
        ct.moduli.len(),
        ct.polys[1].rows.len(),
        "row/moduli mismatch"
    );

    let mut rng = rand_09::rng();
    // One integer smudge polynomial, coefficients uniform on [-2^b, 2^b].
    let half: u128 = 1u128 << smudge_bits;
    let smudge: Vec<i128> = (0..ct.degree)
        .map(|_| rng.random_range(0..=(half << 1)) as i128 - half as i128)
        .collect();

    let h: Vec<Vec<u64>> = ct
        .moduli
        .iter()
        .enumerate()
        .map(|(i, &q)| {
            let mut row = ternary_negacyclic_mul(&share.coeffs, &ct.polys[1].rows[i], q);
            for (rj, &e) in row.iter_mut().zip(smudge.iter()) {
                let em = e.rem_euclid(q as i128) as u64;
                *rj = add_mod(*rj, em, q);
            }
            row
        })
        .collect();

    DecryptShare {
        h,
        ct: ct.clone(),
        party: share.party,
        n_parties: share.n_parties,
        smudge_bits,
    }
}

/// Combine n partial decrypts → plaintext. Refuses < n shares or param disagreement.
///
/// Returns the full SIMD slot vector (degree entries; callers slice their live prefix).
pub fn combine(shares: &[DecryptShare], params: &BfvParams) -> Result<Vec<u64>> {
    let first = shares
        .first()
        .ok_or(ThresholdError::QuorumTooSmall { have: 0, need: 1 })?;
    let need = first.n_parties;

    // Every share must be over the SAME ciphertext, quorum and parameter set.
    for s in shares {
        if s.n_parties != need || s.ct != first.ct || s.h.len() != s.ct.moduli.len() {
            return Err(ThresholdError::ParamMismatch);
        }
    }
    if first.ct.moduli != params.moduli() || first.ct.degree != params.degree() {
        return Err(ThresholdError::ParamMismatch);
    }
    if shares.len() > need {
        // Extra/duplicate shares would double-count noise masks; refuse rather than guess.
        return Err(ThresholdError::ParamMismatch);
    }
    // n-of-n: every party exactly once.
    let mut parties: Vec<usize> = shares.iter().map(|s| s.party).collect();
    parties.sort_unstable();
    parties.dedup();
    if parties.iter().any(|&p| p >= need) {
        return Err(ThresholdError::ParamMismatch);
    }
    if parties.len() < need {
        return Err(ThresholdError::QuorumTooSmall {
            have: parties.len(),
            need,
        });
    }
    // The no-viewer property is only as strong as the weakest smudge (module doc / Smudging.lean).
    if shares.iter().any(|s| s.smudge_bits < MIN_SMUDGE_BITS) {
        return Err(ThresholdError::SmudgeTooSmall);
    }

    // c0' = c0 + Σ hᵢ (our RNS arithmetic, same add discipline as bfv_lean::fold_add).
    let mut c0 = first.ct.polys[0].rows.clone();
    for s in shares {
        for (row, (hrow, &q)) in c0.iter_mut().zip(s.h.iter().zip(first.ct.moduli.iter())) {
            for (rj, &hj) in row.iter_mut().zip(hrow.iter()) {
                *rj = add_mod(*rj, hj, q);
            }
        }
    }

    // (c0', c1) decrypted under the all-zero key is exactly the tail of fhe.rs mbfv's own
    // Aggregate<DecryptionShare>: phase = c0' + c1·0, then the t/q scale + round. fhe.rs is the
    // authority for that rounding — we hand it our bytes.
    let combined = LeanCiphertext {
        polys: vec![
            RnsPoly { rows: c0 },
            RnsPoly {
                rows: first.ct.polys[1].rows.clone(),
            },
        ],
        ..first.ct.clone()
    };
    let fhe_ct = Ciphertext::from_bytes(&combined.to_fhe_bytes(), params.arc())
        .expect("fhe.rs accepts our re-serialized combined ciphertext");
    let zero_sk = sk_from_coeffs(&vec![0i64; params.degree()], params.arc());
    let pt = zero_sk
        .try_decrypt(&fhe_ct)
        .expect("zero-key scale/round of the combined ciphertext");
    let slots = Vec::<u64>::try_decode(&pt, Encoding::simd_at_level(first.ct.level as usize))
        .expect("simd decode");
    Ok(slots)
}

// ---------------------------------------------------------------------------
// tests — fhe.rs is the ORACLE; nothing here verifies us against ourselves alone
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use fhe::bfv::Plaintext;
    use fhe::mbfv::{AggregateIter, DecryptionShare as MbfvDecryptionShare};
    use fhe_traits::{FheEncoder, FheEncrypter, Serialize as FheSerialize};

    use crate::bfv_lean::fold;

    fn encrypt_slots(
        cpk: &CollectivePublicKey,
        params: &BfvParams,
        slots: &[u64],
        plain_bound: u64,
    ) -> LeanCiphertext {
        let mut rng = rand_09::rng();
        let pt = Plaintext::try_encode(slots, Encoding::simd(), params.arc()).expect("encode");
        let ct = cpk.pk.try_encrypt(&pt, &mut rng).expect("encrypt");
        LeanCiphertext::from_fhe_bytes(
            &ct.to_bytes(),
            params.moduli(),
            params.degree(),
            plain_bound,
        )
        .expect("parse")
    }

    /// Our zigzag/packed-sint64 SecretKey proto must round-trip through fhe.rs's OWN codec:
    /// build from chosen coeffs, serialize with fhe.rs, byte-compare to our encoding.
    #[test]
    fn sk_proto_roundtrips_through_fhe_rs() {
        let params = BfvParams::fold_set();
        let mut coeffs = vec![0i64; params.degree()];
        coeffs[0] = 1;
        coeffs[1] = -1;
        coeffs[7] = 1;
        coeffs[params.degree() - 1] = -1;
        let sk = sk_from_coeffs(&coeffs, params.arc());
        // fhe.rs re-serializes what it decoded from us; prost's packed sint64 encoding must
        // equal ours byte-for-byte (same message, canonical packed encoding).
        let mut ours = Vec::new();
        let mut payload = Vec::new();
        for &c in &coeffs {
            push_varint(&mut payload, zigzag(c));
        }
        ours.push(0x0a);
        push_varint(&mut ours, payload.len() as u64);
        ours.extend_from_slice(&payload);
        assert_eq!(
            sk.to_bytes(),
            ours,
            "prost disagrees with our sint64 packing"
        );
    }

    /// Monomial ground truth for the negacyclic convolution: X^1 · c rotates with the wrap-around
    /// SIGN FLIP; a sign error here is invisible to small-noise decrypts, so pin it directly.
    #[test]
    fn negacyclic_monomial_rotation() {
        let q = crate::bfv_lean::FOLD_MODULI[0];
        let n = 8;
        let c: Vec<u64> = (1..=n as u64).collect();
        // s = X^1
        let mut s = vec![0i64; n];
        s[1] = 1;
        let got = ternary_negacyclic_mul(&s, &c, q);
        let mut want = vec![0u64; n];
        want[0] = q - c[n - 1]; // -c[n-1] wraps negacyclically
        for j in 1..n {
            want[j] = c[j - 1];
        }
        assert_eq!(got, want);
        // s = -1 (constant): negation
        let mut sneg = vec![0i64; n];
        sneg[0] = -1;
        let gotneg = ternary_negacyclic_mul(&sneg, &c, q);
        let wantneg: Vec<u64> = c.iter().map(|&x| q - x).collect();
        assert_eq!(gotneg, wantneg);
    }

    /// THE MAIN TOOTH: n parties collective-keygen (real mbfv), encrypt to the collective key,
    /// fold with bfv_lean, n smudged partial-decrypts, combine == the plaintext sums — pinned
    /// against BOTH fhe.rs oracles: the joint-key decrypt AND fhe.rs mbfv's own DecryptionShare
    /// aggregation over the same key shares. Agreement with a real library cannot be faked.
    #[test]
    fn n_of_n_collective_decrypt_matches_fhe_rs_oracles() {
        let params = BfvParams::fold_set();
        let t = params.plaintext_modulus();
        let n = 3;
        let (cpk, key_shares) = collective_keygen(n, &params);

        // Three bucket-increment style vectors, folded homomorphically.
        let k = 16;
        let mk = |base: u64| -> Vec<u64> {
            let mut v = vec![0u64; params.degree()];
            for (i, slot) in v.iter_mut().take(k).enumerate() {
                *slot = base + i as u64;
            }
            v
        };
        let (v1, v2, v3) = (mk(10), mk(300), mk(71));
        let cts = [
            encrypt_slots(&cpk, &params, &v1, 10 + k as u64),
            encrypt_slots(&cpk, &params, &v2, 300 + k as u64),
            encrypt_slots(&cpk, &params, &v3, 71 + k as u64),
        ];
        let folded = fold(&cts, t).expect("fold under budget");

        // n smudged partial decrypts + combine.
        let shares: Vec<DecryptShare> = key_shares
            .iter()
            .map(|ks| partial_decrypt(ks, &folded, 80))
            .collect();
        let got = combine(&shares, &params).expect("full quorum combines");
        let expected: Vec<u64> = v1
            .iter()
            .zip(&v2)
            .zip(&v3)
            .map(|((a, b), c)| (a + b + c) % t)
            .collect();
        assert_eq!(&got[..], &expected[..], "combine != plaintext sums");

        // ORACLE 1: the joint key s = Σ sᵢ decrypts the same folded ciphertext to the same slots
        // through fhe.rs's normal single-key decrypt.
        let mut joint = vec![0i64; params.degree()];
        for ks in &key_shares {
            for (j, &c) in ks.coeffs.iter().enumerate() {
                joint[j] += c;
            }
        }
        let joint_sk = sk_from_coeffs(&joint, params.arc());
        let fhe_folded =
            Ciphertext::from_bytes(&folded.to_fhe_bytes(), params.arc()).expect("bytes");
        let pt = joint_sk.try_decrypt(&fhe_folded).expect("joint decrypt");
        let oracle1 = Vec::<u64>::try_decode(&pt, Encoding::simd()).expect("decode");
        assert_eq!(
            &got[..],
            &oracle1[..],
            "combine != fhe.rs joint-key decrypt"
        );

        // ORACLE 2: fhe.rs mbfv's OWN DecryptionShare aggregation over the same key shares.
        let mut rng = rand_09::rng();
        let arc_ct = std::sync::Arc::new(fhe_folded);
        let pt2: Plaintext = key_shares
            .iter()
            .map(|ks| {
                let sk = sk_from_coeffs(&ks.coeffs, params.arc());
                MbfvDecryptionShare::new(&sk, &arc_ct, &mut rng)
            })
            .aggregate()
            .expect("mbfv aggregate");
        let oracle2 = Vec::<u64>::try_decode(&pt2, Encoding::simd()).expect("decode");
        assert_eq!(&got[..], &oracle2[..], "combine != fhe.rs mbfv aggregation");
    }

    /// n-of-n means n: k < n shares REFUSE (and a duplicated share is not a quorum).
    #[test]
    fn quorum_below_n_refused() {
        let params = BfvParams::fold_set();
        let n = 3;
        let (cpk, key_shares) = collective_keygen(n, &params);
        let ct = encrypt_slots(&cpk, &params, &vec![5u64; params.degree()], 5);
        let shares: Vec<DecryptShare> = key_shares
            .iter()
            .map(|ks| partial_decrypt(ks, &ct, MIN_SMUDGE_BITS))
            .collect();

        assert_eq!(
            combine(&shares[..2], &params),
            Err(ThresholdError::QuorumTooSmall { have: 2, need: 3 })
        );
        assert_eq!(
            combine(&[], &params),
            Err(ThresholdError::QuorumTooSmall { have: 0, need: 1 })
        );
        // A duplicate does not smuggle a quorum: {s0, s0, s1} has 2 distinct parties.
        let dup = vec![shares[0].clone(), shares[0].clone(), shares[1].clone()];
        assert_eq!(
            combine(&dup, &params),
            Err(ThresholdError::QuorumTooSmall { have: 2, need: 3 })
        );
        // And the full quorum still works (the refusals above are not a broken combine).
        assert!(combine(&shares, &params).is_ok());
    }

    /// The Lean-bound enforcement point: any share smudged below MIN_SMUDGE_BITS is refused.
    #[test]
    fn smudge_below_lean_bound_refused() {
        let params = BfvParams::fold_set();
        let (cpk, key_shares) = collective_keygen(2, &params);
        let ct = encrypt_slots(&cpk, &params, &vec![9u64; params.degree()], 9);
        let mut shares: Vec<DecryptShare> = key_shares
            .iter()
            .map(|ks| partial_decrypt(ks, &ct, MIN_SMUDGE_BITS))
            .collect();
        // One under-smudged share poisons the quorum.
        shares[1] = partial_decrypt(&key_shares[1], &ct, MIN_SMUDGE_BITS - 1);
        assert_eq!(
            combine(&shares, &params),
            Err(ThresholdError::SmudgeTooSmall)
        );
    }

    /// Shares over DIFFERENT ciphertexts never combine.
    #[test]
    fn cross_ciphertext_shares_refused() {
        let params = BfvParams::fold_set();
        let (cpk, key_shares) = collective_keygen(2, &params);
        let ct_a = encrypt_slots(&cpk, &params, &vec![1u64; params.degree()], 1);
        let ct_b = encrypt_slots(&cpk, &params, &vec![2u64; params.degree()], 2);
        let shares = vec![
            partial_decrypt(&key_shares[0], &ct_a, MIN_SMUDGE_BITS),
            partial_decrypt(&key_shares[1], &ct_b, MIN_SMUDGE_BITS),
        ];
        assert_eq!(
            combine(&shares, &params),
            Err(ThresholdError::ParamMismatch)
        );
    }

    // ------------------------------------------------------------------
    // THE NO-VIEWER STATISTICAL TOOTH
    // ------------------------------------------------------------------
    // The (n-1)-share aggregate c0 + Σ_{i≠j} hᵢ = Δm + e_ct − s_j·c1 + smudges is masked by the
    // MISSING party's RLWE term s_j·c1. Measured claim (each of these CAN fail):
    //   (a) its CRT-reconstructed coefficients are indistinguishable between m = 0 and m = random
    //       (plaintext-independent: nothing about m leaks before the last share), and
    //   (b) indistinguishable between smudge widths 80 and 82 (smudge-independent: the partial
    //       view's shape is the missing mask, not our noise knob), while
    //   (c) the FULL n-share aggregate of m = 0 is grossly DISTINGUISHABLE from any partial one
    //       (coefficients collapse to ±noise around 0 mod q) — the positive control proving the
    //       statistic has teeth: the flip from "uniform garbage" to "structured plaintext"
    //       happens EXACTLY at the n-th share.
    // Statistic: total-variation distance between 16-bin histograms of coeff·16/q over the 4096
    // coefficients. Two independent uniform samples of 4096 over 16 bins sit near TV ≈ 0.04;
    // thresholds 0.15 / 0.5 are far from both sides' expectations.

    /// CRT-combine one coefficient's RNS residues to `x mod q` (q = Πqᵢ ≈ 2^109 fits u128).
    struct Crt {
        q: u128,
        c: Vec<u128>, // c_i = M_i · (M_i^{-1} mod q_i), M_i = q / q_i
    }
    impl Crt {
        fn new(moduli: &[u64]) -> Self {
            let q: u128 = moduli.iter().map(|&m| m as u128).product();
            let c = moduli
                .iter()
                .map(|&m| {
                    let big_m = q / m as u128;
                    let inv = modpow_u64((big_m % m as u128) as u64, m - 2, m); // qᵢ prime
                    (big_m * inv as u128) % q // < 2^109 · 1 before mod: big_m < 2^74, inv < 2^37
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

    /// `a·b mod q` for a,q < 2^110, b < 2^64 — shift-add (the 128×64 product overflows u128).
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

    /// The aggregate c0 + Σ hᵢ over the given shares, CRT-combined per coefficient.
    fn aggregate_coeffs(shares: &[DecryptShare], crt: &Crt) -> Vec<u128> {
        let ct = &shares[0].ct;
        let nmod = ct.moduli.len();
        let mut rows = ct.polys[0].rows.clone();
        for s in shares {
            for i in 0..nmod {
                let q = ct.moduli[i];
                for (rj, &hj) in rows[i].iter_mut().zip(s.h[i].iter()) {
                    *rj = add_mod(*rj, hj, q);
                }
            }
        }
        (0..ct.degree)
            .map(|j| {
                let residues: Vec<u64> = (0..nmod).map(|i| rows[i][j]).collect();
                crt.combine(&residues)
            })
            .collect()
    }

    fn hist16(coeffs: &[u128], q: u128) -> [f64; 16] {
        let mut h = [0f64; 16];
        for &x in coeffs {
            let bin = ((x * 16) / q).min(15) as usize;
            h[bin] += 1.0;
        }
        let n = coeffs.len() as f64;
        for b in h.iter_mut() {
            *b /= n;
        }
        h
    }

    fn tv(a: &[f64; 16], b: &[f64; 16]) -> f64 {
        0.5 * a
            .iter()
            .zip(b.iter())
            .map(|(x, y)| (x - y).abs())
            .sum::<f64>()
    }

    #[test]
    fn no_viewer_partial_aggregate_is_plaintext_and_smudge_independent() {
        let params = BfvParams::fold_set();
        let t = params.plaintext_modulus();
        let n = 3;
        let (cpk, key_shares) = collective_keygen(n, &params);
        let crt = Crt::new(params.moduli());
        // CRT sanity pin: a small integer reconstructs to itself.
        {
            let v = 123_456_789u64;
            let residues: Vec<u64> = params.moduli().iter().map(|&m| v % m).collect();
            assert_eq!(crt.combine(&residues), v as u128);
        }

        let mut rng = rand_09::rng();
        let zeros = vec![0u64; params.degree()];
        let randoms: Vec<u64> = (0..params.degree())
            .map(|_| rng.random_range(0..t))
            .collect();
        let ct_zero = encrypt_slots(&cpk, &params, &zeros, 0);
        let ct_rand = encrypt_slots(&cpk, &params, &randoms, t - 1);

        let mk_shares = |ct: &LeanCiphertext, bits: u32| -> Vec<DecryptShare> {
            key_shares
                .iter()
                .map(|ks| partial_decrypt(ks, ct, bits))
                .collect()
        };
        let sh_zero_min = mk_shares(&ct_zero, MIN_SMUDGE_BITS);
        let sh_zero_82 = mk_shares(&ct_zero, 82);
        let sh_rand_min = mk_shares(&ct_rand, MIN_SMUDGE_BITS);

        // Partial (n-1 shares: the coalition's view) vs full (all n).
        let p_zero_min = hist16(&aggregate_coeffs(&sh_zero_min[..n - 1], &crt), crt.q);
        let p_zero_82 = hist16(&aggregate_coeffs(&sh_zero_82[..n - 1], &crt), crt.q);
        let p_rand_min = hist16(&aggregate_coeffs(&sh_rand_min[..n - 1], &crt), crt.q);
        let f_zero_min = hist16(&aggregate_coeffs(&sh_zero_min, &crt), crt.q);

        // (a) plaintext-independence of the coalition view
        let tv_plain = tv(&p_zero_min, &p_rand_min);
        // (b) smudge-independence of the coalition view
        let tv_smudge = tv(&p_zero_min, &p_zero_82);
        // (c) positive control / failing side: the FULL aggregate is structured (m=0 collapses
        //     coefficients to ±total-noise ≈ 2^82 around 0 mod q ≈ 2^109: bins 0/15 only).
        let tv_full = tv(&f_zero_min, &p_zero_min);

        assert!(
            tv_plain < 0.15,
            "coalition view leaks the plaintext: TV(m=0, m=rand) = {tv_plain}"
        );
        assert!(
            tv_smudge < 0.15,
            "coalition view depends on the smudge width: TV(b=80, b=82) = {tv_smudge}"
        );
        assert!(
            tv_full > 0.5,
            "positive control FAILED — the statistic cannot even see the full-aggregate structure \
             (TV = {tv_full}); the two small-TV assertions above would be vacuous"
        );
        // And the structured full aggregate really is the plaintext: same shares combine to m.
        let got = combine(&sh_zero_min, &params).expect("combine");
        assert_eq!(&got[..], &zeros[..]);
    }
}
