//! The commit-then-reveal beacon CORE — the two safety properties, over a
//! collision-resistant hash.
//!
//! This is the executable counterpart of `metatheory/Dregg2/Crypto/
//! RandomnessBeacon.lean`. A party `i` holds a secret contribution `cᵢ`, first
//! publishes a binding hash commitment `cmᵢ = H("commit", i, cᵢ)`, and only
//! later reveals `cᵢ`. The beacon output is a hash-combine over the committed
//! contribution multiset — `H("output", sorted[(i, cᵢ)])`. The combine sorts by
//! party index so it depends only on the committed SET-WITH-MULTIPLICITY, not on
//! message arrival order (the Lean `Multiset` combine — `beacon_output_determined`).
//!
//! # The two properties, as code (each reduces to hash collision-resistance)
//!
//! * **UNBIASABILITY.** [`combine`] is honest-slot collision-resistant: fixing
//!   every other (adversarial) contribution, distinct honest contributions give
//!   distinct outputs — the honest contribution MOVES the beacon, so a coalition
//!   that committed first cannot pin the output to a predetermined value
//!   (`honest_makes_unbiasable`). A "bias" (output insensitive to a distinct
//!   honest reveal) would be a hash collision (`bias_breaks_honest_slot_cr`).
//! * **UNPREDICTABILITY.** [`Commitment`] binds a party to one `cᵢ`
//!   ([`verify_opening`] = `commitment_binding`). Before an honest `cᵢ` is
//!   revealed the adversary holds only `cmᵢ`; predicting the output means
//!   inverting/colliding the hash (`output_unpredictable_before_reveal`,
//!   `prediction_matching_two_reveals_breaks_hashcr`).
//!
//! Both bottom out at the ONE named carrier `HashCR` — here blake3 (a
//! collision-resistant hash modelled as a programmable QROM: the PQ-security
//! floor). See `RandomnessBeacon.lean` for the machine-checked reductions.

use blake3::Hasher;

/// A party's secret contribution `cᵢ` — 32 bytes of local randomness. The
/// unbiasability/unpredictability arguments need only that an HONEST party's
/// contribution is unpredictable to the adversary before reveal; the bytes
/// themselves are opaque to the beacon.
pub type Contribution = [u8; 32];

/// A hash commitment `cmᵢ = H("commit", i, cᵢ)` — 32 bytes. Binding (a party
/// cannot open it to a second contribution without a hash collision) and hiding
/// (the QROM floor). Broadcast in round 1; the contribution stays local until
/// round 2.
pub type Commitment = [u8; 32];

/// The beacon output — 32 bytes, `H("output", sorted[(i, cᵢ)])` over the
/// committed contribution set.
pub type BeaconOutput = [u8; 32];

const DOMAIN_COMMIT: &[u8] = b"hashrand/commit/v1";
const DOMAIN_OUTPUT: &[u8] = b"hashrand/output/v1";

/// Length-framed absorb: `len(u64 LE) ‖ bytes`, so no two distinct field
/// sequences share an encoding (injective framing — a prerequisite for reading
/// the collision-resistance of the combine off the collision-resistance of the
/// underlying hash).
fn absorb(h: &mut Hasher, bytes: &[u8]) {
    h.update(&(bytes.len() as u64).to_le_bytes());
    h.update(bytes);
}

/// The commitment `cmᵢ = H("commit", i, cᵢ)`, binding party `i` to `c`.
///
/// This is the Lean `cmᵢ = H(i, cᵢ)`: the party index is bound in so that two
/// parties committing the same contribution get distinct commitments, and an
/// equivocation (opening `cmᵢ` to `c' ≠ c`) is exactly a collision on this hash.
pub fn commit(party: u64, c: &Contribution) -> Commitment {
    let mut h = Hasher::new();
    absorb(&mut h, DOMAIN_COMMIT);
    absorb(&mut h, &party.to_le_bytes());
    absorb(&mut h, c);
    *h.finalize().as_bytes()
}

/// Verify an opening: does `c` open the commitment `cm` for party `i`? This is
/// `CommitReveal.opens` / `commitment_binding` — a party that reveals `c' ≠ c`
/// for a `cm` it committed to `c` fails here (the equivocation is CAUGHT), which
/// is the rushing/bias defense's teeth.
pub fn verify_opening(party: u64, cm: &Commitment, c: &Contribution) -> bool {
    // blake3 output comparison; the reference is not constant-time (commitments
    // are public, so there is no secret-dependent branch to protect here).
    &commit(party, c) == cm
}

/// The beacon output `H("output", sorted[(i, cᵢ)])` over the committed set.
///
/// The contributions are sorted by party index before absorbing, so the output
/// is a deterministic function of the committed multiset ONLY — independent of
/// the order reveals arrived (`beacon_output_determined`). Duplicate indices are
/// permitted and preserved (a genuine multiset combine); a caller enforcing one
/// contribution per party rejects duplicates upstream.
pub fn combine(reveals: &[(u64, Contribution)]) -> BeaconOutput {
    let mut sorted: Vec<(u64, Contribution)> = reveals.to_vec();
    sorted.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));

    let mut h = Hasher::new();
    absorb(&mut h, DOMAIN_OUTPUT);
    h.update(&(sorted.len() as u64).to_le_bytes());
    for (party, c) in &sorted {
        h.update(&party.to_le_bytes());
        h.update(c);
    }
    *h.finalize().as_bytes()
}

/// Deterministic test-only contribution derivation (a party samples locally
/// from a CSPRNG in deployment; here a domain-separated hash gives reproducible
/// "randomness" so the tests are differential, not just self-green).
pub fn derive_contribution(seed: u64, party: u64) -> Contribution {
    let mut h = Hasher::new();
    absorb(&mut h, b"hashrand/test-contribution/v1");
    absorb(&mut h, &seed.to_le_bytes());
    absorb(&mut h, &party.to_le_bytes());
    *h.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The output is a deterministic function of the committed set: reordering
    /// the reveals does not change it (`beacon_output_determined` — the
    /// Multiset combine).
    #[test]
    fn output_determined_by_committed_set() {
        let a = derive_contribution(1, 1);
        let b = derive_contribution(1, 2);
        let c = derive_contribution(1, 3);
        let forward = combine(&[(1, a), (2, b), (3, c)]);
        let shuffled = combine(&[(3, c), (1, a), (2, b)]);
        assert_eq!(
            forward, shuffled,
            "output depends on the SET, not arrival order"
        );
    }

    /// UNBIASABILITY (honest-slot collision-resistance): with every OTHER
    /// contribution fixed, changing the honest party's contribution changes the
    /// output — the honest contribution moves the beacon, so a coalition that
    /// committed first cannot pin it (`honest_makes_unbiasable`). And the honest
    /// contribution is BAKED IN: the full output differs from the
    /// adversary-only combine, so the adversary did not set the beacon.
    #[test]
    fn honest_contribution_makes_unbiasable() {
        // Party 1 is honest; parties 2,3 are the adversarial coalition `rest`.
        let honest = derive_contribution(7, 1);
        let honest_alt = derive_contribution(999, 1);
        assert_ne!(honest, honest_alt);
        let rest = [
            (2, derive_contribution(7, 2)),
            (3, derive_contribution(7, 3)),
        ];

        let with_honest: Vec<_> = [(1, honest)].into_iter().chain(rest).collect();
        let with_honest_alt: Vec<_> = [(1, honest_alt)].into_iter().chain(rest).collect();

        // Distinct honest contributions ⇒ distinct outputs (honest slot injective).
        assert_ne!(combine(&with_honest), combine(&with_honest_alt));

        // The honest contribution is baked in: dropping it changes the output,
        // so the adversary-controlled `rest` alone does NOT determine the beacon.
        assert_ne!(combine(&with_honest), combine(&rest));

        // The adversary changing ITS OWN contributions cannot reproduce a target
        // output that omits the honest one either — the honest slot moves it.
        let adv_changed = [
            (2, derive_contribution(42, 2)),
            (3, derive_contribution(42, 3)),
        ];
        let with_adv_changed: Vec<_> = [(1, honest)].into_iter().chain(adv_changed).collect();
        assert_ne!(combine(&with_honest), combine(&with_adv_changed));
    }

    /// COMMIT-BINDING (`commitment_binding` / the equivocation tooth): the
    /// commitment opens ONLY to the contribution it was made from; any other
    /// reveal is rejected. Equivocation is caught.
    #[test]
    fn commitment_binds_and_catches_equivocation() {
        let party = 4u64;
        let c = derive_contribution(11, party);
        let cm = commit(party, &c);

        // The genuine opening verifies.
        assert!(verify_opening(party, &cm, &c));

        // Any equivocated reveal (c' ≠ c) is rejected — the rushing/bias defense.
        let c_prime = derive_contribution(22, party);
        assert_ne!(c, c_prime);
        assert!(!verify_opening(party, &cm, &c_prime));

        // The index is bound: the same contribution under a different party
        // index does not open this commitment.
        assert!(!verify_opening(party + 1, &cm, &c));
    }

    /// UNPREDICTABILITY (`output_unpredictable_before_reveal`): before an honest
    /// `cᵢ` is revealed the output hash is injective in it, so no single value is
    /// the output for two distinct honest reveals — an a-priori prediction
    /// matches at most one honest contribution, i.e. the adversary must invert
    /// the commitment to predict the beacon.
    #[test]
    fn output_injective_in_honest_reveal() {
        let rest = [(2, derive_contribution(5, 2))];
        let mut outputs = std::collections::HashSet::new();
        for k in 0..256u64 {
            let honest = derive_contribution(k, 1);
            let full: Vec<_> = [(1, honest)].into_iter().chain(rest).collect();
            // Distinct honest reveals hash to distinct outputs (no collision seen).
            assert!(
                outputs.insert(combine(&full)),
                "collision on honest slot at k={k}"
            );
        }
    }
}
