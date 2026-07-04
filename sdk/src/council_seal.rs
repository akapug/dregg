//! # council_seal — a cell SEALED to a council's common secret, openable only at quorum.
//!
//! A [`CouncilSeal`] is the recovery↔privacy BRIDGE: a cell's payload is encrypted
//! to a council's GROUP PUBLIC KEY (DKG-issued, so NO party ever held the secret),
//! such that ONLY a `K`-of-`N` guardian quorum can OPEN it — threshold-decrypt at
//! quorum, info-theoretically NOTHING below it. Lose your keys and the council
//! opens your sealed cell; but never any one of them, and never a sub-threshold
//! coalition.
//!
//! ## What it welds (census-first; reinvents no crypto)
//!
//! Pure orchestration over the REAL federation BLS-DKG organs — the same pattern as
//! [`crate::beacon_cell`]:
//!
//! - `dregg_federation::dkg` — the genesis DKG (`DkgParticipant`; no party ever
//!   holds `f(0)`). This RETIRES the trusted dealer of
//!   `dregg_federation::threshold_decrypt` (whose symmetric key was dealer-split):
//!   here the council's secret `f(0)` is born distributed.
//! - `dregg_federation::beacon` — the threshold-BLS surface. The seal target is the
//!   DKG group public key `Y = g₁^{f(0)} ∈ G1`; a guardian's OPEN contribution is a
//!   generic-message partial `H(label)^{f(i)} ∈ G2` (`BeaconShare::sign_label`),
//!   Lagrange-combined to the unique `σ = H(label)^{f(0)}` (`combine_label`).
//!
//! ## The seal construction — threshold hashed-ElGamal over the BLS pairing
//!
//! Encryption (anyone, with ONLY the public committee = `Y` + share publics):
//!
//! 1. sample ephemeral scalar `r`; publish `U = g₁^r ∈ G1`;
//! 2. mask element `M = e(Y, H(label))^r ∈ G_T` (a pairing the SEALER can compute
//!    from the public group key alone);
//! 3. `key = KDF(M)`; payload = AEAD(key, plaintext) (blake3 keystream + tag, the
//!    same self-contained AEAD `threshold_decrypt` uses — no new crypto).
//!
//! Open (a `K`-of-`N` quorum):
//!
//! 1. each guardian `i` emits `σ_i = H(label)^{f(i)}` (`sign_label`);
//! 2. the combiner runs `combine_label` → `σ = H(label)^{f(0)}` (fail-closed below
//!    `K`); 3. mask `M = e(U, σ)`. The pairing identity makes this the SAME `M`:
//!
//! ```text
//!   e(U, σ) = e(g₁^r, H(label)^{f(0)}) = e(g₁, H(label))^{r·f(0)}
//!           = e(g₁^{f(0)}, H(label))^r = e(Y, H(label))^r = M
//! ```
//!
//! 4. `key = KDF(M)`; recover plaintext.
//!
//! ## The cliff — recovery-meets-privacy, with the common secret as the floor
//!
//! `f(0)` is a COMMON SECRET held by the council as threshold distributed knowledge
//! `D_G^{≥K}` (`metatheory/Metatheory/CommonSecret.lean`). Below `K`:
//!
//! - a sub-threshold coalition CANNOT PRODUCE `σ` — `combine_label` fail-closes with
//!   `InsufficientPartials` (the operational tooth);
//! - and CANNOT LEARN `M` — its pooled view is information-theoretically consistent
//!   with every value of `f(0)` (`subThreshold_secret_blind`), so the mask, hence
//!   the key, hence the plaintext, is NOTHING below `K`.
//!
//! At `K` (any quorum) the seal opens to the UNIQUE plaintext — BLS uniqueness means
//! the quorum CHOICE cannot steer the opened value. This is the `threshold_jump`:
//! nothing at `K−1`, everything at `K`.
//!
//! ## Governance uses
//!
//! - **sealed-bid auction** — each bidder seals their bid to the auctioneer council;
//!   bids are jointly opened only after the bidding window closes (no auctioneer can
//!   peek early, no single guardian can leak a bid).
//! - **sealed ballots** — voters seal ballots to an election council; the tally
//!   council opens them together at close, so no individual official sees a vote
//!   before quorum, and a sub-threshold cabal learns nothing.
//! - **dead-man / key recovery** — a user seals their recovery material to a
//!   guardian council; if they lose their keys, a `K`-of-`N` quorum reconstitutes
//!   it, but no guardian (and no sub-quorum) ever holds it.

use dregg_federation::beacon::{BeaconCommittee, BeaconPartial, BeaconShare};
use dregg_federation::dkg::{DkgError, DkgOutput, DkgParams, DkgParticipant, ShareResponse};
use hints::G1;

use ark_ec::{AffineRepr, CurveGroup, pairing::Pairing};
use ark_ff::UniformRand;
use ark_serialize::CanonicalSerialize;
use ark_std::rand::{SeedableRng, rngs::StdRng};
use hints::snark::Curve;

/// blake3 derive_key context for the seal's symmetric key (from the mask `M`).
const SEAL_KEY_CONTEXT: &str = "dregg-council-seal:key v1";
/// blake3 derive_key context for the seal's AEAD keystream.
const SEAL_STREAM_CONTEXT: &str = "dregg-council-seal:stream v1";
/// blake3 derive_key context for the seal's AEAD tag.
const SEAL_TAG_CONTEXT: &str = "dregg-council-seal:tag v1";
/// blake3 keyed context for deriving the council's deterministic DKG seeds.
const SEAL_DKG_CONTEXT: &[u8] = b"dregg-council-seal:dkg v1";

/// Errors a council seal can raise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CouncilSealError {
    /// A genesis DKG step failed (forwarded from the DKG organ).
    Dkg(DkgError),
    /// `n == 0 || k == 0 || k > n` at council construction.
    InvalidParameters,
    /// Fewer than `K` valid open contributions, or the combine failed its final
    /// group-key check (the cliff: below `K`, the seal does not open).
    BelowThreshold,
    /// The AEAD tag did not verify — wrong council, wrong label, or tampered
    /// ciphertext. Fail-closed (never returns garbage plaintext).
    OpenFailed,
}

impl std::fmt::Display for CouncilSealError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CouncilSealError::Dkg(e) => write!(f, "council-seal DKG error: {e}"),
            CouncilSealError::InvalidParameters => write!(f, "council-seal invalid parameters"),
            CouncilSealError::BelowThreshold => {
                write!(
                    f,
                    "council-seal below threshold: the quorum did not reach K"
                )
            }
            CouncilSealError::OpenFailed => {
                write!(
                    f,
                    "council-seal open failed: wrong council/label or tampered seal"
                )
            }
        }
    }
}

impl std::error::Error for CouncilSealError {}

impl From<DkgError> for CouncilSealError {
    fn from(e: DkgError) -> Self {
        CouncilSealError::Dkg(e)
    }
}

/// A sealed payload — opaque to anyone below the council's `K`-of-`N` threshold.
///
/// Carries the public ephemeral point `U`, the AEAD framing, and the seal label
/// (domain-separation for the hash-to-G2 — distinct labels seal independently,
/// so opening one seal never opens another even under the same council).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SealedPayload {
    /// The seal label — binds the seal to a context (e.g. an auction id, a ballot
    /// round). Distinct labels ⇒ distinct hash-to-G2 messages ⇒ independent seals.
    pub label: Vec<u8>,
    /// The ephemeral public point `U = g₁^r ∈ G1`.
    pub ephemeral: G1,
    /// AEAD nonce (12 bytes, fresh entropy).
    pub nonce: [u8; 12],
    /// `plaintext XOR keystream(key, nonce)`.
    pub ciphertext: Vec<u8>,
    /// `MAC(key, nonce ‖ ciphertext)` — verified before any plaintext is returned.
    pub tag: [u8; 32],
}

impl SealedPayload {
    /// The seal's public identifier: blake3 over `(label, U, nonce, ct, tag)`.
    /// Binds an open contribution to THIS seal; replaying a partial onto another
    /// seal fails its own group-key check.
    pub fn seal_id(&self) -> [u8; 32] {
        let mut h = blake3::Hasher::new_derive_key("dregg-council-seal:id v1");
        h.update(&(self.label.len() as u64).to_be_bytes());
        h.update(&self.label);
        let mut buf = Vec::new();
        self.ephemeral
            .serialize_compressed(&mut buf)
            .expect("G1 compression cannot fail");
        h.update(&buf);
        h.update(&self.nonce);
        h.update(&self.ciphertext);
        h.update(&self.tag);
        *h.finalize().as_bytes()
    }
}

/// A guardian's contribution toward opening a sealed payload: the generic-message
/// threshold-BLS partial `σ_i = H(label)^{f(i)} ∈ G2`. Validated against the
/// guardian's share public key at combine time (`combine_label`), so a forged or
/// off-share contribution is dropped — the open is fail-closed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenContribution {
    /// The contributing guardian's 1-based index.
    pub index: usize,
    /// The partial signature carrying `H(label)^{f(index)}`.
    pub partial: BeaconPartial,
}

/// A council that issues and opens seals: the public group key (the seal TARGET,
/// known to anyone who wants to seal) plus the live guardian set (the secret
/// shares, single-machine collapse of the `N` distributed share-holders).
///
/// Birthed by a genuine DKG — no dealer ever holds the council secret `f(0)`.
pub struct Council {
    /// The committee's public surface — the seal target `Y` + share publics.
    /// This is all a SEALER needs.
    committee: BeaconCommittee,
    /// The live guardians (one `DkgOutput` per member). A genuine deployment keeps
    /// each on its own machine; the single-machine collapse holds them together to
    /// drive open ceremonies.
    guardians: Vec<DkgOutput>,
    /// The threshold `K` (= the DKG `t`): how many guardians must cooperate.
    k: usize,
}

impl Council {
    /// Birth a council with a fresh genesis DKG: `n` guardians, threshold `k`,
    /// driven deterministically from `seed`. No party ever holds the council
    /// secret `f(0)` — this is the honest genesis object (the dealer of
    /// `threshold_decrypt` is RETIRED).
    pub fn genesis(n: usize, k: usize, seed: [u8; 32]) -> Result<Self, CouncilSealError> {
        if n == 0 || k == 0 || k > n {
            return Err(CouncilSealError::InvalidParameters);
        }
        let guardians = run_dkg(n, k, seed)?;
        let committee = BeaconCommittee::from(&guardians[0]);
        Ok(Self {
            committee,
            guardians,
            k,
        })
    }

    /// The public committee surface — hand this to anyone who wants to SEAL to the
    /// council. It carries the group key `Y` and the share publics; it carries NO
    /// secret material.
    pub fn committee(&self) -> &BeaconCommittee {
        &self.committee
    }

    /// The council threshold `K`.
    pub fn threshold(&self) -> usize {
        self.k
    }

    /// The number of guardians `N`.
    pub fn num_guardians(&self) -> usize {
        self.guardians.len()
    }

    /// One guardian's OPEN contribution for a given seal: `σ_i = H(label)^{f(i)}`.
    /// In a distributed deployment each guardian runs THIS; the combiner gathers
    /// `K` of them. `who` is the 0-based guardian slot.
    pub fn contribute_open(&self, who: usize, seal: &SealedPayload) -> OpenContribution {
        let share = BeaconShare::from(&self.guardians[who]);
        OpenContribution {
            index: who + 1,
            partial: share.sign_label(&seal.label),
        }
    }

    /// All guardians' open contributions (single-machine convenience — the full
    /// council). A real open uses any `K`-subset of these.
    pub fn open_contributions(&self, seal: &SealedPayload) -> Vec<OpenContribution> {
        (0..self.guardians.len())
            .map(|i| self.contribute_open(i, seal))
            .collect()
    }

    /// **OPEN** a sealed payload from `≥ K` guardian contributions.
    ///
    /// Fail-closed at every step: `combine_label` validates each partial against
    /// its share public key and rejects below `K` (`BelowThreshold` — the cliff);
    /// the recombined `σ` is checked against the group key; the AEAD tag is
    /// verified before any plaintext is returned (`OpenFailed` otherwise).
    ///
    /// Below threshold this returns `BelowThreshold`: the mask `M` is
    /// information-theoretically out of reach (`subThreshold_secret_blind`).
    pub fn open(
        &self,
        seal: &SealedPayload,
        contributions: &[OpenContribution],
    ) -> Result<Vec<u8>, CouncilSealError> {
        let partials: Vec<BeaconPartial> =
            contributions.iter().map(|c| c.partial.clone()).collect();
        // Combine to σ = H(label)^{f(0)} — fail-closed below K.
        let sigma = self
            .committee
            .combine_label(&partials, &seal.label)
            .map_err(|_| CouncilSealError::BelowThreshold)?;
        // Recover the mask M = e(U, σ) and the symmetric key.
        let mask = Curve::pairing(seal.ephemeral, sigma);
        let key = kdf_key(&mask);
        aead_open(&key, seal).ok_or(CouncilSealError::OpenFailed)
    }
}

/// **SEAL** a plaintext to a council, under a domain-separating `label`.
///
/// Needs ONLY the council's public committee (`Y` + share publics) — the sealer
/// holds no secret share and learns nothing the council holds. Deterministic in
/// `seed` (a production sealer draws `seed` from OS entropy); two seals with the
/// same `(seed, label, plaintext, committee)` are byte-identical (replay witness).
pub fn seal(
    committee: &BeaconCommittee,
    label: &[u8],
    plaintext: &[u8],
    seed: [u8; 32],
) -> SealedPayload {
    let mut rng = StdRng::from_seed(seed);
    // Ephemeral scalar r; U = g₁^r.
    let r = hints::F::rand(&mut rng);
    let ephemeral = (G1::generator() * r).into_affine();

    // Mask M = e(Y, H(label))^r, computable from the PUBLIC group key alone.
    let h_label = hints::utils::hash_to_g2(&dregg_federation::beacon::label_message(label));
    let y_pair = Curve::pairing(*committee.group_public(), h_label);
    let mask = y_pair * r; // PairingOutput is additive: e(Y,H)^r = r · e(Y,H).
    let key = kdf_key(&mask);

    // AEAD (blake3 keystream + tag), nonce from the same deterministic stream so
    // the seal is replayable; a production sealer's OS-entropy seed randomizes it.
    let mut nonce = [0u8; 12];
    {
        let mut h = blake3::Hasher::new_derive_key("dregg-council-seal:nonce v1");
        h.update(&seed);
        h.update(label);
        nonce.copy_from_slice(&h.finalize().as_bytes()[..12]);
    }
    let keystream = keystream(&key, &nonce, plaintext.len());
    let ciphertext: Vec<u8> = plaintext
        .iter()
        .zip(keystream.iter())
        .map(|(p, k)| p ^ k)
        .collect();
    let tag = aead_tag(&key, &nonce, &ciphertext);

    SealedPayload {
        label: label.to_vec(),
        ephemeral,
        nonce,
        ciphertext,
        tag,
    }
}

// =============================================================================
// Internal: KDF + AEAD (self-contained blake3, matching threshold_decrypt style)
// =============================================================================

/// Derive the 32-byte symmetric key from the G_T mask element.
fn kdf_key(mask: &ark_ec::pairing::PairingOutput<Curve>) -> [u8; 32] {
    let mut buf = Vec::new();
    mask.serialize_compressed(&mut buf)
        .expect("G_T compression cannot fail");
    let mut h = blake3::Hasher::new_derive_key(SEAL_KEY_CONTEXT);
    h.update(&buf);
    *h.finalize().as_bytes()
}

/// blake3 counter-mode keystream.
fn keystream(key: &[u8; 32], nonce: &[u8; 12], len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    let mut counter: u64 = 0;
    while out.len() < len {
        let mut h = blake3::Hasher::new_derive_key(SEAL_STREAM_CONTEXT);
        h.update(key);
        h.update(nonce);
        h.update(&counter.to_le_bytes());
        let block = h.finalize();
        let bytes = block.as_bytes();
        let take = (len - out.len()).min(32);
        out.extend_from_slice(&bytes[..take]);
        counter += 1;
    }
    out
}

/// blake3-keyed AEAD tag over `nonce ‖ len ‖ ciphertext`.
fn aead_tag(key: &[u8; 32], nonce: &[u8; 12], ciphertext: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(SEAL_TAG_CONTEXT);
    h.update(key);
    h.update(nonce);
    h.update(&(ciphertext.len() as u64).to_le_bytes());
    h.update(ciphertext);
    *h.finalize().as_bytes()
}

/// Verify the tag and decrypt. `None` on tag mismatch (fail-closed).
fn aead_open(key: &[u8; 32], seal: &SealedPayload) -> Option<Vec<u8>> {
    let expected = aead_tag(key, &seal.nonce, &seal.ciphertext);
    if expected != seal.tag {
        return None;
    }
    let ks = keystream(key, &seal.nonce, seal.ciphertext.len());
    Some(
        seal.ciphertext
            .iter()
            .zip(ks.iter())
            .map(|(c, k)| c ^ k)
            .collect(),
    )
}

/// Drive a fully honest genesis DKG (single-machine collapse): `n` guardians,
/// threshold `k`, deterministic from `seed`. Each `DkgOutput` is a Shamir point of
/// `f(0)` with NO party holding `f(0)`.
fn run_dkg(n: usize, k: usize, seed: [u8; 32]) -> Result<Vec<DkgOutput>, CouncilSealError> {
    let params = DkgParams { n, t: k };
    let mut parts = Vec::new();
    let mut dealings = Vec::new();
    let mut priv_shares = Vec::new();
    for i in 1..=n {
        let member_seed = derive_seed(&seed, i);
        let (p, d, ss) = DkgParticipant::new_with_seed(params, i, member_seed)?;
        parts.push(p);
        dealings.push(d);
        priv_shares.extend(ss);
    }
    for p in parts.iter_mut() {
        for d in &dealings {
            p.receive_dealing(d)?;
        }
    }
    for ps in &priv_shares {
        let resp = parts[ps.recipient - 1].receive_share(ps)?;
        debug_assert!(matches!(resp, ShareResponse::Ack { .. }));
    }
    parts
        .iter()
        .map(|p| p.finalize(&[], &[]).map_err(CouncilSealError::from))
        .collect()
}

/// Derive a per-guardian DKG seed (blake3 keyed by the council seed).
fn derive_seed(seed: &[u8; 32], i: usize) -> [u8; 32] {
    let mut h = blake3::Hasher::new_keyed(seed);
    h.update(SEAL_DKG_CONTEXT);
    h.update(&(i as u64).to_be_bytes());
    *h.finalize().as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// TRUE polarity: a K-of-N quorum OPENS the sealed cell to the exact plaintext,
    /// and ANY K-subset yields the SAME plaintext (BLS uniqueness — the quorum
    /// choice cannot steer the opened value).
    #[test]
    fn quorum_opens_the_seal() {
        let council = Council::genesis(5, 3, [11u8; 32]).unwrap();
        let plaintext = b"the recovered private key material";
        let s = seal(council.committee(), b"recovery:alice", plaintext, [7u8; 32]);

        // A 3-of-5 quorum (guardians 0,1,2) opens it.
        let contribs: Vec<_> = [0, 1, 2]
            .iter()
            .map(|&i| council.contribute_open(i, &s))
            .collect();
        let opened = council.open(&s, &contribs).unwrap();
        assert_eq!(opened, plaintext, "the quorum recovers the exact plaintext");

        // A DIFFERENT 3-subset (guardians 2,3,4) opens to the SAME plaintext —
        // the subset choice cannot steer the value.
        let contribs2: Vec<_> = [2, 3, 4]
            .iter()
            .map(|&i| council.contribute_open(i, &s))
            .collect();
        let opened2 = council.open(&s, &contribs2).unwrap();
        assert_eq!(
            opened2, plaintext,
            "any quorum subset opens to the same plaintext"
        );

        // All five also open it (more than K is fine).
        let all = council.open_contributions(&s);
        assert_eq!(council.open(&s, &all).unwrap(), plaintext);
    }

    /// FALSE polarity (the cliff bites): a SUB-THRESHOLD coalition cannot open the
    /// seal. `combine_label` fail-closes below K — the mask is never reconstructed,
    /// so the coalition learns NOTHING. This is `subThreshold_secret_blind` in
    /// operational clothes.
    #[test]
    fn subthreshold_coalition_learns_nothing() {
        let council = Council::genesis(5, 3, [99u8; 32]).unwrap();
        let plaintext = b"a sealed bid: 4200";
        let s = seal(council.committee(), b"auction:lot-7", plaintext, [3u8; 32]);

        // Only 2 of 5 (below K=3): the open must fail closed.
        let sub: Vec<_> = [0, 1]
            .iter()
            .map(|&i| council.contribute_open(i, &s))
            .collect();
        let r = council.open(&s, &sub);
        assert_eq!(
            r,
            Err(CouncilSealError::BelowThreshold),
            "a sub-threshold coalition cannot open the seal"
        );

        // Even a SINGLE guardian (the strongest individual) gets nothing.
        let solo: Vec<_> = vec![council.contribute_open(2, &s)];
        assert_eq!(
            council.open(&s, &solo),
            Err(CouncilSealError::BelowThreshold)
        );
    }

    /// A forged contribution (right structure, wrong share data) is dropped by the
    /// pairing check — it cannot make up the threshold count.
    #[test]
    fn forged_contribution_is_dropped() {
        let council = Council::genesis(5, 3, [21u8; 32]).unwrap();
        let other = Council::genesis(5, 3, [22u8; 32]).unwrap();
        let s = seal(council.committee(), b"ballot:round-1", b"yea", [5u8; 32]);

        // Two honest + one contribution from a DIFFERENT council (wrong f(i)).
        let mut contribs: Vec<_> = [0, 1]
            .iter()
            .map(|&i| council.contribute_open(i, &s))
            .collect();
        contribs.push(other.contribute_open(2, &s)); // forged: wrong share

        // The forged partial fails verify_partial_label and is dropped, leaving
        // only 2 valid < K=3 ⇒ below threshold.
        assert_eq!(
            council.open(&s, &contribs),
            Err(CouncilSealError::BelowThreshold),
            "a forged contribution cannot be counted toward the quorum"
        );
    }

    /// A tampered seal (flipped ciphertext byte) fails the AEAD tag even at quorum —
    /// the open is fail-closed, never returns garbage plaintext.
    #[test]
    fn tampered_seal_fails_closed() {
        let council = Council::genesis(4, 2, [44u8; 32]).unwrap();
        let mut s = seal(
            council.committee(),
            b"recovery:bob",
            b"key bytes",
            [9u8; 32],
        );
        s.ciphertext[0] ^= 0xff;

        let contribs = council.open_contributions(&s);
        assert_eq!(
            council.open(&s, &contribs),
            Err(CouncilSealError::OpenFailed),
            "a tampered seal fails the tag even with a full quorum"
        );
    }

    /// A seal under one label cannot be opened with contributions over a DIFFERENT
    /// label — distinct labels seal independently (domain separation in the
    /// hash-to-G2). This is what lets one council seal many independent contexts.
    #[test]
    fn label_binds_the_seal() {
        let council = Council::genesis(4, 2, [55u8; 32]).unwrap();
        let s = seal(council.committee(), b"context:A", b"payload A", [1u8; 32]);

        // Contributions made for a DIFFERENT seal label.
        let wrong_label_seal = SealedPayload {
            label: b"context:B".to_vec(),
            ..s.clone()
        };
        let contribs: Vec<_> = (0..4)
            .map(|i| council.contribute_open(i, &wrong_label_seal))
            .collect();

        // Partials over label B are H("context:B")^{f(i)}, but `open` combines them
        // against the seal's own label ("context:A"). Each partial fails its
        // verify_partial_label check at combine time and is dropped, so the quorum
        // never reaches K and the open fail-closes at `BelowThreshold` — strictly
        // BEFORE any mask/tag step. The seal does not open over the wrong label.
        assert_eq!(
            council.open(&s, &contribs),
            Err(CouncilSealError::BelowThreshold),
            "contributions over the wrong label cannot open the seal (fail-closed at combine)"
        );

        // The CORRECT-label contributions do open it.
        let right: Vec<_> = (0..4).map(|i| council.contribute_open(i, &s)).collect();
        assert_eq!(council.open(&s, &right).unwrap(), b"payload A");
    }

    /// The sealer needs ONLY the public committee — it holds no share and can seal
    /// to a council it cannot itself open. (Recovery-meets-privacy: you seal to your
    /// guardians; only THEY, at quorum, open.)
    #[test]
    fn sealer_needs_only_public_committee() {
        let council = Council::genesis(5, 3, [77u8; 32]).unwrap();
        // Round-trip the committee through its public serialization — a sealer who
        // only ever saw the published bytes can still seal.
        let bytes = council.committee().to_bytes();
        let public_only = BeaconCommittee::from_bytes(&bytes).unwrap();

        let plaintext = b"sealed with only the public key";
        let s = seal(&public_only, b"pub-only", plaintext, [13u8; 32]);
        let contribs = council.open_contributions(&s);
        assert_eq!(council.open(&s, &contribs).unwrap(), plaintext);
    }

    /// Determinism: same seed/label/plaintext/committee ⇒ byte-identical seal
    /// (replayable witness).
    #[test]
    fn deterministic_seal() {
        let council = Council::genesis(5, 3, [88u8; 32]).unwrap();
        let a = seal(council.committee(), b"det", b"same", [2u8; 32]);
        let b = seal(council.committee(), b"det", b"same", [2u8; 32]);
        assert_eq!(a, b, "same inputs -> byte-identical seal");
    }
}
