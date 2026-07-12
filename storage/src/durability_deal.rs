//! k-of-n durability deals: a grain's bytes survive across bonded operators.
//!
//! An [`AvailabilityManifest`] proves a blob is *reconstructable* from any
//! `n_data` of `n_total` erasure shards (see [`crate::availability`]), and an
//! [`ErasureChunk`] carries a Merkle proof that opens against the manifest
//! root at its committed position (see [`crate::erasure`]). This module
//! composes those two into a **durability deal**: the small, durable record
//! that binds each of the `n` shards to a specific *bonded operator*, so that
//!
//! * the blob reconstructs from **any `k = n_data`** shards (no single
//!   operator's loss can destroy it — indeed no `n - k` of them can), and
//! * each operator can be **challenged** (PoR-style) to prove it still holds
//!   its assigned shard: it returns the shard plus its Merkle proof, which
//!   [`DurabilityDeal::verify_challenge`] authenticates against the deal root
//!   via [`crate::erasure::verify_chunk_against_root`].
//!
//! The deal itself ([`DurabilityDeal`]) is metadata only — root, `k`, `n`, the
//! per-shard commitment, and the operator each shard was placed with. The
//! shard *bytes* live with the operators; [`create`] returns them alongside
//! the deal so they can be disseminated.
//!
//! # What is real, and the one named Lean seam
//!
//! The Reed–Solomon codec ([`ErasureEncoder`]) and the challenge/opening
//! relation ([`verify_chunk_against_root`](crate::erasure::verify_chunk_against_root))
//! are **real and tested** here: reconstruction from every `k`-subset, refusal
//! below `k`, refusal of a lying shard (a genuine proof for position `i`
//! presented as position `j`), and a PoR challenge on a genuinely-held shard.
//!
//! The remaining obligation is a **Lean seam, named not hidden**: a verifying
//! PoR opening proves the operator holds *the committed leaf at position `i`*
//! (Merkle membership). That the committed leaf-set is a *valid RS codeword* —
//! i.e. that any `k` of the openable shards reconstruct the *same* blob named
//! by `content_hash` — is guaranteed by construction at [`create`] time but is
//! not re-derived *from a challenge response alone*. Tying "operator proved it
//! holds shard `i`" to "shard `i` is a genuine RS shard of this codeword whose
//! any-`k` reconstruction equals the committed blob" is the bridge left to
//! `metatheory/Dregg2/Storage/*` (the RS `rs_decode_correct` /
//! `no_wrong_reconstruction` pair and the `por_sound` opening relation already
//! exist there separately; welding them is the open lemma). The Rust code below
//! never *reimplements* the codec — it reuses [`crate::erasure`] wholesale.

use crate::ContentHash;
use crate::availability::{self, AvailabilityError, AvailabilityManifest};
use crate::erasure::{self, ErasureChunk};
use ed25519_dalek::{Signature, Verifier, VerifyingKey};

/// One erasure shard bound to the bonded operator that stores it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShardPlacement<Op> {
    /// Shard index in `0..n` (data shards first, then parity — matches
    /// [`ErasureChunk::index`]).
    pub index: usize,
    /// Whether this is a parity shard (`index >= k`).
    pub is_parity: bool,
    /// BLAKE3 commitment of this shard (its Merkle leaf under the deal root).
    pub commitment: [u8; 32],
    /// The bonded operator assigned to hold this shard.
    pub operator: Op,
}

/// A k-of-n durability deal over a single blob.
///
/// Durable metadata only; the shard bytes live with the operators named in
/// `placements`. Build one with [`create`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DurabilityDeal<Op> {
    /// BLAKE3 content hash of the original blob. A reconstruction is accepted
    /// only if it hashes to this.
    pub content_hash: ContentHash,
    /// Erasure-set Merkle root: every shard's proof opens against this.
    pub root: ContentHash,
    /// Reconstruction threshold — any `k` shards suffice.
    pub k: usize,
    /// Total shards placed (`k * expansion_factor`).
    pub n: usize,
    /// Shard size in bytes (the encoder's chunk size).
    pub chunk_size: usize,
    /// Original blob size (needed to strip padding on reconstruction).
    pub original_size: usize,
    /// Per-shard commitment + operator assignment, in shard-index order.
    pub placements: Vec<ShardPlacement<Op>>,
}

/// Failure to construct a deal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DealError {
    /// The caller supplied a bonded-operator list whose length is not the shard
    /// count `n` the encoder produced (one operator per shard is required).
    OperatorCountMismatch { expected: usize, got: usize },
}

impl std::fmt::Display for DealError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DealError::OperatorCountMismatch { expected, got } => write!(
                f,
                "durability deal needs one operator per shard: expected {expected}, got {got}"
            ),
        }
    }
}

impl std::error::Error for DealError {}

/// Failure of a PoR challenge against an operator's response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChallengeError {
    /// The response was for a different shard than the one challenged.
    WrongShard { challenged: usize, responded: usize },
    /// No shard with the challenged index exists in this deal.
    UnknownShard { index: usize },
    /// The response did not open against the deal root at the challenged
    /// position (tampered data, forged leaf, wrong-position, or wrong shard
    /// entirely). This is the PoR-genuineness verdict.
    ProofInvalid { index: usize },
    /// The operator identity placed with this shard is not a well-formed
    /// ed25519 verifying key, so no signature over it can be checked.
    BadOperatorKey { index: usize },
    /// The response opened correctly, but its authenticating signature was not
    /// produced by the operator this shard was placed with over the exact
    /// `(deal_root, shard_index, challenge_nonce)` challenged. This is the
    /// operator-authentication verdict: it fails a copy-holder that is not the
    /// assigned operator, and a stale or replayed nonce.
    SignatureInvalid { index: usize },
}

impl std::fmt::Display for ChallengeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ChallengeError::WrongShard {
                challenged,
                responded,
            } => write!(
                f,
                "challenged shard {challenged} but response was for {responded}"
            ),
            ChallengeError::UnknownShard { index } => {
                write!(f, "no shard {index} in this deal")
            }
            ChallengeError::ProofInvalid { index } => {
                write!(f, "shard {index} did not open against the deal root")
            }
            ChallengeError::BadOperatorKey { index } => {
                write!(f, "shard {index} operator is not a valid ed25519 key")
            }
            ChallengeError::SignatureInvalid { index } => {
                write!(
                    f,
                    "shard {index} response was not signed by its assigned operator over the challenged nonce"
                )
            }
        }
    }
}

impl std::error::Error for ChallengeError {}

/// Domain separator for the PoR challenge preimage, so an operator's shard
/// signature can never be replayed as a signature in any other protocol.
const POR_CHALLENGE_DOMAIN: &[u8] = b"dregg-storage/durability-deal/por-challenge/v1";

/// The exact bytes an assigned operator must sign to answer a PoR challenge:
/// the domain tag, the deal root, the challenged shard index, and the challenge
/// nonce. Binding all three means a valid signature proves *this operator*
/// answered *this shard* under *this* nonce — a stale nonce, a different shard,
/// or a different deal yields a different preimage and thus a failing check.
pub fn challenge_message(deal_root: &ContentHash, shard_index: usize, nonce: u64) -> Vec<u8> {
    let mut m = Vec::with_capacity(POR_CHALLENGE_DOMAIN.len() + 32 + 8 + 8);
    m.extend_from_slice(POR_CHALLENGE_DOMAIN);
    m.extend_from_slice(&deal_root.0);
    m.extend_from_slice(&(shard_index as u64).to_le_bytes());
    m.extend_from_slice(&nonce.to_le_bytes());
    m
}

/// An operator identity from which the ed25519 verifying key it is bonded under
/// can be recovered, so a PoR response can be authenticated as coming from the
/// *assigned* operator rather than any holder of a shard copy.
///
/// Implemented for [`VerifyingKey`] directly and for a raw 32-byte key, so a
/// deal can be parameterised either way; a bonded-operator id in practice *is*
/// its key (or a hash the caller resolves to a key before building the deal).
pub trait OperatorKey {
    /// The operator's ed25519 verifying key, or `None` if the identity is not a
    /// well-formed key (a malformed placement, surfaced as `BadOperatorKey`).
    fn verifying_key(&self) -> Option<VerifyingKey>;
}

impl OperatorKey for VerifyingKey {
    fn verifying_key(&self) -> Option<VerifyingKey> {
        Some(*self)
    }
}

impl OperatorKey for [u8; 32] {
    fn verifying_key(&self) -> Option<VerifyingKey> {
        VerifyingKey::from_bytes(self).ok()
    }
}

/// The `(k, n)` shard layout a blob of `data_len` bytes will produce under the
/// given encoder parameters — so a caller can size its bonded-operator set
/// *before* calling [`create`]. Matches [`ErasureEncoder`]'s clamping exactly
/// (`chunk_size ≥ 1`, `expansion_factor ≥ 2`, `k = ceil(len/chunk) ≥ 1`).
pub fn shard_layout(data_len: usize, chunk_size: usize, expansion_factor: usize) -> (usize, usize) {
    let cs = chunk_size.max(1);
    let ef = expansion_factor.max(2);
    let k = data_len.div_ceil(cs).max(1);
    (k, k * ef)
}

/// Encode `data` into a k-of-n durability deal, placing each of the `n` shards
/// with the corresponding operator in `operators`.
///
/// `operators.len()` must equal the shard count `n` (use [`shard_layout`] to
/// compute it up front); shard `i` is placed with `operators[i]`. Returns the
/// durable [`DurabilityDeal`] together with the `n` [`ErasureChunk`]s to
/// disseminate to those operators.
///
/// The erasure codec is reused verbatim ([`availability::encode_bytes_for_availability`]);
/// this function only *binds* the resulting shards to operators.
pub fn create<Op: Clone>(
    data: &[u8],
    chunk_size: usize,
    expansion_factor: usize,
    operators: &[Op],
) -> Result<(DurabilityDeal<Op>, Vec<ErasureChunk>), DealError> {
    let (manifest, chunks) =
        availability::encode_bytes_for_availability(data, chunk_size, expansion_factor);
    let n = chunks.len();
    if operators.len() != n {
        return Err(DealError::OperatorCountMismatch {
            expected: n,
            got: operators.len(),
        });
    }

    let placements = chunks
        .iter()
        .map(|c| ShardPlacement {
            index: c.index,
            is_parity: c.is_parity,
            commitment: c.commitment,
            // `c.index` is exactly the shard's position in `0..n`, so this is
            // a total, in-range index into `operators` (len checked above).
            operator: operators[c.index].clone(),
        })
        .collect();

    let deal = DurabilityDeal {
        content_hash: manifest.content_hash,
        root: manifest.root,
        k: manifest.n_data,
        n: manifest.n_total,
        chunk_size: manifest.chunk_size,
        original_size: manifest.original_size,
        placements,
    };
    Ok((deal, chunks))
}

impl<Op> DurabilityDeal<Op> {
    /// The [`AvailabilityManifest`] this deal is equivalent to — the bridge
    /// that lets it reuse the availability reconstruct/verify path unchanged.
    pub fn manifest(&self) -> AvailabilityManifest {
        AvailabilityManifest {
            content_hash: self.content_hash,
            root: self.root,
            original_size: self.original_size,
            chunk_size: self.chunk_size,
            n_data: self.k,
            n_total: self.n,
        }
    }

    /// The operator assigned to hold shard `index`, if any.
    pub fn operator_for(&self, index: usize) -> Option<&Op> {
        self.placements
            .iter()
            .find(|p| p.index == index)
            .map(|p| &p.operator)
    }

    /// Deterministically pick a shard index to challenge from an audit nonce.
    /// (`n ≥ 2` for every real deal, so this always names a live shard.)
    pub fn challenge_index(&self, nonce: u64) -> usize {
        (nonce % self.n as u64) as usize
    }

    /// Reconstruct the original blob from a surviving subset of shard
    /// responses (any `k` of `n` suffice).
    ///
    /// Delegates to [`availability::reconstruct`], so every supplied shard is
    /// integrity-checked, Merkle-verified against the deal root, and the
    /// recovered bytes are bound to `content_hash` — a lying or wrong-blob
    /// shard is rejected, never silently folded in.
    pub fn reconstruct(&self, responses: &[ErasureChunk]) -> Result<Vec<u8>, AvailabilityError> {
        availability::reconstruct(&self.manifest(), responses)
    }

    /// Verify a bonded operator's PoR response for the shard `shard_index` it
    /// was challenged on.
    ///
    /// The operator returns the shard (`response`) plus its Merkle proof. This
    /// passes iff the response is *that* shard (its committed leaf matches the
    /// placement) and it opens against the deal root at that position. A
    /// genuine proof for a *different* position — the classic
    /// availability-confidence-inflation attack — is rejected, because
    /// [`verify_chunk_against_root`](crate::erasure::verify_chunk_against_root)
    /// binds `response.index == response.proof.leaf_index` and this method
    /// additionally binds it to the challenged index.
    pub fn verify_challenge(
        &self,
        shard_index: usize,
        response: &ErasureChunk,
    ) -> Result<(), ChallengeError> {
        if response.index != shard_index {
            return Err(ChallengeError::WrongShard {
                challenged: shard_index,
                responded: response.index,
            });
        }
        let placement = self
            .placements
            .iter()
            .find(|p| p.index == shard_index)
            .ok_or(ChallengeError::UnknownShard { index: shard_index })?;
        // The response must be the committed shard for this placement...
        if response.commitment != placement.commitment {
            return Err(ChallengeError::ProofInvalid { index: shard_index });
        }
        // ...and open against the deal root at its committed position.
        if !erasure::verify_chunk_against_root(response, &self.root) {
            return Err(ChallengeError::ProofInvalid { index: shard_index });
        }
        Ok(())
    }
}

impl<Op: OperatorKey> DurabilityDeal<Op> {
    /// PoR challenge that authenticates the **assigned operator**, not merely
    /// the existence of an opening.
    ///
    /// The challenger picks `nonce` and asks the operator holding `shard_index`
    /// to return its shard (`response`) *and* an ed25519 signature over
    /// [`challenge_message`]`(root, shard_index, nonce)`. Verification passes
    /// iff **both** legs hold:
    ///
    /// 1. the opening leg — [`verify_challenge`](Self::verify_challenge): the
    ///    response is the committed shard for this placement and opens against
    ///    the deal root at that position (a genuine RS shard, not a lie); and
    /// 2. the operator leg — `signature` verifies under the ed25519 key named
    ///    by `placements[shard_index].operator` over that exact preimage.
    ///
    /// Because the key is taken from the *placement*, a copy-holder that is not
    /// the assigned operator cannot answer (leg 2 fails); because the nonce is
    /// bound into the signed preimage, a stale or replayed nonce fails (the
    /// preimage differs). That is what makes the challenge a proof that *that
    /// operator* still holds *that shard*, closing the durability PoR hole where
    /// only the opening was checked.
    pub fn verify_challenge_authenticated(
        &self,
        shard_index: usize,
        nonce: u64,
        response: &ErasureChunk,
        signature: &Signature,
    ) -> Result<(), ChallengeError> {
        // Leg 1: the shard itself is genuine (unchanged — both legs must pass).
        self.verify_challenge(shard_index, response)?;

        // Leg 2: authenticate the operator. The key comes from the placement,
        // so only the operator this shard was bonded to can produce a passing
        // signature over the exact challenged (root, index, nonce) preimage.
        let placement = self
            .placements
            .iter()
            .find(|p| p.index == shard_index)
            .ok_or(ChallengeError::UnknownShard { index: shard_index })?;
        let vk = placement
            .operator
            .verifying_key()
            .ok_or(ChallengeError::BadOperatorKey { index: shard_index })?;
        let message = challenge_message(&self.root, shard_index, nonce);
        vk.verify(&message, signature)
            .map_err(|_| ChallengeError::SignatureInvalid { index: shard_index })?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build a deal over `data` with one distinct `u32` operator per shard.
    fn deal_for(
        data: &[u8],
        chunk_size: usize,
        expansion: usize,
    ) -> (DurabilityDeal<u32>, Vec<ErasureChunk>) {
        let (_, n) = shard_layout(data.len(), chunk_size, expansion);
        let operators: Vec<u32> = (0..n as u32).collect();
        create(data, chunk_size, expansion, &operators).unwrap()
    }

    /// All `k`-element index subsets of `0..n`.
    fn k_subsets(n: usize, k: usize) -> Vec<Vec<usize>> {
        fn go(start: usize, n: usize, k: usize, cur: &mut Vec<usize>, out: &mut Vec<Vec<usize>>) {
            if cur.len() == k {
                out.push(cur.clone());
                return;
            }
            for i in start..n {
                cur.push(i);
                go(i + 1, n, k, cur, out);
                cur.pop();
            }
        }
        let mut out = Vec::new();
        go(0, n, k, &mut Vec::new(), &mut out);
        out
    }

    #[test]
    fn layout_matches_encoder() {
        // 16 bytes / chunk 8 => k=2; expansion 2 => n=4. Empty => k=1.
        assert_eq!(shard_layout(16, 8, 2), (2, 4));
        assert_eq!(shard_layout(0, 8, 2), (1, 2));
        // clamps: chunk 0 -> 1, expansion 1 -> 2.
        assert_eq!(shard_layout(3, 0, 1), (3, 6));
        // And the layout equals what create actually produced.
        let (deal, chunks) = deal_for(b"abcdefghijklmnop", 8, 2);
        assert_eq!((deal.k, deal.n), (2, 4));
        assert_eq!(chunks.len(), deal.n);
    }

    #[test]
    fn create_places_each_shard_with_its_operator() {
        let (deal, chunks) = deal_for(b"one operator per shard, distinct ids", 8, 2);
        assert_eq!(deal.placements.len(), deal.n);
        for (i, p) in deal.placements.iter().enumerate() {
            assert_eq!(p.index, i);
            assert_eq!(p.operator, i as u32, "shard {i} placed with wrong operator");
            assert_eq!(p.commitment, chunks[i].commitment);
            assert_eq!(p.is_parity, chunks[i].is_parity);
            assert_eq!(deal.operator_for(i), Some(&(i as u32)));
        }
        assert_eq!(deal.operator_for(deal.n), None);
    }

    #[test]
    fn create_rejects_wrong_operator_count() {
        let data = b"need exactly n operators, no more no less";
        let (_, n) = shard_layout(data.len(), 8, 2);
        let too_few: Vec<u32> = (0..(n as u32 - 1)).collect();
        assert_eq!(
            create(data, 8, 2, &too_few).unwrap_err(),
            DealError::OperatorCountMismatch {
                expected: n,
                got: n - 1
            }
        );
        let too_many: Vec<u32> = (0..(n as u32 + 3)).collect();
        assert_eq!(
            create(data, 8, 2, &too_many).unwrap_err(),
            DealError::OperatorCountMismatch {
                expected: n,
                got: n + 3
            }
        );
    }

    #[test]
    fn reconstruct_from_every_k_subset() {
        // Sweep several (k, n) so the any-k guarantee is exercised broadly.
        for (data_len, chunk_size, expansion) in [
            (16usize, 8usize, 2usize),
            (16, 8, 3),
            (24, 8, 2),
            (32, 8, 2),
        ] {
            let data: Vec<u8> = (0..data_len)
                .map(|i| (i as u8).wrapping_mul(31).wrapping_add(7))
                .collect();
            let (deal, chunks) = deal_for(&data, chunk_size, expansion);
            for subset_idx in k_subsets(deal.n, deal.k) {
                let subset: Vec<ErasureChunk> =
                    subset_idx.iter().map(|&i| chunks[i].clone()).collect();
                let recovered = deal.reconstruct(&subset).unwrap_or_else(|e| {
                    panic!(
                        "(k={}, n={}) subset {subset_idx:?} failed: {e:?}",
                        deal.k, deal.n
                    )
                });
                assert_eq!(
                    recovered, data,
                    "(k={}, n={}) subset {subset_idx:?} wrong bytes",
                    deal.k, deal.n
                );
            }
        }
    }

    #[test]
    fn reconstruct_fails_below_k() {
        let data = b"this blob spans several shards for the threshold test yes";
        let (deal, chunks) = deal_for(data, 8, 2);
        assert!(deal.k >= 2);
        // Every subset strictly below k must fail (no silent bytes).
        for size in 0..deal.k {
            for subset_idx in k_subsets(deal.n, size) {
                let subset: Vec<ErasureChunk> =
                    subset_idx.iter().map(|&i| chunks[i].clone()).collect();
                match deal.reconstruct(&subset) {
                    Err(AvailabilityError::Reconstruct(_)) => {}
                    other => panic!(
                        "subset {subset_idx:?} of size {size} < k={} should fail, got {other:?}",
                        deal.k
                    ),
                }
            }
        }
    }

    #[test]
    fn durability_survives_operator_loss_up_to_n_minus_k() {
        // No single operator can lose the blob — indeed no `n - k` of them can.
        let data: Vec<u8> = (0..200u32).map(|i| (i % 251) as u8).collect();
        let (deal, chunks) = deal_for(&data, 40, 3); // k=5, n=15
        assert_eq!((deal.k, deal.n), (5, 15));
        let tolerable = deal.n - deal.k; // 10 losses tolerated

        // Losing exactly `tolerable` shards (any prefix) still reconstructs.
        let survivors: Vec<ErasureChunk> = chunks[tolerable..].to_vec();
        assert_eq!(survivors.len(), deal.k);
        assert_eq!(deal.reconstruct(&survivors).unwrap(), data);

        // Losing one more (only k-1 survive) must fail.
        let too_few: Vec<ErasureChunk> = chunks[tolerable + 1..].to_vec();
        assert_eq!(too_few.len(), deal.k - 1);
        assert!(matches!(
            deal.reconstruct(&too_few),
            Err(AvailabilityError::Reconstruct(_))
        ));
    }

    #[test]
    fn por_challenge_on_held_shard_verifies() {
        let data = b"a por challenge on a genuinely held shard must verify";
        let (deal, chunks) = deal_for(data, 8, 2);
        // Challenge every shard with the operator's honest response.
        for i in 0..deal.n {
            let response = chunks[i].clone(); // the operator returns its held shard + proof
            assert_eq!(
                deal.verify_challenge(i, &response),
                Ok(()),
                "honest shard {i} failed its PoR challenge"
            );
        }
        // And the deterministic nonce->index selector names a live shard that verifies.
        let idx = deal.challenge_index(0xDEAD_BEEF);
        assert!(idx < deal.n);
        assert_eq!(deal.verify_challenge(idx, &chunks[idx]), Ok(()));
    }

    #[test]
    fn lying_shard_with_genuine_proof_is_rejected() {
        // A shard whose data/commitment/proof are all GENUINE for position i,
        // presented as position j != i. The raw Merkle path still verifies (it
        // speaks for leaf_index = i), so without position-binding a DAS sampler
        // would count it as evidence position j is held.
        let data = b"a proof for position i must not vouch for position j at all";
        let (deal, chunks) = deal_for(data, 8, 2);
        assert!(deal.n > 3, "need distinct i, j");

        let mut liar = chunks[1].clone(); // genuine everything for i = 1...
        liar.index = 3; // ...but claims to be shard 3.

        // The raw Merkle path still verifies against the root (the attack).
        assert!(liar.proof.verify(&liar.commitment, &deal.root.0));

        // Challenge on shard 3: the response's committed leaf is shard 1's, not
        // shard 3's -> rejected as a PoR-genuineness failure.
        assert_eq!(
            deal.verify_challenge(3, &liar),
            Err(ChallengeError::ProofInvalid { index: 3 })
        );
        // Challenge on shard 1: the operator responded for shard 3 -> wrong shard.
        assert_eq!(
            deal.verify_challenge(1, &liar),
            Err(ChallengeError::WrongShard {
                challenged: 1,
                responded: 3
            })
        );

        // Reconstruction refuses the lie too: substitute the liar in for shard 3.
        let mut set = chunks.clone();
        set[3] = liar;
        assert_eq!(
            deal.reconstruct(&set),
            Err(AvailabilityError::ChunkProofInvalid { index: 3 })
        );

        // The honest shard 3 still passes end to end.
        assert_eq!(deal.verify_challenge(3, &chunks[3]), Ok(()));
    }

    #[test]
    fn tampered_shard_fails_challenge_and_reconstruct() {
        let data = b"tamper a held shard and the challenge catches it flat";
        let (deal, mut chunks) = deal_for(data, 8, 2);
        // Tamper data and recompute the leaf so the integrity leg passes; the
        // forged leaf is not in the deal tree, so membership (the PoR opening)
        // must reject it.
        let mut forged = chunks[0].clone();
        forged.data[0] ^= 0xFF;
        forged.commitment = erasure::chunk_commitment_dual(&forged.data).blake3;
        assert!(erasure::verify_chunk(&forged)); // integrity now passes...
        assert_eq!(
            deal.verify_challenge(0, &forged),
            Err(ChallengeError::ProofInvalid { index: 0 })
        );
        chunks[0] = forged;
        assert_eq!(
            deal.reconstruct(&chunks),
            Err(AvailabilityError::ChunkProofInvalid { index: 0 })
        );
    }

    #[test]
    fn operator_ids_can_be_arbitrary_bonded_identifiers() {
        // The operator type is caller-supplied; a 32-byte bonded id works.
        let data = b"bonded operator ids are 32-byte keys in practice";
        let (_, n) = shard_layout(data.len(), 16, 2);
        let operators: Vec<[u8; 32]> = (0..n).map(|i| [i as u8; 32]).collect();
        let (deal, chunks) = create(data, 16, 2, &operators).unwrap();
        assert_eq!(deal.operator_for(0), Some(&[0u8; 32]));
        assert_eq!(deal.operator_for(n - 1), Some(&[(n as u8 - 1); 32]));
        // Still reconstructs from the data shards alone.
        let data_only: Vec<ErasureChunk> = chunks.into_iter().filter(|c| !c.is_parity).collect();
        assert_eq!(deal.reconstruct(&data_only).unwrap(), data);
    }

    use ed25519_dalek::{Signer, SigningKey, VerifyingKey};

    /// Deterministic signing key from a one-byte seed (no rng dependency).
    fn signer(seed: u8) -> SigningKey {
        SigningKey::from_bytes(&[seed; 32])
    }

    /// Build a deal whose operators are real ed25519 keys, returning the deal,
    /// the shards, and the signing keys (in shard-index order) so a test can
    /// mint honest or forged challenge responses.
    fn signed_deal(
        data: &[u8],
        chunk_size: usize,
        expansion: usize,
    ) -> (
        DurabilityDeal<VerifyingKey>,
        Vec<ErasureChunk>,
        Vec<SigningKey>,
    ) {
        let (_, n) = shard_layout(data.len(), chunk_size, expansion);
        let signers: Vec<SigningKey> = (0..n as u8).map(signer).collect();
        let operators: Vec<VerifyingKey> = signers.iter().map(|s| s.verifying_key()).collect();
        let (deal, chunks) = create(data, chunk_size, expansion, &operators).unwrap();
        (deal, chunks, signers)
    }

    #[test]
    fn authenticated_challenge_by_assigned_operator_verifies() {
        let data = b"the assigned operator signs the challenge and both legs pass";
        let (deal, chunks, signers) = signed_deal(data, 8, 2);
        let nonce = 0x0A11_CE00_u64;
        for i in 0..deal.n {
            let msg = challenge_message(&deal.root, i, nonce);
            let sig = signers[i].sign(&msg);
            assert_eq!(
                deal.verify_challenge_authenticated(i, nonce, &chunks[i], &sig),
                Ok(()),
                "assigned operator {i} failed the authenticated PoR challenge"
            );
        }
    }

    #[test]
    fn authenticated_challenge_by_wrong_operator_is_rejected() {
        // A different key signs a byte-perfect opening for the challenged shard.
        // The opening leg passes (the shard is genuine), but the operator leg
        // fails: a copy-holder is not the bonded operator.
        let data = b"a copy holder cannot answer for the operator it is not, no";
        let (deal, chunks, signers) = signed_deal(data, 8, 2);
        assert!(deal.n >= 2);
        let nonce = 7;
        let target = 0usize;
        let impostor = 1usize; // a different assigned key, standing in as a copy-holder
        let msg = challenge_message(&deal.root, target, nonce);
        let sig = signers[impostor].sign(&msg);
        assert_eq!(
            deal.verify_challenge_authenticated(target, nonce, &chunks[target], &sig),
            Err(ChallengeError::SignatureInvalid { index: target })
        );
        // A brand-new key never placed in the deal is likewise rejected.
        let outsider = signer(200).sign(&msg);
        assert_eq!(
            deal.verify_challenge_authenticated(target, nonce, &chunks[target], &outsider),
            Err(ChallengeError::SignatureInvalid { index: target })
        );
    }

    #[test]
    fn authenticated_challenge_with_stale_nonce_is_rejected() {
        // The operator signs an OLD nonce; the challenger verifies under the
        // CURRENT one. The signed preimage differs, so the check fails even
        // though the signer is the correct assigned operator with a genuine
        // shard. Then the SAME operator signing the CURRENT nonce passes.
        let data = b"a signature over a stale nonce must not answer a fresh one";
        let (deal, chunks, signers) = signed_deal(data, 8, 2);
        let stale = 100_u64;
        let current = 101_u64;
        let target = 0usize;
        let stale_sig = signers[target].sign(&challenge_message(&deal.root, target, stale));
        assert_eq!(
            deal.verify_challenge_authenticated(target, current, &chunks[target], &stale_sig),
            Err(ChallengeError::SignatureInvalid { index: target })
        );
        let fresh_sig = signers[target].sign(&challenge_message(&deal.root, target, current));
        assert_eq!(
            deal.verify_challenge_authenticated(target, current, &chunks[target], &fresh_sig),
            Ok(())
        );
    }

    #[test]
    fn authenticated_challenge_still_requires_a_genuine_opening() {
        // Both legs must pass: even the correct operator's signature cannot
        // rescue a shard that fails the opening leg (a forged/tampered shard).
        let data = b"the operator signature does not excuse a lying shard opening";
        let (deal, chunks, signers) = signed_deal(data, 8, 2);
        let nonce = 42;
        let target = 0usize;
        // Tamper the shard but recompute its integrity leaf; the forged leaf is
        // not in the deal tree, so the opening leg rejects it before leg 2.
        let mut forged = chunks[target].clone();
        forged.data[0] ^= 0xFF;
        forged.commitment = erasure::chunk_commitment_dual(&forged.data).blake3;
        let sig = signers[target].sign(&challenge_message(&deal.root, target, nonce));
        assert_eq!(
            deal.verify_challenge_authenticated(target, nonce, &forged, &sig),
            Err(ChallengeError::ProofInvalid { index: target })
        );
    }

    #[test]
    fn authenticated_challenge_rejects_wrong_shard_response() {
        // Operator signs the right nonce but returns a different shard's
        // opening; the opening leg's shard-binding catches it up front.
        let data = b"an operator must answer the shard it was actually challenged on";
        let (deal, chunks, signers) = signed_deal(data, 8, 2);
        assert!(deal.n >= 2);
        let nonce = 9;
        let challenged = 0usize;
        let responded = 1usize;
        let sig = signers[challenged].sign(&challenge_message(&deal.root, challenged, nonce));
        assert_eq!(
            deal.verify_challenge_authenticated(challenged, nonce, &chunks[responded], &sig),
            Err(ChallengeError::WrongShard {
                challenged,
                responded,
            })
        );
    }

    #[test]
    fn raw_byte_key_operators_authenticate() {
        // The OperatorKey impl for a raw 32-byte id: a deal keyed by the
        // operators' key BYTES authenticates the same way as one keyed by
        // VerifyingKey, so a bonded id that *is* a key works directly.
        let data = b"raw 32-byte operator ids that are ed25519 keys authenticate";
        let (_, n) = shard_layout(data.len(), 8, 2);
        assert!(n >= 2);
        let signers: Vec<SigningKey> = (0..n as u8).map(signer).collect();
        let operators: Vec<[u8; 32]> = signers
            .iter()
            .map(|s| s.verifying_key().to_bytes())
            .collect();
        let (deal, chunks) = create(data, 8, 2, &operators).unwrap();
        let nonce = 555;
        let target = 0usize;
        let sig = signers[target].sign(&challenge_message(&deal.root, target, nonce));
        assert_eq!(
            deal.verify_challenge_authenticated(target, nonce, &chunks[target], &sig),
            Ok(())
        );
        // A non-assigned key over the raw-byte deal is still rejected.
        let wrong = signers[1].sign(&challenge_message(&deal.root, target, nonce));
        assert_eq!(
            deal.verify_challenge_authenticated(target, nonce, &chunks[target], &wrong),
            Err(ChallengeError::SignatureInvalid { index: target })
        );
    }
}
