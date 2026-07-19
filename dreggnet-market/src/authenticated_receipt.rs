//! Authenticated co-endorsement weld for the Dark Bazaar clearing path.
//!
//! [`certified_settlement_digest`] commits to every field of the deterministic
//! book, settlement, Cert-F program/witness, winner, and price using a fixed,
//! domain-separated binary encoding. The digest must occur exactly once as an
//! ordered commitment input in fhegg-fhe's canonical
//! [`ClearingClaim`](fhegg_fhe::attestation::ClearingClaim). The quorum
//! signatures therefore co-endorse the exact ciphertext digests, this exact
//! certified clearing, and the output `(p*, V*)` as distinct claim fields.
//!
//! **Named residual:** this module does not prove that those ciphertexts decrypt
//! or open to the orders in the certified book. A ciphertext-opening / committed-
//! order relation needs the fixed-shape proof path; mere co-membership in a signed
//! claim is not that relation. Until then, computation correctness means only
//! that the configured signing policy includes an honest verifier that checked
//! the missing relation before signing.
//!
//! The trust statement is deliberately narrow: successful verification proves
//! that the certified clearing verifies from scratch and that the configured
//! threshold of distinct roster keys endorsed its exact canonical MPC claim.
//! It is not a UC/MPC-correctness or ciphertext-source-binding theorem unless
//! the quorum policy additionally assumes an honest computation verifier.

use std::fmt;

use fhegg_fhe::attestation::{
    AttestationError, AttestedClearingReceipt, ComputationIntegrityVerifier, Digest32,
    ExpectedClearingContext, InputDigestKind, ReplayGuard,
};

use crate::certified_clearing::{BookBid, CertifiedClearing, CertifiedError, verify_certified};

const SETTLEMENT_DIGEST_DOMAIN: &str = "dreggnet-market/authenticated-certified-settlement/v1";

#[derive(Default)]
struct CanonicalBytes(Vec<u8>);

impl CanonicalBytes {
    fn u8(&mut self, value: u8) {
        self.0.push(value);
    }

    fn u32(&mut self, value: u32) {
        self.0.extend_from_slice(&value.to_be_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.0.extend_from_slice(&value.to_be_bytes());
    }

    fn i8(&mut self, value: i8) {
        self.u8(value as u8);
    }

    fn i64(&mut self, value: i64) {
        self.0.extend_from_slice(&value.to_be_bytes());
    }

    fn i128(&mut self, value: i128) {
        self.0.extend_from_slice(&value.to_be_bytes());
    }

    fn usize(&mut self, value: usize) {
        self.u64(value as u64);
    }

    fn bytes(&mut self, value: &[u8]) {
        self.usize(value.len());
        self.0.extend_from_slice(value);
    }

    fn string(&mut self, value: &str) {
        self.bytes(value.as_bytes());
    }

    fn option_u32(&mut self, value: Option<u32>) {
        match value {
            Some(value) => {
                self.u8(1);
                self.u32(value);
            }
            None => self.u8(0),
        }
    }

    fn option_u64(&mut self, value: Option<u64>) {
        match value {
            Some(value) => {
                self.u8(1);
                self.u64(value);
            }
            None => self.u8(0),
        }
    }
}

fn encode_grid(out: &mut CanonicalBytes, grid: &fhegg_solver::wire::TickGrid) {
    out.u64(grid.base);
    out.u64(grid.tick);
    out.u32(grid.k);
    out.i8(grid.price_exponent);
}

/// Canonical, domain-separated digest of the complete certified clearing.
///
/// This intentionally does not use `Debug` or JSON. Vector order, option tags,
/// enum tags, signed integer widths, and string lengths are all explicit, so a
/// producer and verifier cannot disagree about what the quorum endorsed.
pub fn certified_settlement_digest(receipt: &CertifiedClearing) -> Digest32 {
    let mut out = CanonicalBytes::default();

    out.u32(receipt.book.version);
    out.string(&receipt.book.market_id);
    encode_grid(&mut out, &receipt.book.grid);
    out.usize(receipt.book.orders.len());
    for order in &receipt.book.orders {
        out.string(&order.id);
        out.u8(match order.side {
            fhegg_solver::wire::WireSide::Bid => 0,
            fhegg_solver::wire::WireSide::Ask => 1,
        });
        out.u64(order.qty);
        out.u64(order.price);
    }

    out.u32(receipt.settlement.version);
    out.string(&receipt.settlement.market_id);
    encode_grid(&mut out, &receipt.settlement.grid);
    out.u8(u8::from(receipt.settlement.crossed));
    out.option_u32(receipt.settlement.clearing_price_index);
    out.option_u64(receipt.settlement.clearing_price);
    out.u64(receipt.settlement.cleared_volume);
    out.u64(receipt.settlement.buy_volume);
    out.u64(receipt.settlement.sell_volume);
    out.usize(receipt.settlement.fills.len());
    for fill in &receipt.settlement.fills {
        out.string(&fill.order_id);
        out.u64(fill.qty);
    }

    out.usize(receipt.cert.n_nodes);
    out.usize(receipt.cert.edges.len());
    for &(tail, head) in &receipt.cert.edges {
        out.u32(tail);
        out.u32(head);
    }
    for values in [
        &receipt.cert.w,
        &receipt.cert.c,
        &receipt.cert.f,
        &receipt.cert.pi,
        &receipt.cert.s,
    ] {
        out.usize(values.len());
        for &value in values {
            out.i64(value);
        }
    }
    out.i64(receipt.cert.epsilon);
    out.u64(receipt.winner);
    out.i128(receipt.price);

    *blake3::Hasher::new_derive_key(SETTLEMENT_DIGEST_DOMAIN)
        .update(&out.0)
        .finalize()
        .as_bytes()
}

/// A certified market clearing co-endorsed with an authenticated canonical
/// FHE/MPC claim. Public fields support transport adapters; verification never
/// trusts them and independently recomputes every represented equality. This
/// does not assert that the ciphertexts open to the certified book.
#[derive(Clone, Debug)]
pub struct AuthenticatedCertifiedClearing {
    pub certified: CertifiedClearing,
    pub settlement_digest: Digest32,
    pub claim_digest: Digest32,
    pub attestation: AttestedClearingReceipt,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AuthenticatedClearingError {
    Certified(CertifiedError),
    Attestation(AttestationError),
    SettlementDigestMismatch,
    ClaimDigestMismatch,
    /// The independently supplied ordered input list must contain the exact
    /// certified-settlement commitment once for co-endorsement, not zero times
    /// or ambiguously. This is not a ciphertext-opening relation.
    SettlementCommitmentCount {
        found: usize,
    },
    /// The MPC output must name the certified settlement's crossing exactly.
    OutcomeMismatch,
}

impl fmt::Display for AuthenticatedClearingError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Certified(error) => write!(f, "certified clearing refused: {error}"),
            Self::Attestation(error) => write!(f, "MPC attestation refused: {error}"),
            Self::SettlementDigestMismatch => {
                write!(
                    f,
                    "stored settlement digest does not match the certified clearing"
                )
            }
            Self::ClaimDigestMismatch => {
                write!(
                    f,
                    "stored claim digest does not match the canonical attestation"
                )
            }
            Self::SettlementCommitmentCount { found } => write!(
                f,
                "expected exactly one co-endorsed certified-settlement commitment alongside the ciphertext inputs, found {found}"
            ),
            Self::OutcomeMismatch => write!(
                f,
                "MPC crossing output does not match the certified settlement"
            ),
        }
    }
}

impl std::error::Error for AuthenticatedClearingError {}

impl From<CertifiedError> for AuthenticatedClearingError {
    fn from(error: CertifiedError) -> Self {
        Self::Certified(error)
    }
}

impl From<AttestationError> for AuthenticatedClearingError {
    fn from(error: AttestationError) -> Self {
        Self::Attestation(error)
    }
}

fn verify_weld(
    receipt: &AuthenticatedCertifiedClearing,
    expected: &ExpectedClearingContext<'_>,
) -> Result<(), AuthenticatedClearingError> {
    let digest = certified_settlement_digest(&receipt.certified);
    if receipt.settlement_digest != digest {
        return Err(AuthenticatedClearingError::SettlementDigestMismatch);
    }
    if receipt.claim_digest != receipt.attestation.claim_digest() {
        return Err(AuthenticatedClearingError::ClaimDigestMismatch);
    }

    let found = expected
        .ordered_inputs
        .iter()
        .filter(|input| {
            input.kind == InputDigestKind::Commitment && input.digest == receipt.settlement_digest
        })
        .count();
    if found != 1 {
        return Err(AuthenticatedClearingError::SettlementCommitmentCount { found });
    }

    let expected_price = receipt
        .certified
        .settlement
        .clearing_price_index
        .map(u64::from);
    if expected.crossing.p_star.map(|price| price as u64) != expected_price
        || expected.crossing.v_star != receipt.certified.settlement.cleared_volume
    {
        return Err(AuthenticatedClearingError::OutcomeMismatch);
    }
    Ok(())
}

/// Build the transport envelope after checking the certified receipt, its exact
/// co-endorsed commitment in the expected MPC inputs, its output crossing, and
/// the complete canonical claim equality. This does not prove that the
/// ciphertexts open to the certified book. Computation-integrity evidence is checked by
/// [`verify_authenticated_certified`], where replay can be consumed atomically.
pub fn weld_authenticated_certified(
    bids: &[BookBid],
    reserve: i128,
    certified: CertifiedClearing,
    expected: &ExpectedClearingContext<'_>,
    attestation: AttestedClearingReceipt,
) -> Result<AuthenticatedCertifiedClearing, AuthenticatedClearingError> {
    verify_certified(bids, reserve, &certified)?;
    attestation.verify_binding(expected)?;
    let receipt = AuthenticatedCertifiedClearing {
        settlement_digest: certified_settlement_digest(&certified),
        claim_digest: attestation.claim_digest(),
        certified,
        attestation,
    };
    verify_weld(&receipt, expected)?;
    Ok(receipt)
}

/// Verify the complete market/FHE co-endorsement from scratch, require the
/// configured authenticated computation-integrity policy, and consume the
/// session replay id only after every represented check succeeds. The missing
/// ciphertext-opening / committed-order relation remains a policy assumption.
pub fn verify_authenticated_certified<V: ComputationIntegrityVerifier, R: ReplayGuard>(
    bids: &[BookBid],
    reserve: i128,
    receipt: &AuthenticatedCertifiedClearing,
    expected: &ExpectedClearingContext<'_>,
    verifier: &V,
    replay_guard: &mut R,
) -> Result<(), AuthenticatedClearingError> {
    verify_certified(bids, reserve, &receipt.certified)?;
    verify_weld(receipt, expected)?;
    receipt
        .attestation
        .verify_full(expected, verifier, replay_guard)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use ed25519_dalek::SigningKey;
    use fhegg_fhe::attestation::{
        AttestedClearingReceipt, AuthenticatedQuorumVerifier, BfvPublicIdentity,
        ComputationIntegrityEvidence, ComputationIntegrityResidual, ExpectedClearingContext,
        InMemoryReplayGuard, InputDigest,
    };
    use fhegg_fhe::mpc::Crossing;
    use fhegg_fhe::mpc_party::{PartyMpcSession, simulate_public_transcript};
    use rand::{SeedableRng, rngs::StdRng};

    use super::*;
    use crate::certified_clearing::clear_certified;

    #[test]
    fn authenticated_certified_clearing_coendorses_exact_claim_and_replay() {
        let bids = vec![(10, 30), (11, 50), (12, 40)];
        let certified = clear_certified(&bids, 25).expect("certified clearing");
        let settlement_digest = certified_settlement_digest(&certified);

        let keys: Vec<SigningKey> = [[0x81; 32], [0x82; 32], [0x83; 32]]
            .into_iter()
            .map(|seed| SigningKey::from_bytes(&seed))
            .collect();
        let verifier = AuthenticatedQuorumVerifier::new(
            keys.iter()
                .map(|key| key.verifying_key().to_bytes())
                .collect(),
            2,
        )
        .expect("2-of-3 verifier");
        let roster = verifier.ordered_roster().to_vec();

        let session = PartyMpcSession::new([0x91; 32], 3, 64, 8, 257, Duration::from_secs(1))
            .expect("valid public session");
        let bfv = BfvPublicIdentity {
            n_parties: 3,
            degree: 4096,
            moduli_digest: [0x31; 32],
            plaintext_modulus: 257,
            crp_seed: [0x42; 32],
            collective_public_key_digest: [0x53; 32],
        };
        let inputs = vec![
            InputDigest::ciphertext_bytes(b"canonical-demand-ciphertext"),
            InputDigest::ciphertext_bytes(b"canonical-supply-ciphertext"),
            InputDigest::commitment(settlement_digest),
        ];
        let crossing = Crossing {
            p_star: certified
                .settlement
                .clearing_price_index
                .map(|price| price as usize),
            v_star: certified.settlement.cleared_volume,
        };
        let mut rng = StdRng::seed_from_u64(0xa771_57ed);
        let transcript = simulate_public_transcript(&crossing, &session, &mut rng)
            .expect("strict reveal-only transcript");
        let expected = ExpectedClearingContext {
            session: &session,
            ordered_roster: &roster,
            bfv: &bfv,
            ordered_inputs: &inputs,
            transcript: &transcript,
            crossing: &crossing,
        };

        let mut attestation = AttestedClearingReceipt::issue(
            &expected,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .expect("canonical claim");
        let claim_digest = attestation.claim_digest();
        let signatures = [
            verifier
                .sign_claim(&claim_digest, 0, &keys[0])
                .expect("party 0"),
            verifier
                .sign_claim(&claim_digest, 1, &keys[1])
                .expect("party 1"),
        ];
        attestation.computation_integrity = verifier
            .assemble_evidence(&claim_digest, &signatures)
            .expect("authenticated quorum evidence");

        let receipt =
            weld_authenticated_certified(&bids, 25, certified.clone(), &expected, attestation)
                .expect("exact market/FHE weld");
        let mut replay = InMemoryReplayGuard::default();
        verify_authenticated_certified(&bids, 25, &receipt, &expected, &verifier, &mut replay)
            .expect("authenticated receipt passes once");
        assert!(matches!(
            verify_authenticated_certified(&bids, 25, &receipt, &expected, &verifier, &mut replay),
            Err(AuthenticatedClearingError::Attestation(
                AttestationError::ReplayDetected
            ))
        ));

        // SOURCE-RELATION RESIDUAL, made executable: the settlement commitment and
        // ciphertext digests are distinct claim fields. Replacing a ciphertext
        // digest makes the OLD quorum evidence fail, because it changes the exact
        // combined claim. But a quorum can sign the new combined claim and this
        // layer accepts it without proving that either ciphertext opens to `bids`.
        // The fixed-shape ciphertext-opening/committed-order proof must close that
        // relation; this test prevents co-endorsement from being misnamed as one.
        let unrelated_inputs = vec![
            InputDigest::ciphertext_bytes(b"an-unrelated-demand-ciphertext"),
            InputDigest::ciphertext_bytes(b"canonical-supply-ciphertext"),
            InputDigest::commitment(settlement_digest),
        ];
        let unrelated_expected = ExpectedClearingContext {
            session: &session,
            ordered_roster: &roster,
            bfv: &bfv,
            ordered_inputs: &unrelated_inputs,
            transcript: &transcript,
            crossing: &crossing,
        };
        assert_eq!(
            verify_authenticated_certified(
                &bids,
                25,
                &receipt,
                &unrelated_expected,
                &verifier,
                &mut InMemoryReplayGuard::default()
            ),
            Err(AuthenticatedClearingError::Attestation(
                AttestationError::BindingMismatch
            )),
            "old signatures cannot be moved to a different ciphertext digest"
        );

        let mut unrelated_attestation = AttestedClearingReceipt::issue(
            &unrelated_expected,
            ComputationIntegrityEvidence::BindingOnly(
                ComputationIntegrityResidual::OutputOnlySelfAssertion,
            ),
        )
        .expect("the unrelated digest is structurally a valid claim input");
        let unrelated_claim_digest = unrelated_attestation.claim_digest();
        let unrelated_signatures = [
            verifier
                .sign_claim(&unrelated_claim_digest, 0, &keys[0])
                .expect("party 0 explicitly co-endorses the changed claim"),
            verifier
                .sign_claim(&unrelated_claim_digest, 1, &keys[1])
                .expect("party 1 explicitly co-endorses the changed claim"),
        ];
        unrelated_attestation.computation_integrity = verifier
            .assemble_evidence(&unrelated_claim_digest, &unrelated_signatures)
            .expect("quorum signs the exact changed combined claim");
        let unrelated_receipt = weld_authenticated_certified(
            &bids,
            25,
            certified.clone(),
            &unrelated_expected,
            unrelated_attestation,
        )
        .expect("co-endorsement does not pretend to prove a source relation");
        verify_authenticated_certified(
            &bids,
            25,
            &unrelated_receipt,
            &unrelated_expected,
            &verifier,
            &mut InMemoryReplayGuard::default(),
        )
        .expect("fresh exact quorum endorsement passes its stated policy");

        let mut tampered = receipt.clone();
        tampered.settlement_digest[0] ^= 1;
        assert_eq!(
            verify_authenticated_certified(
                &bids,
                25,
                &tampered,
                &expected,
                &verifier,
                &mut InMemoryReplayGuard::default()
            ),
            Err(AuthenticatedClearingError::SettlementDigestMismatch)
        );

        let mut tampered = receipt.clone();
        tampered.claim_digest[0] ^= 1;
        assert_eq!(
            verify_authenticated_certified(
                &bids,
                25,
                &tampered,
                &expected,
                &verifier,
                &mut InMemoryReplayGuard::default()
            ),
            Err(AuthenticatedClearingError::ClaimDigestMismatch)
        );

        let mut tampered = receipt.clone();
        tampered.certified.price = 40;
        assert!(matches!(
            verify_authenticated_certified(
                &bids,
                25,
                &tampered,
                &expected,
                &verifier,
                &mut InMemoryReplayGuard::default()
            ),
            Err(AuthenticatedClearingError::Certified(_))
        ));

        let wrong_inputs = vec![
            InputDigest::ciphertext_bytes(b"canonical-demand-ciphertext"),
            InputDigest::ciphertext_bytes(b"canonical-supply-ciphertext"),
            InputDigest::commitment([0xdd; 32]),
        ];
        let wrong_expected = ExpectedClearingContext {
            session: &session,
            ordered_roster: &roster,
            bfv: &bfv,
            ordered_inputs: &wrong_inputs,
            transcript: &transcript,
            crossing: &crossing,
        };
        assert_eq!(
            verify_authenticated_certified(
                &bids,
                25,
                &receipt,
                &wrong_expected,
                &verifier,
                &mut InMemoryReplayGuard::default()
            ),
            Err(AuthenticatedClearingError::SettlementCommitmentCount { found: 0 })
        );

        let mut duplicate_inputs = inputs.clone();
        duplicate_inputs.push(InputDigest::commitment(settlement_digest));
        let duplicate_expected = ExpectedClearingContext {
            session: &session,
            ordered_roster: &roster,
            bfv: &bfv,
            ordered_inputs: &duplicate_inputs,
            transcript: &transcript,
            crossing: &crossing,
        };
        assert_eq!(
            verify_authenticated_certified(
                &bids,
                25,
                &receipt,
                &duplicate_expected,
                &verifier,
                &mut InMemoryReplayGuard::default()
            ),
            Err(AuthenticatedClearingError::SettlementCommitmentCount { found: 2 }),
            "duplicating the commitment is ambiguous, not a stronger weld"
        );

        let mut binding_only = receipt.clone();
        binding_only.attestation.computation_integrity = ComputationIntegrityEvidence::BindingOnly(
            ComputationIntegrityResidual::OutputOnlySelfAssertion,
        );
        assert!(matches!(
            verify_authenticated_certified(
                &bids,
                25,
                &binding_only,
                &expected,
                &verifier,
                &mut InMemoryReplayGuard::default()
            ),
            Err(AuthenticatedClearingError::Attestation(
                AttestationError::ComputationIntegrityResidual(_)
            ))
        ));
    }
}
