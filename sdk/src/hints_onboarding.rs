//! The HINTS guardian-onboarding ceremony — *a guardian JOINS a council*.
//!
//! Social recovery (`tests/identity_social_recovery_e2e.rs`) proves a *fixed*
//! guardian committee can authorize an identity's KERI rotation. This module
//! builds the frontier that comes BEFORE that committee is fixed: the seam by
//! which a prospective guardian is admitted into the sitting council, growing
//! the weighted-threshold quorum that future recoveries answer to.
//!
//! # The three legs of the ceremony
//!
//! 1. **The prospective guardian enrolls.** They generate a fresh BLS keypair
//!    against the council's shared `GlobalData` (the KZG universal params) and,
//!    crucially, a *hint*: `hints::generate_hint` produces the
//!    universal-params commitment that weighted aggregation needs to bind their
//!    key into a constant-size quorum certificate. The hint is the
//!    onboarding-specific artifact — without it the candidate's key cannot be
//!    folded into the universe verifier key. [`GuardianEnrollment`].
//!
//! 2. **The council admits them — a quorum-authorized add.** Admission is not
//!    unilateral: the *sitting* committee certifies the candidate by signing the
//!    canonical admission message (the candidate's enrollment commitment) with a
//!    weighted-threshold quorum. This is the SAME [`FederationCommittee`]
//!    threshold-BLS primitive social recovery uses to authorize a rotation, so
//!    onboarding *composes* with guardian rotation: a sub-threshold council
//!    cannot admit, exactly as a sub-threshold council cannot recover.
//!    [`AdmissionCertificate`].
//!
//! 3. **The assembled committee commits its aggregate verifier key.** With the
//!    new guardian's key + hint folded in, the council re-runs `setup_universe`
//!    to produce a fresh universe — and with it a new aggregate *verifier key*.
//!    Its content address ([`GuardianRoster::committed_vk`]) is what an identity
//!    cell pins as the `commitment` its recovery predicate answers under: a
//!    guardian set is identified by what its assembled committee can verify.
//!
//! # Empowered, never amplified — fail-closed on a bad hint
//!
//! A candidate cannot smuggle authority in by presenting a hint that does not
//! correspond to the public key they declare. `setup_universe` pair-checks every
//! hint against its slot's Lagrange commitment; a mismatched hint yields a
//! `PartyError::PairingCheckFailed`, and [`GuardianRoster::assemble`] refuses to
//! build a committee with any party error. So the assembled committee either
//! verifies a REAL aggregate over the genuinely-admitted guardians, or it does
//! not assemble at all. (Both polarities are exercised in the tests below.)
//!
//! This module is gpui-free and adds no crypto: it welds `dregg-federation`'s
//! HINTS committee wrapper (`threshold.rs`) and the `hints` primitives
//! (`generate_hint` / `setup_universe`) into the onboarding shape.

use dregg_federation::threshold::{
    FederationCommittee, MemberSecret, ThresholdError, ThresholdQC,
};
use hints::{
    GlobalData, Hint, PublicKey as BlsPublicKey, SecretKey as BlsSecretKey, generate_hint,
    setup_universe, snark::F,
};
use std::sync::Arc;

/// The HINTS weight field element `1` / `0`, obtained via `From<u64>` so this
/// module needs no direct `ark_ff` dependency (`F: From<u64>` is re-exported).
fn f_one() -> F {
    F::from(1u64)
}
fn f_zero() -> F {
    F::from(0u64)
}

// =============================================================================
// Errors
// =============================================================================

/// Failures of the onboarding ceremony.
#[derive(Debug)]
pub enum OnboardingError {
    /// The underlying HINTS / threshold layer rejected the operation (e.g. a
    /// hint that does not pair-check against its declared public key, or a
    /// universe whose participant count is malformed).
    Threshold(ThresholdError),
    /// The sitting council's admission quorum did not meet the threshold, so the
    /// candidate is NOT admitted.
    AdmissionRefused,
    /// A candidate's enrollment was already present in the roster (an idempotent
    /// double-admit is rejected so weights stay one-per-guardian).
    DuplicateGuardian,
    /// The roster is empty (a council must have a founding member to admit into).
    EmptyRoster,
}

impl std::fmt::Display for OnboardingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OnboardingError::Threshold(e) => write!(f, "onboarding threshold error: {e}"),
            OnboardingError::AdmissionRefused => {
                write!(f, "the council's admission quorum did not meet the threshold")
            }
            OnboardingError::DuplicateGuardian => {
                write!(f, "that guardian is already admitted to the council")
            }
            OnboardingError::EmptyRoster => write!(f, "the guardian roster is empty"),
        }
    }
}

impl std::error::Error for OnboardingError {}

impl From<ThresholdError> for OnboardingError {
    fn from(e: ThresholdError) -> Self {
        OnboardingError::Threshold(e)
    }
}

// =============================================================================
// Leg 1: the prospective guardian's enrollment
// =============================================================================

/// What a prospective guardian generates to JOIN a council: a BLS public key and
/// the *hint* that binds it into weighted-threshold aggregation.
///
/// The hint is produced by `hints::generate_hint` against the council's shared
/// `GlobalData` at the slot the candidate will occupy. It does not depend on the
/// other members' keys or the weights, so a candidate can prepare it offline and
/// present it to the council — it is the universal-params commitment the universe
/// setup needs to fold the key into the aggregate verifier key.
#[derive(Clone, Debug)]
pub struct GuardianEnrollment {
    /// The candidate's BLS public key (the verification side of their share).
    pub public_key: BlsPublicKey,
    /// The universal-params commitment binding `public_key` at `slot`.
    pub hint: Hint,
    /// The committee slot this enrollment is bound to. The hint pair-checks only
    /// at this slot, so an enrollment cannot be replayed into a different slot.
    pub slot: usize,
}

impl GuardianEnrollment {
    /// Build an enrollment from a candidate's secret key, for the `slot` the
    /// council will seat them in, against the council's shared `gd`.
    ///
    /// `domain_size` is the power-of-two HINTS domain the assembled committee
    /// will use (one more than the number of participant slots). The candidate
    /// must know it to bind their hint to the right Lagrange basis.
    pub fn from_secret(
        gd: &GlobalData,
        secret_key: &BlsSecretKey,
        domain_size: usize,
        slot: usize,
    ) -> Result<Self, OnboardingError> {
        let public_key = secret_key.public(gd);
        let hint = generate_hint(gd, secret_key, domain_size, slot)
            .map_err(|e| OnboardingError::Threshold(ThresholdError::Hints(e)))?;
        Ok(Self {
            public_key,
            hint,
            slot,
        })
    }

    /// The 32-byte content address of this enrollment — the candidate's pubkey
    /// and hint, committed. This is what the sitting council signs to admit the
    /// candidate (so the admission QC is bound to EXACTLY the key+hint being
    /// folded in, not merely to "some guardian").
    pub fn commitment(&self) -> [u8; 32] {
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"deos-guardian-enrollment-v1");
        // `PublicKey` and `Hint` both derive `serde::Serialize` over their
        // compressed-checked wire form; postcard gives a canonical byte image
        // without pulling `ark_serialize` into this crate.
        let pk_bytes =
            postcard::to_allocvec(&self.public_key).expect("pubkey serialization is infallible");
        hasher.update(&pk_bytes);
        let hint_bytes =
            postcard::to_allocvec(&self.hint).expect("hint serialization is infallible");
        hasher.update(&hint_bytes);
        hasher.update(&(self.slot as u64).to_le_bytes());
        hasher.finalize().into()
    }
}

// =============================================================================
// Leg 2: the council's quorum-authorized admission
// =============================================================================

/// The canonical message the sitting council signs to admit a candidate. Binds
/// the candidate's enrollment commitment and the slot they will occupy, under a
/// domain-separated tag (so an admission QC can never be replayed as a recovery
/// QC or vice versa).
pub fn admission_signing_message(enrollment: &GuardianEnrollment) -> Vec<u8> {
    let mut msg = Vec::with_capacity(64);
    msg.extend_from_slice(b"deos-guardian-admit-v1");
    msg.extend_from_slice(&enrollment.commitment());
    msg.extend_from_slice(&(enrollment.slot as u64).to_le_bytes());
    msg
}

/// A weighted-threshold certificate that the SITTING council admitted a
/// candidate. It is a real `ThresholdQC` over [`admission_signing_message`],
/// verifiable against the sitting committee — the same primitive a recovery QC
/// uses, so admission and rotation compose under one threshold algebra.
#[derive(Clone, Debug)]
pub struct AdmissionCertificate {
    /// The enrollment that was admitted.
    pub enrollment: GuardianEnrollment,
    /// The sitting council's aggregate quorum certificate over the admission
    /// message.
    pub qc: ThresholdQC,
}

impl AdmissionCertificate {
    /// Have the sitting council admit `enrollment`: `signers` (referring to
    /// `sitting_members` by position) sign the admission message, and the
    /// resulting shares are aggregated against `sitting`. Fails with
    /// [`OnboardingError::AdmissionRefused`] if the signing set is below the
    /// sitting council's threshold.
    pub fn issue(
        sitting: &FederationCommittee,
        sitting_members: &[MemberSecret],
        signers: &[usize],
        enrollment: GuardianEnrollment,
    ) -> Result<Self, OnboardingError> {
        let message = admission_signing_message(&enrollment);
        let shares: Vec<_> = signers
            .iter()
            .map(|&i| (sitting_members[i].index, sitting.sign_share(&sitting_members[i], &message)))
            .collect();
        // Below threshold -> the aggregator refuses to certify the QC.
        let qc = sitting
            .aggregate(&shares, &message)
            .map_err(|_| OnboardingError::AdmissionRefused)?;
        Ok(Self { enrollment, qc })
    }

    /// Verify this admission certificate against the sitting council. The host
    /// checks the QC against the council it TRUSTS, not any committee the
    /// presenter supplies — so a candidate cannot self-admit by standing up
    /// their own council.
    pub fn verify(&self, sitting: &FederationCommittee) -> Result<(), OnboardingError> {
        let message = admission_signing_message(&self.enrollment);
        sitting
            .verify(&self.qc, &message)
            .map_err(|_| OnboardingError::AdmissionRefused)
    }
}

// =============================================================================
// Leg 3: the assembled committee + committed aggregate verifier key
// =============================================================================

/// A guardian's seat in the roster: the public verification material the
/// assembled committee folds into its aggregate verifier key.
#[derive(Clone)]
pub struct GuardianSeat {
    pub public_key: BlsPublicKey,
    pub hint: Hint,
}

/// The assembled guardian roster — the ordered set of seated guardians whose
/// public keys + hints define the committee. Onboarding GROWS this roster: each
/// admitted candidate adds a seat, and the roster re-assembles into a fresh
/// `FederationCommittee` whose aggregate verifier key is content-addressed.
#[derive(Clone)]
pub struct GuardianRoster {
    seats: Vec<GuardianSeat>,
    threshold: u64,
    global: Arc<GlobalData>,
}

impl GuardianRoster {
    /// Found a roster from an existing committee's member public keys, against a
    /// shared `gd`. Each founding member contributes their pubkey + a hint at
    /// their slot. `threshold` is the weighted floor future quorums must meet.
    pub fn found(
        gd: Arc<GlobalData>,
        founders: &[MemberSecret],
        threshold: u64,
    ) -> Result<Self, OnboardingError> {
        if founders.is_empty() {
            return Err(OnboardingError::EmptyRoster);
        }
        let domain_size = (founders.len() + 1).next_power_of_two();
        let seats = founders
            .iter()
            .enumerate()
            .map(|(slot, m)| {
                let hint = generate_hint(&gd, &m.secret_key, domain_size, slot)
                    .map_err(|e| OnboardingError::Threshold(ThresholdError::Hints(e)))?;
                Ok(GuardianSeat {
                    public_key: m.public_key.clone(),
                    hint,
                })
            })
            .collect::<Result<Vec<_>, OnboardingError>>()?;
        Ok(Self {
            seats,
            threshold,
            global: gd,
        })
    }

    /// The HINTS domain size for the CURRENT roster size.
    fn domain_size(&self) -> usize {
        (self.seats.len() + 1).next_power_of_two()
    }

    /// The slot the NEXT admitted guardian will occupy.
    pub fn next_slot(&self) -> usize {
        self.seats.len()
    }

    /// The number of seated guardians.
    pub fn len(&self) -> usize {
        self.seats.len()
    }

    /// Whether the roster has no seats.
    pub fn is_empty(&self) -> bool {
        self.seats.is_empty()
    }

    /// The shared universal params the roster (and any candidate enrolling into
    /// it) is bound to.
    pub fn global(&self) -> &Arc<GlobalData> {
        &self.global
    }

    /// Admit a candidate whose admission is certified by the SITTING council.
    ///
    /// The certificate's QC is checked against the committee assembled from the
    /// CURRENT roster (the sitting council) before the new seat is added — so a
    /// candidate enters only on a genuine quorum's blessing. On success the
    /// roster grows by one seat (the new guardian's pubkey + hint).
    ///
    /// Rejects a duplicate guardian and a certificate whose enrollment slot does
    /// not match the seat the roster will assign (so the admission QC is bound to
    /// exactly the seat being filled).
    pub fn admit(&mut self, cert: &AdmissionCertificate) -> Result<(), OnboardingError> {
        let sitting = self.assemble()?;
        cert.verify(&sitting)?;

        if cert.enrollment.slot != self.next_slot() {
            return Err(OnboardingError::Threshold(ThresholdError::Hints(
                hints::HintsError::InvalidInput(format!(
                    "enrollment bound to slot {} but the next free seat is {}",
                    cert.enrollment.slot,
                    self.next_slot()
                )),
            )));
        }
        if self
            .seats
            .iter()
            .any(|s| s.public_key == cert.enrollment.public_key)
        {
            return Err(OnboardingError::DuplicateGuardian);
        }

        self.seats.push(GuardianSeat {
            public_key: cert.enrollment.public_key.clone(),
            hint: cert.enrollment.hint.clone(),
        });
        Ok(())
    }

    /// Assemble the current roster into a `FederationCommittee`.
    ///
    /// Re-runs `setup_universe` over the seated guardians (padding zero-weight
    /// dummies up to the HINTS domain), producing the aggregate verifier key. A
    /// seat whose hint does NOT pair-check against its declared public key yields
    /// a `PartyError`, and assembly FAILS — the assembled committee is either
    /// sound over genuine guardians or it does not exist.
    pub fn assemble(&self) -> Result<FederationCommittee, OnboardingError> {
        if self.seats.is_empty() {
            return Err(OnboardingError::EmptyRoster);
        }
        let gd = &self.global;
        let domain_size = self.domain_size();
        let total_slots = domain_size - 1;

        let mut pks: Vec<BlsPublicKey> = self.seats.iter().map(|s| s.public_key.clone()).collect();
        let mut all_hints: Vec<Hint> = self.seats.iter().map(|s| s.hint.clone()).collect();
        let mut weights: Vec<F> = vec![f_one(); self.seats.len()];

        // Pad with zero-weight dummies up to the HINTS participant count.
        let dummy_sk = BlsSecretKey::dummy();
        let dummy_pk = dummy_sk.public(gd);
        for slot in self.seats.len()..total_slots {
            pks.push(dummy_pk.clone());
            all_hints.push(
                generate_hint(gd, &dummy_sk, domain_size, slot)
                    .map_err(|e| OnboardingError::Threshold(ThresholdError::Hints(e)))?,
            );
            weights.push(f_zero());
        }

        let universe = setup_universe(gd, pks, &all_hints, weights)
            .map_err(|e| OnboardingError::Threshold(ThresholdError::Hints(e)))?;

        // FAIL-CLOSED: any party error (a mismatched / malformed hint) means the
        // assembled aggregate is not faithful to the declared guardians. Refuse.
        if !universe.party_errors.is_empty() {
            return Err(OnboardingError::Threshold(ThresholdError::Hints(
                hints::HintsError::InvalidInput(format!(
                    "guardian assembly rejected: party errors {:?}",
                    universe.party_errors
                )),
            )));
        }

        Ok(FederationCommittee {
            global: gd.clone(),
            universe,
            num_members: self.seats.len(),
            threshold: F::from(self.threshold),
            threshold_value: self.threshold,
        })
        // NB `F::from(u64)` is the re-exported `From` impl — no `ark_ff` dep.
    }

    /// The content address of the assembled committee's aggregate VERIFIER KEY.
    ///
    /// This is the `guardian_root`-style commitment an identity cell pins for its
    /// recovery predicate: a guardian set is named by what its assembled
    /// committee can verify. It changes whenever the roster changes (a new
    /// guardian folds a new key into the VK), so a recovery predicate pinned to
    /// the old root will not accept the new committee until re-pinned — admission
    /// is an explicit, witnessed step, never silent.
    pub fn committed_vk(&self) -> Result<[u8; 32], OnboardingError> {
        let committee = self.assemble()?;
        // `VerifierKey` (behind the `CompressedChecked` newtype the `vk` Arc
        // holds) derives `serde::Serialize` over its canonical compressed form;
        // postcard gives a stable byte image without an `ark_serialize` dep.
        let buf = postcard::to_allocvec(&committee.universe.vk).map_err(|e| {
            OnboardingError::Threshold(ThresholdError::SerializationError(e.to_string()))
        })?;
        let mut hasher = blake3::Hasher::new();
        hasher.update(b"deos-guardian-committee-vk-v1");
        hasher.update(&buf);
        hasher.update(&self.threshold.to_le_bytes());
        Ok(hasher.finalize().into())
    }
}

// =============================================================================
// Tests — both polarities of the onboarding tooth.
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_federation::threshold::{generate_test_committee, generate_test_committee_with_seed};
    use hints::PartialSignature;

    /// A founding 3-of-5 council assembled into a roster, returning the roster,
    /// the sitting committee, and the founders' secrets (so they can sign an
    /// admission quorum).
    fn founding_council() -> (GuardianRoster, FederationCommittee, Vec<MemberSecret>) {
        let (committee, members) = generate_test_committee(5, 3).unwrap();
        let roster = GuardianRoster::found(committee.global.clone(), &members, 3).unwrap();
        (roster, committee, members)
    }

    /// Generate a fresh candidate secret against the council's shared params.
    /// Uses the federation `MemberSecret::generate` (OS entropy) so this test
    /// module needs no direct `ark_std` RNG dependency, and each candidate is a
    /// genuinely distinct key.
    fn fresh_candidate(gd: &GlobalData) -> BlsSecretKey {
        MemberSecret::generate(gd, 0).secret_key
    }

    // ---- TRUE polarity --------------------------------------------------------

    /// A prospective guardian enrolls, the SITTING 3-of-5 council admits them on
    /// a genuine quorum, the roster grows to six, and the assembled committee
    /// verifies a REAL aggregate signature over a fresh message. Onboarding
    /// produced a working larger committee.
    #[test]
    fn guardian_onboards_and_committee_verifies_real_aggregate() {
        let (mut roster, sitting, sitting_members) = founding_council();
        assert_eq!(roster.len(), 5);

        // Leg 1: the candidate enrolls against the council's shared params, at
        // the next free seat. Domain grows to 8 (the next pow2 above 6 seats).
        let new_domain = (roster.len() + 1 + 1).next_power_of_two();
        let candidate_sk = fresh_candidate(&roster.global().clone());
        let enrollment = GuardianEnrollment::from_secret(
            &roster.global().clone(),
            &candidate_sk,
            new_domain,
            roster.next_slot(),
        )
        .expect("a well-formed candidate must enroll");

        // Leg 2: a 3-of-5 quorum of the SITTING council admits the candidate.
        let cert = AdmissionCertificate::issue(
            &sitting,
            &sitting_members,
            &[0, 2, 4],
            enrollment,
        )
        .expect("a 3-of-5 quorum must certify the admission");

        // The admission QC verifies against the sitting council.
        cert.verify(&sitting)
            .expect("a genuine admission QC verifies against the sitting council");

        // Leg 3: the roster grows and re-assembles.
        roster.admit(&cert).expect("a certified candidate is admitted");
        assert_eq!(roster.len(), 6, "the council grew by one guardian");

        // The assembled SIX-guardian committee verifies a REAL aggregate. Build
        // a quorum that INCLUDES the newly-onboarded guardian to prove their key
        // was genuinely folded into the universe verifier key.
        let assembled = roster.assemble().expect("the grown roster assembles");
        let message = b"deos-recovery-after-onboarding:rotate-v1";

        // Reconstruct the members for the assembled committee: the 5 founders at
        // their original slots, plus the new guardian at slot 5.
        let mut signers: Vec<(usize, PartialSignature)> = sitting_members[0..3]
            .iter()
            .map(|m| (m.index, assembled.sign_share(m, message)))
            .collect();
        let new_member = MemberSecret {
            secret_key: candidate_sk.clone(),
            public_key: candidate_sk.public(roster.global()),
            index: 5,
        };
        signers.push((new_member.index, assembled.sign_share(&new_member, message)));

        let qc = assembled
            .aggregate(&signers, message)
            .expect("4 of 6 guardians (incl. the new one) meet the 3-floor");
        assert!(
            assembled.verify(&qc, message).is_ok(),
            "the assembled committee verifies a real aggregate including the onboarded guardian"
        );

        // The committed VK is well-formed and stable.
        let vk_a = roster.committed_vk().expect("committed VK");
        let vk_b = roster.committed_vk().expect("committed VK again");
        assert_eq!(vk_a, vk_b, "the committed VK is deterministic");
    }

    /// Admission GROWS the committee's commitment: the committed VK after
    /// onboarding differs from before, so a recovery predicate pinned to the old
    /// root will not silently accept the new committee.
    #[test]
    fn onboarding_changes_the_committed_vk() {
        let (mut roster, sitting, sitting_members) = founding_council();
        let before = roster.committed_vk().expect("VK before");

        let new_domain = (roster.len() + 1 + 1).next_power_of_two();
        let candidate_sk = fresh_candidate(&roster.global().clone());
        let enrollment = GuardianEnrollment::from_secret(
            &roster.global().clone(),
            &candidate_sk,
            new_domain,
            roster.next_slot(),
        )
        .unwrap();
        let cert =
            AdmissionCertificate::issue(&sitting, &sitting_members, &[0, 1, 2], enrollment).unwrap();
        roster.admit(&cert).unwrap();

        let after = roster.committed_vk().expect("VK after");
        assert_ne!(
            before, after,
            "folding a new guardian into the committee changes its verifier-key commitment"
        );
    }

    // ---- FALSE polarity -------------------------------------------------------

    /// A candidate who presents a hint that does NOT correspond to the public key
    /// they declare is REJECTED: the assembled committee's `setup_universe`
    /// pair-check fails for that seat, and `assemble` refuses to build the
    /// committee at all. A forged hint cannot smuggle a guardian in.
    #[test]
    fn mismatched_hint_is_rejected() {
        let (mut roster, sitting, sitting_members) = founding_council();

        let new_domain = (roster.len() + 1 + 1).next_power_of_two();
        let slot = roster.next_slot();

        // The candidate declares the public key of `candidate_sk` …
        let candidate_sk = fresh_candidate(&roster.global().clone());
        let declared_pk = candidate_sk.public(roster.global());

        // … but presents a hint generated from a DIFFERENT secret key (an
        // attacker who cannot prove possession of `candidate_sk`, or a corrupted
        // enrollment). The hint will not pair-check against `declared_pk`.
        let mut other_sk = fresh_candidate(&roster.global().clone());
        // Ensure it is genuinely distinct from the declared key (OS entropy makes
        // a collision astronomically unlikely, but loop to be unconditional).
        while other_sk.public(roster.global()) == declared_pk {
            other_sk = fresh_candidate(&roster.global().clone());
        }
        let mismatched_hint =
            generate_hint(roster.global(), &other_sk, new_domain, slot).unwrap();

        let forged = GuardianEnrollment {
            public_key: declared_pk,
            hint: mismatched_hint,
            slot,
        };

        // The sitting council might even be tricked into admitting the
        // commitment (it signs the bytes, not the pairing) — but the ASSEMBLY
        // fails closed when the roster tries to re-build its universe.
        let cert =
            AdmissionCertificate::issue(&sitting, &sitting_members, &[0, 1, 2], forged).unwrap();

        let err = roster
            .admit(&cert)
            .map(|_| roster.assemble())
            .and_then(|r| r) // flatten admit-then-assemble
            .err();

        // Either `admit`'s own re-assembly of the (now-grown) roster fails, or a
        // direct `assemble` fails — in all cases the forged-hint committee does
        // not exist.
        let assemble_err = roster.assemble().err();
        assert!(
            err.is_some() || assemble_err.is_some(),
            "a mismatched hint must make the assembled committee unbuildable"
        );

        // Belt and braces: a direct assembly of a roster carrying the forged seat
        // is unambiguously rejected with a party error.
        match roster.assemble() {
            Err(OnboardingError::Threshold(ThresholdError::Hints(
                hints::HintsError::InvalidInput(msg),
            ))) => {
                assert!(
                    msg.contains("party errors") || msg.contains("PairingCheckFailed"),
                    "rejection cites the hint pair-check failure, got: {msg}"
                );
            }
            Err(other) => panic!("expected a party-error rejection, got {other:?}"),
            Ok(_) => panic!("a roster carrying a forged-hint seat must not assemble"),
        }
    }

    /// A SUB-THRESHOLD council cannot admit: two signers below the 3-of-5 floor
    /// fail to certify the admission, so the candidate never enters the roster.
    /// Admission is empowered, never amplified — exactly as recovery is.
    #[test]
    fn sub_threshold_admission_refused() {
        let (roster, sitting, sitting_members) = founding_council();
        let before_len = roster.len();

        let new_domain = (roster.len() + 1 + 1).next_power_of_two();
        let candidate_sk = fresh_candidate(&roster.global().clone());
        let enrollment = GuardianEnrollment::from_secret(
            &roster.global().clone(),
            &candidate_sk,
            new_domain,
            roster.next_slot(),
        )
        .unwrap();

        // Only TWO sitting guardians sign — below the 3-of-5 floor.
        let result =
            AdmissionCertificate::issue(&sitting, &sitting_members, &[0, 1], enrollment);
        assert!(
            matches!(result, Err(OnboardingError::AdmissionRefused)),
            "a 2-of-5 admission quorum must be refused, got: {result:?}"
        );

        assert_eq!(
            roster.len(),
            before_len,
            "no admission landed — the roster did not grow"
        );
    }

    /// A valid admission QC from the WRONG (attacker) council is REFUSED: the
    /// roster verifies the certificate against the council it trusts (the sitting
    /// committee assembled from the current seats), not any committee the
    /// presenter supplies.
    #[test]
    fn wrong_council_admission_refused() {
        let (mut roster, _sitting, _sitting_members) = founding_council();
        let before_len = roster.len();

        // The attacker stands up their OWN 3-of-5 committee on a DISTINCT setup
        // (a different seed -> genuinely different keys + verifier key than the
        // sitting council assembled by `founding_council`).
        let (attacker_committee, attacker_members) =
            generate_test_committee_with_seed(5, 3, [0x9A; 32]).unwrap();

        let new_domain = (roster.len() + 1 + 1).next_power_of_two();
        let candidate_sk = fresh_candidate(&roster.global().clone());
        let enrollment = GuardianEnrollment::from_secret(
            &roster.global().clone(),
            &candidate_sk,
            new_domain,
            roster.next_slot(),
        )
        .unwrap();

        // A perfectly valid quorum — of the WRONG council.
        let cert = AdmissionCertificate::issue(
            &attacker_committee,
            &attacker_members,
            &[0, 1, 2],
            enrollment,
        )
        .expect("the attacker can certify over their own committee");

        let err = roster
            .admit(&cert)
            .expect_err("a QC from a committee other than the sitting council must be refused");
        assert!(
            matches!(err, OnboardingError::AdmissionRefused),
            "rejection is at the admission-quorum boundary, got: {err:?}"
        );
        assert_eq!(
            roster.len(),
            before_len,
            "no admission landed — the wrong-council quorum did not grow the roster"
        );
    }
}
