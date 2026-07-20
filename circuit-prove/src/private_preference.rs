//! Fixed `N=4,K=4` private preference aggregation proof producer.
//!
//! The relation and AIR descriptor are authored in Lean at
//! `Dregg2/Games/PrivatePreferenceDescriptor.lean`. This module only validates
//! inputs, fills that fixed layout, and proves the emitted artifact. Four
//! private participants score four options from 0 through 3; the verifier sees
//! only `(session, rule, ballot_root[0..8), winner)`, where `winner` is the
//! lowest-index aggregate maximizer. Aggregate totals and the winning score stay
//! private.
//!
//! [`prove_zk`] uses `HidingFriPcs`. It hides ballots from proof consumers, but
//! the process constructing the trace sees them: this is a Tier-1
//! operator/prover-visible shielded receipt, not a Tier-0 no-single-viewer
//! voting service. FHE/MPC can later produce or compose the same public relation
//! without giving one process all plaintext ballots.

use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2, prove_vm_descriptor2_for_config,
    verify_vm_descriptor2, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

/// Exact Lean-emitted descriptor artifact.
pub const PRIVATE_PREFERENCE_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-preference-n4k4.json");

pub const PARTICIPANT_COUNT: usize = 4;
pub const OPTION_COUNT: usize = 4;
pub const MAX_SCORE: u8 = 3;
pub const RULE_ID: u32 = 1_347_571_252;
pub const ROOT_DOMAIN_TAG: u32 = 1_347_569_204;
pub const DIGEST_WIDTH: usize = 8;
pub const PUBLIC_INPUT_COUNT: usize = 11;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";
pub const HIDING_VERIFIER_MANIFEST: &str =
    "private-preference-n4k4-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

const TRACE_WIDTH: usize = 118;
const SESSION: usize = 0;
const RULE: usize = 1;
const ROOT_BASE: usize = 2;
const WINNER: usize = 10;
const BLINDING_BASE: usize = 11;
const PACKED_LOW: usize = 19;
const PACKED_HIGH: usize = 20;
const SCORE_BASE: usize = 21;
const SCORE_STRIDE: usize = 3;
const TOTAL_BASE: usize = 69;
const SELECT_BASE: usize = 73;
const MAX_SCORE_COL: usize = 77;
const MAX_DIFF_BASE: usize = 78;
const MAX_DIFF_BITS_BASE: usize = 82;
const LOW_SLACK_BASE: usize = 98;
const LOW_SLACK_BITS_BASE: usize = 102;
const SCORE_BITS: usize = 2;
const TOTAL_BITS: usize = 4;

#[inline]
const fn score_col(participant: usize, option: usize) -> usize {
    SCORE_BASE + SCORE_STRIDE * (OPTION_COUNT * participant + option)
}

#[inline]
const fn score_bit_col(participant: usize, option: usize, bit: usize) -> usize {
    score_col(participant, option) + 1 + bit
}

#[inline]
const fn max_diff_bit_col(option: usize, bit: usize) -> usize {
    MAX_DIFF_BITS_BASE + TOTAL_BITS * option + bit
}

#[inline]
const fn low_slack_bit_col(option: usize, bit: usize) -> usize {
    LOW_SLACK_BITS_BASE + TOTAL_BITS * option + bit
}

/// One participant's canonical four-option bounded-score ballot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrivateBallot {
    pub scores: [u8; OPTION_COUNT],
}

impl PrivateBallot {
    pub fn try_new(scores: [u8; OPTION_COUNT]) -> Result<Self, String> {
        let ballot = Self { scores };
        ballot.validate()?;
        Ok(ballot)
    }

    fn validate(self) -> Result<(), String> {
        for (option, score) in self.scores.into_iter().enumerate() {
            if score > MAX_SCORE {
                return Err(format!(
                    "score {score} for option {option} is outside fixed two-bit range [0,{MAX_SCORE}]"
                ));
            }
        }
        Ok(())
    }

    #[inline]
    fn packed(self) -> u32 {
        self.scores
            .into_iter()
            .enumerate()
            .map(|(option, score)| (score as u32) * 4u32.pow(option as u32))
            .sum()
    }
}

/// Exactly four private ballots plus a faithful eight-felt commitment blind.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivatePreferenceWitness {
    pub ballots: [PrivateBallot; PARTICIPANT_COUNT],
    /// Canonical BabyBear representatives. Privacy-sensitive callers should use
    /// a fresh CSPRNG or jointly generated distributed blind.
    pub blinding: [u32; DIGEST_WIDTH],
}

impl PrivatePreferenceWitness {
    /// Build from four ballots and caller-owned blinding. The exact participant
    /// count and every score/blind lane fail closed before field reduction.
    pub fn try_from_ballots_with_blinding(
        ballots: &[PrivateBallot],
        blinding: [u32; DIGEST_WIDTH],
    ) -> Result<Self, String> {
        let ballots: [PrivateBallot; PARTICIPANT_COUNT] = ballots.try_into().map_err(|_| {
            format!(
                "private preference family requires exactly N={PARTICIPANT_COUNT} ballots, got {}",
                ballots.len()
            )
        })?;
        for ballot in ballots {
            ballot.validate()?;
        }
        validate_blinding(blinding)?;
        Ok(Self { ballots, blinding })
    }

    /// Build with eight independently rejection-sampled BabyBear elements from
    /// OS entropy. A no-viewer producer should instead supply jointly generated
    /// limbs through [`Self::try_from_ballots_with_blinding`].
    pub fn try_from_ballots_fresh(ballots: &[PrivateBallot]) -> Result<Self, String> {
        Self::try_from_ballots_with_blinding(ballots, fresh_blinding()?)
    }

    fn validate(&self) -> Result<(), String> {
        for ballot in self.ballots {
            ballot.validate()?;
        }
        validate_blinding(self.blinding)
    }
}

fn validate_blinding(blinding: [u32; DIGEST_WIDTH]) -> Result<(), String> {
    for (lane, blind) in blinding.into_iter().enumerate() {
        if blind >= BABYBEAR_P {
            return Err(format!(
                "blinding lane {lane}={blind} is noncanonical for BabyBear modulus {BABYBEAR_P}"
            ));
        }
    }
    Ok(())
}

fn fresh_blinding() -> Result<[u32; DIGEST_WIDTH], String> {
    let modulus = BABYBEAR_P as u64;
    let accept_below = ((u32::MAX as u64 + 1) / modulus) * modulus;
    let mut blinding = [0u32; DIGEST_WIDTH];
    for blind in &mut blinding {
        loop {
            let mut bytes = [0u8; 4];
            getrandom::fill(&mut bytes)
                .map_err(|e| format!("OS randomness failed for preference blinding: {e}"))?;
            let candidate = u32::from_le_bytes(bytes) as u64;
            if candidate < accept_below {
                *blind = (candidate % modulus) as u32;
                break;
            }
        }
    }
    Ok(blinding)
}

/// The only eleven public felts: session, rule, faithful root8, and winner.
/// `winner` maps directly to the option index used by privacy-voting,
/// `PartyFork`, matchmaking, or a quest-choice resolver.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub session: u32,
    pub rule: u32,
    pub ballot_root: [u32; DIGEST_WIDTH],
    pub winner: u32,
}

/// Application-facing result returned only after the hiding proof verifies.
/// This is the clean seam into a party fork, guild vote, matchmaking selector,
/// or quest branch without making those lightweight crates depend on the heavy
/// proving stack.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedDecision {
    pub session: u32,
    pub ballot_root: [u32; DIGEST_WIDTH],
    pub winner: usize,
}

impl PublicStatement {
    pub fn as_felts(self) -> [BabyBear; PUBLIC_INPUT_COUNT] {
        let mut public = [BabyBear::ZERO; PUBLIC_INPUT_COUNT];
        public[0] = BabyBear::new(self.session);
        public[1] = BabyBear::new(self.rule);
        for (lane, root) in self.ballot_root.into_iter().enumerate() {
            public[2 + lane] = BabyBear::new(root);
        }
        public[10] = BabyBear::new(self.winner);
        public
    }

    pub fn as_u32_vec(self) -> Vec<u32> {
        self.as_felts().map(BabyBear::as_u32).to_vec()
    }

    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "private preference expects {PUBLIC_INPUT_COUNT} public inputs, got {}",
                values.len()
            ));
        }
        let statement = Self {
            session: values[0],
            rule: values[1],
            ballot_root: values[2..10].try_into().expect("length checked"),
            winner: values[10],
        };
        statement.validate_shape()?;
        Ok(statement)
    }

    pub fn validate_shape(self) -> Result<(), String> {
        if self.session >= BABYBEAR_P {
            return Err(format!(
                "session {} is noncanonical for BabyBear modulus {BABYBEAR_P}",
                self.session
            ));
        }
        if self.rule != RULE_ID {
            return Err(format!(
                "rule {} is not fixed private-preference rule {RULE_ID}",
                self.rule
            ));
        }
        if self.winner as usize >= OPTION_COUNT {
            return Err(format!(
                "winner {} is outside fixed K={OPTION_COUNT} family",
                self.winner
            ));
        }
        for (lane, root) in self.ballot_root.into_iter().enumerate() {
            if root >= BABYBEAR_P {
                return Err(format!(
                    "ballot-root lane {lane}={root} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        Ok(())
    }
}

/// Binding but explicitly non-hiding compatibility/debug proof.
pub struct PrivatePreferenceNonHidingProof {
    proof: Ir2BatchProof<DreggStarkConfig>,
}

/// Private-ballot proof using `HidingFriPcs` and fresh prover randomness.
pub struct PrivatePreferenceZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl PrivatePreferenceZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private preference proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private preference proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(PRIVATE_PREFERENCE_DESCRIPTOR_JSON)?;
    if desc.name != "private-preference-n4k4::score2-wide-poseidon2-v1"
        || desc.trace_width != TRACE_WIDTH
        || desc.public_input_count != 11
    {
        return Err("private preference emitted descriptor shape drifted".to_string());
    }
    Ok(desc)
}

/// Fingerprint of the exact Lean-emitted AIR bytes.
pub fn air_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-preference-air-v1");
    hasher.update(PRIVATE_PREFERENCE_DESCRIPTOR_JSON.as_bytes());
    *hasher.finalize().as_bytes()
}

/// Stable identity of the privacy-facing HidingFri verifier/config family.
pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-preference-hiding-config-v1");
    hasher.update(HIDING_VERIFIER_MANIFEST.as_bytes());
    hasher.update(PLONKY3_REV.as_bytes());
    for knob in [
        ZK_FRI_LOG_BLOWUP,
        ZK_FRI_LOG_FINAL_POLY_LEN,
        ZK_FRI_MAX_LOG_ARITY,
        ZK_FRI_NUM_QUERIES,
        ZK_FRI_QUERY_POW_BITS,
        ZK_EXT_DEGREE,
    ] {
        hasher.update(&(knob as u64).to_le_bytes());
    }
    hasher.update(&air_fingerprint());
    *hasher.finalize().as_bytes()
}

pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut out = vec![0];
    out.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    out.extend_from_slice(PLONKY3_REV.as_bytes());
    out
}

/// Canonical standalone verifier identity. The custom-cell variant has its own
/// descriptor and therefore a deliberately different VK identity.
pub fn canonical_vk_hash() -> [u8; 32] {
    let verifier_source = hiding_verifier_config_fingerprint();
    let mut verifier = blake3::Hasher::new_derive_key("dregg-verifier-fingerprint-v1");
    verifier.update(&[0]);
    verifier.update(&verifier_source);
    let verifier_canonical = *verifier.finalize().as_bytes();
    let proving_system = proving_system_canonical_bytes();
    let program = PRIVATE_PREFERENCE_DESCRIPTOR_JSON.as_bytes();

    let mut hasher = blake3::Hasher::new_derive_key("dregg-vk-v2");
    hasher.update(&(program.len() as u64).to_le_bytes());
    hasher.update(program);
    hasher.update(&air_fingerprint());
    hasher.update(&verifier_canonical);
    hasher.update(&(proving_system.len() as u64).to_le_bytes());
    hasher.update(&proving_system);
    *hasher.finalize().as_bytes()
}

#[inline]
fn set_bits(row: &mut [BabyBear], value: u32, bits: usize, col: impl Fn(usize) -> usize) {
    for bit in 0..bits {
        row[col(bit)] = BabyBear::new((value >> bit) & 1);
    }
}

fn build_row(
    session: u32,
    witness: &PrivatePreferenceWitness,
) -> Result<(Vec<BabyBear>, PublicStatement), String> {
    witness.validate()?;
    if session >= BABYBEAR_P {
        return Err(format!(
            "session {session} is noncanonical for BabyBear modulus {BABYBEAR_P}"
        ));
    }

    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[SESSION] = BabyBear::new(session);
    row[RULE] = BabyBear::new(RULE_ID);
    for (lane, blind) in witness.blinding.into_iter().enumerate() {
        row[BLINDING_BASE + lane] = BabyBear::new(blind);
    }

    let ballot_packs = witness.ballots.map(PrivateBallot::packed);
    let packed_low = ballot_packs[0] + 256 * ballot_packs[1];
    let packed_high = ballot_packs[2] + 256 * ballot_packs[3];
    debug_assert!(packed_low < (1 << 16));
    debug_assert!(packed_high < (1 << 16));
    row[PACKED_LOW] = BabyBear::new(packed_low);
    row[PACKED_HIGH] = BabyBear::new(packed_high);

    let mut totals = [0u32; OPTION_COUNT];
    for (participant, ballot) in witness.ballots.into_iter().enumerate() {
        for (option, score) in ballot.scores.into_iter().enumerate() {
            let score = score as u32;
            row[score_col(participant, option)] = BabyBear::new(score);
            set_bits(&mut row, score, SCORE_BITS, |bit| {
                score_bit_col(participant, option, bit)
            });
            totals[option] += score;
        }
    }
    for (option, total) in totals.into_iter().enumerate() {
        row[TOTAL_BASE + option] = BabyBear::new(total);
    }

    let mut winner = 0usize;
    for option in 1..OPTION_COUNT {
        if totals[option] > totals[winner] {
            winner = option;
        }
    }
    let max_score = totals[winner];
    row[WINNER] = BabyBear::new(winner as u32);
    row[SELECT_BASE + winner] = BabyBear::ONE;
    row[MAX_SCORE_COL] = BabyBear::new(max_score);

    for (option, total) in totals.into_iter().enumerate() {
        let max_diff = max_score - total;
        let later_selected = u32::from(option < winner);
        let low_slack = max_diff.checked_sub(later_selected).ok_or_else(|| {
            "internal lowest-index tie witness failed: an earlier option ties the selected winner"
                .to_string()
        })?;
        row[MAX_DIFF_BASE + option] = BabyBear::new(max_diff);
        set_bits(&mut row, max_diff, TOTAL_BITS, |bit| {
            max_diff_bit_col(option, bit)
        });
        row[LOW_SLACK_BASE + option] = BabyBear::new(low_slack);
        set_bits(&mut row, low_slack, TOTAL_BITS, |bit| {
            low_slack_bit_col(option, bit)
        });
    }

    // Full arity-16 is load-bearing. The deployed chip's smaller special
    // arities seed/tag lanes differently; this exact 16-lane framing absorbs
    // both score packs and all eight blind limbs.
    let mut root_preimage = Vec::with_capacity(16);
    root_preimage.extend([
        BabyBear::new(ROOT_DOMAIN_TAG),
        row[SESSION],
        row[RULE],
        row[PACKED_LOW],
        row[PACKED_HIGH],
    ]);
    root_preimage.extend(witness.blinding.map(BabyBear::new));
    root_preimage.extend([BabyBear::ZERO; 3]);
    let root = chip_absorb_all_lanes(root_preimage.len(), &root_preimage);
    row[ROOT_BASE..ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&root);

    let statement = PublicStatement {
        session,
        rule: RULE_ID,
        ballot_root: root.map(BabyBear::as_u32),
        winner: winner as u32,
    };
    Ok((row, statement))
}

/// Commit the private ballots and compute the exact winner without proving.
pub fn statement(
    session: u32,
    witness: &PrivatePreferenceWitness,
) -> Result<PublicStatement, String> {
    build_row(session, witness).map(|(_, public)| public)
}

pub(crate) fn trace_and_public(
    session: u32,
    witness: &PrivatePreferenceWitness,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (row, public) = build_row(session, witness)?;
    let desc = descriptor()?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((desc, trace, public))
}

/// Prove through the binding, non-hiding compatibility configuration. The
/// witness is not a PI, but raw FRI openings are not hidden; privacy-sensitive
/// callers must use [`prove_zk`].
pub fn prove_non_hiding(
    session: u32,
    witness: &PrivatePreferenceWitness,
) -> Result<(PrivatePreferenceNonHidingProof, PublicStatement), String> {
    let (desc, trace, public) = trace_and_public(session, witness)?;
    let proof = prove_vm_descriptor2(
        &desc,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
    )?;
    Ok((PrivatePreferenceNonHidingProof { proof }, public))
}

pub fn verify_non_hiding(
    proof: &PrivatePreferenceNonHidingProof,
    public: PublicStatement,
) -> Result<(), String> {
    public.validate_shape()?;
    verify_vm_descriptor2(&descriptor()?, &proof.proof, &public.as_felts())
}

/// Produce a shielded receipt through `DreggZkStarkConfig` and `HidingFriPcs`.
/// Each invocation uses fresh OS-seeded Merkle salts, random trace rows, and
/// random FRI codewords. The trace-building process still sees all ballots.
pub fn prove_zk(
    session: u32,
    witness: &PrivatePreferenceWitness,
) -> Result<(PrivatePreferenceZkProof, PublicStatement), String> {
    let (desc, trace, public) = trace_and_public(session, witness)?;
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    Ok((PrivatePreferenceZkProof { proof }, public))
}

/// CSPRNG-backed convenience entry: exactly four ballots in, hiding proof and
/// winner-only public statement out.
pub fn prove_ballots_zk(
    session: u32,
    ballots: &[PrivateBallot],
) -> Result<(PrivatePreferenceZkProof, PublicStatement), String> {
    let witness = PrivatePreferenceWitness::try_from_ballots_fresh(ballots)?;
    prove_zk(session, &witness)
}

pub fn verify_zk(proof: &PrivatePreferenceZkProof, public: PublicStatement) -> Result<(), String> {
    public.validate_shape()?;
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts(), &config)
}

/// Verify and return the winner-only application decision. Hosts should call
/// this before mapping `winner` to a `PartyFork` path or privacy-voting choice.
pub fn verify_decision_zk(
    proof: &PrivatePreferenceZkProof,
    public: PublicStatement,
) -> Result<VerifiedDecision, String> {
    verify_zk(proof, public)?;
    Ok(VerifiedDecision {
        session: public.session,
        ballot_root: public.ballot_root,
        winner: public.winner as usize,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    fn blind() -> [u32; DIGEST_WIDTH] {
        core::array::from_fn(|lane| 900 + lane as u32)
    }

    fn ballots() -> [PrivateBallot; PARTICIPANT_COUNT] {
        [
            PrivateBallot::try_new([3, 2, 0, 1]).expect("ballot 0"),
            PrivateBallot::try_new([2, 3, 0, 1]).expect("ballot 1"),
            PrivateBallot::try_new([0, 3, 2, 1]).expect("ballot 2"),
            PrivateBallot::try_new([1, 2, 3, 0]).expect("ballot 3"),
        ]
    }

    fn fixture() -> PrivatePreferenceWitness {
        PrivatePreferenceWitness::try_from_ballots_with_blinding(&ballots(), blind())
            .expect("fixed preference witness")
    }

    #[test]
    fn private_preference_shape_and_public_surface_fail_closed() {
        assert!(PrivateBallot::try_new([0, 1, 2, 4]).is_err());
        assert!(
            PrivatePreferenceWitness::try_from_ballots_with_blinding(&ballots()[..3], blind())
                .is_err()
        );
        let mut noncanonical = blind();
        noncanonical[4] = BABYBEAR_P;
        assert!(
            PrivatePreferenceWitness::try_from_ballots_with_blinding(&ballots(), noncanonical)
                .is_err()
        );
        assert!(statement(BABYBEAR_P, &fixture()).is_err());

        let fresh_a =
            PrivatePreferenceWitness::try_from_ballots_fresh(&ballots()).expect("OS-seeded blind");
        let fresh_b = PrivatePreferenceWitness::try_from_ballots_fresh(&ballots())
            .expect("second OS-seeded blind");
        assert_ne!(fresh_a.blinding, fresh_b.blinding);
        assert_ne!(
            statement(77, &fresh_a)
                .expect("fresh statement")
                .ballot_root,
            statement(77, &fresh_b)
                .expect("second statement")
                .ballot_root
        );

        let desc = descriptor().expect("emitted descriptor decodes");
        assert_eq!(desc.public_input_count, 11);
        assert_eq!(desc.trace_width, TRACE_WIDTH);
        let mut pins = desc
            .constraints
            .iter()
            .filter_map(|constraint| match constraint {
                VmConstraint2::Base(VmConstraint::PiBinding { row, col, pi_index }) => {
                    Some((*row, *col, *pi_index))
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        pins.sort_by_key(|(_, _, pi)| *pi);
        let mut expected = vec![(VmRow::First, SESSION, 0), (VmRow::First, RULE, 1)];
        expected.extend((0..DIGEST_WIDTH).map(|lane| (VmRow::First, ROOT_BASE + lane, 2 + lane)));
        expected.push((VmRow::First, WINNER, 10));
        assert_eq!(pins, expected);
    }

    #[test]
    fn private_preference_statement_is_exact_lowest_argmax_and_bound() {
        let witness = fixture();
        let public = statement(77, &witness).expect("statement");
        assert_eq!(public.winner, 1);
        assert_eq!(public.rule, RULE_ID);

        let tie_ballot = PrivateBallot::try_new([2, 2, 0, 0]).expect("tie ballot");
        let tie = PrivatePreferenceWitness::try_from_ballots_with_blinding(
            &[tie_ballot; PARTICIPANT_COUNT],
            blind(),
        )
        .expect("tie witness");
        assert_eq!(
            statement(77, &tie).expect("tie statement").winner,
            0,
            "equal maxima must select the lowest option index"
        );

        let mut changed = witness.clone();
        changed.ballots[0].scores[0] = 2;
        let changed_public = statement(77, &changed).expect("changed statement");
        assert_eq!(changed_public.winner, public.winner);
        assert_ne!(changed_public.ballot_root, public.ballot_root);
        assert_ne!(
            statement(78, &witness).expect("new session").ballot_root,
            public.ballot_root
        );
        let mut reblinded = witness.clone();
        reblinded.blinding[7] += 1;
        assert_ne!(
            statement(77, &reblinded).expect("new blind").ballot_root,
            public.ballot_root,
            "all eight blinding lanes must enter the wide commitment"
        );
    }

    #[test]
    fn private_preference_hiding_randomizes_and_public_tampers_refuse() {
        let (proof, public) = prove_zk(77, &fixture()).expect("honest ballots prove hiding");
        verify_zk(&proof, public).expect("honest hiding proof verifies");
        assert_eq!(
            verify_decision_zk(&proof, public)
                .expect("verified application decision")
                .winner,
            1
        );
        assert!(proof.proof.commitments.random.is_some());
        assert!(
            proof
                .proof
                .opened_values
                .instances
                .iter()
                .all(|instance| instance.base_opened_values.random.is_some())
        );

        let (rerun, rerun_public) = prove_zk(77, &fixture()).expect("second hiding proof");
        assert_eq!(rerun_public, public);
        assert_ne!(
            format!("{:?}", proof.proof.commitments.random),
            format!("{:?}", rerun.proof.commitments.random)
        );
        verify_zk(&rerun, rerun_public).expect("second hiding proof verifies");

        let mut changed = fixture();
        changed.ballots[0].scores[0] = 2;
        let (changed_proof, changed_public) =
            prove_zk(77, &changed).expect("changed private ballots prove");
        verify_zk(&changed_proof, changed_public).expect("changed proof verifies at its own root");
        assert_eq!(changed_public.winner, public.winner);
        assert_ne!(changed_public.ballot_root, public.ballot_root);
        assert!(verify_zk(&changed_proof, public).is_err());

        let mut forged_root = public;
        forged_root.ballot_root[0] = (forged_root.ballot_root[0] + 1) % BABYBEAR_P;
        assert!(verify_zk(&proof, forged_root).is_err());

        let mut forged_winner = public;
        forged_winner.winner = 0;
        assert!(verify_zk(&proof, forged_winner).is_err());
    }
}
