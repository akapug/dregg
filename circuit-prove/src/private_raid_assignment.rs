//! Fixed `N=4` private raid/matchmaking role assignment.
//!
//! The relation and AIR are authored in Lean at
//! `Dregg2/Games/PrivateRaidAssignmentDescriptor.lean`. Rust only validates
//! inputs, fills the emitted layout, and drives the HidingFri prover/verifier.
//! Four participants privately provide one suitability score in `0..=3` and
//! one independent admissibility bit for each of four roles. `score == 0` is
//! deliberately not treated as forbidden.
//!
//! The public statement is exactly `(session, rule, input_root8, roles[4])`.
//! The role vector is a permutation, is admissible, globally maximizes total
//! suitability over all 24 permutations, and is lexicographically lowest on
//! ties. Scores, admissibility bits, blinds, and the aggregate score remain
//! private from the verifier.
//!
//! This is honest Tier-1 producer visibility: the process constructing the
//! trace sees the private matrix. [`prove_zk`] hides it from proof consumers;
//! MPC input assembly or distributed matching is a separate protocol layer.

use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

/// Exact artifact emitted by the Lean author.
pub const PRIVATE_RAID_ASSIGNMENT_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-raid-assignment-n4.json");

pub const SEAT_COUNT: usize = 4;
pub const ROLE_COUNT: usize = 4;
pub const DIGEST_WIDTH: usize = 8;
pub const CANDIDATE_COUNT: usize = 24;
pub const PUBLIC_INPUT_COUNT: usize = 14;
pub const RULE_ID: u32 = 1_380_007_220;
pub const ROOT_DOMAIN_TAG: u32 = 1_380_006_196;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";
pub const HIDING_VERIFIER_MANIFEST: &str =
    "private-raid-assignment-n4-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

const TRACE_WIDTH: usize = 299;
const SESSION: usize = 0;
const RULE: usize = 1;
const ROOT_BASE: usize = 2;
const SCORE_BASE: usize = 10;
const SCORE_BIT_BASE: usize = 26;
const ADMISSIBLE_BASE: usize = 58;
const ASSIGNED_BASE: usize = 74;
const SELECT_BASE: usize = 78;
const TOTAL: usize = 94;
const TOTAL_BIT_BASE: usize = 95;
const BLIND_BASE: usize = 99;
const CANDIDATE_CHOSEN_BASE: usize = 107;
const CANDIDATE_ALLOWED_BASE: usize = 131;
const DIFF_BASE: usize = 155;
const DIFF_BIT_BASE: usize = 179;
const DIFF_NONZERO_BASE: usize = 275;

/// All four-role permutations in lexicographic order. This order is part of
/// the Lean-authored deterministic tie-break certificate.
const CANDIDATES: [[u8; ROLE_COUNT]; CANDIDATE_COUNT] = [
    [0, 1, 2, 3],
    [0, 1, 3, 2],
    [0, 2, 1, 3],
    [0, 2, 3, 1],
    [0, 3, 1, 2],
    [0, 3, 2, 1],
    [1, 0, 2, 3],
    [1, 0, 3, 2],
    [1, 2, 0, 3],
    [1, 2, 3, 0],
    [1, 3, 0, 2],
    [1, 3, 2, 0],
    [2, 0, 1, 3],
    [2, 0, 3, 1],
    [2, 1, 0, 3],
    [2, 1, 3, 0],
    [2, 3, 0, 1],
    [2, 3, 1, 0],
    [3, 0, 1, 2],
    [3, 0, 2, 1],
    [3, 1, 0, 2],
    [3, 1, 2, 0],
    [3, 2, 0, 1],
    [3, 2, 1, 0],
];

#[inline]
const fn score_col(seat: usize, role: usize) -> usize {
    SCORE_BASE + ROLE_COUNT * seat + role
}

#[inline]
const fn score_bit_col(seat: usize, role: usize, bit: usize) -> usize {
    SCORE_BIT_BASE + 2 * (ROLE_COUNT * seat + role) + bit
}

#[inline]
const fn admissible_col(seat: usize, role: usize) -> usize {
    ADMISSIBLE_BASE + ROLE_COUNT * seat + role
}

#[inline]
const fn select_col(seat: usize, role: usize) -> usize {
    SELECT_BASE + ROLE_COUNT * seat + role
}

#[inline]
const fn diff_bit_col(candidate: usize, bit: usize) -> usize {
    DIFF_BIT_BASE + 4 * candidate + bit
}

/// Private suitability/admissibility matrix and faithful root blinding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateRaidWitness {
    pub scores: [[u8; ROLE_COUNT]; SEAT_COUNT],
    pub admissible: [[bool; ROLE_COUNT]; SEAT_COUNT],
    pub blinding: [u32; DIGEST_WIDTH],
}

impl PrivateRaidWitness {
    /// Construct with caller-owned blinds. Suitable for deterministic fixtures
    /// and distributed blind assembly.
    pub fn try_new(
        scores: [[u8; ROLE_COUNT]; SEAT_COUNT],
        admissible: [[bool; ROLE_COUNT]; SEAT_COUNT],
        blinding: [u32; DIGEST_WIDTH],
    ) -> Result<Self, String> {
        let witness = Self {
            scores,
            admissible,
            blinding,
        };
        witness.validate()?;
        Ok(witness)
    }

    /// Construct with eight rejection-sampled BabyBear blind felts from OS
    /// entropy. This does not hide inputs from the Tier-1 trace producer.
    pub fn try_new_fresh(
        scores: [[u8; ROLE_COUNT]; SEAT_COUNT],
        admissible: [[bool; ROLE_COUNT]; SEAT_COUNT],
    ) -> Result<Self, String> {
        let mut blinding = [0u32; DIGEST_WIDTH];
        for lane in &mut blinding {
            *lane = fresh_field_element()?;
        }
        Self::try_new(scores, admissible, blinding)
    }

    fn validate(&self) -> Result<(), String> {
        for seat in 0..SEAT_COUNT {
            for role in 0..ROLE_COUNT {
                let score = self.scores[seat][role];
                if score > 3 {
                    return Err(format!(
                        "seat {seat} role {role} score {score} is outside bounded range 0..=3"
                    ));
                }
            }
        }
        for (lane, &value) in self.blinding.iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "blinding lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        if !CANDIDATES
            .iter()
            .any(|roles| assignment_admissible(self, roles))
        {
            return Err("no admissible one-seat/one-role assignment exists".to_string());
        }
        Ok(())
    }
}

fn fresh_field_element() -> Result<u32, String> {
    let modulus = BABYBEAR_P as u64;
    let accept_below = ((u32::MAX as u64 + 1) / modulus) * modulus;
    loop {
        let mut bytes = [0u8; 4];
        getrandom::fill(&mut bytes)
            .map_err(|e| format!("OS randomness failed for raid-assignment blinding: {e}"))?;
        let candidate = u32::from_le_bytes(bytes) as u64;
        if candidate < accept_below {
            return Ok((candidate % modulus) as u32);
        }
    }
}

/// The only public values. Private total suitability is intentionally absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub session: u32,
    pub rule: u32,
    pub input_root: [u32; DIGEST_WIDTH],
    pub roles: [u8; SEAT_COUNT],
}

impl PublicStatement {
    pub fn as_u32_vec(self) -> Vec<u32> {
        let mut public = Vec::with_capacity(PUBLIC_INPUT_COUNT);
        public.extend([self.session, self.rule]);
        public.extend(self.input_root);
        public.extend(self.roles.map(u32::from));
        public
    }

    fn as_felts(self) -> [BabyBear; 14] {
        let mut public = [BabyBear::ZERO; 14];
        public[0] = BabyBear::new(self.session);
        public[1] = BabyBear::new(self.rule);
        for (lane, value) in self.input_root.into_iter().enumerate() {
            public[2 + lane] = BabyBear::new(value);
        }
        for (seat, role) in self.roles.into_iter().enumerate() {
            public[10 + seat] = BabyBear::new(role as u32);
        }
        public
    }

    pub fn validate(self) -> Result<(), String> {
        if self.session >= BABYBEAR_P {
            return Err(format!(
                "session {} is noncanonical for BabyBear modulus {BABYBEAR_P}",
                self.session
            ));
        }
        if self.rule != RULE_ID {
            return Err(format!(
                "rule {} is not fixed private-raid rule {RULE_ID}",
                self.rule
            ));
        }
        for (lane, value) in self.input_root.into_iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "input-root lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        validate_role_permutation(&self.roles)
    }

    /// Decode the descriptor's exact public ABI and reject noncanonical field
    /// or role representatives before any proof work.
    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "private raid assignment expects {PUBLIC_INPUT_COUNT} public inputs, got {}",
                values.len()
            ));
        }
        let mut roles = [0u8; SEAT_COUNT];
        for (seat, &role) in values[10..14].iter().enumerate() {
            roles[seat] = u8::try_from(role).map_err(|_| {
                format!("seat {seat} carries noncanonical u8 role representative {role}")
            })?;
        }
        let public = Self {
            session: values[0],
            rule: values[1],
            input_root: values[2..10].try_into().expect("length checked"),
            roles,
        };
        public.validate()?;
        Ok(public)
    }
}

/// Hiding proof of the fixed-four globally-optimal assignment relation.
pub struct PrivateRaidZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl PrivateRaidZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private raid assignment proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private raid assignment proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

/// Compact application seam obtainable only from successful verification.
/// It deliberately contains no aggregate score or private admissibility data.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifiedAssignment {
    public: PublicStatement,
}

impl VerifiedAssignment {
    pub fn session(self) -> u32 {
        self.public.session
    }

    pub fn rule(self) -> u32 {
        self.public.rule
    }

    pub fn input_root(self) -> [u32; DIGEST_WIDTH] {
        self.public.input_root
    }

    pub fn roles(self) -> [u8; SEAT_COUNT] {
        self.public.roles
    }

    pub fn public_statement(self) -> PublicStatement {
        self.public
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(PRIVATE_RAID_ASSIGNMENT_DESCRIPTOR_JSON)?;
    if desc.name != "private-raid-assignment-n4::admissible-max-lex-v1"
        || desc.trace_width != TRACE_WIDTH
        || desc.public_input_count != 14
    {
        return Err("private raid assignment emitted descriptor shape drifted".to_string());
    }
    Ok(desc)
}

/// Fingerprint of the exact Lean-emitted AIR artifact.
pub fn air_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-raid-assignment-air-v1");
    hasher.update(PRIVATE_RAID_ASSIGNMENT_DESCRIPTOR_JSON.as_bytes());
    *hasher.finalize().as_bytes()
}

/// Stable identity of the privacy-facing verifier/config family.
pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut hasher =
        blake3::Hasher::new_derive_key("dregg-private-raid-assignment-hiding-config-v1");
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

/// Canonical verifier identity over descriptor bytes, AIR fingerprint, hiding
/// config, and pinned proving system. This identifies the standalone receipt
/// verifier; it is not an `Effect::Custom` state-binding claim.
pub fn canonical_vk_hash() -> [u8; 32] {
    let verifier_source = hiding_verifier_config_fingerprint();
    let mut verifier = blake3::Hasher::new_derive_key("dregg-verifier-fingerprint-v1");
    verifier.update(&[0]);
    verifier.update(&verifier_source);
    let verifier_canonical = *verifier.finalize().as_bytes();
    let proving_system = proving_system_canonical_bytes();
    let program = PRIVATE_RAID_ASSIGNMENT_DESCRIPTOR_JSON.as_bytes();

    let mut hasher = blake3::Hasher::new_derive_key("dregg-vk-v2");
    hasher.update(&(program.len() as u64).to_le_bytes());
    hasher.update(program);
    hasher.update(&air_fingerprint());
    hasher.update(&verifier_canonical);
    hasher.update(&(proving_system.len() as u64).to_le_bytes());
    hasher.update(&proving_system);
    *hasher.finalize().as_bytes()
}

fn validate_role_permutation(roles: &[u8; SEAT_COUNT]) -> Result<(), String> {
    let mut seen = [false; ROLE_COUNT];
    for (seat, &role) in roles.iter().enumerate() {
        let role = role as usize;
        if role >= ROLE_COUNT {
            return Err(format!(
                "seat {seat} carries role {role}, outside canonical range 0..3"
            ));
        }
        if std::mem::replace(&mut seen[role], true) {
            return Err(format!(
                "role {role} appears more than once; assignment must be a permutation"
            ));
        }
    }
    Ok(())
}

fn assignment_admissible(witness: &PrivateRaidWitness, roles: &[u8; SEAT_COUNT]) -> bool {
    (0..SEAT_COUNT).all(|seat| witness.admissible[seat][roles[seat] as usize])
}

fn assignment_score(witness: &PrivateRaidWitness, roles: &[u8; SEAT_COUNT]) -> u8 {
    (0..SEAT_COUNT)
        .map(|seat| witness.scores[seat][roles[seat] as usize])
        .sum()
}

fn best_assignment(witness: &PrivateRaidWitness) -> Result<([u8; SEAT_COUNT], u8), String> {
    witness.validate()?;
    let mut best: Option<([u8; SEAT_COUNT], u8)> = None;
    for roles in CANDIDATES {
        if !assignment_admissible(witness, &roles) {
            continue;
        }
        let score = assignment_score(witness, &roles);
        if best.is_none_or(|(_, best_score)| score > best_score) {
            best = Some((roles, score));
        }
    }
    best.ok_or_else(|| "no admissible one-seat/one-role assignment exists".to_string())
}

fn participant_pack(witness: &PrivateRaidWitness, seat: usize) -> u32 {
    let score = witness.scores[seat];
    let admissible = witness.admissible[seat];
    score[0] as u32
        + 4 * score[1] as u32
        + 16 * score[2] as u32
        + 64 * score[3] as u32
        + 256 * admissible[0] as u32
        + 512 * admissible[1] as u32
        + 1024 * admissible[2] as u32
        + 2048 * admissible[3] as u32
}

fn root_digest(session: u32, witness: &PrivateRaidWitness) -> [BabyBear; DIGEST_WIDTH] {
    let packed_low = participant_pack(witness, 0) + 4096 * participant_pack(witness, 1);
    let packed_high = participant_pack(witness, 2) + 4096 * participant_pack(witness, 3);
    let mut preimage = Vec::with_capacity(16);
    preimage.extend([
        BabyBear::new(ROOT_DOMAIN_TAG),
        BabyBear::new(session),
        BabyBear::new(RULE_ID),
        BabyBear::new(packed_low),
        BabyBear::new(packed_high),
    ]);
    preimage.extend(witness.blinding.map(BabyBear::new));
    preimage.extend([BabyBear::ZERO; 3]);
    debug_assert_eq!(preimage.len(), 16);
    chip_absorb_all_lanes(preimage.len(), &preimage)
}

fn fill_bits(row: &mut [BabyBear], value: u8, base: usize, count: usize) {
    for bit in 0..count {
        row[base + bit] = BabyBear::new(((value >> bit) & 1) as u32);
    }
}

fn build_row_for_assignment(
    session: u32,
    witness: &PrivateRaidWitness,
    roles: [u8; SEAT_COUNT],
) -> Result<(Vec<BabyBear>, PublicStatement), String> {
    witness.validate()?;
    if session >= BABYBEAR_P {
        return Err(format!(
            "session {session} is noncanonical for BabyBear modulus {BABYBEAR_P}"
        ));
    }
    validate_role_permutation(&roles)?;

    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[SESSION] = BabyBear::new(session);
    row[RULE] = BabyBear::new(RULE_ID);
    for seat in 0..SEAT_COUNT {
        for role in 0..ROLE_COUNT {
            let score = witness.scores[seat][role];
            row[score_col(seat, role)] = BabyBear::new(score as u32);
            fill_bits(&mut row, score, score_bit_col(seat, role, 0), 2);
            row[admissible_col(seat, role)] = BabyBear::new(witness.admissible[seat][role] as u32);
        }
        let role = roles[seat] as usize;
        row[ASSIGNED_BASE + seat] = BabyBear::new(role as u32);
        row[select_col(seat, role)] = BabyBear::ONE;
    }

    let chosen_total = assignment_score(witness, &roles);
    row[TOTAL] = BabyBear::new(chosen_total as u32);
    fill_bits(&mut row, chosen_total, TOTAL_BIT_BASE, 4);
    for (lane, &blind) in witness.blinding.iter().enumerate() {
        row[BLIND_BASE + lane] = BabyBear::new(blind);
    }

    for (candidate, candidate_roles) in CANDIDATES.iter().enumerate() {
        let chosen = (*candidate_roles == roles) as u32;
        let allowed = assignment_admissible(witness, candidate_roles);
        let candidate_total = assignment_score(witness, candidate_roles);
        let diff = if allowed && chosen_total >= candidate_total {
            chosen_total - candidate_total
        } else {
            0
        };
        row[CANDIDATE_CHOSEN_BASE + candidate] = BabyBear::new(chosen);
        row[CANDIDATE_ALLOWED_BASE + candidate] = BabyBear::new(allowed as u32);
        row[DIFF_BASE + candidate] = BabyBear::new(diff as u32);
        fill_bits(&mut row, diff, diff_bit_col(candidate, 0), 4);
        row[DIFF_NONZERO_BASE + candidate] = BabyBear::new((diff != 0) as u32);
    }

    let root = root_digest(session, witness);
    row[ROOT_BASE..ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&root);
    let public = PublicStatement {
        session,
        rule: RULE_ID,
        input_root: root.map(BabyBear::as_u32),
        roles,
    };
    Ok((row, public))
}

fn trace_and_public(
    session: u32,
    witness: &PrivateRaidWitness,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (roles, _) = best_assignment(witness)?;
    let (row, public) = build_row_for_assignment(session, witness, roles)?;
    let desc = descriptor()?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((desc, trace, public))
}

/// Compute the globally optimal, deterministic public assignment without
/// proving. The private aggregate score is not returned.
pub fn statement(session: u32, witness: &PrivateRaidWitness) -> Result<PublicStatement, String> {
    let (_, _, public) = trace_and_public(session, witness)?;
    Ok(public)
}

/// Produce the only proof API, using `HidingFriPcs` with fresh prover
/// randomness. The Tier-1 trace builder still sees the private inputs.
pub fn prove_zk(
    session: u32,
    witness: &PrivateRaidWitness,
) -> Result<(PrivateRaidZkProof, PublicStatement), String> {
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
    Ok((PrivateRaidZkProof { proof }, public))
}

/// Verify and mint the compact application seam. `VerifiedAssignment` cannot
/// be constructed through this module without a valid proof for the same
/// public statement.
pub fn verify_zk(
    proof: &PrivateRaidZkProof,
    public: PublicStatement,
) -> Result<VerifiedAssignment, String> {
    public.validate()?;
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts(), &config)?;
    Ok(VerifiedAssignment { public })
}

/// Verify the stable transport form without exposing the concrete proof layout.
pub fn verify_postcard(
    proof_bytes: &[u8],
    public_values: &[u32],
) -> Result<VerifiedAssignment, String> {
    let proof = PrivateRaidZkProof::from_postcard(proof_bytes)?;
    verify_zk(&proof, PublicStatement::try_from_u32s(public_values)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};

    fn blinds() -> [u32; DIGEST_WIDTH] {
        core::array::from_fn(|lane| 10_000 + lane as u32)
    }

    fn optimizer_fixture() -> PrivateRaidWitness {
        // The tempting diagonal role for seat 0 is forbidden despite score 3.
        // Global optimum is [1,0,2,3] with score 11.
        PrivateRaidWitness::try_new(
            [[3, 2, 0, 0], [3, 0, 1, 0], [0, 0, 3, 1], [0, 1, 0, 3]],
            [
                [false, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
                [true, true, true, true],
            ],
            blinds(),
        )
        .expect("admissible fixture")
    }

    fn all_allowed_equal_fixture() -> PrivateRaidWitness {
        PrivateRaidWitness::try_new(
            [[1; ROLE_COUNT]; SEAT_COUNT],
            [[true; ROLE_COUNT]; SEAT_COUNT],
            blinds(),
        )
        .expect("all assignments feasible")
    }

    fn prove_refuses(row: Vec<BabyBear>, public: PublicStatement) {
        let trace = vec![row.clone(), row.clone(), row.clone(), row];
        let refusal = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(
                &descriptor().expect("descriptor"),
                &trace,
                &public.as_felts(),
                &MemBoundaryWitness::default(),
                &[],
            )
        }));
        assert!(
            refusal.is_err() || refusal.expect("non-panicking prover").is_err(),
            "malformed assignment witness must be refused"
        );
    }

    #[test]
    fn shape_admissibility_and_score_zero_are_distinct() {
        let mut bad_score = optimizer_fixture();
        bad_score.scores[2][2] = 4;
        assert!(bad_score.validate().is_err());

        let mut bad_blind = optimizer_fixture();
        bad_blind.blinding[4] = BABYBEAR_P;
        assert!(bad_blind.validate().is_err());

        let impossible = PrivateRaidWitness {
            scores: [[3; ROLE_COUNT]; SEAT_COUNT],
            admissible: [[false; ROLE_COUNT]; SEAT_COUNT],
            blinding: blinds(),
        };
        assert!(impossible.validate().is_err());

        let zero_but_allowed = PrivateRaidWitness::try_new(
            [[0; ROLE_COUNT]; SEAT_COUNT],
            [[true; ROLE_COUNT]; SEAT_COUNT],
            blinds(),
        )
        .expect("zero suitability is still admissible");
        assert_eq!(
            statement(7, &zero_but_allowed)
                .expect("lex assignment")
                .roles,
            [0, 1, 2, 3]
        );
    }

    #[test]
    fn optimizer_is_global_admissible_and_lex_deterministic() {
        let public = statement(77, &optimizer_fixture()).expect("optimized statement");
        assert_eq!(public.roles, [1, 0, 2, 3]);

        let tied = statement(77, &all_allowed_equal_fixture()).expect("tied statement");
        assert_eq!(tied.roles, [0, 1, 2, 3]);
    }

    #[test]
    fn root_binds_every_private_input_family() {
        let fixture = optimizer_fixture();
        let root = statement(77, &fixture).expect("statement").input_root;

        let mut score_change = fixture.clone();
        score_change.scores[3][0] ^= 1;
        assert_ne!(
            statement(77, &score_change)
                .expect("score change")
                .input_root,
            root
        );

        let mut admissibility_change = fixture.clone();
        admissibility_change.admissible[3][0] = false;
        assert_ne!(
            statement(77, &admissibility_change)
                .expect("admissibility change")
                .input_root,
            root
        );

        let mut blind_change = fixture.clone();
        blind_change.blinding[7] += 1;
        assert_ne!(
            statement(77, &blind_change)
                .expect("blind change")
                .input_root,
            root
        );
    }

    #[test]
    fn emitted_air_refuses_suboptimal_assignment_with_consistent_public_root() {
        let fixture = optimizer_fixture();
        let (row, public) = build_row_for_assignment(77, &fixture, [1, 2, 0, 3])
            .expect("well-shaped admissible but suboptimal assignment row");
        prove_refuses(row, public);
    }

    #[test]
    fn emitted_air_refuses_lex_later_equal_score_assignment() {
        let fixture = all_allowed_equal_fixture();
        let (row, public) = build_row_for_assignment(77, &fixture, [0, 1, 3, 2])
            .expect("well-shaped tied but lex-later row");
        prove_refuses(row, public);
    }

    #[test]
    fn hiding_proof_mints_verified_assignment_and_public_tampers_refuse() {
        let (proof, public) = prove_zk(77, &optimizer_fixture()).expect("hiding assignment proof");
        let verified = verify_zk(&proof, public).expect("honest proof verifies");
        assert_eq!(verified.session(), 77);
        assert_eq!(verified.rule(), RULE_ID);
        assert_eq!(verified.input_root(), public.input_root);
        assert_eq!(verified.roles(), [1, 0, 2, 3]);
        assert_eq!(verified.public_statement(), public);

        let mut root_tamper = public;
        root_tamper.input_root[6] = (root_tamper.input_root[6] + 1) % BABYBEAR_P;
        assert!(verify_zk(&proof, root_tamper).is_err());

        let mut session_tamper = public;
        session_tamper.session += 1;
        assert!(verify_zk(&proof, session_tamper).is_err());

        let mut roles_tamper = public;
        roles_tamper.roles.swap(0, 1);
        assert!(verify_zk(&proof, roles_tamper).is_err());

        let mut duplicate_role = public;
        duplicate_role.roles[1] = duplicate_role.roles[0];
        assert!(verify_zk(&proof, duplicate_role).is_err());

        let mut rule_tamper = public;
        rule_tamper.rule ^= 1;
        assert!(verify_zk(&proof, rule_tamper).is_err());

        let proof_bytes = proof.to_postcard().expect("proof transport");
        let public_values = public.as_u32_vec();
        assert_eq!(
            PublicStatement::try_from_u32s(&public_values).unwrap(),
            public
        );
        assert_eq!(
            verify_postcard(&proof_bytes, &public_values)
                .expect("transport proof verifies")
                .roles(),
            public.roles
        );

        let mut corrupt_proof = proof_bytes;
        let at = corrupt_proof.len() / 2;
        corrupt_proof[at] ^= 1;
        assert!(verify_postcard(&corrupt_proof, &public_values).is_err());
    }

    #[test]
    fn public_abi_and_canonical_hiding_verifier_identity_are_stable() {
        let public = statement(77, &optimizer_fixture()).unwrap();
        assert_eq!(public.as_u32_vec().len(), PUBLIC_INPUT_COUNT);
        assert!(PublicStatement::try_from_u32s(&public.as_u32_vec()[..13]).is_err());

        let mut noncanonical_role = public.as_u32_vec();
        noncanonical_role[10] = u8::MAX as u32 + 1;
        assert!(PublicStatement::try_from_u32s(&noncanonical_role).is_err());

        assert_ne!(air_fingerprint(), hiding_verifier_config_fingerprint());
        assert_ne!(canonical_vk_hash(), [0u8; 32]);
        assert_eq!(canonical_vk_hash(), canonical_vk_hash());
    }
}
