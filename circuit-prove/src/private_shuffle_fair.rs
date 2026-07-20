//! Fixed-eight joint-entropy fairness layer for the private shuffle.
//!
//! The relation is authored in Lean at
//! `Dregg2/Games/PrivateShuffleFairDescriptor.lean`. Eight private 16-bit
//! participant contributions are committed under a faithful `root8`, then
//! added in `ZMod 2^16`. Values below `8! = 40320` are accepted directly as
//! permutation ranks; larger values produce a proved rejected attempt. There
//! is no `% 40320` bias.
//!
//! The accepted rank is decoded through the same recursive
//! `Perm.decomposeFin` mixed-radix equivalence proved bijective in Lean. The
//! resulting deal uses the existing private-shuffle `SHF8` leaf framing, so
//! existing selective openings can consume the accepted `deal_root8`.
//!
//! This is a Tier-1 hiding proof: proof consumers do not see contributions or
//! cards, while the process constructing the trace does. Commit-before-reveal,
//! at least one conditionally uniform contribution, and mandatory recording of
//! rejected/aborted attempts are temporal protocol premises, not consequences
//! of this static AIR.

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

pub const PRIVATE_SHUFFLE_FAIR_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-shuffle-fair-n8.json");

pub const PARTICIPANT_COUNT: usize = 8;
pub const SEAT_COUNT: usize = 8;
pub const CARD_COUNT: usize = 8;
pub const DIGEST_WIDTH: usize = 8;
pub const PUBLIC_INPUT_COUNT: usize = 20;
pub const ENTROPY_SPACE: u32 = 65_536;
pub const PERMUTATION_COUNT: u32 = 40_320;
pub const RULE_ID: u32 = 1_246_122_552;
pub const COMMIT_DOMAIN_TAG: u32 = 1_246_051_896;
pub const SHUFFLE_RULE_ID: u32 = 1_346_720_312;
pub const SHUFFLE_LEAF_DOMAIN_TAG: u32 = 1_397_245_496;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";
pub const HIDING_VERIFIER_MANIFEST: &str =
    "private-shuffle-fair-n8-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

const TRACE_WIDTH: usize = 823;
const SESSION: usize = 0;
const RULE: usize = 1;
const ATTEMPT: usize = 2;
const COMMIT_ROOT_BASE: usize = 3;
const ACCEPTED: usize = 11;
const DEAL_ROOT_PUBLIC_BASE: usize = 12;
const SEED_BASE: usize = 20;
const SEED_BIT_BASE: usize = 28;
const CARRY: usize = 156;
const CARRY_BIT_BASE: usize = 157;
const ENTROPY_COL: usize = 160;
const ENTROPY_BIT_BASE: usize = 161;
const LOW_SLACK: usize = 177;
const LOW_SLACK_BIT_BASE: usize = 178;
const HIGH_SLACK: usize = 194;
const HIGH_SLACK_BIT_BASE: usize = 195;
const RANK: usize = 211;
const REMAINDER_BASE: usize = 212;
const DIGIT_BASE: usize = 218;
const DIGIT_SELECTOR_BASE: usize = 225;
const PERM_SELECTOR_BASE: usize = 260;
const COMMIT_BLIND_BASE: usize = 463;
const COMMIT_LEAF_BASE: usize = 527;
const COMMIT_LEVEL1_BASE: usize = 591;
const COMMIT_LEVEL2_BASE: usize = 623;
const DEAL_BLIND_BASE: usize = 639;
const DEAL_LEAF_BASE: usize = 703;
const DEAL_LEVEL1_BASE: usize = 767;
const DEAL_LEVEL2_BASE: usize = 799;
const DEAL_CALC_ROOT_BASE: usize = 815;

const FACTORIALS: [u32; 9] = [1, 1, 2, 6, 24, 120, 720, 5_040, 40_320];

#[inline]
const fn seed_bit_col(participant: usize, bit: usize) -> usize {
    SEED_BIT_BASE + 16 * participant + bit
}

#[inline]
const fn digit_selector_offset(stage: usize) -> usize {
    match stage {
        0 => 0,
        1 => 8,
        2 => 15,
        3 => 21,
        4 => 26,
        5 => 30,
        _ => 33,
    }
}

#[inline]
const fn digit_selector_col(stage: usize, value: usize) -> usize {
    DIGIT_SELECTOR_BASE + digit_selector_offset(stage) + value
}

#[inline]
const fn rank_stage_col(stage: usize) -> usize {
    if stage == 0 {
        RANK
    } else {
        REMAINDER_BASE + stage - 1
    }
}

#[inline]
const fn perm_selector_offset(size: usize) -> usize {
    match size {
        2 => 0,
        3 => 4,
        4 => 13,
        5 => 29,
        6 => 54,
        7 => 90,
        _ => 139,
    }
}

#[inline]
const fn perm_selector_col(size: usize, pos: usize, card: usize) -> usize {
    PERM_SELECTOR_BASE + perm_selector_offset(size) + size * pos + card
}

#[inline]
const fn commit_blind_col(participant: usize, lane: usize) -> usize {
    COMMIT_BLIND_BASE + DIGEST_WIDTH * participant + lane
}

#[inline]
const fn commit_leaf_col(participant: usize, lane: usize) -> usize {
    COMMIT_LEAF_BASE + DIGEST_WIDTH * participant + lane
}

#[inline]
const fn commit_level1_col(pair: usize, lane: usize) -> usize {
    COMMIT_LEVEL1_BASE + DIGEST_WIDTH * pair + lane
}

#[inline]
const fn commit_level2_col(pair: usize, lane: usize) -> usize {
    COMMIT_LEVEL2_BASE + DIGEST_WIDTH * pair + lane
}

#[inline]
const fn deal_blind_col(seat: usize, lane: usize) -> usize {
    DEAL_BLIND_BASE + DIGEST_WIDTH * seat + lane
}

#[inline]
const fn deal_leaf_col(seat: usize, lane: usize) -> usize {
    DEAL_LEAF_BASE + DIGEST_WIDTH * seat + lane
}

#[inline]
const fn deal_level1_col(pair: usize, lane: usize) -> usize {
    DEAL_LEVEL1_BASE + DIGEST_WIDTH * pair + lane
}

#[inline]
const fn deal_level2_col(pair: usize, lane: usize) -> usize {
    DEAL_LEVEL2_BASE + DIGEST_WIDTH * pair + lane
}

type Digest = [BabyBear; DIGEST_WIDTH];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FairShuffleWitness {
    pub seeds: [u16; PARTICIPANT_COUNT],
    pub commitment_blinding: [[u32; DIGEST_WIDTH]; PARTICIPANT_COUNT],
    pub deal_blinding: [[u32; DIGEST_WIDTH]; SEAT_COUNT],
}

impl FairShuffleWitness {
    pub fn try_new(
        seeds: [u16; PARTICIPANT_COUNT],
        commitment_blinding: [[u32; DIGEST_WIDTH]; PARTICIPANT_COUNT],
        deal_blinding: [[u32; DIGEST_WIDTH]; SEAT_COUNT],
    ) -> Result<Self, String> {
        let witness = Self {
            seeds,
            commitment_blinding,
            deal_blinding,
        };
        witness.validate()?;
        Ok(witness)
    }

    pub fn fresh(seeds: [u16; PARTICIPANT_COUNT]) -> Result<Self, String> {
        let mut commitment_blinding = [[0u32; DIGEST_WIDTH]; PARTICIPANT_COUNT];
        let mut deal_blinding = [[0u32; DIGEST_WIDTH]; SEAT_COUNT];
        for blind in commitment_blinding
            .iter_mut()
            .chain(deal_blinding.iter_mut())
        {
            for lane in blind {
                *lane = fresh_field_element()?;
            }
        }
        Self::try_new(seeds, commitment_blinding, deal_blinding)
    }

    fn validate(&self) -> Result<(), String> {
        for (kind, all) in [
            ("commitment", &self.commitment_blinding),
            ("deal", &self.deal_blinding),
        ] {
            for (owner, blind) in all.iter().enumerate() {
                for (lane, &value) in blind.iter().enumerate() {
                    if value >= BABYBEAR_P {
                        return Err(format!(
                            "{kind} blind {owner}:{lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                        ));
                    }
                }
            }
        }
        Ok(())
    }

    pub fn joint_entropy(&self) -> u16 {
        self.seeds
            .iter()
            .fold(0u16, |acc, &seed| acc.wrapping_add(seed))
    }

    pub fn is_accepted(&self) -> bool {
        u32::from(self.joint_entropy()) < PERMUTATION_COUNT
    }

    pub fn cards(&self) -> [u8; CARD_COUNT] {
        let rank = if self.is_accepted() {
            u32::from(self.joint_entropy())
        } else {
            0
        };
        permutation_of_rank(rank).expect("accepted/fallback rank is in 0..8!")
    }
}

fn fresh_field_element() -> Result<u32, String> {
    let modulus = BABYBEAR_P as u64;
    let accept_below = ((u32::MAX as u64 + 1) / modulus) * modulus;
    loop {
        let mut bytes = [0u8; 4];
        getrandom::fill(&mut bytes)
            .map_err(|e| format!("OS randomness failed for fair-shuffle blinding: {e}"))?;
        let candidate = u32::from_le_bytes(bytes) as u64;
        if candidate < accept_below {
            return Ok((candidate % modulus) as u32);
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub session: u32,
    pub rule: u32,
    pub attempt: u32,
    pub commitment_root: [u32; DIGEST_WIDTH],
    pub accepted: bool,
    pub deal_root: [u32; DIGEST_WIDTH],
}

impl PublicStatement {
    pub fn as_u32_vec(self) -> Vec<u32> {
        let mut public = Vec::with_capacity(PUBLIC_INPUT_COUNT);
        public.extend([self.session, self.rule, self.attempt]);
        public.extend(self.commitment_root);
        public.push(u32::from(self.accepted));
        public.extend(self.deal_root);
        public
    }

    fn as_felts(self) -> [BabyBear; 20] {
        let mut public = [BabyBear::ZERO; 20];
        public[SESSION] = BabyBear::new(self.session);
        public[RULE] = BabyBear::new(self.rule);
        public[ATTEMPT] = BabyBear::new(self.attempt);
        for lane in 0..DIGEST_WIDTH {
            public[COMMIT_ROOT_BASE + lane] = BabyBear::new(self.commitment_root[lane]);
        }
        public[ACCEPTED] = BabyBear::new(u32::from(self.accepted));
        for lane in 0..DIGEST_WIDTH {
            public[DEAL_ROOT_PUBLIC_BASE + lane] = BabyBear::new(self.deal_root[lane]);
        }
        public
    }

    pub fn validate(self) -> Result<(), String> {
        if self.session >= BABYBEAR_P || self.attempt >= BABYBEAR_P {
            return Err("session/attempt is noncanonical for BabyBear".to_string());
        }
        if self.rule != RULE_ID {
            return Err(format!(
                "rule {} is not fixed fair-shuffle rule {RULE_ID}",
                self.rule
            ));
        }
        for (label, root) in [
            ("commitment", self.commitment_root),
            ("deal", self.deal_root),
        ] {
            for (lane, value) in root.into_iter().enumerate() {
                if value >= BABYBEAR_P {
                    return Err(format!(
                        "{label}-root lane {lane}={value} is noncanonical for BabyBear"
                    ));
                }
            }
        }
        if !self.accepted && self.deal_root != [0; DIGEST_WIDTH] {
            return Err("rejected fair-shuffle attempt must publish zero deal_root8".to_string());
        }
        Ok(())
    }

    /// Decode the exact 20-word public ABI. Boolean and field values must use
    /// canonical representatives; the decoder never silently reduces them.
    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "private fair shuffle expects {PUBLIC_INPUT_COUNT} public inputs, got {}",
                values.len()
            ));
        }
        let accepted = match values[ACCEPTED] {
            0 => false,
            1 => true,
            value => {
                return Err(format!(
                    "accepted flag has non-boolean representative {value}"
                ));
            }
        };
        let public = Self {
            session: values[SESSION],
            rule: values[RULE],
            attempt: values[ATTEMPT],
            commitment_root: values[COMMIT_ROOT_BASE..COMMIT_ROOT_BASE + DIGEST_WIDTH]
                .try_into()
                .expect("length checked"),
            accepted,
            deal_root: values[DEAL_ROOT_PUBLIC_BASE..DEAL_ROOT_PUBLIC_BASE + DIGEST_WIDTH]
                .try_into()
                .expect("length checked"),
        };
        public.validate()?;
        Ok(public)
    }
}

pub struct FairShuffleZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl FairShuffleZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private fair-shuffle proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private fair-shuffle proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedAttempt {
    Accepted(PublicStatement),
    Rejected(PublicStatement),
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(PRIVATE_SHUFFLE_FAIR_DESCRIPTOR_JSON)?;
    if desc.name != "private-shuffle-fair-n8::add16-reject40320-decomposefin-v1"
        || desc.trace_width != TRACE_WIDTH
        || desc.public_input_count != 20
    {
        return Err("private fair shuffle emitted descriptor shape drifted".to_string());
    }
    Ok(desc)
}

/// Fingerprint of the exact Lean-emitted AIR artifact.
pub fn air_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-shuffle-fair-air-v1");
    hasher.update(PRIVATE_SHUFFLE_FAIR_DESCRIPTOR_JSON.as_bytes());
    *hasher.finalize().as_bytes()
}

/// Stable identity of the privacy-facing HidingFri verifier/config family.
pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-shuffle-fair-hiding-config-v1");
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

/// Canonical identity of this standalone verifier. This does not claim an
/// `Effect::Custom` binding to a cell transition.
pub fn canonical_vk_hash() -> [u8; 32] {
    let verifier_source = hiding_verifier_config_fingerprint();
    let mut verifier = blake3::Hasher::new_derive_key("dregg-verifier-fingerprint-v1");
    verifier.update(&[0]);
    verifier.update(&verifier_source);
    let verifier_canonical = *verifier.finalize().as_bytes();
    let proving_system = proving_system_canonical_bytes();
    let program = PRIVATE_SHUFFLE_FAIR_DESCRIPTOR_JSON.as_bytes();

    let mut hasher = blake3::Hasher::new_derive_key("dregg-vk-v2");
    hasher.update(&(program.len() as u64).to_le_bytes());
    hasher.update(program);
    hasher.update(&air_fingerprint());
    hasher.update(&verifier_canonical);
    hasher.update(&(proving_system.len() as u64).to_le_bytes());
    hasher.update(&proving_system);
    *hasher.finalize().as_bytes()
}

/// The exact recursive decoder used by Lean's `Perm.decomposeFin` equivalence.
pub fn permutation_of_rank(rank: u32) -> Result<[u8; CARD_COUNT], String> {
    if rank >= PERMUTATION_COUNT {
        return Err(format!("rank {rank} is outside exact range 0..8!"));
    }
    let mut remainder = rank;
    let mut digits = [0u8; 7];
    for (stage, digit) in digits.iter_mut().enumerate() {
        let size = 8 - stage;
        let weight = FACTORIALS[size - 1];
        *digit = (remainder / weight) as u8;
        remainder %= weight;
    }
    debug_assert_eq!(remainder, 0);

    let mut current = vec![0u8];
    for size in 2..=8 {
        let chosen = digits[8 - size];
        let mut next = Vec::with_capacity(size);
        next.push(chosen);
        next.extend(current.into_iter().map(|card| {
            let lifted = card + 1;
            if chosen != 0 && lifted == chosen {
                0
            } else {
                lifted
            }
        }));
        current = next;
    }
    current
        .try_into()
        .map_err(|_| "internal decomposeFin decoder length drifted".to_string())
}

fn fill_bits(row: &mut [BabyBear], value: u32, base: usize, bits: usize) {
    for bit in 0..bits {
        row[base + bit] = BabyBear::new((value >> bit) & 1);
    }
}

fn node8(left: Digest, right: Digest) -> Digest {
    let mut preimage = Vec::with_capacity(16);
    preimage.extend(left);
    preimage.extend(right);
    chip_absorb_all_lanes(preimage.len(), &preimage)
}

fn commitment_leaf_digest(
    session: u32,
    attempt: u32,
    participant: usize,
    seed: u16,
    blind: [u32; DIGEST_WIDTH],
) -> Digest {
    let mut preimage = Vec::with_capacity(16);
    preimage.extend([
        BabyBear::new(COMMIT_DOMAIN_TAG),
        BabyBear::new(session),
        BabyBear::new(RULE_ID),
        BabyBear::new(attempt),
        BabyBear::new(participant as u32),
        BabyBear::new(seed.into()),
    ]);
    preimage.extend(blind.map(BabyBear::new));
    preimage.extend([BabyBear::ZERO; 2]);
    chip_absorb_all_lanes(preimage.len(), &preimage)
}

/// Public commitment emitted before a participant reveals its seed to the
/// local proof producer. It binds session, attempt, participant index, seed,
/// and all eight blinding lanes.
pub fn participant_commitment(
    session: u32,
    attempt: u32,
    participant: usize,
    seed: u16,
    blind: [u32; DIGEST_WIDTH],
) -> Result<[u32; DIGEST_WIDTH], String> {
    if session >= BABYBEAR_P || attempt >= BABYBEAR_P {
        return Err("session/attempt is noncanonical for BabyBear".to_string());
    }
    if participant >= PARTICIPANT_COUNT {
        return Err(format!(
            "participant {participant} is outside fixed range 0..{}",
            PARTICIPANT_COUNT - 1
        ));
    }
    for (lane, value) in blind.into_iter().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "commitment blind lane {lane}={value} is noncanonical for BabyBear"
            ));
        }
    }
    Ok(commitment_leaf_digest(session, attempt, participant, seed, blind).map(BabyBear::as_u32))
}

/// Reconstruct the AIR's fixed depth-three participant commitment tree from
/// the eight public leaf commitments recorded during commit-before-reveal.
pub fn commitment_root_from_leaves(
    leaves: [[u32; DIGEST_WIDTH]; PARTICIPANT_COUNT],
) -> Result<[u32; DIGEST_WIDTH], String> {
    for (participant, digest) in leaves.iter().enumerate() {
        for (lane, &value) in digest.iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "participant commitment {participant}:{lane}={value} is noncanonical for BabyBear"
                ));
            }
        }
    }
    let leaves = leaves.map(|digest| digest.map(BabyBear::new));
    let level1: [Digest; 4] =
        core::array::from_fn(|pair| node8(leaves[2 * pair], leaves[2 * pair + 1]));
    let level2: [Digest; 2] =
        core::array::from_fn(|pair| node8(level1[2 * pair], level1[2 * pair + 1]));
    Ok(node8(level2[0], level2[1]).map(BabyBear::as_u32))
}

fn deal_leaf_digest(session: u32, seat: usize, card: u8, blind: [u32; DIGEST_WIDTH]) -> Digest {
    let mut preimage = Vec::with_capacity(16);
    preimage.extend([
        BabyBear::new(SHUFFLE_LEAF_DOMAIN_TAG),
        BabyBear::new(session),
        BabyBear::new(SHUFFLE_RULE_ID),
        BabyBear::new(seat as u32),
        BabyBear::new(card.into()),
    ]);
    preimage.extend(blind.map(BabyBear::new));
    preimage.extend([BabyBear::ZERO; 3]);
    chip_absorb_all_lanes(preimage.len(), &preimage)
}

fn fill_commitment_tree(row: &mut [BabyBear], witness: &FairShuffleWitness) -> Digest {
    let leaves: [Digest; 8] = core::array::from_fn(|participant| {
        commitment_leaf_digest(
            row[SESSION].as_u32(),
            row[ATTEMPT].as_u32(),
            participant,
            witness.seeds[participant],
            witness.commitment_blinding[participant],
        )
    });
    let level1: [Digest; 4] =
        core::array::from_fn(|pair| node8(leaves[2 * pair], leaves[2 * pair + 1]));
    let level2: [Digest; 2] =
        core::array::from_fn(|pair| node8(level1[2 * pair], level1[2 * pair + 1]));
    let root = node8(level2[0], level2[1]);

    for (participant, digest) in leaves.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[commit_leaf_col(participant, lane)] = value;
        }
    }
    for (pair, digest) in level1.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[commit_level1_col(pair, lane)] = value;
        }
    }
    for (pair, digest) in level2.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[commit_level2_col(pair, lane)] = value;
        }
    }
    row[COMMIT_ROOT_BASE..COMMIT_ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&root);
    root
}

fn fill_deal_tree(
    row: &mut [BabyBear],
    witness: &FairShuffleWitness,
    cards: [u8; CARD_COUNT],
) -> Digest {
    let leaves: [Digest; 8] = core::array::from_fn(|seat| {
        deal_leaf_digest(
            row[SESSION].as_u32(),
            seat,
            cards[seat],
            witness.deal_blinding[seat],
        )
    });
    let level1: [Digest; 4] =
        core::array::from_fn(|pair| node8(leaves[2 * pair], leaves[2 * pair + 1]));
    let level2: [Digest; 2] =
        core::array::from_fn(|pair| node8(level1[2 * pair], level1[2 * pair + 1]));
    let root = node8(level2[0], level2[1]);

    for (seat, digest) in leaves.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[deal_leaf_col(seat, lane)] = value;
        }
    }
    for (pair, digest) in level1.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[deal_level1_col(pair, lane)] = value;
        }
    }
    for (pair, digest) in level2.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[deal_level2_col(pair, lane)] = value;
        }
    }
    row[DEAL_CALC_ROOT_BASE..DEAL_CALC_ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&root);
    root
}

fn build_row(
    session: u32,
    attempt: u32,
    witness: &FairShuffleWitness,
) -> Result<(Vec<BabyBear>, PublicStatement), String> {
    witness.validate()?;
    if session >= BABYBEAR_P || attempt >= BABYBEAR_P {
        return Err("session/attempt is noncanonical for BabyBear".to_string());
    }

    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[SESSION] = BabyBear::new(session);
    row[RULE] = BabyBear::new(RULE_ID);
    row[ATTEMPT] = BabyBear::new(attempt);

    let seed_sum: u32 = witness.seeds.iter().map(|&seed| u32::from(seed)).sum();
    let entropy = seed_sum % ENTROPY_SPACE;
    let carry = seed_sum / ENTROPY_SPACE;
    let accepted = entropy < PERMUTATION_COUNT;
    let rank = if accepted { entropy } else { 0 };

    for participant in 0..PARTICIPANT_COUNT {
        let seed = u32::from(witness.seeds[participant]);
        row[SEED_BASE + participant] = BabyBear::new(seed);
        fill_bits(&mut row, seed, seed_bit_col(participant, 0), 16);
        for lane in 0..DIGEST_WIDTH {
            row[commit_blind_col(participant, lane)] =
                BabyBear::new(witness.commitment_blinding[participant][lane]);
        }
    }
    row[CARRY] = BabyBear::new(carry);
    fill_bits(&mut row, carry, CARRY_BIT_BASE, 3);
    row[ENTROPY_COL] = BabyBear::new(entropy);
    fill_bits(&mut row, entropy, ENTROPY_BIT_BASE, 16);
    row[ACCEPTED] = BabyBear::new(u32::from(accepted));

    let (low_slack, high_slack) = if accepted {
        (PERMUTATION_COUNT - 1 - entropy, 0)
    } else {
        (0, entropy - PERMUTATION_COUNT)
    };
    row[LOW_SLACK] = BabyBear::new(low_slack);
    fill_bits(&mut row, low_slack, LOW_SLACK_BIT_BASE, 16);
    row[HIGH_SLACK] = BabyBear::new(high_slack);
    fill_bits(&mut row, high_slack, HIGH_SLACK_BIT_BASE, 16);
    row[RANK] = BabyBear::new(rank);

    let mut remainder = rank;
    let mut digits = [0usize; 7];
    for stage in 0..7 {
        let size = 8 - stage;
        let weight = FACTORIALS[size - 1];
        let digit = (remainder / weight) as usize;
        row[rank_stage_col(stage)] = BabyBear::new(remainder);
        row[DIGIT_BASE + stage] = BabyBear::new(digit as u32);
        row[digit_selector_col(stage, digit)] = BabyBear::ONE;
        digits[stage] = digit;
        remainder %= weight;
    }
    debug_assert_eq!(remainder, 0);

    let mut current = vec![0usize];
    for size in 2..=8 {
        let chosen = digits[8 - size];
        let mut next = Vec::with_capacity(size);
        next.push(chosen);
        next.extend(current.into_iter().map(|card| {
            let lifted = card + 1;
            if chosen != 0 && lifted == chosen {
                0
            } else {
                lifted
            }
        }));
        for (pos, &card) in next.iter().enumerate() {
            row[perm_selector_col(size, pos, card)] = BabyBear::ONE;
        }
        current = next;
    }
    let cards: [u8; CARD_COUNT] = current
        .into_iter()
        .map(|card| card as u8)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| "internal permutation length drifted".to_string())?;

    for seat in 0..SEAT_COUNT {
        for lane in 0..DIGEST_WIDTH {
            row[deal_blind_col(seat, lane)] = BabyBear::new(witness.deal_blinding[seat][lane]);
        }
    }

    let commitment_root = fill_commitment_tree(&mut row, witness);
    let computed_deal_root = fill_deal_tree(&mut row, witness, cards);
    let public_deal_root = if accepted {
        computed_deal_root
    } else {
        [BabyBear::ZERO; DIGEST_WIDTH]
    };
    row[DEAL_ROOT_PUBLIC_BASE..DEAL_ROOT_PUBLIC_BASE + DIGEST_WIDTH]
        .copy_from_slice(&public_deal_root);

    let public = PublicStatement {
        session,
        rule: RULE_ID,
        attempt,
        commitment_root: commitment_root.map(BabyBear::as_u32),
        accepted,
        deal_root: public_deal_root.map(BabyBear::as_u32),
    };
    Ok((row, public))
}

pub fn statement(
    session: u32,
    attempt: u32,
    witness: &FairShuffleWitness,
) -> Result<PublicStatement, String> {
    build_row(session, attempt, witness).map(|(_, public)| public)
}

fn trace_and_public(
    session: u32,
    attempt: u32,
    witness: &FairShuffleWitness,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (row, public) = build_row(session, attempt, witness)?;
    let desc = descriptor()?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((desc, trace, public))
}

pub fn prove_zk(
    session: u32,
    attempt: u32,
    witness: &FairShuffleWitness,
) -> Result<(FairShuffleZkProof, PublicStatement), String> {
    let (desc, trace, public) = trace_and_public(session, attempt, witness)?;
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
    Ok((FairShuffleZkProof { proof }, public))
}

pub fn verify_zk(
    proof: &FairShuffleZkProof,
    public: PublicStatement,
) -> Result<VerifiedAttempt, String> {
    public.validate()?;
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts(), &config)?;
    Ok(if public.accepted {
        VerifiedAttempt::Accepted(public)
    } else {
        VerifiedAttempt::Rejected(public)
    })
}

/// Verify the stable transport form without exposing the concrete proof type.
pub fn verify_postcard(
    proof_bytes: &[u8],
    public_values: &[u32],
) -> Result<VerifiedAttempt, String> {
    let proof = FairShuffleZkProof::from_postcard(proof_bytes)?;
    verify_zk(&proof, PublicStatement::try_from_u32s(public_values)?)
}

/// Open one card from an accepted fair-shuffle witness using the existing
/// `SHF8` Merkle-opening format. Rejected attempts have no public deal root and
/// therefore cannot issue card openings.
pub fn deal_opening(
    session: u32,
    witness: &FairShuffleWitness,
    seat: usize,
) -> Result<crate::private_shuffle::CardOpening, String> {
    witness.validate()?;
    if !witness.is_accepted() {
        return Err("rejected fair-shuffle attempt has no openable deal".to_string());
    }
    let shuffle_witness =
        crate::private_shuffle::PrivateShuffleWitness::try_from_assignment_with_blinding(
            &witness.cards(),
            witness.deal_blinding,
        )?;
    crate::private_shuffle::opening(session, &shuffle_witness, seat)
}

/// Verify one selective opening against the accepted deal root. The fair
/// proof must be verified separately first; game consumers do that before
/// admitting this opening into state.
pub fn verify_deal_opening(
    public: PublicStatement,
    opening: &crate::private_shuffle::CardOpening,
) -> Result<(), String> {
    public.validate()?;
    if !public.accepted {
        return Err("rejected fair-shuffle attempt has no openable deal".to_string());
    }
    crate::private_shuffle::verify_opening(
        crate::private_shuffle::PublicStatement {
            session: public.session,
            rule: SHUFFLE_RULE_ID,
            deal_root: public.deal_root,
        },
        opening,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};
    use std::collections::HashSet;

    fn blinds(base: u32) -> [[u32; DIGEST_WIDTH]; 8] {
        core::array::from_fn(|owner| {
            core::array::from_fn(|lane| base + (owner * DIGEST_WIDTH + lane) as u32)
        })
    }

    fn fixture_with_seed0(seed0: u16) -> FairShuffleWitness {
        let mut seeds = [0u16; 8];
        seeds[0] = seed0;
        FairShuffleWitness::try_new(seeds, blinds(1_000), blinds(2_000)).unwrap()
    }

    #[test]
    fn exact_rank_decoder_is_a_bijection_over_all_eight_factorial_ranks() {
        let mut seen = HashSet::with_capacity(PERMUTATION_COUNT as usize);
        for rank in 0..PERMUTATION_COUNT {
            let cards = permutation_of_rank(rank).expect("in-range rank");
            let unique: HashSet<_> = cards.into_iter().collect();
            assert_eq!(unique.len(), CARD_COUNT);
            assert!(seen.insert(cards), "rank decoder collided at {rank}");
        }
        assert_eq!(seen.len(), PERMUTATION_COUNT as usize);
        assert!(permutation_of_rank(PERMUTATION_COUNT).is_err());
    }

    #[test]
    fn rejection_boundary_and_every_bound_input_have_teeth() {
        let accepted = fixture_with_seed0(40_319);
        let rejected = fixture_with_seed0(40_320);
        let a = statement(77, 4, &accepted).unwrap();
        let r = statement(77, 5, &rejected).unwrap();
        assert!(a.accepted);
        assert!(!r.accepted);
        assert_ne!(a.deal_root, [0; DIGEST_WIDTH]);
        assert_eq!(r.deal_root, [0; DIGEST_WIDTH]);
        assert_ne!(a.commitment_root, r.commitment_root);

        let mut seed_tamper = accepted.clone();
        seed_tamper.seeds[7] = 1;
        assert_ne!(
            statement(77, 4, &seed_tamper).unwrap().commitment_root,
            a.commitment_root
        );
        let mut blind_tamper = accepted.clone();
        blind_tamper.commitment_blinding[6][7] += 1;
        assert_ne!(
            statement(77, 4, &blind_tamper).unwrap().commitment_root,
            a.commitment_root
        );
        assert_ne!(
            statement(77, 6, &accepted).unwrap().commitment_root,
            a.commitment_root
        );
    }

    #[test]
    fn emitted_air_refuses_rank_permutation_mutation() {
        let witness = fixture_with_seed0(12_345);
        let (mut row, public) = build_row(77, 0, &witness).unwrap();
        let cards = witness.cards();
        let wrong = (usize::from(cards[0]) + 1) % CARD_COUNT;
        row[perm_selector_col(8, 0, usize::from(cards[0]))] = BabyBear::ZERO;
        row[perm_selector_col(8, 0, wrong)] = BabyBear::ONE;
        let trace = vec![row.clone(), row.clone(), row.clone(), row];
        let refusal = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_vm_descriptor2(
                &descriptor().unwrap(),
                &trace,
                &public.as_felts(),
                &MemBoundaryWitness::default(),
                &[],
            )
        }));
        assert!(refusal.is_err() || refusal.unwrap().is_err());
    }

    #[test]
    fn hiding_proof_verifies_and_public_tampers_refuse() {
        let witness = fixture_with_seed0(12_345);
        let (proof, public) = prove_zk(77, 3, &witness).expect("honest hiding fair-shuffle proof");
        assert!(matches!(
            verify_zk(&proof, public).expect("honest proof verifies"),
            VerifiedAttempt::Accepted(_)
        ));
        assert!(proof.proof.commitments.random.is_some());

        let proof_bytes = proof.to_postcard().expect("proof transport");
        let public_values = public.as_u32_vec();
        assert_eq!(public_values.len(), PUBLIC_INPUT_COUNT);
        assert_eq!(
            PublicStatement::try_from_u32s(&public_values).unwrap(),
            public
        );
        assert_eq!(
            verify_postcard(&proof_bytes, &public_values).unwrap(),
            VerifiedAttempt::Accepted(public)
        );

        let leaves = core::array::from_fn(|participant| {
            participant_commitment(
                77,
                3,
                participant,
                witness.seeds[participant],
                witness.commitment_blinding[participant],
            )
            .unwrap()
        });
        assert_eq!(
            commitment_root_from_leaves(leaves).unwrap(),
            public.commitment_root
        );

        let opening = deal_opening(77, &witness, 5).expect("selective deal opening");
        verify_deal_opening(public, &opening).expect("opening binds accepted deal root");
        let mut wrong_opening = opening;
        wrong_opening.card = (wrong_opening.card + 1) % CARD_COUNT as u8;
        assert!(verify_deal_opening(public, &wrong_opening).is_err());

        let mut attempt_tamper = public;
        attempt_tamper.attempt += 1;
        assert!(verify_zk(&proof, attempt_tamper).is_err());

        let mut commit_tamper = public;
        commit_tamper.commitment_root[0] = (commit_tamper.commitment_root[0] + 1) % BABYBEAR_P;
        assert!(verify_zk(&proof, commit_tamper).is_err());

        let mut accepted_tamper = public;
        accepted_tamper.accepted = false;
        accepted_tamper.deal_root = [0; DIGEST_WIDTH];
        assert!(verify_zk(&proof, accepted_tamper).is_err());

        let mut root_tamper = public;
        root_tamper.deal_root[7] = (root_tamper.deal_root[7] + 1) % BABYBEAR_P;
        assert!(verify_zk(&proof, root_tamper).is_err());

        assert_ne!(air_fingerprint(), hiding_verifier_config_fingerprint());
        assert_ne!(canonical_vk_hash(), [0; 32]);

        let rejected_witness = fixture_with_seed0(40_320);
        let (rejected_proof, rejected_public) =
            prove_zk(77, 4, &rejected_witness).expect("rejected attempt is still provable");
        assert!(!rejected_public.accepted);
        assert_eq!(rejected_public.deal_root, [0; DIGEST_WIDTH]);
        assert!(matches!(
            verify_zk(&rejected_proof, rejected_public).expect("rejection proof verifies"),
            VerifiedAttempt::Rejected(_)
        ));
    }
}
