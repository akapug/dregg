//! Fixed `N=8` private shuffle/deal proof producer.
//!
//! The relation and AIR are authored in Lean at
//! `Dregg2/Games/PrivateShuffleDescriptor.lean`. Rust only validates/fills that
//! fixed layout, proves the emitted descriptor, and verifies selective card
//! openings. The public statement is exactly `(session, rule, deal_root8)`.
//!
//! Each seat has an independently blinded, full-arity-16 leaf commitment:
//!
//! `[domain, session, rule, seat, card, blind0..blind7, 0, 0, 0]`.
//!
//! Eight leaves are folded through a depth-three full-width `node8` tree. A
//! recipient can therefore receive one [`CardOpening`] without learning other
//! cards.
//!
//! [`prove_zk`] uses `HidingFriPcs`; there is intentionally no public
//! non-hiding proof API. The process constructing the trace still sees the
//! assignment. Most importantly, permutation correctness is **not** unbiased
//! randomness: a coordinator can choose a valid but biased permutation.
//! Distributed randomness, MPC shuffling, or a verifiable mix is a separate
//! protocol layer.

use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};

/// Exact artifact emitted by the Lean author.
pub const PRIVATE_SHUFFLE_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-shuffle-n8.json");

pub const CARD_COUNT: usize = 8;
pub const SEAT_COUNT: usize = 8;
pub const DIGEST_WIDTH: usize = 8;
pub const TREE_DEPTH: usize = 3;
pub const RULE_ID: u32 = 1_346_720_312;
pub const LEAF_DOMAIN_TAG: u32 = 1_397_245_496;

const TRACE_WIDTH: usize = 258;
const SESSION: usize = 0;
const RULE: usize = 1;
const ROOT_BASE: usize = 2;
const CARD_BASE: usize = 10;
const BLIND_BASE: usize = 18;
const SELECT_BASE: usize = 82;
const LEAF_BASE: usize = 146;
const LEVEL1_BASE: usize = 210;
const LEVEL2_BASE: usize = 242;

#[inline]
const fn blind_col(seat: usize, lane: usize) -> usize {
    BLIND_BASE + DIGEST_WIDTH * seat + lane
}

#[inline]
const fn select_col(seat: usize, card: usize) -> usize {
    SELECT_BASE + CARD_COUNT * seat + card
}

#[inline]
const fn leaf_col(seat: usize, lane: usize) -> usize {
    LEAF_BASE + DIGEST_WIDTH * seat + lane
}

#[inline]
const fn level1_col(pair: usize, lane: usize) -> usize {
    LEVEL1_BASE + DIGEST_WIDTH * pair + lane
}

#[inline]
const fn level2_col(pair: usize, lane: usize) -> usize {
    LEVEL2_BASE + DIGEST_WIDTH * pair + lane
}

/// Exactly eight canonical cards, one per public seat, and one independent
/// eight-felt blinding vector per card leaf.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateShuffleWitness {
    pub cards: [u8; CARD_COUNT],
    pub blinding: [[u32; DIGEST_WIDTH]; SEAT_COUNT],
}

impl PrivateShuffleWitness {
    /// Construct from an exact assignment and caller-owned blinds. This is the
    /// entry for deterministic fixtures and distributed blind generation.
    pub fn try_from_assignment_with_blinding(
        cards: &[u8],
        blinding: [[u32; DIGEST_WIDTH]; SEAT_COUNT],
    ) -> Result<Self, String> {
        let cards: [u8; CARD_COUNT] = cards.try_into().map_err(|_| {
            format!(
                "private shuffle requires exactly {CARD_COUNT} cards for {SEAT_COUNT} seats, got {}",
                cards.len()
            )
        })?;
        let witness = Self { cards, blinding };
        witness.validate()?;
        Ok(witness)
    }

    /// Construct with 64 rejection-sampled BabyBear blind felts from OS
    /// entropy. This does not make the permutation itself unbiased.
    pub fn try_from_assignment_fresh(cards: &[u8]) -> Result<Self, String> {
        let mut blinding = [[0u32; DIGEST_WIDTH]; SEAT_COUNT];
        for seat in &mut blinding {
            for lane in seat {
                *lane = fresh_field_element()?;
            }
        }
        Self::try_from_assignment_with_blinding(cards, blinding)
    }

    fn validate(&self) -> Result<(), String> {
        let mut seen = [false; CARD_COUNT];
        for (seat, &card) in self.cards.iter().enumerate() {
            let card = card as usize;
            if card >= CARD_COUNT {
                return Err(format!(
                    "seat {seat} carries card {card}, outside canonical range 0..{}",
                    CARD_COUNT - 1
                ));
            }
            if std::mem::replace(&mut seen[card], true) {
                return Err(format!(
                    "card {card} appears more than once; the fixed deal must be an exact permutation"
                ));
            }
        }
        if let Some(card) = seen.iter().position(|present| !present) {
            return Err(format!(
                "card {card} is omitted; the fixed deal must contain every canonical card exactly once"
            ));
        }
        for (seat, blind) in self.blinding.iter().enumerate() {
            for (lane, &value) in blind.iter().enumerate() {
                if value >= BABYBEAR_P {
                    return Err(format!(
                        "seat {seat} blinding lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                    ));
                }
            }
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
            .map_err(|e| format!("OS randomness failed for shuffle blinding: {e}"))?;
        let candidate = u32::from_le_bytes(bytes) as u64;
        if candidate < accept_below {
            return Ok((candidate % modulus) as u32);
        }
    }
}

/// The only public values: session, fixed rule, and the faithful eight-felt
/// deal root. Cards and commitment openings are absent.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub session: u32,
    pub rule: u32,
    pub deal_root: [u32; DIGEST_WIDTH],
}

impl PublicStatement {
    fn as_felts(self) -> [BabyBear; 10] {
        let mut public = [BabyBear::ZERO; 10];
        public[0] = BabyBear::new(self.session);
        public[1] = BabyBear::new(self.rule);
        for (lane, value) in self.deal_root.into_iter().enumerate() {
            public[2 + lane] = BabyBear::new(value);
        }
        public
    }

    fn validate_shape(self) -> Result<(), String> {
        if self.session >= BABYBEAR_P {
            return Err(format!(
                "session {} is noncanonical for BabyBear modulus {BABYBEAR_P}",
                self.session
            ));
        }
        if self.rule != RULE_ID {
            return Err(format!(
                "rule {} is not fixed private-shuffle rule {RULE_ID}",
                self.rule
            ));
        }
        for (lane, value) in self.deal_root.into_iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "deal-root lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
        Ok(())
    }
}

/// Hiding proof of the fixed-eight permutation relation.
pub struct PrivateShuffleZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

/// One recipient's selective deal opening. The public statement supplies the
/// session/rule/root; no other card is present here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CardOpening {
    pub seat: u8,
    pub card: u8,
    pub blinding: [u32; DIGEST_WIDTH],
    /// Leaf sibling, level-one sibling, level-two sibling.
    pub siblings: [[u32; DIGEST_WIDTH]; TREE_DEPTH],
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(PRIVATE_SHUFFLE_DESCRIPTOR_JSON)?;
    if desc.name != "private-shuffle-n8::leaf16-node8-v1"
        || desc.trace_width != TRACE_WIDTH
        || desc.public_input_count != 10
    {
        return Err("private shuffle emitted descriptor shape drifted".to_string());
    }
    Ok(desc)
}

fn leaf_digest(
    session: u32,
    seat: usize,
    card: u8,
    blinding: [u32; DIGEST_WIDTH],
) -> [BabyBear; DIGEST_WIDTH] {
    let mut preimage = Vec::with_capacity(16);
    preimage.extend([
        BabyBear::new(LEAF_DOMAIN_TAG),
        BabyBear::new(session),
        BabyBear::new(RULE_ID),
        BabyBear::new(seat as u32),
        BabyBear::new(card as u32),
    ]);
    preimage.extend(blinding.map(BabyBear::new));
    preimage.extend([BabyBear::ZERO; 3]);
    debug_assert_eq!(preimage.len(), 16);
    chip_absorb_all_lanes(preimage.len(), &preimage)
}

fn node8(
    left: [BabyBear; DIGEST_WIDTH],
    right: [BabyBear; DIGEST_WIDTH],
) -> [BabyBear; DIGEST_WIDTH] {
    let mut preimage = Vec::with_capacity(16);
    preimage.extend(left);
    preimage.extend(right);
    debug_assert_eq!(preimage.len(), 16);
    chip_absorb_all_lanes(preimage.len(), &preimage)
}

type Digest = [BabyBear; DIGEST_WIDTH];

fn commitment_tree(
    session: u32,
    witness: &PrivateShuffleWitness,
) -> ([Digest; 8], [Digest; 4], [Digest; 2], Digest) {
    let leaves = core::array::from_fn(|seat| {
        leaf_digest(session, seat, witness.cards[seat], witness.blinding[seat])
    });
    let level1 = core::array::from_fn(|pair| node8(leaves[2 * pair], leaves[2 * pair + 1]));
    let level2 = core::array::from_fn(|pair| node8(level1[2 * pair], level1[2 * pair + 1]));
    let root = node8(level2[0], level2[1]);
    (leaves, level1, level2, root)
}

fn fill_commitment_columns(row: &mut [BabyBear]) -> [BabyBear; DIGEST_WIDTH] {
    let leaves: [Digest; 8] = core::array::from_fn(|seat| {
        let blind = core::array::from_fn(|lane| row[blind_col(seat, lane)].as_u32());
        leaf_digest(
            row[SESSION].as_u32(),
            seat,
            row[CARD_BASE + seat].as_u32() as u8,
            blind,
        )
    });
    let level1: [Digest; 4] =
        core::array::from_fn(|pair| node8(leaves[2 * pair], leaves[2 * pair + 1]));
    let level2: [Digest; 2] =
        core::array::from_fn(|pair| node8(level1[2 * pair], level1[2 * pair + 1]));
    let root = node8(level2[0], level2[1]);

    for (seat, digest) in leaves.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[leaf_col(seat, lane)] = value;
        }
    }
    for (pair, digest) in level1.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[level1_col(pair, lane)] = value;
        }
    }
    for (pair, digest) in level2.into_iter().enumerate() {
        for (lane, value) in digest.into_iter().enumerate() {
            row[level2_col(pair, lane)] = value;
        }
    }
    row[ROOT_BASE..ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&root);
    root
}

fn build_row(
    session: u32,
    witness: &PrivateShuffleWitness,
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
    for seat in 0..SEAT_COUNT {
        let card = witness.cards[seat] as usize;
        row[CARD_BASE + seat] = BabyBear::new(card as u32);
        row[select_col(seat, card)] = BabyBear::ONE;
        for lane in 0..DIGEST_WIDTH {
            row[blind_col(seat, lane)] = BabyBear::new(witness.blinding[seat][lane]);
        }
    }
    let root = fill_commitment_columns(&mut row);
    let public = PublicStatement {
        session,
        rule: RULE_ID,
        deal_root: root.map(BabyBear::as_u32),
    };
    Ok((row, public))
}

/// Compute the public root statement without proving.
pub fn statement(session: u32, witness: &PrivateShuffleWitness) -> Result<PublicStatement, String> {
    build_row(session, witness).map(|(_, public)| public)
}

fn trace_and_public(
    session: u32,
    witness: &PrivateShuffleWitness,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (row, public) = build_row(session, witness)?;
    let desc = descriptor()?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((desc, trace, public))
}

/// Produce the only privacy-facing proof API, using `HidingFriPcs` with fresh
/// prover randomness. This proves exact permutation correctness and root
/// binding, not unbiased selection of the permutation.
pub fn prove_zk(
    session: u32,
    witness: &PrivateShuffleWitness,
) -> Result<(PrivateShuffleZkProof, PublicStatement), String> {
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
    Ok((PrivateShuffleZkProof { proof }, public))
}

pub fn verify_zk(proof: &PrivateShuffleZkProof, public: PublicStatement) -> Result<(), String> {
    public.validate_shape()?;
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts(), &config)
}

/// Build one seat's selective opening. This exposes exactly that seat's card,
/// blind, and depth-three authentication path.
pub fn opening(
    session: u32,
    witness: &PrivateShuffleWitness,
    seat: usize,
) -> Result<CardOpening, String> {
    witness.validate()?;
    if session >= BABYBEAR_P {
        return Err(format!(
            "session {session} is noncanonical for BabyBear modulus {BABYBEAR_P}"
        ));
    }
    if seat >= SEAT_COUNT {
        return Err(format!("seat {seat} is outside fixed range 0..7"));
    }
    let (leaves, level1, level2, _) = commitment_tree(session, witness);
    Ok(CardOpening {
        seat: seat as u8,
        card: witness.cards[seat],
        blinding: witness.blinding[seat],
        siblings: [
            leaves[seat ^ 1].map(BabyBear::as_u32),
            level1[(seat / 2) ^ 1].map(BabyBear::as_u32),
            level2[(seat / 4) ^ 1].map(BabyBear::as_u32),
        ],
    })
}

/// Verify a selective opening against all eight faithful root lanes.
///
/// This proves only that this `(seat, card, blind, path)` is a member of
/// `public.deal_root`. Exact-permutation/no-duplicate correctness comes from
/// separately calling [`verify_zk`] on the **same** [`PublicStatement`]. A game
/// consumer must require both checks before treating an opened card as dealt by
/// the proved shuffle.
pub fn verify_opening(public: PublicStatement, opening: &CardOpening) -> Result<(), String> {
    public.validate_shape()?;
    let seat = opening.seat as usize;
    if seat >= SEAT_COUNT {
        return Err(format!("opening seat {seat} is outside fixed range 0..7"));
    }
    if opening.card as usize >= CARD_COUNT {
        return Err(format!(
            "opening card {} is outside canonical range 0..7",
            opening.card
        ));
    }
    for (lane, &value) in opening.blinding.iter().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "opening blinding lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
            ));
        }
    }
    for (level, sibling) in opening.siblings.iter().enumerate() {
        for (lane, &value) in sibling.iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "opening sibling level {level} lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                ));
            }
        }
    }

    let mut current = leaf_digest(public.session, seat, opening.card, opening.blinding);
    let mut index = seat;
    for sibling in opening.siblings {
        let sibling = sibling.map(BabyBear::new);
        current = if index & 1 == 0 {
            node8(current, sibling)
        } else {
            node8(sibling, current)
        };
        index >>= 1;
    }
    let got = current.map(BabyBear::as_u32);
    if got != public.deal_root {
        return Err("card opening does not reconstruct the public faithful root8".to_string());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::{MemBoundaryWitness, prove_vm_descriptor2};

    fn cards() -> [u8; CARD_COUNT] {
        [3, 0, 7, 2, 5, 1, 6, 4]
    }

    fn blinds() -> [[u32; DIGEST_WIDTH]; SEAT_COUNT] {
        core::array::from_fn(|seat| {
            core::array::from_fn(|lane| 1_000 + (seat * DIGEST_WIDTH + lane) as u32)
        })
    }

    fn fixture() -> PrivateShuffleWitness {
        PrivateShuffleWitness::try_from_assignment_with_blinding(&cards(), blinds())
            .expect("exact permutation")
    }

    #[test]
    fn shape_and_host_permutation_boundary_fail_closed() {
        assert!(
            PrivateShuffleWitness::try_from_assignment_with_blinding(&cards()[..7], blinds())
                .is_err()
        );
        let mut duplicate = cards();
        duplicate[1] = duplicate[0];
        assert!(
            PrivateShuffleWitness::try_from_assignment_with_blinding(&duplicate, blinds()).is_err()
        );
        let mut out_of_range = cards();
        out_of_range[2] = 8;
        assert!(
            PrivateShuffleWitness::try_from_assignment_with_blinding(&out_of_range, blinds())
                .is_err()
        );
        let mut bad_blind = blinds();
        bad_blind[4][6] = BABYBEAR_P;
        assert!(
            PrivateShuffleWitness::try_from_assignment_with_blinding(&cards(), bad_blind).is_err()
        );
        assert!(statement(BABYBEAR_P, &fixture()).is_err());

        let desc = descriptor().expect("Lean-emitted descriptor decodes");
        assert_eq!(desc.trace_width, TRACE_WIDTH);
        assert_eq!(desc.public_input_count, 10);
    }

    #[test]
    fn assignment_session_and_every_blind_bind_the_root() {
        let witness = fixture();
        let public = statement(77, &witness).expect("statement");

        let mut swapped = witness.clone();
        swapped.cards.swap(0, 1);
        assert_ne!(
            statement(77, &swapped)
                .expect("swapped statement")
                .deal_root,
            public.deal_root
        );
        assert_ne!(
            statement(78, &witness)
                .expect("new-session statement")
                .deal_root,
            public.deal_root
        );
        let mut reblinded = witness.clone();
        reblinded.blinding[7][7] += 1;
        assert_ne!(
            statement(77, &reblinded)
                .expect("reblinded statement")
                .deal_root,
            public.deal_root
        );
    }

    #[test]
    fn emitted_air_refuses_duplicate_even_with_consistent_leaf_tree() {
        let (mut row, _) = build_row(77, &fixture()).expect("honest row");

        // Seat 1 changes from card 0 to the card already held by seat 0. Keep
        // its row one-hot and card reconstruction honest, and recompute every
        // commitment node. Only the column-one permutation teeth now fail.
        let old = row[CARD_BASE + 1].as_u32() as usize;
        let duplicate = row[CARD_BASE].as_u32() as usize;
        row[CARD_BASE + 1] = BabyBear::new(duplicate as u32);
        row[select_col(1, old)] = BabyBear::ZERO;
        row[select_col(1, duplicate)] = BabyBear::ONE;
        let root = fill_commitment_columns(&mut row);
        let public = PublicStatement {
            session: 77,
            rule: RULE_ID,
            deal_root: root.map(BabyBear::as_u32),
        };
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
            "duplicate/omission must be refused by the emitted column-one gates"
        );
    }

    #[test]
    fn selective_openings_reveal_one_card_and_tampers_refuse() {
        let witness = fixture();
        let public = statement(77, &witness).expect("statement");
        for seat in 0..SEAT_COUNT {
            let opening = opening(77, &witness, seat).expect("selective opening");
            assert_eq!(opening.card, witness.cards[seat]);
            verify_opening(public, &opening).expect("opening reconstructs root8");
        }

        let honest = opening(77, &witness, 3).expect("opening");
        let mut card_tamper = honest;
        card_tamper.card = (card_tamper.card + 1) % CARD_COUNT as u8;
        assert!(verify_opening(public, &card_tamper).is_err());

        let mut blind_tamper = honest;
        blind_tamper.blinding[7] += 1;
        assert!(verify_opening(public, &blind_tamper).is_err());

        let mut path_tamper = honest;
        path_tamper.siblings[1][4] = (path_tamper.siblings[1][4] + 1) % BABYBEAR_P;
        assert!(verify_opening(public, &path_tamper).is_err());

        let mut seat_tamper = honest;
        seat_tamper.seat ^= 1;
        assert!(verify_opening(public, &seat_tamper).is_err());

        let mut root_tamper = public;
        root_tamper.deal_root[6] = (root_tamper.deal_root[6] + 1) % BABYBEAR_P;
        assert!(verify_opening(root_tamper, &honest).is_err());
    }

    #[test]
    fn hiding_proof_verifies_and_public_tampers_refuse() {
        let (proof, public) = prove_zk(77, &fixture()).expect("honest hiding shuffle proof");
        verify_zk(&proof, public).expect("honest proof verifies");
        assert!(proof.proof.commitments.random.is_some());
        assert!(
            proof
                .proof
                .opened_values
                .instances
                .iter()
                .all(|instance| instance.base_opened_values.random.is_some())
        );

        let mut root_tamper = public;
        root_tamper.deal_root[0] = (root_tamper.deal_root[0] + 1) % BABYBEAR_P;
        assert!(verify_zk(&proof, root_tamper).is_err());

        let mut session_tamper = public;
        session_tamper.session += 1;
        assert!(verify_zk(&proof, session_tamper).is_err());

        let mut rule_tamper = public;
        rule_tamper.rule ^= 1;
        assert!(verify_zk(&proof, rule_tamper).is_err());
    }
}
