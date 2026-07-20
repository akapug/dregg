//! Hiding proof producer for the Lean-authored bounded private graph-rewrite relation.
//!
//! This module is only a witness filler for
//! `Dregg2/Crypto/PrivateGraphRewriteDescriptor.lean`.  The hidden statement is
//! one injective, match-driven bounded hyperedge replacement over four ordered
//! host slots, two LHS slots, two RHS slots, two preserved-context slots, and
//! four pattern variables.  It is deliberately **not** advertised as full DPO:
//! freshness and dangling conditions are not part of this first relation.
//!
//! The public ABI is exactly
//! `[domain, session, version, shape, index, ruleset_root8, old_root8, new_root8]`.
//! The new graph's ordered slots are canonically
//! `[context0, context1, instantiated_rhs0, instantiated_rhs1]`; this ordering is
//! load-bearing because the public root commits to slots, not an unordered
//! multiset.  The old graph may be any ordering reachable from
//! `[context0, context1, instantiated_lhs0, instantiated_lhs1]` through the
//! descriptor's complete six-switch adjacent-swap network.

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
pub const PRIVATE_GRAPH_REWRITE_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-graph-rewrite-4x2.json");

pub const GRAPH_SLOTS: usize = 4;
pub const PATTERN_SLOTS: usize = 2;
pub const CONTEXT_SLOTS: usize = 2;
pub const VARIABLE_COUNT: usize = 4;
pub const RULE_COUNT: usize = 2;
pub const DIGEST_WIDTH: usize = 8;
pub const BLIND_WIDTH: usize = 4;
pub const TRACE_HEIGHT: usize = 4;
pub const TRACE_WIDTH: usize = 310;
pub const PUBLIC_INPUT_COUNT: usize = 29;
pub const PROTOCOL_VERSION: u32 = 1;
pub const SHAPE_ID: u32 = 4_216_242;
pub const GRAPH_STATE_TAG: u32 = 7_301;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";

/// Stable name of the exact hiding verifier/config family.
pub const HIDING_VERIFIER_MANIFEST: &str =
    "private-graph-rewrite-4x2-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

const DOMAIN: usize = 0;
const SESSION: usize = 1;
const VERSION: usize = 2;
const SHAPE: usize = 3;
const RULE_SLOT: usize = 4;
const OLD_BLIND_BASE: usize = 5;
const NEW_BLIND_BASE: usize = 9;
const RULE_BLIND_BASE: usize = 13;
const SIGMA_BASE: usize = 21;
const SIGMA_INV_BASE: usize = 25;
const RULE_BASE: usize = 31;
const CONTEXT_BASE: usize = 95;
const OLD_STAGE_BASE: usize = 103;
const NEW_STAGE_BASE: usize = 215;
const OLD_SWAP_BASE: usize = 231;
const OLD_CORE_BASE: usize = 237;
const OLD_ROOT_BASE: usize = 245;
const NEW_CORE_BASE: usize = 253;
const NEW_ROOT_BASE: usize = 261;
const RULE0_CORE_BASE: usize = 269;
const RULE0_LEAF_BASE: usize = 277;
const RULE1_CORE_BASE: usize = 285;
const RULE1_LEAF_BASE: usize = 293;
const RULESET_ROOT_BASE: usize = 301;
const INDEX: usize = 309;

const R_ACTIVE: usize = 0;
const R_LABEL: usize = 1;
const R_SRC: usize = 2;
const R_DST: usize = 3;
const R_SRC_B0: usize = 4;
const R_SRC_B1: usize = 5;
const R_DST_B0: usize = 6;
const R_DST_B1: usize = 7;

const E_ACTIVE: usize = 0;
const E_LABEL: usize = 1;
const E_SRC: usize = 2;
const E_DST: usize = 3;

const SWAP_PAIRS: [(usize, usize); 6] = [(0, 1), (1, 2), (2, 3), (0, 1), (1, 2), (0, 1)];
const SIGMA_PAIRS: [(usize, usize); 6] = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];

#[inline]
const fn rule_col(rule: usize, slot: usize, field: usize) -> usize {
    RULE_BASE + 32 * rule + 8 * slot + field
}

#[inline]
const fn context_col(slot: usize, field: usize) -> usize {
    CONTEXT_BASE + 4 * slot + field
}

#[inline]
const fn stage_col(base: usize, stage: usize, slot: usize, field: usize) -> usize {
    base + 16 * stage + 4 * slot + field
}

/// One bounded directed, labelled host edge.  An inactive slot is the unique
/// all-zero padding encoding.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HostEdgeSlot {
    pub active: bool,
    pub label: u8,
    pub src: u8,
    pub dst: u8,
}

impl HostEdgeSlot {
    pub const fn edge(label: u8, src: u8, dst: u8) -> Self {
        Self {
            active: true,
            label,
            src,
            dst,
        }
    }

    pub const fn padding() -> Self {
        Self {
            active: false,
            label: 0,
            src: 0,
            dst: 0,
        }
    }

    fn validate(self, at: &str) -> Result<(), String> {
        for (name, value) in [("label", self.label), ("src", self.src), ("dst", self.dst)] {
            if value >= 16 {
                return Err(format!("{at} {name}={value} is outside Fin 16"));
            }
        }
        if !self.active && (self.label != 0 || self.src != 0 || self.dst != 0) {
            return Err(format!(
                "{at} is inactive but not canonical all-zero padding"
            ));
        }
        Ok(())
    }

    fn felts(self) -> [BabyBear; 4] {
        [
            if self.active {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            },
            BabyBear::new(self.label as u32),
            BabyBear::new(self.src as u32),
            BabyBear::new(self.dst as u32),
        ]
    }
}

/// One bounded rule edge over variables `0..3`.  Inactive slots use the same
/// unique all-zero padding convention.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct RuleEdgeSlot {
    pub active: bool,
    pub label: u8,
    pub src: u8,
    pub dst: u8,
}

impl RuleEdgeSlot {
    pub const fn edge(label: u8, src: u8, dst: u8) -> Self {
        Self {
            active: true,
            label,
            src,
            dst,
        }
    }

    pub const fn padding() -> Self {
        Self {
            active: false,
            label: 0,
            src: 0,
            dst: 0,
        }
    }

    fn validate(self, at: &str) -> Result<(), String> {
        if self.label >= 16 {
            return Err(format!("{at} label={} is outside Fin 16", self.label));
        }
        for (name, value) in [("src", self.src), ("dst", self.dst)] {
            if value >= VARIABLE_COUNT as u8 {
                return Err(format!("{at} {name}={value} is outside Fin 4"));
            }
        }
        if !self.active && (self.label != 0 || self.src != 0 || self.dst != 0) {
            return Err(format!(
                "{at} is inactive but not canonical all-zero padding"
            ));
        }
        Ok(())
    }

    fn felts(self) -> [BabyBear; 4] {
        [
            if self.active {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            },
            BabyBear::new(self.label as u32),
            BabyBear::new(self.src as u32),
            BabyBear::new(self.dst as u32),
        ]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundedGraph {
    pub slots: [HostEdgeSlot; GRAPH_SLOTS],
}

impl BoundedGraph {
    fn validate(self, at: &str) -> Result<(), String> {
        for (slot, edge) in self.slots.into_iter().enumerate() {
            edge.validate(&format!("{at} slot {slot}"))?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundedPattern {
    pub slots: [RuleEdgeSlot; PATTERN_SLOTS],
}

impl BoundedPattern {
    fn validate(self, at: &str) -> Result<(), String> {
        for (slot, edge) in self.slots.into_iter().enumerate() {
            edge.validate(&format!("{at} slot {slot}"))?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundedRule {
    pub lhs: BoundedPattern,
    pub rhs: BoundedPattern,
}

impl BoundedRule {
    fn validate(self, at: &str) -> Result<(), String> {
        self.lhs.validate(&format!("{at} lhs"))?;
        self.rhs.validate(&format!("{at} rhs"))
    }

    fn slots(self) -> [RuleEdgeSlot; 4] {
        [
            self.lhs.slots[0],
            self.lhs.slots[1],
            self.rhs.slots[0],
            self.rhs.slots[1],
        ]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BoundedContext {
    pub slots: [HostEdgeSlot; CONTEXT_SLOTS],
}

impl BoundedContext {
    fn validate(self) -> Result<(), String> {
        for (slot, edge) in self.slots.into_iter().enumerate() {
            edge.validate(&format!("context slot {slot}"))?;
        }
        Ok(())
    }
}

/// Complete private opening of the bounded one-step relation.  Both rules and
/// both rule blindings are present, so the proof opens the full committed
/// two-rule set before privately selecting `rule_slot`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateGraphRewriteWitness {
    pub old_graph: BoundedGraph,
    pub new_graph: BoundedGraph,
    pub rules: [BoundedRule; RULE_COUNT],
    pub sigma: [u8; VARIABLE_COUNT],
    pub context: BoundedContext,
    pub old_blind: [u32; BLIND_WIDTH],
    pub new_blind: [u32; BLIND_WIDTH],
    pub rule_blinds: [[u32; BLIND_WIDTH]; RULE_COUNT],
    pub rule_slot: bool,
}

impl PrivateGraphRewriteWitness {
    pub fn selected_rule(&self) -> BoundedRule {
        self.rules[usize::from(self.rule_slot)]
    }

    /// Validate the exact bounded relation and derive the descriptor's six
    /// adjacent-swap controls.  No caller supplies these bits.
    pub fn validate(&self) -> Result<(), String> {
        self.old_graph.validate("old graph")?;
        self.new_graph.validate("new graph")?;
        self.context.validate()?;
        for (rule, value) in self.rules.into_iter().enumerate() {
            value.validate(&format!("rule {rule}"))?;
        }
        for (var, &node) in self.sigma.iter().enumerate() {
            if node >= 16 {
                return Err(format!("sigma[{var}]={node} is outside Fin 16"));
            }
        }
        for left in 0..VARIABLE_COUNT {
            for right in left + 1..VARIABLE_COUNT {
                if self.sigma[left] == self.sigma[right] {
                    return Err(format!(
                        "sigma is not injective: variables {left} and {right} both map to {}",
                        self.sigma[left]
                    ));
                }
            }
        }
        validate_blind("old graph", self.old_blind)?;
        validate_blind("new graph", self.new_blind)?;
        for (rule, blind) in self.rule_blinds.into_iter().enumerate() {
            validate_blind(&format!("rule {rule}"), blind)?;
        }

        let selected = self.selected_rule();
        if selected.lhs.slots.iter().all(|edge| !edge.active) {
            return Err("selected rule LHS must contain at least one live edge".to_string());
        }

        let lhs = instantiate_pattern(&selected.lhs, self.sigma);
        let rhs = instantiate_pattern(&selected.rhs, self.sigma);
        let old_source = source_stage(self.context, lhs);
        let new_source = source_stage(self.context, rhs);
        if self.new_graph.slots != new_source {
            return Err(
                "new graph slots must equal canonical [context0, context1, rhs0, rhs1] order"
                    .to_string(),
            );
        }
        derive_swap_bits(old_source, self.old_graph.slots)?;
        Ok(())
    }
}

/// Public statement carried by the exact 29-felt descriptor ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub domain: u32,
    pub session: u32,
    pub version: u32,
    pub shape: u32,
    pub index: u32,
    pub ruleset_root: [u32; DIGEST_WIDTH],
    pub old_root: [u32; DIGEST_WIDTH],
    pub new_root: [u32; DIGEST_WIDTH],
}

impl PublicStatement {
    pub fn as_u32_vec(self) -> Vec<u32> {
        let mut out = Vec::with_capacity(PUBLIC_INPUT_COUNT);
        out.extend([
            self.domain,
            self.session,
            self.version,
            self.shape,
            self.index,
        ]);
        out.extend(self.ruleset_root);
        out.extend(self.old_root);
        out.extend(self.new_root);
        out
    }

    pub fn as_felts(self) -> Vec<BabyBear> {
        self.as_u32_vec().into_iter().map(BabyBear::new).collect()
    }

    pub fn validate(self) -> Result<(), String> {
        if self.version != PROTOCOL_VERSION {
            return Err(format!(
                "private graph rewrite version {} != {PROTOCOL_VERSION}",
                self.version
            ));
        }
        if self.shape != SHAPE_ID {
            return Err(format!(
                "private graph rewrite shape {} != {SHAPE_ID}",
                self.shape
            ));
        }
        for (pi, value) in self.as_u32_vec().into_iter().enumerate() {
            if value >= BABYBEAR_P {
                return Err(format!(
                    "private graph rewrite PI {pi}={value} is noncanonical for BabyBear"
                ));
            }
        }
        Ok(())
    }

    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "private graph rewrite expects {PUBLIC_INPUT_COUNT} public inputs, got {}",
                values.len()
            ));
        }
        let statement = Self {
            domain: values[0],
            session: values[1],
            version: values[2],
            shape: values[3],
            index: values[4],
            ruleset_root: values[5..13].try_into().expect("length checked"),
            old_root: values[13..21].try_into().expect("length checked"),
            new_root: values[21..29].try_into().expect("length checked"),
        };
        statement.validate()?;
        Ok(statement)
    }
}

/// Opaque HidingFri proof of the bounded relation.
pub struct PrivateGraphRewriteZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl PrivateGraphRewriteZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|e| format!("private graph rewrite proof encode failed: {e}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|e| format!("private graph rewrite proof decode failed: {e}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(PRIVATE_GRAPH_REWRITE_DESCRIPTOR_JSON)?;
    if desc.name != "private-graph-rewrite-4x2::injective-swapnet-poseidon2-v1"
        || desc.trace_width != TRACE_WIDTH
        || desc.public_input_count != PUBLIC_INPUT_COUNT
    {
        return Err("private graph rewrite emitted descriptor shape drifted".to_string());
    }
    Ok(desc)
}

/// Descriptor/AIR fingerprint over the exact Lean-emitted bytes.
pub fn air_fingerprint() -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg-private-graph-rewrite-air-v1");
    h.update(PRIVATE_GRAPH_REWRITE_DESCRIPTOR_JSON.as_bytes());
    *h.finalize().as_bytes()
}

/// Hiding verifier fingerprint binding the exact AIR, Plonky3 revision, and
/// every exported FRI/extension knob used by `create_zk_config`.
pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg-private-graph-rewrite-hiding-config-v1");
    h.update(HIDING_VERIFIER_MANIFEST.as_bytes());
    h.update(PLONKY3_REV.as_bytes());
    for knob in [
        ZK_FRI_LOG_BLOWUP,
        ZK_FRI_LOG_FINAL_POLY_LEN,
        ZK_FRI_MAX_LOG_ARITY,
        ZK_FRI_NUM_QUERIES,
        ZK_FRI_QUERY_POW_BITS,
        ZK_EXT_DEGREE,
    ] {
        h.update(&(knob as u64).to_le_bytes());
    }
    h.update(&air_fingerprint());
    *h.finalize().as_bytes()
}

/// Canary identity for the forbidden non-hiding verifier family.
pub fn non_hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg-private-graph-rewrite-non-hiding-config-v1");
    h.update(b"DreggStarkConfig|non-hiding FriPcs");
    h.update(PLONKY3_REV.as_bytes());
    h.update(&air_fingerprint());
    *h.finalize().as_bytes()
}

/// Canonical bytes of `ProvingSystemId::Plonky3BabyBearFri` for the pinned rev.
pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut out = vec![0];
    out.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    out.extend_from_slice(PLONKY3_REV.as_bytes());
    out
}

/// Canonical-v2 VK identity, mirrored without a dependency on `dregg-cell`.
pub fn canonical_vk_hash() -> [u8; 32] {
    let verifier_source = hiding_verifier_config_fingerprint();
    let mut verifier = blake3::Hasher::new_derive_key("dregg-verifier-fingerprint-v1");
    verifier.update(&[0]);
    verifier.update(&verifier_source);
    let verifier_canonical = *verifier.finalize().as_bytes();
    let proving_system = proving_system_canonical_bytes();
    let program = PRIVATE_GRAPH_REWRITE_DESCRIPTOR_JSON.as_bytes();

    let mut h = blake3::Hasher::new_derive_key("dregg-vk-v2");
    h.update(&(program.len() as u64).to_le_bytes());
    h.update(program);
    h.update(&air_fingerprint());
    h.update(&verifier_canonical);
    h.update(&(proving_system.len() as u64).to_le_bytes());
    h.update(&proving_system);
    *h.finalize().as_bytes()
}

fn validate_blind(at: &str, blind: [u32; BLIND_WIDTH]) -> Result<(), String> {
    for (lane, value) in blind.into_iter().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "{at} blinding lane {lane}={value} is noncanonical for BabyBear"
            ));
        }
    }
    Ok(())
}

/// Four rejection-sampled canonical BabyBear blind felts from OS entropy.
pub fn fresh_blind4() -> Result<[u32; BLIND_WIDTH], String> {
    let mut blind = [0u32; BLIND_WIDTH];
    for lane in &mut blind {
        let modulus = BABYBEAR_P as u64;
        let accept_below = ((u32::MAX as u64 + 1) / modulus) * modulus;
        loop {
            let mut bytes = [0u8; 4];
            getrandom::fill(&mut bytes)
                .map_err(|e| format!("OS randomness failed for graph blinding: {e}"))?;
            let candidate = u32::from_le_bytes(bytes) as u64;
            if candidate < accept_below {
                *lane = (candidate % modulus) as u32;
                break;
            }
        }
    }
    Ok(blind)
}

fn instantiate_pattern(
    pattern: &BoundedPattern,
    sigma: [u8; VARIABLE_COUNT],
) -> [HostEdgeSlot; PATTERN_SLOTS] {
    pattern.slots.map(|edge| {
        if edge.active {
            HostEdgeSlot::edge(
                edge.label,
                sigma[edge.src as usize],
                sigma[edge.dst as usize],
            )
        } else {
            HostEdgeSlot::padding()
        }
    })
}

fn source_stage(
    context: BoundedContext,
    instantiated: [HostEdgeSlot; PATTERN_SLOTS],
) -> [HostEdgeSlot; GRAPH_SLOTS] {
    [
        context.slots[0],
        context.slots[1],
        instantiated[0],
        instantiated[1],
    ]
}

fn apply_swap_stage(
    mut slots: [HostEdgeSlot; GRAPH_SLOTS],
    stage: usize,
    swap: bool,
) -> [HostEdgeSlot; GRAPH_SLOTS] {
    if swap {
        let (left, right) = SWAP_PAIRS[stage];
        slots.swap(left, right);
    }
    slots
}

/// Derive the descriptor's complete six-control swap witness by exhaustive
/// search.  Sixty-four candidates is preferable to a second permutation
/// algorithm whose convention could drift from the Lean network.
fn derive_swap_bits(
    source: [HostEdgeSlot; GRAPH_SLOTS],
    target: [HostEdgeSlot; GRAPH_SLOTS],
) -> Result<[bool; 6], String> {
    for mask in 0u8..64 {
        let bits = core::array::from_fn(|stage| ((mask >> stage) & 1) == 1);
        let mut current = source;
        for (stage, &bit) in bits.iter().enumerate() {
            current = apply_swap_stage(current, stage, bit);
        }
        if current == target {
            return Ok(bits);
        }
    }
    Err("old graph is not a slot permutation of [context0, context1, lhs0, lhs1]".to_string())
}

fn hash16(inputs: &[BabyBear; 16]) -> [BabyBear; DIGEST_WIDTH] {
    chip_absorb_all_lanes(inputs.len(), inputs)
}

fn edge_block(slots: [HostEdgeSlot; GRAPH_SLOTS]) -> [BabyBear; 16] {
    let mut out = [BabyBear::ZERO; 16];
    for (slot, edge) in slots.into_iter().enumerate() {
        out[4 * slot..4 * slot + 4].copy_from_slice(&edge.felts());
    }
    out
}

fn rule_block(rule: BoundedRule) -> [BabyBear; 16] {
    let mut out = [BabyBear::ZERO; 16];
    for (slot, edge) in rule.slots().into_iter().enumerate() {
        out[4 * slot..4 * slot + 4].copy_from_slice(&edge.felts());
    }
    out
}

fn graph_root(
    core: [BabyBear; DIGEST_WIDTH],
    blind: [u32; BLIND_WIDTH],
    domain: u32,
    session: u32,
) -> [BabyBear; DIGEST_WIDTH] {
    let mut inputs = [BabyBear::ZERO; 16];
    inputs[0..8].copy_from_slice(&core);
    for (lane, value) in blind.into_iter().enumerate() {
        inputs[8 + lane] = BabyBear::new(value);
    }
    inputs[12] = BabyBear::new(domain);
    inputs[13] = BabyBear::new(session);
    inputs[14] = BabyBear::new(PROTOCOL_VERSION);
    inputs[15] = BabyBear::new(GRAPH_STATE_TAG);
    hash16(&inputs)
}

fn rule_leaf(
    core: [BabyBear; DIGEST_WIDTH],
    blind: [u32; BLIND_WIDTH],
    domain: u32,
    rule: usize,
) -> [BabyBear; DIGEST_WIDTH] {
    let mut inputs = [BabyBear::ZERO; 16];
    inputs[0..8].copy_from_slice(&core);
    for (lane, value) in blind.into_iter().enumerate() {
        inputs[8 + lane] = BabyBear::new(value);
    }
    inputs[12] = BabyBear::new(domain);
    inputs[13] = BabyBear::new(PROTOCOL_VERSION);
    inputs[14] = BabyBear::new(SHAPE_ID);
    inputs[15] = BabyBear::new(rule as u32);
    hash16(&inputs)
}

fn put_digest(row: &mut [BabyBear], base: usize, digest: [BabyBear; DIGEST_WIDTH]) {
    row[base..base + DIGEST_WIDTH].copy_from_slice(&digest);
}

fn put_stage(row: &mut [BabyBear], base: usize, stage: usize, slots: [HostEdgeSlot; GRAPH_SLOTS]) {
    for (slot, edge) in slots.into_iter().enumerate() {
        row[stage_col(base, stage, slot, E_ACTIVE)] = if edge.active {
            BabyBear::ONE
        } else {
            BabyBear::ZERO
        };
        row[stage_col(base, stage, slot, E_LABEL)] = BabyBear::new(edge.label as u32);
        row[stage_col(base, stage, slot, E_SRC)] = BabyBear::new(edge.src as u32);
        row[stage_col(base, stage, slot, E_DST)] = BabyBear::new(edge.dst as u32);
    }
}

fn build_row(
    domain: u32,
    session: u32,
    index: u32,
    witness: &PrivateGraphRewriteWitness,
) -> Result<(Vec<BabyBear>, PublicStatement, [bool; 6]), String> {
    for (name, value) in [("domain", domain), ("session", session), ("index", index)] {
        if value >= BABYBEAR_P {
            return Err(format!(
                "private graph rewrite {name}={value} is noncanonical for BabyBear"
            ));
        }
    }
    witness.validate()?;

    let selected = witness.selected_rule();
    let lhs = instantiate_pattern(&selected.lhs, witness.sigma);
    let rhs = instantiate_pattern(&selected.rhs, witness.sigma);
    let old_source = source_stage(witness.context, lhs);
    let new_source = source_stage(witness.context, rhs);
    let swap_bits = derive_swap_bits(old_source, witness.old_graph.slots)?;

    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[DOMAIN] = BabyBear::new(domain);
    row[SESSION] = BabyBear::new(session);
    row[VERSION] = BabyBear::new(PROTOCOL_VERSION);
    row[SHAPE] = BabyBear::new(SHAPE_ID);
    row[RULE_SLOT] = if witness.rule_slot {
        BabyBear::ONE
    } else {
        BabyBear::ZERO
    };
    for lane in 0..BLIND_WIDTH {
        row[OLD_BLIND_BASE + lane] = BabyBear::new(witness.old_blind[lane]);
        row[NEW_BLIND_BASE + lane] = BabyBear::new(witness.new_blind[lane]);
        for rule in 0..RULE_COUNT {
            row[RULE_BLIND_BASE + 4 * rule + lane] = BabyBear::new(witness.rule_blinds[rule][lane]);
        }
    }
    for (var, node) in witness.sigma.into_iter().enumerate() {
        row[SIGMA_BASE + var] = BabyBear::new(node as u32);
    }
    for (pair, (left, right)) in SIGMA_PAIRS.into_iter().enumerate() {
        let diff = row[SIGMA_BASE + left] - row[SIGMA_BASE + right];
        row[SIGMA_INV_BASE + pair] = diff
            .inverse()
            .expect("witness validation proved the substitution injective");
    }

    for (rule_index, rule) in witness.rules.into_iter().enumerate() {
        for (slot, edge) in rule.slots().into_iter().enumerate() {
            row[rule_col(rule_index, slot, R_ACTIVE)] = if edge.active {
                BabyBear::ONE
            } else {
                BabyBear::ZERO
            };
            row[rule_col(rule_index, slot, R_LABEL)] = BabyBear::new(edge.label as u32);
            row[rule_col(rule_index, slot, R_SRC)] = BabyBear::new(edge.src as u32);
            row[rule_col(rule_index, slot, R_DST)] = BabyBear::new(edge.dst as u32);
            row[rule_col(rule_index, slot, R_SRC_B0)] = BabyBear::new((edge.src & 1) as u32);
            row[rule_col(rule_index, slot, R_SRC_B1)] = BabyBear::new(((edge.src >> 1) & 1) as u32);
            row[rule_col(rule_index, slot, R_DST_B0)] = BabyBear::new((edge.dst & 1) as u32);
            row[rule_col(rule_index, slot, R_DST_B1)] = BabyBear::new(((edge.dst >> 1) & 1) as u32);
        }
    }
    for (slot, edge) in witness.context.slots.into_iter().enumerate() {
        let fields = edge.felts();
        for (field, value) in fields.into_iter().enumerate() {
            row[context_col(slot, field)] = value;
        }
    }

    let mut old_stage = old_source;
    put_stage(&mut row, OLD_STAGE_BASE, 0, old_stage);
    for (stage, bit) in swap_bits.into_iter().enumerate() {
        row[OLD_SWAP_BASE + stage] = if bit { BabyBear::ONE } else { BabyBear::ZERO };
        old_stage = apply_swap_stage(old_stage, stage, bit);
        put_stage(&mut row, OLD_STAGE_BASE, stage + 1, old_stage);
    }
    debug_assert_eq!(old_stage, witness.old_graph.slots);
    put_stage(&mut row, NEW_STAGE_BASE, 0, new_source);

    let old_core = hash16(&edge_block(old_stage));
    let old_root = graph_root(old_core, witness.old_blind, domain, session);
    let new_core = hash16(&edge_block(new_source));
    let new_root = graph_root(new_core, witness.new_blind, domain, session);
    put_digest(&mut row, OLD_CORE_BASE, old_core);
    put_digest(&mut row, OLD_ROOT_BASE, old_root);
    put_digest(&mut row, NEW_CORE_BASE, new_core);
    put_digest(&mut row, NEW_ROOT_BASE, new_root);

    let rule_cores = witness.rules.map(|rule| hash16(&rule_block(rule)));
    let rule_leaves: [[BabyBear; DIGEST_WIDTH]; RULE_COUNT] = core::array::from_fn(|rule| {
        rule_leaf(rule_cores[rule], witness.rule_blinds[rule], domain, rule)
    });
    put_digest(&mut row, RULE0_CORE_BASE, rule_cores[0]);
    put_digest(&mut row, RULE0_LEAF_BASE, rule_leaves[0]);
    put_digest(&mut row, RULE1_CORE_BASE, rule_cores[1]);
    put_digest(&mut row, RULE1_LEAF_BASE, rule_leaves[1]);
    let mut ruleset_inputs = [BabyBear::ZERO; 16];
    ruleset_inputs[0..8].copy_from_slice(&rule_leaves[0]);
    ruleset_inputs[8..16].copy_from_slice(&rule_leaves[1]);
    let ruleset_root = hash16(&ruleset_inputs);
    put_digest(&mut row, RULESET_ROOT_BASE, ruleset_root);
    row[INDEX] = BabyBear::new(index);

    let public = PublicStatement {
        domain,
        session,
        version: PROTOCOL_VERSION,
        shape: SHAPE_ID,
        index,
        ruleset_root: ruleset_root.map(BabyBear::as_u32),
        old_root: old_root.map(BabyBear::as_u32),
        new_root: new_root.map(BabyBear::as_u32),
    };
    Ok((row, public, swap_bits))
}

/// Compute the exact public statement without proving.
pub fn statement(
    domain: u32,
    session: u32,
    index: u32,
    witness: &PrivateGraphRewriteWitness,
) -> Result<PublicStatement, String> {
    build_row(domain, session, index, witness).map(|(_, public, _)| public)
}

/// Build the exact four-row constant trace authored in Lean.
pub fn trace_and_public(
    domain: u32,
    session: u32,
    index: u32,
    witness: &PrivateGraphRewriteWitness,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let (row, public, _) = build_row(domain, session, index, witness)?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((descriptor()?, trace, public))
}

/// Produce the privacy-facing proof through `HidingFriPcs` with fresh prover
/// randomness.  No public non-hiding proof API is exposed.
pub fn prove_zk(
    domain: u32,
    session: u32,
    index: u32,
    witness: &PrivateGraphRewriteWitness,
) -> Result<(PrivateGraphRewriteZkProof, PublicStatement), String> {
    let (desc, trace, public) = trace_and_public(domain, session, index, witness)?;
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &create_zk_config(),
    )?;
    Ok((PrivateGraphRewriteZkProof { proof }, public))
}

pub fn verify_zk(
    proof: &PrivateGraphRewriteZkProof,
    public: PublicStatement,
) -> Result<(), String> {
    public.validate()?;
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &public.as_felts(),
        &create_zk_config(),
    )
}

pub fn verify_postcard(proof_bytes: &[u8], public_values: &[u32]) -> Result<(), String> {
    let proof = PrivateGraphRewriteZkProof::from_postcard(proof_bytes)?;
    verify_zk(&proof, PublicStatement::try_from_u32s(public_values)?)
}

/// Decode the custom-registry byte ABI (`u32` little-endian per PI), refusing
/// noncanonical field representatives before proof verification.
pub fn decode_public_input_bytes(bytes: &[u8]) -> Result<Vec<u32>, String> {
    if bytes.len() != 4 * PUBLIC_INPUT_COUNT {
        return Err(format!(
            "private graph rewrite PI bytes must be {}, got {}",
            4 * PUBLIC_INPUT_COUNT,
            bytes.len()
        ));
    }
    bytes
        .chunks_exact(4)
        .map(|chunk| {
            let value = u32::from_le_bytes(chunk.try_into().expect("chunk width"));
            if value >= BABYBEAR_P {
                Err(format!("noncanonical BabyBear public input {value}"))
            } else {
                Ok(value)
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pattern(slots: [RuleEdgeSlot; 2]) -> BoundedPattern {
        BoundedPattern { slots }
    }

    fn fixture() -> PrivateGraphRewriteWitness {
        let sigma = [4, 5, 6, 7];
        let context = BoundedContext {
            slots: [HostEdgeSlot::edge(4, 7, 8), HostEdgeSlot::edge(5, 8, 9)],
        };
        let rule0 = BoundedRule {
            lhs: pattern([RuleEdgeSlot::edge(1, 0, 1), RuleEdgeSlot::padding()]),
            rhs: pattern([RuleEdgeSlot::edge(2, 0, 1), RuleEdgeSlot::edge(3, 1, 2)]),
        };
        let rule1 = BoundedRule {
            lhs: pattern([RuleEdgeSlot::edge(6, 2, 3), RuleEdgeSlot::padding()]),
            rhs: pattern([RuleEdgeSlot::edge(7, 3, 2), RuleEdgeSlot::padding()]),
        };
        let lhs = instantiate_pattern(&rule0.lhs, sigma);
        let rhs = instantiate_pattern(&rule0.rhs, sigma);
        let old_source = source_stage(context, lhs);
        let old_slots = [old_source[2], old_source[0], old_source[3], old_source[1]];
        let new_slots = source_stage(context, rhs);
        PrivateGraphRewriteWitness {
            old_graph: BoundedGraph { slots: old_slots },
            new_graph: BoundedGraph { slots: new_slots },
            rules: [rule0, rule1],
            sigma,
            context,
            old_blind: [101, 102, 103, 104],
            new_blind: [201, 202, 203, 204],
            rule_blinds: [[301, 302, 303, 304], [401, 402, 403, 404]],
            rule_slot: false,
        }
    }

    #[test]
    fn descriptor_shape_swapnet_and_public_abi_are_exact() {
        let witness = fixture();
        witness.validate().expect("valid injective bounded rewrite");
        let desc = descriptor().expect("Lean-emitted descriptor parses");
        assert_eq!(desc.trace_width, TRACE_WIDTH);
        assert_eq!(desc.public_input_count, PUBLIC_INPUT_COUNT);
        assert_ne!(air_fingerprint(), hiding_verifier_config_fingerprint());
        assert_ne!(
            hiding_verifier_config_fingerprint(),
            non_hiding_verifier_config_fingerprint()
        );

        let (row, public, swap_bits) = build_row(11, 77, 9, &witness).unwrap();
        assert_eq!(row.len(), TRACE_WIDTH);
        assert!(swap_bits.iter().any(|bit| *bit));
        assert_eq!(public.as_u32_vec().len(), PUBLIC_INPUT_COUNT);
        assert_eq!(&public.as_u32_vec()[5..13], &public.ruleset_root);
        assert_eq!(&public.as_u32_vec()[13..21], &public.old_root);
        assert_eq!(&public.as_u32_vec()[21..29], &public.new_root);
        let (_, trace, _) = trace_and_public(11, 77, 9, &witness).unwrap();
        assert_eq!(trace.len(), TRACE_HEIGHT);
        assert!(trace.windows(2).all(|rows| rows[0] == rows[1]));
    }

    #[test]
    fn validation_refuses_noninjective_padding_and_noncanonical_output_order() {
        let mut bad_sigma = fixture();
        bad_sigma.sigma[3] = bad_sigma.sigma[2];
        assert!(bad_sigma.validate().unwrap_err().contains("not injective"));

        let mut dirty_padding = fixture();
        dirty_padding.rules[0].lhs.slots[1].label = 1;
        assert!(
            dirty_padding
                .validate()
                .unwrap_err()
                .contains("not canonical all-zero padding")
        );

        let mut permuted_output = fixture();
        permuted_output.new_graph.slots.swap(0, 1);
        assert!(
            permuted_output
                .validate()
                .unwrap_err()
                .contains("canonical [context0")
        );

        let mut wrong_old_multiset = fixture();
        wrong_old_multiset.old_graph.slots[0] = HostEdgeSlot::edge(15, 1, 2);
        assert!(
            wrong_old_multiset
                .validate()
                .unwrap_err()
                .contains("not a slot permutation")
        );

        let mut empty_lhs = fixture();
        empty_lhs.rules[0].lhs.slots = [RuleEdgeSlot::padding(); 2];
        assert!(empty_lhs.validate().unwrap_err().contains("at least one"));

        let mut bad_blind = fixture();
        bad_blind.rule_blinds[1][3] = BABYBEAR_P;
        assert!(bad_blind.validate().unwrap_err().contains("noncanonical"));
    }

    #[test]
    fn every_committed_opening_family_binds_its_root() {
        let witness = fixture();
        let public = statement(11, 77, 9, &witness).unwrap();

        let mut old_reblind = witness.clone();
        old_reblind.old_blind[0] += 1;
        let old_changed = statement(11, 77, 9, &old_reblind).unwrap();
        assert_ne!(old_changed.old_root, public.old_root);
        assert_eq!(old_changed.new_root, public.new_root);
        assert_eq!(old_changed.ruleset_root, public.ruleset_root);

        let mut new_reblind = witness.clone();
        new_reblind.new_blind[3] += 1;
        let new_changed = statement(11, 77, 9, &new_reblind).unwrap();
        assert_ne!(new_changed.new_root, public.new_root);
        assert_eq!(new_changed.old_root, public.old_root);

        let mut other_rule_opening = witness.clone();
        other_rule_opening.rules[1].rhs.slots[0].label ^= 1;
        let rules_changed = statement(11, 77, 9, &other_rule_opening).unwrap();
        assert_ne!(rules_changed.ruleset_root, public.ruleset_root);
        assert_eq!(rules_changed.old_root, public.old_root);
        assert_eq!(rules_changed.new_root, public.new_root);

        let new_session = statement(11, 78, 9, &witness).unwrap();
        assert_ne!(new_session.old_root, public.old_root);
        assert_ne!(new_session.new_root, public.new_root);
        assert_eq!(new_session.ruleset_root, public.ruleset_root);
    }

    #[test]
    fn hiding_proof_verifies_and_every_public_family_tamper_refuses() {
        let (proof, public) = prove_zk(11, 77, 9, &fixture()).expect("honest hiding proof");
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

        for pi in [0usize, 1, 4, 5, 13, 21] {
            let mut values = public.as_u32_vec();
            values[pi] = (values[pi] + 1) % BABYBEAR_P;
            let tampered = PublicStatement::try_from_u32s(&values).unwrap();
            assert!(verify_zk(&proof, tampered).is_err(), "PI {pi} must bind");
        }

        let proof_bytes = proof.to_postcard().expect("postcard proof");
        verify_postcard(&proof_bytes, &public.as_u32_vec()).expect("postcard roundtrip");
        let mut corrupt = proof_bytes;
        let at = corrupt.len() / 2;
        corrupt[at] ^= 1;
        assert!(verify_postcard(&corrupt, &public.as_u32_vec()).is_err());

        let mut bytes: Vec<u8> = public
            .as_u32_vec()
            .into_iter()
            .flat_map(u32::to_le_bytes)
            .collect();
        assert_eq!(decode_public_input_bytes(&bytes).unwrap().len(), 29);
        bytes[0..4].copy_from_slice(&BABYBEAR_P.to_le_bytes());
        assert!(decode_public_input_bytes(&bytes).is_err());
    }
}
