//! Hiding prover/verifier for the Lean-authored Warden private-quest graph AIR.
//!
//! The reusable [`crate::private_graph_rewrite`] relation permits two arbitrary
//! privately committed rules.  This specialization uses the same witness and
//! 29-felt history ABI, but its emitted AIR fixes every private rule column to
//! the actual two-step Warden quest.  Consequently a valid receipt proves the
//! authored game reduction, not merely a reduction in a producer-chosen hidden
//! ruleset.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

use crate::private_graph_rewrite::{
    BoundedPattern, BoundedRule, PUBLIC_INPUT_COUNT, PrivateGraphRewriteWitness, PublicStatement,
    RuleEdgeSlot, TRACE_WIDTH,
};

pub const PRIVATE_QUEST_GRAPH_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-quest-graph-4x2.json");
pub const PLONKY3_REV: &str = crate::private_graph_rewrite::PLONKY3_REV;
pub const HIDING_VERIFIER_MANIFEST: &str = "private-quest-graph-4x2-warden-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

const LABEL_SEALED_APPROACH: u8 = 1;
const LABEL_REVEALED_TRAIL: u8 = 2;
const LABEL_ENGAGED_WARDEN: u8 = 3;
const LABEL_BROKEN_SEAL: u8 = 8;

const fn pattern(slots: [RuleEdgeSlot; 2]) -> BoundedPattern {
    BoundedPattern { slots }
}

/// The exact rules pinned by the Lean descriptor.  Exposing this constructor
/// lets the witness producer share one constant definition with the verifier
/// surface; security does not rely on the Rust equality check below—the 64 AIR
/// gates independently enforce it.
pub const fn warden_rules() -> [BoundedRule; 2] {
    [
        BoundedRule {
            lhs: pattern([
                RuleEdgeSlot::edge(LABEL_SEALED_APPROACH, 0, 1),
                RuleEdgeSlot::padding(),
            ]),
            rhs: pattern([
                RuleEdgeSlot::edge(LABEL_REVEALED_TRAIL, 0, 1),
                RuleEdgeSlot::edge(LABEL_ENGAGED_WARDEN, 1, 2),
            ]),
        },
        BoundedRule {
            lhs: pattern([
                RuleEdgeSlot::edge(LABEL_REVEALED_TRAIL, 0, 1),
                RuleEdgeSlot::edge(LABEL_ENGAGED_WARDEN, 1, 2),
            ]),
            rhs: pattern([
                RuleEdgeSlot::edge(LABEL_BROKEN_SEAL, 0, 2),
                RuleEdgeSlot::padding(),
            ]),
        },
    ]
}

pub struct PrivateQuestGraphZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl PrivateQuestGraphZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private quest graph proof encode failed: {error}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private quest graph proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(PRIVATE_QUEST_GRAPH_DESCRIPTOR_JSON)?;
    if descriptor.name != "private-quest-graph-4x2::warden-fixed-rules-hiding-v1"
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PUBLIC_INPUT_COUNT
    {
        return Err("private quest graph emitted descriptor shape drifted".to_string());
    }
    Ok(descriptor)
}

pub fn air_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-quest-graph-air-v1");
    hasher.update(PRIVATE_QUEST_GRAPH_DESCRIPTOR_JSON.as_bytes());
    *hasher.finalize().as_bytes()
}

pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut hasher = blake3::Hasher::new_derive_key("dregg-private-quest-graph-hiding-config-v1");
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

pub fn canonical_vk_hash() -> [u8; 32] {
    let verifier_source = hiding_verifier_config_fingerprint();
    let mut verifier = blake3::Hasher::new_derive_key("dregg-verifier-fingerprint-v1");
    verifier.update(&[0]);
    verifier.update(&verifier_source);
    let verifier_canonical = *verifier.finalize().as_bytes();
    let proving_system = crate::private_graph_rewrite::proving_system_canonical_bytes();
    let program = PRIVATE_QUEST_GRAPH_DESCRIPTOR_JSON.as_bytes();

    let mut hasher = blake3::Hasher::new_derive_key("dregg-vk-v2");
    hasher.update(&(program.len() as u64).to_le_bytes());
    hasher.update(program);
    hasher.update(&air_fingerprint());
    hasher.update(&verifier_canonical);
    hasher.update(&(proving_system.len() as u64).to_le_bytes());
    hasher.update(&proving_system);
    *hasher.finalize().as_bytes()
}

pub fn prove_zk(
    domain: u32,
    session: u32,
    index: u32,
    witness: &PrivateGraphRewriteWitness,
) -> Result<(PrivateQuestGraphZkProof, PublicStatement), String> {
    if witness.rules != warden_rules() {
        return Err("private quest witness attempted a non-Warden ruleset".to_string());
    }
    let (_, trace, public) =
        crate::private_graph_rewrite::trace_and_public(domain, session, index, witness)?;
    let proof = prove_vm_descriptor2_for_config(
        &descriptor()?,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &create_zk_config(),
    )?;
    Ok((PrivateQuestGraphZkProof { proof }, public))
}

pub fn verify_zk(proof: &PrivateQuestGraphZkProof, public: PublicStatement) -> Result<(), String> {
    public.validate()?;
    verify_vm_descriptor2_with_config(
        &descriptor()?,
        &proof.proof,
        &public.as_felts(),
        &create_zk_config(),
    )
}

pub fn verify_postcard(proof_bytes: &[u8], public_values: &[u32]) -> Result<(), String> {
    let proof = PrivateQuestGraphZkProof::from_postcard(proof_bytes)?;
    verify_zk(&proof, PublicStatement::try_from_u32s(public_values)?)
}
