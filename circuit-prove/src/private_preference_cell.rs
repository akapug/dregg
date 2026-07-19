//! Cell-bound hiding private-preference custom proof.
//!
//! The relation is the exact Lean-emitted
//! `PrivatePreferenceCellDescriptor`; Rust only fills its fixed columns.  Its
//! public inputs are canonically
//! `[old_commit8 || new_commit8 || session || rule || ballot_root8 || winner]`.
//! PI 26 is the app-root scalar connected by the custom recursion fold to the
//! decision cell's committed field 0.

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::effect_vm::custom_state_binding::AppRootBinding;
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{
    DreggZkStarkConfig, ZK_EXT_DEGREE, ZK_FRI_LOG_BLOWUP, ZK_FRI_LOG_FINAL_POLY_LEN,
    ZK_FRI_MAX_LOG_ARITY, ZK_FRI_NUM_QUERIES, ZK_FRI_QUERY_POW_BITS, create_zk_config,
};

use crate::joint_turn_aggregation::{CustomIr2VkRecipe, CustomIr2WitnessBundle};
use crate::private_preference::{
    DIGEST_WIDTH, PrivatePreferenceWitness, PublicStatement, trace_and_public,
};

/// Exact Lean-emitted cell descriptor bytes.  These bytes are also the
/// canonical v2 VK `program_bytes`; a different descriptor therefore has a
/// different registry key before proof verification begins.
pub const PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/private-preference-cell-n4k4.json");

pub const CELL_TRACE_WIDTH: usize = 134;
pub const CELL_PUBLIC_INPUT_COUNT: usize = 27;
pub const CELL_APP_PI_BASE: usize = 16;
pub const WINNER_PI: usize = 26;
pub const DECISION_WINNER_FIELD_KEY: usize = 0;
pub const PLONKY3_REV: &str = "82cfad73cd734d37a0d51953094f970c531817ec";

/// Stable manifest of the exact hiding verifier/config family.  The numerical
/// knobs below are also hashed by [`hiding_verifier_config_fingerprint`].
pub const HIDING_VERIFIER_MANIFEST: &str =
    "private-preference-cell-v1|BabyBear|Poseidon2-W16|HidingFriPcs|salt=4|random-codewords=4";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CellPublicStatement {
    pub old_commit: [u32; DIGEST_WIDTH],
    pub new_commit: [u32; DIGEST_WIDTH],
    pub preference: PublicStatement,
}

impl CellPublicStatement {
    pub fn as_u32_vec(self) -> Vec<u32> {
        let mut out = Vec::with_capacity(CELL_PUBLIC_INPUT_COUNT);
        out.extend(self.old_commit);
        out.extend(self.new_commit);
        out.extend(self.preference.as_felts().map(BabyBear::as_u32));
        out
    }

    pub fn as_felts(self) -> Vec<BabyBear> {
        self.as_u32_vec().into_iter().map(BabyBear::new).collect()
    }

    pub fn validate(self) -> Result<(), String> {
        for (side, roots) in [("old", self.old_commit), ("new", self.new_commit)] {
            for (lane, value) in roots.into_iter().enumerate() {
                if value >= BABYBEAR_P {
                    return Err(format!(
                        "{side} commitment lane {lane}={value} is noncanonical for BabyBear"
                    ));
                }
            }
        }
        self.preference.validate_shape()
    }

    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != CELL_PUBLIC_INPUT_COUNT {
            return Err(format!(
                "private-preference cell expects {CELL_PUBLIC_INPUT_COUNT} public inputs, got {}",
                values.len()
            ));
        }
        let old_commit = values[0..8].try_into().expect("length checked");
        let new_commit = values[8..16].try_into().expect("length checked");
        let ballot_root = values[18..26].try_into().expect("length checked");
        let statement = Self {
            old_commit,
            new_commit,
            preference: PublicStatement {
                session: values[16],
                rule: values[17],
                ballot_root,
                winner: values[26],
            },
        };
        statement.validate()?;
        Ok(statement)
    }
}

/// Hiding proof verified by the executor-side custom registry.  The recursion
/// fold intentionally mints a second proof of the same descriptor from retained
/// trace rows under `DreggRecursionConfig`.
pub struct PrivatePreferenceCellZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl PrivatePreferenceCellZkProof {
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|e| format!("private-preference cell proof encode failed: {e}"))
    }

    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|e| format!("private-preference cell proof decode failed: {e}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let desc = parse_vm_descriptor2(PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON)?;
    if desc.name != "private-preference-cell-n4k4::score2-wide-poseidon2-v1"
        || desc.trace_width != CELL_TRACE_WIDTH
        || desc.public_input_count != CELL_PUBLIC_INPUT_COUNT
    {
        return Err("private-preference cell emitted descriptor shape drifted".to_string());
    }
    Ok(desc)
}

/// Descriptor/AIR fingerprint: domain-separated exact emitted bytes.
pub fn air_fingerprint() -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key("dregg-private-preference-cell-air-v1");
    h.update(PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON.as_bytes());
    *h.finalize().as_bytes()
}

/// Dedicated verifier/config fingerprint.  This is deliberately distinct from
/// the descriptor fingerprint: it binds HidingFriPcs, the pinned Plonky3
/// revision, and every exported FRI/extension knob used by `create_zk_config`.
pub fn hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut h =
        blake3::Hasher::new_derive_key("dregg-private-preference-cell-hiding-verifier-config-v1");
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

/// Canary fingerprint for the non-hiding verifier family.  It must never equal
/// the registered hiding fingerprint.
pub fn non_hiding_verifier_config_fingerprint() -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(
        "dregg-private-preference-cell-non-hiding-verifier-config-v1",
    );
    h.update(b"DreggStarkConfig|non-hiding FriPcs");
    h.update(PLONKY3_REV.as_bytes());
    h.update(&air_fingerprint());
    *h.finalize().as_bytes()
}

/// Canonical bytes of `ProvingSystemId::Plonky3BabyBearFri` for the pinned
/// revision, mirrored here to keep the prove crate independent of `dregg-cell`.
pub fn proving_system_canonical_bytes() -> Vec<u8> {
    let mut out = vec![0];
    out.extend_from_slice(&(PLONKY3_REV.len() as u64).to_le_bytes());
    out.extend_from_slice(PLONKY3_REV.as_bytes());
    out
}

/// Exact canonical-v2 recipe shared by executor registration and the retained
/// direct-IR2 recursion witness.
pub fn vk_recipe() -> CustomIr2VkRecipe {
    CustomIr2VkRecipe::source_hash(
        PRIVATE_PREFERENCE_CELL_DESCRIPTOR_JSON.as_bytes().to_vec(),
        air_fingerprint(),
        hiding_verifier_config_fingerprint(),
        proving_system_canonical_bytes(),
    )
}

pub fn canonical_vk_hash() -> [u8; 32] {
    vk_recipe().canonical_vk_hash()
}

fn trace_and_statement(
    session: u32,
    witness: &PrivatePreferenceWitness,
    old_commit: [u32; DIGEST_WIDTH],
    new_commit: [u32; DIGEST_WIDTH],
) -> Result<
    (
        EffectVmDescriptor2,
        Vec<Vec<BabyBear>>,
        CellPublicStatement,
        Vec<BabyBear>,
    ),
    String,
> {
    let (_base_desc, mut trace, preference) = trace_and_public(session, witness)?;
    let public = CellPublicStatement {
        old_commit,
        new_commit,
        preference,
    };
    public.validate()?;
    for row in &mut trace {
        row.extend(old_commit.map(BabyBear::new));
        row.extend(new_commit.map(BabyBear::new));
        debug_assert_eq!(row.len(), CELL_TRACE_WIDTH);
    }
    let pis = public.as_felts();
    Ok((descriptor()?, trace, public, pis))
}

/// Prove the hiding cell relation and retain the exact descriptor/trace bundle
/// needed by the direct-IR2 recursion carrier.
pub fn prove_zk(
    session: u32,
    witness: &PrivatePreferenceWitness,
    old_commit: [u32; DIGEST_WIDTH],
    new_commit: [u32; DIGEST_WIDTH],
) -> Result<
    (
        PrivatePreferenceCellZkProof,
        CellPublicStatement,
        CustomIr2WitnessBundle,
    ),
    String,
> {
    let (desc, trace, public, pis) = trace_and_statement(session, witness, old_commit, new_commit)?;
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &desc,
        &trace,
        &pis,
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    let retained = CustomIr2WitnessBundle {
        descriptor: desc,
        base_trace: trace,
        public_inputs: pis,
        vk_recipe: vk_recipe(),
        app_root_binding: AppRootBinding {
            app_root_pi_offset: WINNER_PI,
            app_root_len: 1,
            field_key: DECISION_WINNER_FIELD_KEY,
        },
    };
    Ok((PrivatePreferenceCellZkProof { proof }, public, retained))
}

pub fn verify_zk(
    proof: &PrivatePreferenceCellZkProof,
    public: CellPublicStatement,
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
    let proof = PrivatePreferenceCellZkProof::from_postcard(proof_bytes)?;
    verify_zk(&proof, CellPublicStatement::try_from_u32s(public_values)?)
}

/// Decode the canonical custom registry byte ABI (`u32` little-endian per PI).
pub fn decode_public_input_bytes(bytes: &[u8]) -> Result<Vec<u32>, String> {
    if bytes.len() != 4 * CELL_PUBLIC_INPUT_COUNT {
        return Err(format!(
            "private-preference custom PI bytes must be {}, got {}",
            4 * CELL_PUBLIC_INPUT_COUNT,
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
    use crate::private_preference::PrivateBallot;
    use crate::private_preference::{OPTION_COUNT, RULE_ID};

    fn witness() -> PrivatePreferenceWitness {
        let ballots = [
            PrivateBallot::try_new([3, 2, 0, 1]).unwrap(),
            PrivateBallot::try_new([2, 3, 0, 1]).unwrap(),
            PrivateBallot::try_new([0, 3, 2, 1]).unwrap(),
            PrivateBallot::try_new([1, 2, 3, 0]).unwrap(),
        ];
        PrivatePreferenceWitness::try_from_ballots_with_blinding(
            &ballots,
            core::array::from_fn(|i| 900 + i as u32),
        )
        .unwrap()
    }

    #[test]
    fn descriptor_and_vk_config_are_exact_and_hiding_specific() {
        let desc = descriptor().unwrap();
        assert_eq!(desc.public_input_count, 27);
        assert_eq!(desc.trace_width, 134);
        assert_ne!(air_fingerprint(), hiding_verifier_config_fingerprint());
        assert_ne!(
            hiding_verifier_config_fingerprint(),
            non_hiding_verifier_config_fingerprint()
        );
        assert_eq!(vk_recipe().canonical_vk_hash(), canonical_vk_hash());
        vk_recipe().require_exact_descriptor(&desc).unwrap();
    }

    #[test]
    fn canonical_recipe_refuses_wrong_descriptor_with_same_public_abi() {
        let mut wrong = descriptor().unwrap();
        wrong.name.push_str("-substituted");
        let err = vk_recipe().require_exact_descriptor(&wrong).unwrap_err();
        assert!(err.contains("differs from canonical-v2 program bytes"));
    }

    #[test]
    fn cell_statement_layout_is_canonical() {
        let old = core::array::from_fn(|i| 10 + i as u32);
        let new = core::array::from_fn(|i| 20 + i as u32);
        let (_, _, public, pis) = trace_and_statement(77, &witness(), old, new).unwrap();
        assert_eq!(&pis[0..8], &old.map(BabyBear::new));
        assert_eq!(&pis[8..16], &new.map(BabyBear::new));
        assert_eq!(pis[16], BabyBear::new(77));
        assert_eq!(pis[17], BabyBear::new(RULE_ID));
        assert_eq!(pis[WINNER_PI].as_u32(), public.preference.winner);
        assert!((public.preference.winner as usize) < OPTION_COUNT);
    }
}
