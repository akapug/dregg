//! Fixed bounded private AMM transition proof producer.
//!
//! The relation and descriptor are authored in Lean at
//! `Market/DarkAmmPrivateDescriptor.lean`. This module validates canonical host
//! inputs, fills that exact layout, and proves only through `HidingFriPcs`.
//! Public inputs are `(session, rule, k, old_root[0..8), new_root[0..8))`.
//! Old reserves, trade amounts, post reserves, and both eight-felt commitment
//! blinds remain witness columns.
//!
//! This is a Tier-1/operator-visible receipt: the proof hides the witness from
//! proof consumers, while the process constructing the trace sees it. It does
//! not claim BFV ciphertext same-opening, no-single-viewer custody, or a
//! ledger/state-cell weld.

use dregg_circuit::descriptor_ir2::chip_absorb_all_lanes;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2, prove_vm_descriptor2_for_config, verify_vm_descriptor2_with_config,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::stark_zk::{DreggZkStarkConfig, create_zk_config};

/// Exact artifact emitted by `Market.DarkAmmPrivateDescriptor`.
pub const DARK_AMM_PRIVATE_DESCRIPTOR_JSON: &str =
    include_str!("../../circuit/descriptors/by-name/dark-amm-private-v1.json");

pub const RULE_ID: u32 = 1_145_916_752;
/// One domain for a hidden AMM state commitment. A produced `new_root` must be
/// usable verbatim as the next transition's `old_root`.
pub const STATE_ROOT_DOMAIN_TAG: u32 = 1_145_916_751;
pub const OLD_ROOT_DOMAIN_TAG: u32 = STATE_ROOT_DOMAIN_TAG;
pub const NEW_ROOT_DOMAIN_TAG: u32 = STATE_ROOT_DOMAIN_TAG;
pub const DIGEST_WIDTH: usize = 8;
pub const PRIVATE_SCALAR_BOUND: u16 = 1024;
pub const POST_X_BOUND: u16 = 2048;

const TRACE_WIDTH: usize = 104;
pub const PUBLIC_INPUT_COUNT: usize = 19;
const PI_COUNT: usize = PUBLIC_INPUT_COUNT;
const SESSION: usize = 0;
const RULE: usize = 1;
const K: usize = 2;
const OLD_ROOT_BASE: usize = 3;
const NEW_ROOT_BASE: usize = 11;
const X: usize = 19;
const Y: usize = 20;
const DX: usize = 21;
const DY: usize = 22;
const POST_X: usize = 23;
const POST_Y: usize = 24;
const DX_INV: usize = 25;
const DY_INV: usize = 26;
const OLD_BLIND_BASE: usize = 27;
const NEW_BLIND_BASE: usize = 35;
const X_BITS: usize = 43;
const Y_BITS: usize = 53;
const DX_BITS: usize = 63;
const DY_BITS: usize = 73;
const POST_X_BITS: usize = 83;
const POST_Y_BITS: usize = 94;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrivateAmmWitness {
    pub x: u16,
    pub y: u16,
    pub dx: u16,
    pub dy: u16,
    pub old_blind: [u32; DIGEST_WIDTH],
    pub new_blind: [u32; DIGEST_WIDTH],
}

impl PrivateAmmWitness {
    /// Construct one canonical member of the fixed family. The post-state is
    /// derived and both exact integer product equations are checked before any
    /// field conversion occurs.
    pub fn try_new(
        x: u16,
        y: u16,
        dx: u16,
        dy: u16,
        old_blind: [u32; DIGEST_WIDTH],
        new_blind: [u32; DIGEST_WIDTH],
    ) -> Result<Self, String> {
        let witness = Self {
            x,
            y,
            dx,
            dy,
            old_blind,
            new_blind,
        };
        witness.validate()?;
        Ok(witness)
    }

    /// CSPRNG-backed commitment blinds for an otherwise caller-owned private
    /// transition. A distributed producer should supply jointly sampled limbs
    /// to [`Self::try_new`] instead.
    pub fn try_new_fresh(x: u16, y: u16, dx: u16, dy: u16) -> Result<Self, String> {
        Self::try_new(
            x,
            y,
            dx,
            dy,
            sample_blind("old-state")?,
            sample_blind("new-state")?,
        )
    }

    #[inline]
    pub fn post_x(&self) -> u16 {
        self.x + self.dx
    }

    #[inline]
    pub fn post_y(&self) -> u16 {
        self.y - self.dy
    }

    #[inline]
    pub fn invariant(&self) -> u32 {
        u32::from(self.x) * u32::from(self.y)
    }

    fn validate(&self) -> Result<(), String> {
        for (name, value) in [
            ("x", self.x),
            ("y", self.y),
            ("dx", self.dx),
            ("dy", self.dy),
        ] {
            if value >= PRIVATE_SCALAR_BOUND {
                return Err(format!(
                    "{name}={value} is outside canonical ten-bit range [0,{PRIVATE_SCALAR_BOUND})"
                ));
            }
        }
        if self.dx == 0 || self.dy == 0 {
            return Err("private AMM amounts dx and dy must both be nonzero".to_string());
        }
        if self.dy > self.y {
            return Err(format!(
                "private AMM overdraw: dy={} exceeds y={}",
                self.dy, self.y
            ));
        }
        let post_x = self
            .x
            .checked_add(self.dx)
            .ok_or_else(|| "private AMM post-x overflow".to_string())?;
        if post_x >= POST_X_BOUND {
            return Err(format!(
                "post-x={post_x} is outside canonical eleven-bit range [0,{POST_X_BOUND})"
            ));
        }
        let old_k = u32::from(self.x) * u32::from(self.y);
        let new_k = u32::from(post_x) * u32::from(self.y - self.dy);
        if old_k != new_k {
            return Err(format!(
                "private AMM invariant mismatch: old product {old_k}, derived product {new_k}"
            ));
        }
        for (which, blind) in [("old", self.old_blind), ("new", self.new_blind)] {
            for (lane, value) in blind.into_iter().enumerate() {
                if value >= BABYBEAR_P {
                    return Err(format!(
                        "{which} blind lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                    ));
                }
            }
        }
        Ok(())
    }
}

fn sample_blind(label: &str) -> Result<[u32; DIGEST_WIDTH], String> {
    let modulus = BABYBEAR_P as u64;
    let accept_below = ((u32::MAX as u64 + 1) / modulus) * modulus;
    let mut blind = [0u32; DIGEST_WIDTH];
    for lane in &mut blind {
        loop {
            let mut bytes = [0u8; 4];
            getrandom::fill(&mut bytes)
                .map_err(|error| format!("OS randomness failed for {label} AMM blind: {error}"))?;
            let candidate = u32::from_le_bytes(bytes) as u64;
            if candidate < accept_below {
                *lane = (candidate % modulus) as u32;
                break;
            }
        }
    }
    Ok(blind)
}

/// Sample one canonical state-commitment blind from the operating system.
/// Offline custody tools use this for initial and successor private states.
pub fn sample_commitment_blind() -> Result<[u32; DIGEST_WIDTH], String> {
    sample_blind("state")
}

/// The exact 19-felt verifier-visible statement.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PublicStatement {
    pub session: u32,
    pub rule: u32,
    pub k: u32,
    pub old_root: [u32; DIGEST_WIDTH],
    pub new_root: [u32; DIGEST_WIDTH],
}

impl PublicStatement {
    /// Exact verifier ABI as canonical BabyBear representatives.
    pub fn as_u32_array(self) -> [u32; PUBLIC_INPUT_COUNT] {
        let mut public = [0u32; PUBLIC_INPUT_COUNT];
        public[0] = self.session;
        public[1] = self.rule;
        public[2] = self.k;
        public[3..11].copy_from_slice(&self.old_root);
        public[11..19].copy_from_slice(&self.new_root);
        public
    }

    /// Parse and validate the exact 19-value verifier ABI.
    pub fn try_from_u32s(values: &[u32]) -> Result<Self, String> {
        if values.len() != PUBLIC_INPUT_COUNT {
            return Err(format!(
                "private AMM statement expects {PUBLIC_INPUT_COUNT} values, got {}",
                values.len()
            ));
        }
        let statement = Self {
            session: values[0],
            rule: values[1],
            k: values[2],
            old_root: values[3..11].try_into().expect("length checked"),
            new_root: values[11..19].try_into().expect("length checked"),
        };
        statement.validate()?;
        Ok(statement)
    }

    fn as_felts(self) -> [BabyBear; PI_COUNT] {
        let mut public = [BabyBear::ZERO; PI_COUNT];
        public[0] = BabyBear::new(self.session);
        public[1] = BabyBear::new(self.rule);
        public[2] = BabyBear::new(self.k);
        for lane in 0..DIGEST_WIDTH {
            public[3 + lane] = BabyBear::new(self.old_root[lane]);
            public[11 + lane] = BabyBear::new(self.new_root[lane]);
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
                "rule {} is not fixed private-AMM rule {RULE_ID}",
                self.rule
            ));
        }
        if self.k >= BABYBEAR_P {
            return Err(format!(
                "k={} is noncanonical for BabyBear modulus {BABYBEAR_P}",
                self.k
            ));
        }
        for (which, root) in [("old", self.old_root), ("new", self.new_root)] {
            for (lane, value) in root.into_iter().enumerate() {
                if value >= BABYBEAR_P {
                    return Err(format!(
                        "{which} root lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
                    ));
                }
            }
        }
        Ok(())
    }
}

/// A witness-hiding proof. There is deliberately no privacy-ambiguous default
/// or non-hiding proof function in this module.
pub struct DarkAmmPrivateZkProof {
    proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl DarkAmmPrivateZkProof {
    /// Canonical opaque proof body for operation and file transport.
    pub fn to_postcard(&self) -> Result<Vec<u8>, String> {
        postcard::to_allocvec(&self.proof)
            .map_err(|error| format!("private AMM proof encode failed: {error}"))
    }

    /// Decode an opaque proof body. Verification remains an explicit separate
    /// step because the public statement is never trusted from proof bytes.
    pub fn from_postcard(bytes: &[u8]) -> Result<Self, String> {
        let proof = postcard::from_bytes(bytes)
            .map_err(|error| format!("private AMM proof decode failed: {error}"))?;
        Ok(Self { proof })
    }
}

pub fn descriptor() -> Result<EffectVmDescriptor2, String> {
    let descriptor = parse_vm_descriptor2(DARK_AMM_PRIVATE_DESCRIPTOR_JSON)?;
    if descriptor.name != "dark-amm-private-v1::wide-poseidon2-v2"
        || descriptor.trace_width != TRACE_WIDTH
        || descriptor.public_input_count != PI_COUNT
    {
        return Err("private AMM Lean-emitted descriptor shape drifted".to_string());
    }
    Ok(descriptor)
}

#[inline]
fn set_bits(row: &mut [BabyBear], value: u16, bits: usize, base: usize) {
    for bit in 0..bits {
        row[base + bit] = BabyBear::new(u32::from((value >> bit) & 1));
    }
}

fn build_row(
    session: u32,
    witness: &PrivateAmmWitness,
) -> Result<(Vec<BabyBear>, PublicStatement), String> {
    witness.validate()?;
    if session >= BABYBEAR_P {
        return Err(format!(
            "session {session} is noncanonical for BabyBear modulus {BABYBEAR_P}"
        ));
    }

    let post_x = witness.post_x();
    let post_y = witness.post_y();
    let k = witness.invariant();
    let mut row = vec![BabyBear::ZERO; TRACE_WIDTH];
    row[SESSION] = BabyBear::new(session);
    row[RULE] = BabyBear::new(RULE_ID);
    row[K] = BabyBear::new(k);
    row[X] = BabyBear::new(u32::from(witness.x));
    row[Y] = BabyBear::new(u32::from(witness.y));
    row[DX] = BabyBear::new(u32::from(witness.dx));
    row[DY] = BabyBear::new(u32::from(witness.dy));
    row[POST_X] = BabyBear::new(u32::from(post_x));
    row[POST_Y] = BabyBear::new(u32::from(post_y));
    row[DX_INV] = row[DX]
        .inverse()
        .ok_or_else(|| "nonzero dx unexpectedly lacked a BabyBear inverse".to_string())?;
    row[DY_INV] = row[DY]
        .inverse()
        .ok_or_else(|| "nonzero dy unexpectedly lacked a BabyBear inverse".to_string())?;
    for lane in 0..DIGEST_WIDTH {
        row[OLD_BLIND_BASE + lane] = BabyBear::new(witness.old_blind[lane]);
        row[NEW_BLIND_BASE + lane] = BabyBear::new(witness.new_blind[lane]);
    }
    set_bits(&mut row, witness.x, 10, X_BITS);
    set_bits(&mut row, witness.y, 10, Y_BITS);
    set_bits(&mut row, witness.dx, 10, DX_BITS);
    set_bits(&mut row, witness.dy, 10, DY_BITS);
    set_bits(&mut row, post_x, 11, POST_X_BITS);
    set_bits(&mut row, post_y, 10, POST_Y_BITS);

    let old_root =
        state_root(session, k, witness.x, witness.y, witness.old_blind)?.map(BabyBear::new);
    row[OLD_ROOT_BASE..OLD_ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&old_root);

    let new_root = state_root(session, k, post_x, post_y, witness.new_blind)?.map(BabyBear::new);
    row[NEW_ROOT_BASE..NEW_ROOT_BASE + DIGEST_WIDTH].copy_from_slice(&new_root);

    let public = PublicStatement {
        session,
        rule: RULE_ID,
        k,
        old_root: old_root.map(BabyBear::as_u32),
        new_root: new_root.map(BabyBear::as_u32),
    };
    Ok((row, public))
}

/// Compute the exact public statement without producing a proof.
pub fn statement(session: u32, witness: &PrivateAmmWitness) -> Result<PublicStatement, String> {
    build_row(session, witness).map(|(_, public)| public)
}

/// Compute the exact eight-felt commitment for one hidden AMM state without
/// requiring a transition witness. `x` admits the descriptor's eleven-bit
/// post-state range; a state intended as the next transition's old state must
/// additionally satisfy the ten-bit bound enforced by [`PrivateAmmWitness`].
pub fn state_root(
    session: u32,
    k: u32,
    x: u16,
    y: u16,
    blind: [u32; DIGEST_WIDTH],
) -> Result<[u32; DIGEST_WIDTH], String> {
    if session >= BABYBEAR_P {
        return Err(format!(
            "session {session} is noncanonical for BabyBear modulus {BABYBEAR_P}"
        ));
    }
    if k >= BABYBEAR_P {
        return Err(format!(
            "k={k} is noncanonical for BabyBear modulus {BABYBEAR_P}"
        ));
    }
    if x >= POST_X_BOUND {
        return Err(format!(
            "state x={x} is outside canonical eleven-bit range [0,{POST_X_BOUND})"
        ));
    }
    if y >= PRIVATE_SCALAR_BOUND {
        return Err(format!(
            "state y={y} is outside canonical ten-bit range [0,{PRIVATE_SCALAR_BOUND})"
        ));
    }
    if u32::from(x) * u32::from(y) != k {
        return Err(format!(
            "state opening product {} does not equal public k={k}",
            u32::from(x) * u32::from(y)
        ));
    }
    for (lane, value) in blind.into_iter().enumerate() {
        if value >= BABYBEAR_P {
            return Err(format!(
                "state blind lane {lane}={value} is noncanonical for BabyBear modulus {BABYBEAR_P}"
            ));
        }
    }
    let mut preimage = Vec::with_capacity(16);
    preimage.extend([
        BabyBear::new(STATE_ROOT_DOMAIN_TAG),
        BabyBear::new(session),
        BabyBear::new(RULE_ID),
        BabyBear::new(k),
        BabyBear::new(u32::from(x)),
        BabyBear::new(u32::from(y)),
    ]);
    preimage.extend(blind.map(BabyBear::new));
    preimage.extend([BabyBear::ZERO; 2]);
    Ok(chip_absorb_all_lanes(preimage.len(), &preimage).map(BabyBear::as_u32))
}

fn trace_and_public(
    session: u32,
    witness: &PrivateAmmWitness,
) -> Result<(EffectVmDescriptor2, Vec<Vec<BabyBear>>, PublicStatement), String> {
    let descriptor = descriptor()?;
    let (row, public) = build_row(session, witness)?;
    let trace = vec![row.clone(), row.clone(), row.clone(), row];
    Ok((descriptor, trace, public))
}

/// Mint a fresh witness-hiding FRI proof. Every call constructs a new
/// OS-seeded ZK configuration, randomizing salted commitments, random trace
/// rows, and FRI codewords even when the statement and witness are unchanged.
pub fn prove_zk(
    session: u32,
    witness: &PrivateAmmWitness,
) -> Result<(DarkAmmPrivateZkProof, PublicStatement), String> {
    let (descriptor, trace, public) = trace_and_public(session, witness)?;
    let config = create_zk_config();
    let proof = prove_vm_descriptor2_for_config(
        &descriptor,
        &trace,
        &public.as_felts(),
        &MemBoundaryWitness::default(),
        &[],
        &UMemBoundaryWitness::default(),
        &config,
    )?;
    Ok((DarkAmmPrivateZkProof { proof }, public))
}

/// Verify against caller-supplied public values without access to any reserve,
/// amount, or commitment-blind witness value.
pub fn verify_zk(proof: &DarkAmmPrivateZkProof, public: PublicStatement) -> Result<(), String> {
    public.validate()?;
    let config = create_zk_config();
    verify_vm_descriptor2_with_config(&descriptor()?, &proof.proof, &public.as_felts(), &config)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::descriptor_ir2::VmConstraint2;
    use dregg_circuit::lean_descriptor_air::{VmConstraint, VmRow};

    fn blind(base: u32) -> [u32; DIGEST_WIDTH] {
        core::array::from_fn(|lane| base + lane as u32)
    }

    fn fixture() -> PrivateAmmWitness {
        // 100*900 = 150*600 = 90,000.
        PrivateAmmWitness::try_new(100, 900, 50, 300, blind(1_000), blind(2_000))
            .expect("fixed exact-invariant private AMM transition")
    }

    #[test]
    fn private_amm_descriptor_and_input_boundary_fail_closed() {
        let descriptor = descriptor().expect("Lean-emitted descriptor decodes");
        assert_eq!(descriptor.trace_width, TRACE_WIDTH);
        assert_eq!(descriptor.public_input_count, PI_COUNT);
        let mut pins = descriptor
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
        assert_eq!(pins.len(), PI_COUNT);
        assert_eq!(pins[0], (VmRow::First, SESSION, 0));
        assert_eq!(pins[1], (VmRow::First, RULE, 1));
        assert_eq!(pins[2], (VmRow::First, K, 2));
        for lane in 0..DIGEST_WIDTH {
            assert_eq!(
                pins[3 + lane],
                (VmRow::First, OLD_ROOT_BASE + lane, 3 + lane)
            );
            assert_eq!(
                pins[11 + lane],
                (VmRow::First, NEW_ROOT_BASE + lane, 11 + lane)
            );
        }

        assert!(
            PrivateAmmWitness::try_new(100, 900, 50, 301, blind(1_000), blind(2_000)).is_err(),
            "a wrong private quote must fail the exact post-product relation"
        );
        assert!(
            PrivateAmmWitness::try_new(100, 10, 50, 11, blind(1_000), blind(2_000)).is_err(),
            "overdraw must refuse before unsigned subtraction"
        );
        assert!(
            PrivateAmmWitness::try_new(100, 900, 0, 0, blind(1_000), blind(2_000)).is_err(),
            "zero amounts must refuse"
        );
        let mut bad_blind = blind(1_000);
        bad_blind[4] = BABYBEAR_P;
        assert!(
            PrivateAmmWitness::try_new(100, 900, 50, 300, bad_blind, blind(2_000)).is_err(),
            "noncanonical blind must refuse before field reduction"
        );
    }

    #[test]
    fn private_amm_hiding_proves_randomizes_and_public_tampers_refuse() {
        let witness = fixture();
        let (proof, public) = prove_zk(77, &witness).expect("honest transition proves hiding");
        verify_zk(&proof, public).expect("honest hiding proof verifies");
        let public_wire = public.as_u32_array();
        assert_eq!(
            PublicStatement::try_from_u32s(&public_wire).unwrap(),
            public
        );
        let proof_wire = proof.to_postcard().expect("proof transport encodes");
        let decoded =
            DarkAmmPrivateZkProof::from_postcard(&proof_wire).expect("proof transport decodes");
        assert_eq!(decoded.to_postcard().unwrap(), proof_wire);
        verify_zk(&decoded, public).expect("transported proof verifies");
        assert_eq!(public.k, 90_000);
        assert_eq!(
            state_root(77, public.k, witness.x, witness.y, witness.old_blind).unwrap(),
            public.old_root
        );
        assert_eq!(
            state_root(
                77,
                public.k,
                witness.post_x(),
                witness.post_y(),
                witness.new_blind,
            )
            .unwrap(),
            public.new_root
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

        let (rerun, rerun_public) =
            prove_zk(77, &witness).expect("same transition re-proves with fresh hiding randomness");
        assert_eq!(rerun_public, public);
        assert_ne!(
            format!("{:?}", proof.proof.commitments.random),
            format!("{:?}", rerun.proof.commitments.random)
        );
        verify_zk(&rerun, rerun_public).expect("randomized re-proof verifies");

        let mut forged_old = public;
        forged_old.old_root[0] = (forged_old.old_root[0] + 1) % BABYBEAR_P;
        assert!(verify_zk(&proof, forged_old).is_err());

        let mut forged_new = public;
        forged_new.new_root[7] = (forged_new.new_root[7] + 1) % BABYBEAR_P;
        assert!(verify_zk(&proof, forged_new).is_err());

        let mut forged_k = public;
        forged_k.k += 1;
        assert!(verify_zk(&proof, forged_k).is_err());

        // The produced root is an actual state cursor, not a one-shot
        // direction-tagged digest. Carrying the new blind forward makes it the
        // next transition's exact old root.
        let next = PrivateAmmWitness::try_new(
            witness.post_x(),
            witness.post_y(),
            150,
            300,
            witness.new_blind,
            blind(3_000),
        )
        .expect("second exact transition");
        let next_public = statement(77, &next).expect("second public statement");
        assert_eq!(public.new_root, next_public.old_root);
    }
}
