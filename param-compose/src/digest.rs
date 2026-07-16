//! **THE WIDE DIGEST** — a ~124-bit binding built from the only Poseidon2 sites a
//! FOLDABLE custom leaf may carry.
//!
//! # The substrate boundary this works around (measured, not asserted)
//!
//! `dregg_circuit::dsl::circuit::ConstraintExpr::MerkleHash8` is the native one-site
//! 8-felt compression (`cap_node8`, arity-16) and would give a ~124-bit root for ONE
//! permutation. The custom-leaf lowering **refuses it**
//! (`circuit/src/custom_leaf_lowering.rs:625`):
//!
//! > constraint kind MerkleHash8 ... is an 8-OUTPUT Poseidon2 site; this IR-v2 chip
//! > adapter carries single-output (out0) chip sites only.
//!
//! A leaf that must reach the door must fold, so it may use only the single-output forms
//! (`Hash4to1` / `Hash2to1` / `Hash3Cap`), each squeezing lane 0 alone: a **~31-bit**
//! digest. That is not a binding — a 31-bit root is a 2^31 second-preimage (and a 2^15.5
//! collision if the adversary may also author a ruleset), so a "committed" ruleset would
//! stop being load-bearing for grinding work measured in minutes.
//!
//! # The construction
//!
//! `W` parallel 4-ary absorb chains over the SAME canonical stream, each seeded with a
//! distinct IV (`domain * LANE_STRIDE + lane`):
//!
//! ```text
//!   acc[k] := IV(domain, k)
//!   for each 3-felt block B of the stream:  acc[k] := hash_4_to_1([acc[k], B0, B1, B2])
//!   root    := (acc[0], .., acc[W-1])
//! ```
//!
//! Modelling `hash_4_to_1` as a random function, distinct IVs give `W` independent
//! chains, so the concatenated root is a `31*W`-bit digest: at `W = 8` a ~248-bit digest
//! with a ~124-bit collision floor, matching the deployed 8-felt `WideHash` and sitting
//! above the ~112.6-bit FRI floor. This is the standard multi-IV parallel-hash argument;
//! it costs `W` sites where the refused primitive costs one.
//!
//! Every function here is the HOST TWIN of a gadget in `crate::air`, which rebuilds the
//! identical chain over witnessed columns with `ConstraintExpr::Hash4to1`. The two are
//! pinned against each other by `tests/digest_twin.rs`.

use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_4_to_1;

/// Data felts absorbed per site (`hash_4_to_1` takes 4 inputs, one of which is the
/// running accumulator).
pub const ABSORB_RATE: usize = 3;

/// Spacing between lane IVs, so `domain * LANE_STRIDE + lane` never collides across
/// domains for `lane < LANE_STRIDE`.
pub const LANE_STRIDE: u64 = 256;

/// Domain tag: the canonical subjects stream.
pub const DOMAIN_SUBJECTS: u64 = 0x9C01;
/// Domain tag: the canonical ruleset stream (THE COMPOSITION LAW).
pub const DOMAIN_RULESET: u64 = 0x9C02;
/// Domain tag: the outcome.
pub const DOMAIN_OUTCOME: u64 = 0x9C03;
/// Domain tag: the per-term explanation contributions.
pub const DOMAIN_EXPLANATION: u64 = 0x9C04;

/// The initial accumulator for `lane` of `domain`.
pub fn lane_iv(domain: u64, lane: usize) -> BabyBear {
    crate::field::fb((domain * LANE_STRIDE) as i128 + lane as i128)
}

/// The `W`-felt digest of `data` under `domain`. Host twin of `crate::air::wide_chain`.
pub fn wide_digest(domain: u64, data: &[BabyBear], w: usize) -> Vec<BabyBear> {
    (0..w)
        .map(|lane| {
            let mut acc = lane_iv(domain, lane);
            for block in data.chunks(ABSORB_RATE) {
                let mut ins = [acc, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO];
                for (i, v) in block.iter().enumerate() {
                    ins[i + 1] = *v;
                }
                acc = hash_4_to_1(&ins);
            }
            acc
        })
        .collect()
}
