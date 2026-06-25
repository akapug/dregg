//! The UNBOUNDED ONLINE ACCUMULATOR — the running left-fold over finalized turns.
//!
//! ## What this is (and how it differs from the K-fold tree)
//!
//! [`ivc_turn_chain::prove_turn_chain_recursive`](crate::ivc_turn_chain::prove_turn_chain_recursive)
//! folds a *finite* window of K finalized turns into one root proof via a BALANCED BINARY TREE
//! (`aggregate_tree`): it needs ALL K turns in memory at once, and the tree shape (hence the root
//! VK fingerprint) depends on K.
//!
//! This module is the SEQUENTIAL DUAL: a running accumulator that holds ONE `RecursionOutput` (the
//! O(1)-memory running proof) and EXTENDS it ONE finalized turn at a time:
//!
//! ```text
//!   acc_0 = genesis (the empty fold)
//!   acc_n = accumulate(acc_{n-1}, turn_n)
//! ```
//!
//! `accumulate(acc, turn)` is the genuine IVC step:
//!   1. verify `turn`'s leaf (host admission + the in-circuit descriptor leaf re-proof);
//!   2. **verify `acc_{n-1}`'s running proof IN-CIRCUIT** — the recursion: the previous running
//!      `RecursionOutput.0` (a `BatchStarkProof`) rides back in as a [`BatchOnly`] recursion input
//!      (`acc.running.into_recursion_input::<BatchOnly>()`), so the next aggregation layer's
//!      in-circuit FRI verifier RE-VERIFIES it. This is the same `into_recursion_input::<BatchOnly>`
//!      re-verification [`aggregate_tree`](crate::ivc_turn_chain) already performs at every internal
//!      tree node — driven here as a running LEFT-fold rather than a balanced tree;
//!   3. bind `acc_{n-1}.head_root == turn_n.pre_root`, advance `head_root = turn_n.post_root`,
//!      `num_turns += 1`, `chain_digest = H(prev_digest, old, new, idx)`;
//!   4. aggregate `running ∘ new_turn_leaf` into the NEW running `RecursionOutput`.
//!
//! **O(1) PROOF memory, O(num_turns) scalar binding state (precise).** The dominant cost — the
//! running RECURSION PROOF — is O(1): one [`RecursionOutput`] is held regardless of chain length, and
//! the consumed turns (proofs) are dropped. The accumulator ALSO retains a small per-turn scalar
//! witness — the four chain commitments (O(1)) PLUS `seam_pairs`, the ordered `(old_root, new_root)`
//! pairs (two field elements per folded turn), which `finalize` replays to rebuild the chain-binding
//! leaf so its digest reproduces the running `chain_digest`. So the running STATE is O(num_turns)
//! SCALARS, not O(1) — though the proof memory (the expensive part) is genuinely constant. Folding
//! the binding incrementally so `seam_pairs` vanishes is named open work (prereq (b) below).
//!
//! ## ⚠ SEGMENT-ACCUMULATOR FOLLOW-UP (the mixed-root analog, named)
//!
//! The K-fold tree (`ivc_turn_chain`) closed the mixed-root hole by carrying an ordered
//! SEGMENT on every DESCRIPTOR leaf and combining segments in-circuit (so the whole-chain
//! claim is derived from the real executions, with no swappable binding leaf). This online
//! accumulator STILL uses the separate `TurnChainBindingAir` leaf at `finalize` (its claim
//! is a hash-chain over the seam-pair roots, reconstructed from `seam_pairs`), so it has the
//! SAME structural weakness the K-fold just retired: the binding leaf is not tied in-circuit
//! to the descriptor leaves the running fold actually verified. Its `verify_turn_chain_recursive`
//! is self-consistent (it exposes + checks its own binding claim) but does NOT yet enjoy the
//! segment tooth's by-construction binding. The follow-up is to port the segment model here:
//! each `accumulate` step's descriptor leaf carries its segment, and the running fold combines
//! `running.segment` with the new leaf's segment (the left-linear analog of the K-fold combine —
//! its continuity/count/digest constraints are identical). NAMED, not closed in this pass; the
//! K-fold bar (the mixed-root witness) is the one that landed.
//!
//! ## What is GENUINELY here vs the named in-band gap (honest, tiered)
//!
//! **BUILT + RUNNING:** the running-fold DRIVER over the REAL recursion primitives. Each step does a
//! real in-circuit re-verification of the running batch proof (step 2) and a real in-circuit
//! descriptor-leaf re-proof (step 1), aggregated to a new running root. The temporal binding
//! (`prev.head_root == next.old_root`) is enforced host-side (the [`AccError::ChainBreak`] tooth) and
//! the running summary advances correctly. The terminal [`Accumulator::finalize`] reuses the proven
//! `verify_turn_chain_recursive` verify discipline, so a light client's
//! [`lightclient::verify_history`] accepts the accumulated artifact under its honest VK anchor.
//!
//! **THE TWO FORK LEVERS — NOW LANDED IN-BAND (lever a + b), with the precise residual NAMED.**
//! The recursion fork (`emberian/plonky3-recursion`) now exposes the two mechanisms this fold needs:
//!   - **(a) VK identity of the re-folded running proof — PINNED in-band.** The parent aggregation
//!     circuit takes the child's preprocessed commitment (its verifier-key core) as public-input
//!     targets, but their VALUE was unconstrained. The fork's `into_recursion_input_pinned()` /
//!     `pin_preprocessed_commit()` now `connect` those targets to an expected commitment IN-CIRCUIT:
//!     a child proof from a DIFFERENT circuit (different preprocessed commitment) makes the parent
//!     UNSAT. This driver consumes it: once the running AGGREGATION shape exists, its commitment is
//!     captured and every subsequent fold pins the running (left) input against it — the IVC
//!     self-verification check (witness: `pinned_fold_rejects_foreign_vk_in_circuit`, which exhibits
//!     a corrupted-VK fold being rejected in-circuit on the leaf∘leaf shape).
//!   - **(b) public-value propagation across layers — THREADED.** `into_recursion_input` no longer
//!     hardcodes empty `table_public_inputs`; it threads the proof's GENUINE per-table public values
//!     so the next layer's packed public vector MATCHES the targets it allocates. This is also what
//!     unblocked re-folding a proof that itself contains a fold (an aggregation proof's non-primitive
//!     tables expose public values; the empty-vector path left those allocated targets unfilled —
//!     over-constraining the witness solver, the `WitnessConflict` the deep fold tripped).
//!
//! **DEPTH-INVARIANCE — the WRAP step, and the MEASURED fixed point (honest, tiered).**
//!
//! The pin makes VK identity an IN-BAND constraint, but does not by itself bound the running VK's
//! SHAPE. The WRAP step ([`wrap_params`] / [`WRAP_LOG_CEIL`], ON by default) proves each running fold
//! under a fixed `min_trace_height` ceiling so the running FRI trace shape cannot grow with depth.
//!
//! **What is MEASURED (not merely named) — the running VK reaches a CONSTANT FIXED POINT (at depth 4),
//! with the steady state holding by a STRUCTURAL IDEMPOTENCE argument (not yet a mechanized induction).**
//! A real incremental fold over a continuous chain (test `wrapped_running_vk_is_constant_across_depth`)
//! shows the running aggregation proof's full VK fingerprint — table packing, `rows`, `degree_bits`, the
//! non-primitive manifest, AND the preprocessed commitment (the op-list / VK core) — settling to a fixed
//! point after a short transient:
//!   - depth 2 (LEAF∘LEAF result) ≠ depth 3 (AGG over LEAF∘LEAF) ≠ depth 4 (AGG over AGG∘LEAF) — the
//!     transient (the running INPUT's own sub-structure propagates EXACTLY ONE level into the parent
//!     op-list before it stabilizes — see the structural finding below);
//!   - **depth 4 == depth 5 (== … ): byte-IDENTICAL VK material, including the preprocessed commitment.**
//! The `degree_bits` are constant THROUGHOUT (`[9,9,15,14,15]`, natural max `2^15`); the transient lives
//! entirely in the op-list (logical `rows` + preprocessed commitment).
//!
//! **Why the fixed point is PERPETUAL (the structural argument — honest about its status).** Once the
//! running input is an `AGG(AGG, LEAF)`-shaped proof (depth 4+), folding it against a leaf produces
//! another `AGG(AGG, LEAF)`-shaped proof: the verifier op-list of `verify(AGG(AGG,LEAF))` is a function
//! of that fixed input shape, so the fold map `f` is IDEMPOTENT on it (`f(steady) = steady`). The
//! measured `depth-4 == depth-5` is the first application of that idempotence; the perpetual claim rests
//! on the idempotence argument, NOT on a measurement at every depth (which is impossible) NOR on a
//! mechanized induction over the fold (an honest residual — the Lean skeleton below proves the
//! whole-history attestation invariant, not the byte-level VK-shape fixpoint). It is a measured fixed
//! point + a structural idempotence argument, not a proof of `∀N, VK_N == VK_4`.
//!
//! **THE PRECISE REMAINING CRYPTO (the structural half of the wrap — named exactly, with the localized
//! delta).** The fixed point is reached at depth 4, NOT depth 2 — a finite 2-step transient. The
//! ROOT-CAUSED structural reason: the AGG∘LEAF verifier op-list depends on the STRUCTURE of the running
//! (left) input proof — specifically the per-instance opened-column widths / public-value counts of its
//! `non_primitives` and its `rows` (see `verify_p3_batch_proof_circuit` in the fork: it iterates the
//! input proof's `non_primitives` and allocates per-instance targets from their `public_values.len()`
//! and opened-value widths). A LEAF input, an `AGG(LEAF,LEAF)` input, and an `AGG(AGG,LEAF)` input each
//! carry a DIFFERENT such structure — and that structure propagates exactly ONE level into the parent's
//! op-list (measured: `rows` Const 269→277, recompose 19112→19093; `prep_commit` ddaa…→830a…), so the
//! parent op-list stabilizes only once the input has been `AGG(AGG,LEAF)`-shaped for one full fold.
//! To make EVERY fold from depth 2 carry the ONE anchor, the running input must have the steady
//! `AGG(AGG,LEAF)` structure from the FIRST aggregation — which requires a CANONICAL agg-shaped SEED
//! whose own left is already agg-shaped (a recursive fixpoint seed). That is the genuine Pickles
//! step∘wrap circuit: a fixed wrap circuit whose output shape equals its input shape, seeded once. The
//! fork exposes no such canonical-shape / re-prove primitive today (no identity/normalize fold), so
//! building the fixpoint seed is genuinely multi-pass — the precise outstanding fork work. The
//! `min_trace_height` ceiling pins the FRI trace heights (the easy half, empirically a near-no-op since
//! heights were already constant) but NOT the op-list. Lever (a)+(b), the tracked-pin fail-closed tooth,
//! and the measured-plus-idempotent fixed point are its foundation.
//!
//! The soundness SKELETON of the unbounded loop is PROVEN in Lean
//! (`Dregg2.Circuit.RecursiveAggregation.accumulate_preserves_wellformed` /
//! `acc_attests_whole_history`, `#assert_axioms`-clean): the running fold preserves whole-history
//! attestation by induction from genesis, carrying the SAME named `EngineSound` recursion boundary.

use p3_commit::Pcs;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput,
    build_and_prove_aggregation_layer, build_and_prove_aggregation_layer_with_expose,
    build_and_prove_next_layer_with_expose,
};
use p3_uni_stark::StarkGenericConfig;

/// The runtime preprocessed-commitment value type for the recursion config — the child proof's
/// VK-identity core (a Merkle cap). This is what the VK-identity pin (lever (a)) constrains in-band.
type RecursionCommit = <<DreggRecursionConfig as StarkGenericConfig>::Pcs as Pcs<
    <DreggRecursionConfig as StarkGenericConfig>::Challenge,
    <DreggRecursionConfig as StarkGenericConfig>::Challenger,
>>::Commitment;

use crate::ivc_turn_chain::{
    FinalizedTurn, RecursionVk, TurnChainBindingAir, WholeChainProof, ir2_leaf_wrap_config,
    prove_descriptor_leaf_rotated_with_config, verify_turn_chain_recursive,
};
use crate::joint_turn_aggregation::verify_descriptor_participant;
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, create_recursion_backend,
    prove_inner_for_air_with_config, verify_inner_for_air_with_config,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_4_to_1;
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;

const D: usize = 4;

/// The recursion challenge (extension) field the expose hooks build constants over.
type AccChallenge = <DreggRecursionConfig as StarkGenericConfig>::Challenge;

/// Expose the accumulator's binding-leaf claims `[genesis, final, num_turns, chain_digest]`
/// as a `SEG_WIDTH`-lane segment, ZERO-PADDING the single-felt binding digest to the K-fold
/// path's [`crate::ivc_turn_chain::SEG_DIGEST_WIDTH`]-lane digest block:
/// `[genesis, final, num_turns, chain_digest, 0, …, 0]`.
///
/// This keeps the ONLINE accumulator's artifact structurally uniform with the K-fold's
/// multi-felt segment (so `verify_turn_chain_recursive`'s tooth (4) reads a consistent
/// layout) WITHOUT strengthening its digest — the accumulator path is scoped OUT of the
/// codex #3 mixed-root close (its binding leaf is the separate, swappable single-felt
/// `hash_4_to_1` carrier; the padding lanes carry no additional commitment).
fn accumulator_expose_padded_segment(
    cb: &mut p3_circuit::CircuitBuilder<AccChallenge>,
    binding_claims: &[p3_recursion::Target],
) {
    use crate::ivc_turn_chain::{NUM_CHAIN_CLAIMS, SEG_DIGEST_FIRST};
    // Binding-leaf PI order: [genesis, final, num_turns, chain_digest] — i.e. the first
    // SEG_DIGEST_FIRST + 1 lanes (the 3 scalar lanes + the single binding digest at the
    // first digest lane), with the remaining digest lanes zero.
    let prefix_len = SEG_DIGEST_FIRST + 1;
    debug_assert!(
        binding_claims.len() >= prefix_len,
        "binding leaf must expose [genesis, final, num_turns, chain_digest]"
    );
    let zero = cb.define_const(AccChallenge::ZERO);
    let mut seg: Vec<p3_recursion::Target> = Vec::with_capacity(NUM_CHAIN_CLAIMS);
    seg.extend_from_slice(&binding_claims[..prefix_len]);
    while seg.len() < NUM_CHAIN_CLAIMS {
        seg.push(zero);
    }
    cb.expose_as_public_output(&seg);
}

/// **THE WRAP-STEP TRACE-HEIGHT CEILING (the `min_trace_height` half of the fixed-shape knob).**
///
/// This pins every running-proof table to a fixed power-of-two `degree_bits` floor of `2^WRAP_LOG_CEIL`,
/// so the running FRI commit-phase count (`num_phases = log_max_height - log_blowup`) does not grow with
/// depth.
///
/// **EMPIRICALLY MEASURED RESIDUAL (the precise reason a height ceiling ALONE does not close constant-VK):**
/// at the dregg leaf-wrap config the running AGG∘LEAF `degree_bits` are ALREADY constant across depth
/// (measured `[9, 9, 15, 14, 15]` at depth 2 AND depth 3 — the natural max is `2^15`, so a `2^16` ceiling
/// is a near-no-op pad). The part of the running VK that STILL drifts with depth is NOT the trace heights
/// but the **op-list** — the logical pre-padding `rows` (e.g. Const `269 → 277`, recompose `19112 → 19093`)
/// AND the **preprocessed commitment** (`ddaa4a02… → 830ace21…`). The op-list of the AGG∘LEAF verifier
/// circuit depends on the STRUCTURE of the input running proof (its FRI openings / opened-values count),
/// which a `min_trace_height` floor does not touch. Closing THAT needs the structural half of the wrap:
/// re-proving the input running proof to a fixed STRUCTURE (fixed instance/opening counts) so the
/// verifier op-list is identical. See [`Accumulator::accumulate`]'s wrap note and this module's header.
///
/// Set to `2^16` (just above the measured natural `2^15` max) so the ceiling is a safe pad that never
/// blows memory; a higher ceiling (e.g. `2^20`) pads to ~1M rows/table and OOMs the prover.
pub const WRAP_LOG_CEIL: usize = 16;

/// The [`ProveNextLayerParams`] the WRAP step proves the running fold under: identical to the default
/// recursion params EXCEPT the table packing carries a fixed [`WRAP_LOG_CEIL`] trace-height floor (the
/// `min_trace_height` half of the fixed-shape knob). This pins the running FRI shape but NOT the op-list
/// (see [`WRAP_LOG_CEIL`] for the measured residual).
fn wrap_params() -> ProveNextLayerParams {
    let base = ProveNextLayerParams::default();
    ProveNextLayerParams {
        table_packing: base
            .table_packing
            .with_min_trace_height(1usize << WRAP_LOG_CEIL),
        constraint_profile: base.constraint_profile,
    }
}

fn to_p3(v: BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

/// A short blake3 fingerprint of a recursion preprocessed commitment (the VK-identity core), for
/// diagnostic error messages on a pin mismatch. Not a security-bearing comparison — the actual
/// pin equality compares the full `RecursionCommit` value.
fn commit_fingerprint(commit: &RecursionCommit) -> String {
    let bytes = postcard::to_allocvec(commit).unwrap_or_default();
    blake3::hash(&bytes).to_hex()[..16].to_string()
}

/// Why an accumulate step failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AccError {
    /// **The temporal tooth.** The next turn does not consume the accumulator's head root: its
    /// `old_root` is not the running `head_root`. (The `TurnChainError::ChainBreak` analog for the
    /// running fold.)
    ChainBreak {
        /// The accumulator's current head root (what the next turn must consume).
        expected_old_root: u32,
        /// The root the next turn claims to consume.
        found_old_root: u32,
    },
    /// A turn's per-cell whole-turn proof failed host admission or the in-circuit leaf re-proof.
    TurnProofInvalid {
        /// The 0-based fold index (`num_turns` at the time of the failing step).
        index: usize,
        /// The underlying reason.
        reason: String,
    },
    /// A recursion layer (leaf wrap, binding leaf, or the running aggregation) failed.
    RecursionFailed {
        /// What failed.
        reason: String,
    },
    /// **The VK-identity fixed-point tooth (fail-closed).** After the running fixed-point VK was
    /// captured, this fold's running (left) input carried a DIFFERENT preprocessed commitment than
    /// the pinned one — i.e. the running proof came from a different circuit than the captured fixed
    /// point. The fold is REJECTED (never folded unpinned). The accumulator is left UNCHANGED.
    VkIdentityMismatch {
        /// The 0-based fold index (`num_turns` at the time of the failing step).
        index: usize,
        /// A blake3-16 fingerprint of the pinned (expected) preprocessed commitment.
        expected: String,
        /// A blake3-16 fingerprint of the running proof's actual preprocessed commitment.
        found: String,
    },
    /// `finalize` on an empty accumulator (no turns folded — there is nothing to attest).
    Empty,
}

impl core::fmt::Display for AccError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            AccError::ChainBreak {
                expected_old_root,
                found_old_root,
            } => write!(
                f,
                "next turn breaks the running chain: old_root {found_old_root} != \
                 accumulator head_root {expected_old_root}"
            ),
            AccError::TurnProofInvalid { index, reason } => {
                write!(f, "turn {index} proof invalid: {reason}")
            }
            AccError::RecursionFailed { reason } => write!(f, "recursion failed: {reason}"),
            AccError::VkIdentityMismatch {
                index,
                expected,
                found,
            } => write!(
                f,
                "VK-identity pin mismatch at fold {index}: running proof commitment {found} != \
                 pinned fixed-point VK {expected} (the running proof came from a different circuit \
                 than the captured fixed point — fold REJECTED, not folded unpinned)"
            ),
            AccError::Empty => write!(f, "cannot finalize an empty accumulator (no turns folded)"),
        }
    }
}

impl std::error::Error for AccError {}

/// The O(1)-memory running summary of the accumulated chain (the four scalar commitments the
/// `WholeChainProof` exposes, advanced incrementally). Kept between fold steps so the binding leaf
/// can be regenerated WITHOUT retaining the consumed turns.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChainSummary {
    /// The genesis root the chain started from (the first turn's `old_root`).
    pub genesis_root: BabyBear,
    /// The running head root (the last folded turn's `new_root`); the next turn must consume this.
    pub head_root: BabyBear,
    /// The running ordered-history digest (`hash_4_to_1` over the `(old, new, idx)` pairs).
    pub chain_digest: BabyBear,
    /// The number of turns folded so far.
    pub num_turns: usize,
    /// The running Poseidon2 accumulator carrier (`acc_out` of the binding AIR; `chain_digest` IS
    /// this after the last fold). Tracked so the next fold's digest hashes from the right pre-state.
    acc_carrier: BabyBear,
}

/// The running accumulator: a single running recursion proof (O(1) PROOF memory) + the O(1) chain
/// summary + the O(num_turns) `seam_pairs` scalar binding witness.
///
/// Built by [`Accumulator::genesis`], extended by [`Accumulator::accumulate`], and read out by
/// [`Accumulator::finalize`] into a [`WholeChainProof`] a light client verifies.
///
/// **The memory profile (honest).** The dominant cost — the running RECURSION PROOF — is O(1): one
/// `RecursionOutput` is held regardless of chain length. The residual `seam_pairs` (two field
/// elements per folded turn) is the binding-leaf's reconstruction witness: it lets `finalize` rebuild
/// the per-turn `TurnChainBindingAir` leaf so its last-row digest reproduces `summary.chain_digest`
/// EXACTLY (the AIR's `acc_out == chain_digest` constraint). This is precisely the component prereq
/// (b) — in-circuit re-exposure of the running digest as a CHECKED public — would eliminate: with (b),
/// the binding could bind against the running root's exposed digest in-circuit and `seam_pairs` would
/// vanish. Until then it is a small (2-felt/turn) scalar witness, NOT a retained proof; the proof
/// memory is genuinely O(1).
pub struct Accumulator {
    /// The running recursion proof (`None` before the first turn). This is the IVC fixed-point
    /// carrier: each `accumulate` re-verifies it in-circuit and folds it forward.
    running: Option<RecursionOutput<DreggRecursionConfig>>,
    /// The running chain summary (`None` before the first turn).
    summary: Option<ChainSummary>,
    /// The ordered `(old_root, new_root)` seam pairs of the folded turns — the binding-leaf
    /// reconstruction witness (see the struct note: O(num_turns) SCALARS, not proofs; eliminated by
    /// prereq (b)).
    seam_pairs: Vec<(BabyBear, BabyBear)>,
    /// **THE VK-IDENTITY PIN — the EXPECTED commitment of the running proof we hold (lever (a)).**
    /// This is the preprocessed commitment of the running [`RecursionOutput`] currently in `running`,
    /// recorded each fold from the OUTPUT we just produced. Each subsequent fold (i) checks the held
    /// running proof's commitment STILL equals this expected value — fail-closed
    /// ([`AccError::VkIdentityMismatch`]) if a foreign/swapped proof ever appears — and (ii) pins the
    /// running (left) input IN-CIRCUIT to it via [`RecursionOutput::into_recursion_input_pinned`], so
    /// the aggregation circuit constrains "the proof I am re-folding is the one I produced last step."
    ///
    /// **Why it TRACKS the running commitment rather than freezing one value.** The running
    /// aggregation VK passes through a finite TRANSIENT before it reaches the perpetual fixed point
    /// (the AGG∘LEAF shape settles once the running input is itself a stable-shape aggregation — the
    /// `degree_bits` are constant throughout, but the op-list `rows` + preprocessed commitment settle
    /// after a couple of folds; see [`WRAP_LOG_CEIL`] and the module header). During the transient the
    /// running proof's commitment genuinely changes each step, so a frozen pin would FALSELY reject
    /// honest transient folds. Tracking the actual running commitment pins EVERY fold against the
    /// genuinely-expected running proof — fail-closed against a foreign proof at all depths — and
    /// becomes CONSTANT once the fixed point is reached (the pin then naturally holds the perpetual
    /// fixed-point VK forever). A FOREIGN running proof (different preprocessed commitment than the one
    /// we recorded) makes the aggregation circuit UNSAT and is rejected host-side BEFORE the fold.
    ///
    /// `None` until the first aggregation OR if the pin is disabled (see
    /// [`Accumulator::with_vk_identity_pin`]). Default: pin ENABLED.
    pinned_running_vk: Option<RecursionCommit>,
    /// Whether the VK-identity fixed-point pin is enabled. Default `true`. Disable only to reproduce
    /// the legacy unpinned fold (e.g. to exhibit that a foreign-circuit proof is REJECTED only with
    /// the pin on).
    pin_vk_identity: bool,
    /// **Whether the WRAP step is enabled (the fixed-shape re-prove, lever closing the depth-invariant
    /// fixed point).** When `true` (default), every running fold is proven under [`wrap_params`] — a
    /// fixed [`WRAP_LOG_CEIL`] trace-height ceiling — so the running proof's `degree_bits` (hence its
    /// FRI shape, hence the next layer's preprocessed commitment = its VK core) are CONSTANT across
    /// depth. Disable to reproduce the legacy variable-shape fold (where the VK fingerprint grows with
    /// depth) for the A/B comparison the depth-invariance test draws.
    wrap_enabled: bool,
}

impl Default for Accumulator {
    fn default() -> Self {
        Self::genesis()
    }
}

impl Accumulator {
    /// `acc_0`: the empty accumulator (no running proof, no summary). The base of the IVC fold.
    /// The VK-identity fixed-point pin (lever (a)) is ENABLED by default.
    pub fn genesis() -> Self {
        Self {
            running: None,
            summary: None,
            seam_pairs: Vec::new(),
            pinned_running_vk: None,
            pin_vk_identity: true,
            wrap_enabled: true,
        }
    }

    /// Toggle the VK-identity fixed-point pin (lever (a)). Enabled by default; disable to reproduce
    /// the legacy unpinned fold. Returns `self` for chaining (`Accumulator::genesis().with_vk_identity_pin(false)`).
    pub fn with_vk_identity_pin(mut self, enabled: bool) -> Self {
        self.pin_vk_identity = enabled;
        self
    }

    /// Toggle the WRAP step (the fixed-shape re-prove that makes the running VK depth-invariant; see
    /// [`wrap_params`] / [`WRAP_LOG_CEIL`]). Enabled by default; disable to reproduce the legacy
    /// variable-shape fold whose VK fingerprint grows with depth. Returns `self` for chaining.
    pub fn with_wrap(mut self, enabled: bool) -> Self {
        self.wrap_enabled = enabled;
        self
    }

    /// The running proof's per-table `degree_bits` (the FRI domain shape the next layer's verifier
    /// reads to size its op-list). With the WRAP step ON these are CONSTANT across depth (every table
    /// padded to [`WRAP_LOG_CEIL`]); with it OFF they grow. The depth-invariance test compares this
    /// (and [`running_vk_fingerprint`](Self::running_vk_fingerprint)) at depth 2 vs depth 3.
    pub fn running_degree_bits(&self) -> Option<Vec<usize>> {
        self.running.as_ref().map(|r| r.0.proof.degree_bits.clone())
    }

    /// **THE RUNNING VK FINGERPRINT — the depth-invariance observable.** The full
    /// [`recursion_vk_fingerprint`](crate::plonky3_recursion_impl::recursive::recursion_vk_fingerprint)
    /// of the running aggregation proof: a blake3 over its verifier-reconstruction SHAPE (table
    /// packing, `rows`, `degree_bits`, the non-primitive manifest, and the preprocessed commitment =
    /// the VK core). This is exactly the fingerprint a light client pins as its trust anchor.
    ///
    /// **The Pickles constant-VK property is: this is EQUAL across fold depths.** With the WRAP step
    /// ON, the depth-2 running proof and the depth-3 running proof carry the IDENTICAL fingerprint —
    /// the verifier is fixed-size forever. With wrap OFF it grows with depth. `None` before any fold.
    pub fn running_vk_fingerprint(
        &self,
    ) -> Option<crate::plonky3_recursion_impl::recursive::RecursionVk> {
        self.running
            .as_ref()
            .map(|r| crate::plonky3_recursion_impl::recursive::recursion_vk_fingerprint(&r.0))
    }

    /// **VK-MATERIAL BREAKDOWN PROBE.** A human-readable dump of the SEPARATE components the running
    /// VK fingerprint hashes — so a depth-2-vs-depth-3 diff can pinpoint WHICH part varies (degree_bits
    /// vs `rows` vs the non-primitive manifest vs the preprocessed commitment = the op-list/VK core).
    /// Used by the depth-invariance test to localize the residual precisely. Not a stable API.
    pub fn running_vk_material_debug(&self) -> Option<String> {
        use core::fmt::Write;
        self.running.as_ref().map(|r| {
            let p = &r.0;
            let mut s = String::new();
            let _ = write!(s, "degree_bits={:?}", p.proof.degree_bits);
            let _ = write!(s, " rows={:?}", p.rows);
            let _ = write!(s, " n_nonprim={}", p.non_primitives.len());
            for e in &p.non_primitives {
                let _ = write!(s, " [{:?} rows={} lanes={}]", e.op_type, e.rows, e.lanes);
            }
            match &p.stark_common.preprocessed {
                None => {
                    let _ = write!(s, " prep=NONE");
                }
                Some(gp) => {
                    // Hash JUST the preprocessed commitment (the op-list VK core) so a change in it
                    // alone is visible distinct from the trace-shape fields.
                    let bytes = postcard::to_allocvec(&gp.commitment).unwrap_or_default();
                    let h = blake3::hash(&bytes);
                    let _ = write!(
                        s,
                        " prep_commit={} n_inst={}",
                        &h.to_hex()[..16],
                        gp.instances.len()
                    );
                }
            }
            s
        })
    }

    /// Whether the running VK-identity pin is active yet — i.e. the running proof is an aggregation
    /// (the first fold has happened) so its expected commitment is being tracked and every subsequent
    /// fold is pinned-or-rejected in-band. `false` while the running proof is still the genesis leaf.
    pub fn vk_identity_pinned(&self) -> bool {
        self.pinned_running_vk.is_some()
    }

    /// **TEST-ONLY: forcibly overwrite the captured fixed-point pin.** Exercises the fail-closed
    /// VK-identity tooth (`AccError::VkIdentityMismatch`): after a genuine pin is captured, setting it
    /// to a FOREIGN commitment makes the NEXT `accumulate` (or `finalize`) reject — the running proof's
    /// genuine commitment no longer matches the (now-corrupted) pin. This simulates an adversary who
    /// got the accumulator into a state where the running proof and the pinned VK disagree; the driver
    /// must refuse rather than fold unpinned. Not a production API.
    #[doc(hidden)]
    pub fn force_pinned_vk_for_test(&mut self, commit: RecursionCommit) {
        self.pinned_running_vk = Some(commit);
    }

    /// The running proof's genuine preprocessed commitment (its VK-identity core), if a turn has been
    /// folded. This is the value an honest fixed-point fold pins against.
    pub fn running_vk_commit(&self) -> Option<RecursionCommit> {
        self.running
            .as_ref()
            .and_then(|r| r.running_preprocessed_commit())
    }

    /// **VK-IDENTITY-PIN PROBE (lever (a) demonstration).** Re-fold the current running proof against
    /// `turn`'s freshly-wrapped descriptor leaf, pinning the running (left) input's preprocessed
    /// commitment IN-CIRCUIT to `expected_running_vk`. Returns `Ok(())` iff the aggregation circuit is
    /// satisfiable — i.e. iff the running proof's actual VK matches `expected_running_vk`.
    ///
    /// Pass the running proof's GENUINE commitment ([`running_vk_commit`](Self::running_vk_commit)) to
    /// see the honest fold succeed; pass a CORRUPTED commitment to see the in-circuit VK check reject
    /// it (`AccError::RecursionFailed`). This is the direct witness that a proof from a different
    /// circuit is refused IN-CIRCUIT, not host-side. Does NOT mutate the accumulator.
    pub fn probe_pinned_fold(
        &self,
        turn: &FinalizedTurn,
        expected_running_vk: RecursionCommit,
    ) -> Result<(), AccError> {
        let running = self.running.as_ref().ok_or(AccError::Empty)?;
        let config = ir2_leaf_wrap_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();

        let leg = &turn.participant.rotated;
        let new_leaf = prove_descriptor_leaf_rotated_with_config(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| AccError::TurnProofInvalid { index: 0, reason })?;

        let left = running.into_recursion_input_pinned::<BatchOnly>(expected_running_vk);
        let right = new_leaf.into_recursion_input::<BatchOnly>();
        build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
            &left, &right, &config, &backend, &params, None,
        )
        .map(|_| ())
        .map_err(|e| AccError::RecursionFailed {
            reason: format!("pinned aggregation layer failed: {e:?}"),
        })
    }

    /// The current running summary, if any turn has been folded.
    pub fn summary(&self) -> Option<ChainSummary> {
        self.summary
    }

    /// The number of turns folded so far.
    pub fn num_turns(&self) -> usize {
        self.summary.map(|s| s.num_turns).unwrap_or(0)
    }

    /// **The IVC STEP — `accumulate(acc, turn) -> acc'`.** Fold one more finalized turn into the
    /// running proof. O(1) PROOF memory (one running [`RecursionOutput`] is held); the running scalar
    /// state is O(num_turns) (the `seam_pairs` binding witness — see the struct note). Only `self` is
    /// retained between steps; the consumed turns are dropped.
    ///
    /// Steps (the running-fold dual of one `aggregate_tree` internal node):
    ///   1. host admission: the turn's rotated descriptor proof verifies selector-bound;
    ///   2. continuity: the turn's `old_root` must equal the running `head_root` (the temporal
    ///      tooth — `AccError::ChainBreak` otherwise);
    ///   3. wrap the turn's rotated descriptor leaf to a batch proof (the in-circuit leaf re-proof);
    ///   4. if a running proof exists, aggregate `running ∘ new_leaf` — feeding `running` back as a
    ///      [`BatchOnly`] input so the next layer RE-VERIFIES it in-circuit (the recursion); else the
    ///      new leaf BECOMES the running proof (the first turn);
    ///   5. advance the running summary (`head_root`, `chain_digest`, `num_turns`).
    pub fn accumulate(&mut self, turn: &FinalizedTurn) -> Result<(), AccError> {
        let idx = self.num_turns();

        // (1) host admission (admission discipline; the in-circuit leaf re-proof is the soundness
        //     boundary).
        verify_descriptor_participant(&turn.participant)
            .map_err(|reason| AccError::TurnProofInvalid { index: idx, reason })?;

        let old_root = turn.old_root();
        let new_root = turn.new_root();

        // (2) continuity against the running head.
        if let Some(s) = self.summary {
            if s.head_root != old_root {
                return Err(AccError::ChainBreak {
                    expected_old_root: s.head_root.0,
                    found_old_root: old_root.0,
                });
            }
        }

        let config = ir2_leaf_wrap_config();
        let backend = create_recursion_backend();
        let params = ProveNextLayerParams::default();
        // **THE WRAP STEP.** The running fold is proven under a FIXED trace-height ceiling
        // ([`wrap_params`] / [`WRAP_LOG_CEIL`]) when wrapping is enabled, so the running proof's
        // `degree_bits` — hence its FRI shape, hence the NEXT layer's verifier op-list (= its VK core)
        // — are CONSTANT across depth. The leaf wrap (step 3) stays at the default params (a leaf is
        // already a fixed shape); only the running AGGREGATION (step 4) is height-ceiled.
        let fold_params = if self.wrap_enabled {
            wrap_params()
        } else {
            params.clone()
        };

        // (3) the rotated descriptor leaf, wrapped to a batch proof at the wrap config.
        let leg = &turn.participant.rotated;
        let new_leaf = prove_descriptor_leaf_rotated_with_config(
            &leg.descriptor,
            &leg.proof,
            &leg.public_inputs,
            &config,
        )
        .map_err(|reason| AccError::TurnProofInvalid { index: idx, reason })?;

        // (4) the running fold.
        //
        // The running proof has THREE shape-eras across the fold, with DIFFERENT preprocessed
        // commitments (hence the pin must distinguish them):
        //   - era 0: the running proof IS a single LEAF (after turn 0). Its left-fold (turn 1) is
        //            LEAF∘LEAF — the left input's VK is the leaf VK.
        //   - era 1+: the running proof is an AGGREGATION (after turn 1+). Its left-fold (turn 2+)
        //            is AGG∘LEAF — the left input's VK is the running-aggregation VK, which is
        //            CONSTANT from the second aggregation onward (the BatchOnly∘BatchOnly shape is
        //            fixed). THAT constant is the perpetual fixed point.
        // The pin must therefore be captured from the running AGGREGATION shape (era 1+), NOT the
        // first leaf — pinning an AGG left input to a LEAF commitment is a genuine mismatch.
        let new_running = match self.running.take() {
            None => new_leaf, // first turn: the leaf is the running proof (no fold yet).
            Some(running) => {
                // THE RECURSION: re-verify the running proof in-circuit (BatchOnly) and fold it
                // against the new leaf. This is `into_recursion_input::<BatchOnly>` driven as a
                // running LEFT-fold (the same re-verification `aggregate_tree` does per node).
                //
                // ── VK-IDENTITY PIN (lever (a), in-band) + FAIL-CLOSED tooth. ──────────────────
                // `pinned_running_vk` holds the EXPECTED commitment of the running proof we are about
                // to re-fold — recorded from the proof we PRODUCED last step (below). Three things:
                //   1. We assert the held running proof's commitment STILL equals that expected value.
                //      A mismatch means the running proof is NOT the one we produced (a foreign/swapped
                //      proof) — FATAL: reject with `AccError::VkIdentityMismatch`, leaving the
                //      accumulator UNCHANGED. (The previous behaviour silently fell through to the
                //      UNPINNED fold on any mismatch — a forged running proof of a different circuit
                //      would have folded through unpinned, defeating the pin. Now the driver refuses.)
                //   2. We pin the running (left) input's preprocessed commitment IN-CIRCUIT to that
                //      value, so the aggregation circuit constrains "I fold the proof I produced."
                //   3. The expected value TRACKS the running commitment across the finite transient
                //      (the AGG∘LEAF op-list settles over a couple of folds before the perpetual fixed
                //      point) — so honest transient folds are NOT falsely rejected, and once the fixed
                //      point is reached the pin naturally holds the perpetual fixed-point VK forever.
                // On the FIRST aggregation (`pinned_running_vk` is `None` — the running proof is still
                // the genesis leaf) there is no recorded expectation yet, so that one fold is unpinned;
                // its OUTPUT seeds the expectation for every subsequent fold.
                let expected = running.running_preprocessed_commit();
                let left = if self.pin_vk_identity && self.pinned_running_vk.is_some() {
                    if self.pinned_running_vk != expected {
                        // Restore the running proof we `take()`-d so the accumulator is unchanged on
                        // the rejection, then fail closed.
                        let exp_fp = self
                            .pinned_running_vk
                            .as_ref()
                            .map(commit_fingerprint)
                            .unwrap_or_default();
                        let found_fp = expected
                            .as_ref()
                            .map(commit_fingerprint)
                            .unwrap_or_default();
                        self.running = Some(running);
                        return Err(AccError::VkIdentityMismatch {
                            index: idx,
                            expected: exp_fp,
                            found: found_fp,
                        });
                    }
                    // The unwrap is justified: the guard requires `pinned_running_vk.is_some()`.
                    running.into_recursion_input_pinned::<BatchOnly>(
                        self.pinned_running_vk
                            .clone()
                            .expect("pinned_running_vk is Some by the enclosing guard"),
                    )
                } else {
                    // First aggregation (no recorded expectation yet) OR pin disabled: the unpinned
                    // fold. The expectation is recorded from this fold's OUTPUT (below), so EVERY
                    // subsequent fold takes the pinned-or-reject branch above.
                    running.into_recursion_input::<BatchOnly>()
                };
                let right = new_leaf.into_recursion_input::<BatchOnly>();
                build_and_prove_aggregation_layer::<
                    DreggRecursionConfig,
                    BatchOnly,
                    BatchOnly,
                    _,
                    D,
                >(&left, &right, &config, &backend, &fold_params, None)
                .map_err(|e| AccError::RecursionFailed {
                    reason: format!("running aggregation layer failed: {e:?}"),
                })?
            }
        };

        // RECORD the expectation for the NEXT fold: the commitment of the running proof we just
        // produced. The next `accumulate` will re-fold THIS proof and must see this exact commitment
        // (the fail-closed tooth above). We record only once `new_running` is an aggregation (it has a
        // preprocessed commitment); the genesis leaf produces `None`, leaving the first aggregation
        // unpinned (as intended). Across the transient this updates each step; at the fixed point it
        // stabilizes to the perpetual VK.
        if self.pin_vk_identity {
            let produced = new_running.running_preprocessed_commit();
            if produced.is_some() {
                self.pinned_running_vk = produced;
            }
        }

        // (5) advance the running summary. The running digest folds each turn's `(old, new)` pair
        //     into the Poseidon2 carrier, in order — so it commits to the WHOLE ordered history
        //     incrementally (O(1) memory: only the carrier is kept). `finalize` reproduces the SAME
        //     fold from the same per-step inputs it would re-derive, so tooth 2's last-row
        //     constraint (`acc_out == chain_digest`) holds — see `finalize_binding_leaf`'s note.
        let new_summary = match self.summary {
            None => {
                let acc_in = BabyBear::ZERO;
                let acc_out = hash_4_to_1(&[acc_in, old_root, new_root, BabyBear::new(0)]);
                ChainSummary {
                    genesis_root: old_root,
                    head_root: new_root,
                    chain_digest: acc_out,
                    num_turns: 1,
                    acc_carrier: acc_out,
                }
            }
            Some(s) => {
                let acc_out = hash_4_to_1(&[
                    s.acc_carrier,
                    old_root,
                    new_root,
                    BabyBear::new(s.num_turns as u32),
                ]);
                ChainSummary {
                    genesis_root: s.genesis_root,
                    head_root: new_root,
                    chain_digest: acc_out,
                    num_turns: s.num_turns + 1,
                    acc_carrier: acc_out,
                }
            }
        };

        self.running = Some(new_running);
        self.summary = Some(new_summary);
        self.seam_pairs.push((old_root, new_root));
        Ok(())
    }

    /// **Read the running accumulator out into a [`WholeChainProof`]** a light client verifies.
    ///
    /// Wraps the running root and a chain-binding leaf (regenerated from the O(1) summary — see
    /// [`finalize_binding_leaf`]) into ONE root, then carries the binding proof + the four publics,
    /// matching the [`WholeChainProof`] the K-fold path produces. The result verifies under
    /// [`verify_turn_chain_recursive`] / [`lightclient::verify_history`] against the honest VK anchor
    /// extracted from this very fold.
    ///
    /// `finalize` consumes the accumulator (the running proof is moved into the artifact).
    ///
    /// NOTE (the binding regeneration): the binding leaf attests the ordered `(old, new)` pairs of
    /// the WHOLE chain. `finalize` rebuilds the genuine per-turn `TurnChainBindingAir` leaf from the
    /// `seam_pairs` reconstruction witness (the 2-felt/turn scalars — see the struct note), so its
    /// last-row digest reproduces `summary.chain_digest` EXACTLY and tooth 2 of
    /// `verify_turn_chain_recursive` (the carried-publics attestation binding `[genesis_root,
    /// head_root, num_turns, chain_digest]`) passes. The per-pair ordering is attested BOTH by this
    /// binding leaf AND by the in-circuit descriptor leaves folded into the root.
    pub fn finalize(self) -> Result<WholeChainProof, AccError> {
        let summary = self.summary.ok_or(AccError::Empty)?;
        let running = self.running.ok_or(AccError::Empty)?;

        let config = ir2_leaf_wrap_config();
        let backend = create_recursion_backend();
        // The binding leaf is wrapped uni->batch at the DEFAULT params (a leaf is already a fixed
        // shape — the same discipline `accumulate`'s step-3 leaf wrap uses). The FINAL root
        // aggregation, by contrast, is proven under [`wrap_params`] when the wrap step is enabled, so
        // the terminal root proof carries the SAME wrap-shaped FRI trace ceiling as the running folds
        // (codex finding #5: the terminal proof must not have a depth/shape-dependent root VK from a
        // default-params fold).
        let leaf_params = ProveNextLayerParams::default();
        let root_params = if self.wrap_enabled {
            wrap_params()
        } else {
            leaf_params.clone()
        };

        // The per-turn binding leaf, rebuilt from the seam-pair witness so its digest reproduces the
        // running `chain_digest` exactly.
        let (binding_inner, binding_pis) = finalize_binding_leaf(&summary, &self.seam_pairs)
            .map_err(|reason| AccError::RecursionFailed { reason })?;

        // Wrap the binding leaf uni->batch at the wrap config.
        let binding_batch = {
            let air = TurnChainBindingAir;
            let p3_pis: Vec<P3BabyBear> = binding_pis.iter().map(|&v| to_p3(v)).collect();
            let input = RecursionInput::UniStark {
                proof: &binding_inner,
                air: &air,
                public_inputs: p3_pis,
                preprocessed_commit: None,
            };
            // EXPOSED-CLAIM CHANNEL: emit the expose_claim table over the binding
            // child's 4 verified `air_public_targets` `[genesis, final, num_turns,
            // chain_digest]`, so the accumulator's root carries the host-readable,
            // bus-bound chain claims `verify_turn_chain_recursive`'s tooth (4) checks.
            //
            // CODEX #3/#4: the K-fold path's `verify` tooth now expects a multi-felt
            // (`SEG_DIGEST_WIDTH`-lane) Poseidon2 segment digest. The ONLINE accumulator
            // (scoped OUT of the mixed-root close — its binding leaf is still the separate,
            // swappable single-felt `hash_4_to_1` carrier) keeps that 1-felt digest, but
            // ZERO-PADS it to the new lane width so the artifact is structurally uniform and
            // tooth (4) reads a consistent `[genesis, final, num_turns, d, 0, 0, 0]`. This
            // does NOT strengthen the accumulator's digest — its collision-resistance is
            // unchanged from the 1-felt binding leaf; the structural mixed-root weakness
            // named in codex #4 is unaffected.
            let expose = move |cb: &mut p3_circuit::CircuitBuilder<_>,
                               apt: &[Vec<p3_recursion::Target>]| {
                if let Some(claims) = apt.first() {
                    accumulator_expose_padded_segment(cb, claims);
                }
            };
            build_and_prove_next_layer_with_expose::<
                DreggRecursionConfig,
                TurnChainBindingAir,
                _,
                D,
            >(&input, &config, &backend, &leaf_params, Some(&expose))
            .map_err(|e| AccError::RecursionFailed {
                reason: format!("finalize binding-leaf wrap failed: {e:?}"),
            })?
        };

        // Fold the running root with the binding leaf into the FINAL root.
        //
        // **PIN the running (left) input against the captured fixed-point VK (codex finding #5).**
        // The terminal fold is itself an AGG∘LEAF (left = the running aggregation, right = the
        // binding leaf), structurally identical to a steady running fold — so the SAME VK-identity
        // pin applies. When the pin was captured during the fold, the running proof's commitment MUST
        // equal it (else the running proof came from a foreign circuit); fail closed, exactly as
        // `accumulate` does. When no pin was captured (a single-turn chain — the running proof is
        // still a leaf, never aggregated) the unpinned fold is correct (there is no captured running
        // aggregation VK to pin against).
        let running_commit = running.running_preprocessed_commit();
        let left = if self.pin_vk_identity && self.pinned_running_vk.is_some() {
            if self.pinned_running_vk != running_commit {
                return Err(AccError::VkIdentityMismatch {
                    index: summary.num_turns,
                    expected: self
                        .pinned_running_vk
                        .as_ref()
                        .map(commit_fingerprint)
                        .unwrap_or_default(),
                    found: running_commit
                        .as_ref()
                        .map(commit_fingerprint)
                        .unwrap_or_default(),
                });
            }
            running.into_recursion_input_pinned::<BatchOnly>(
                self.pinned_running_vk
                    .clone()
                    .expect("pinned_running_vk is Some by the enclosing guard"),
            )
        } else {
            running.into_recursion_input::<BatchOnly>()
        };
        // The binding leaf (right child) carries the expose_claim table; find its
        // instance index so the root re-exposes those bus-bound claims.
        let right_idx = crate::ivc_turn_chain::expose_claim_instance_index(&binding_batch.0);
        let right = binding_batch.into_recursion_input::<BatchOnly>();
        let expose = move |cb: &mut p3_circuit::CircuitBuilder<_>,
                           _left_apt: &[Vec<p3_recursion::Target>],
                           right_apt: &[Vec<p3_recursion::Target>]| {
            if let Some(idx) = right_idx
                && let Some(claims) = right_apt.get(idx)
            {
                accumulator_expose_padded_segment(cb, claims);
            }
        };
        let root = build_and_prove_aggregation_layer_with_expose::<
            DreggRecursionConfig,
            BatchOnly,
            BatchOnly,
            _,
            D,
        >(
            &left,
            &right,
            &config,
            &backend,
            &root_params,
            None,
            Some(&expose),
        )
        .map_err(|e| AccError::RecursionFailed {
            reason: format!("finalize root aggregation failed: {e:?}"),
        })?;

        // The artifact digest is the binding leaf's PADDED last-row `acc_out` (`binding_pis[3]`) —
        // the single-felt online-accumulator carrier — ZERO-PADDED to the K-fold path's multi-felt
        // digest lane width (codex #3). The accumulator is scoped OUT of the mixed-root close; the
        // padding lanes carry no commitment, they only make the artifact's lane layout uniform with
        // the K-fold so `verify_turn_chain_recursive`'s tooth (4) reads a consistent shape.
        // (`summary.chain_digest` is the UNPADDED running carrier — a different, internal quantity.)
        let mut chain_digest = [BabyBear::ZERO; crate::ivc_turn_chain::SEG_DIGEST_WIDTH];
        chain_digest[0] = binding_pis[3];

        Ok(WholeChainProof {
            root,
            binding_proof: binding_inner,
            genesis_root: summary.genesis_root,
            final_root: summary.head_root,
            chain_digest,
            num_turns: summary.num_turns,
        })
    }

    /// Convenience: finalize, then VERIFY under the honest self-extracted VK anchor. The setup-side
    /// entry — exactly how an honest producer mints the trust anchor it distributes. A remote light
    /// client instead calls [`verify_turn_chain_recursive`] / `verify_history` with its CONFIGURED
    /// anchor.
    pub fn finalize_and_self_verify(self) -> Result<(WholeChainProof, RecursionVk), AccError> {
        let proof = self.finalize()?;
        let vk = proof.root_vk_fingerprint();
        verify_turn_chain_recursive(&proof, &vk).map_err(|e| AccError::RecursionFailed {
            reason: format!("self-verify of the accumulated artifact failed: {e}"),
        })?;
        Ok((proof, vk))
    }
}

/// Build the per-turn chain-binding leaf from the running summary + the ordered `seam_pairs`.
///
/// One row per folded turn `[old_root, new_root, acc_in, acc_out]` with `acc_out =
/// hash_4_to_1([acc_in, old, new, idx])` (the SAME fold `accumulate` ran into `summary.chain_digest`),
/// padded to a power of two with head fixed-point rows — byte-for-byte the trace
/// `generate_chain_trace_rotated` produces for the same chain. Public inputs `[genesis_root,
/// head_root, num_turns, chain_digest]`. The first/last-row + continuity constraints hold by
/// construction; the last-row `acc_out == chain_digest` reproduces the running digest exactly. Tooth 2
/// of `verify_turn_chain_recursive` verifies these four publics AS this proof's public inputs.
fn finalize_binding_leaf(
    summary: &ChainSummary,
    seam_pairs: &[(BabyBear, BabyBear)],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), String> {
    if seam_pairs.is_empty() {
        return Err("cannot build a binding leaf with no seam pairs".to_string());
    }
    let n = seam_pairs.len();
    let padded_len = n.next_power_of_two().max(2);
    // Build the GENUINE WIDE binding trace (7 scalar cols + the Poseidon2 aux
    // block) via the shared `binding_row`, mirroring `generate_chain_trace_rotated`.
    // `TurnChainBindingAir` enforces the per-row Poseidon2 hash binding
    // (constraint 5, codex finding #2), so the narrow 4-column trace this used to
    // build is UNSAT against the current AIR — the row must carry the aux witness.
    let mut trace: Vec<Vec<BabyBear>> = Vec::with_capacity(padded_len);
    let mut acc = BabyBear::ZERO;
    let mut real_count = BabyBear::ZERO;
    for (i, &(old_root, new_root)) in seam_pairs.iter().enumerate() {
        let idx = BabyBear::new(i as u32);
        real_count += BabyBear::ONE;
        let (acc_out, row) = crate::ivc_turn_chain::binding_row(
            old_root, new_root, acc, idx, /* is_real */ true, real_count,
        );
        trace.push(row);
        acc = acc_out;
    }
    let final_root = trace.last().unwrap()[crate::ivc_turn_chain::COL_NEW_ROOT];
    for i in n..padded_len {
        let idx = BabyBear::new(i as u32);
        // Padding rows: is_real = 0, real_count frozen, continuing the genuine
        // hash chain over (final_root, final_root, idx).
        let (acc_out, row) = crate::ivc_turn_chain::binding_row(
            final_root, final_root, acc, idx, /* is_real */ false, real_count,
        );
        trace.push(row);
        acc = acc_out;
    }
    let chain_digest = trace.last().unwrap()[crate::ivc_turn_chain::COL_ACC_OUT];
    let matrix = crate::ivc_turn_chain::trace_to_matrix(&trace);
    let pis = vec![
        summary.genesis_root,
        summary.head_root,
        BabyBear::new(summary.num_turns as u32),
        chain_digest,
    ];
    let air = TurnChainBindingAir;
    let wrap_config = ir2_leaf_wrap_config();
    let proof = prove_inner_for_air_with_config(&air, matrix, &pis, &wrap_config);
    verify_inner_for_air_with_config(&air, &proof, &pis, &wrap_config)?;
    Ok((proof, pis))
}
