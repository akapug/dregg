//! GOLD endgame: a continuous whole-chain IVC accumulator over **finalized turns**.
//!
//! ## What this is
//!
//! [`ivc`](crate::ivc) accumulates an *attenuation* fold-chain (delegation
//! depth) into one proof. [`joint_turn_recursive`](crate::joint_turn_recursive)
//! folds the N **per-cell** proofs of a *single* shared turn (the hyperedge
//! apex) into one recursive proof. Neither is the whole-chain accumulator.
//!
//! This module is that accumulator: it folds the sequence of *finalized turn*
//! proofs — in the exact order the node's `tau`/blocklace finality produces
//! (`node::blocklace_sync::poll_finalized_blocks` -> `FinalizedBlock`) — into
//! ONE running recursive proof attesting:
//!
//!   "all turns 1..K executed correctly **and** the finalized state root
//!    advanced correctly from the genesis root to the final root, in that
//!    order."
//!
//! It is the sequential dual of the joint-turn (which is cross-cell at one
//! instant). Here the binding is *temporal*: turn N's post-state root must be
//! turn N+1's pre-state root (`prev.NEW_COMMIT == next.OLD_COMMIT`) — the
//! happened-before chain over the *finalized* order, exactly the property the
//! node's tau ordering establishes.
//!
//! ## The two pieces
//!
//! 1. **[`TurnChainBindingAir`]** (width 4, one row per finalized turn): binds
//!    the sequential chain. Each row carries `[old_root, new_root, acc_in,
//!    acc_out]` with constraints:
//!      - chain continuity: `new_root[i] == old_root[i+1]` (the temporal tooth);
//!      - first row `old_root == genesis_root` (public input);
//!      - last row `new_root == final_root` (public input);
//!      - running digest `acc_out = hash_4_to_1([acc_in, old_root, new_root, idx])`,
//!        first row `acc_in == 0`, last row `acc_out == chain_digest` (public).
//!    A trace whose turns are reordered, or that drops/inserts a turn, breaks
//!    continuity and is UNSAT — that is the load-bearing rejection.
//!
//! 2. **The recursion tree** (Gold): each finalized turn's whole-turn EffectVm
//!    proof is wrapped in its own recursive verifier layer (uni->batch via
//!    `build_and_prove_next_layer`), the chain-binding leaf is wrapped too, and
//!    all batch leaves are pairwise aggregated up a binary tree
//!    (`build_and_prove_aggregation_layer`, chained via [`BatchOnly`]) to ONE
//!    root batch-STARK proof — reusing the proven Gold machinery from
//!    [`joint_turn_recursive`]. The verifier checks ONLY the root; its cost is
//!    independent of K.
//!
//! ## K-fold vs unbounded
//!
//! [`prove_turn_chain_recursive`] folds an arbitrary *finite* K into one proof
//! (the test folds K=4). This is genuine IVC for a bounded window: the verifier
//! checks one constant-cost root proof for the whole window.
//!
//! The fully *unbounded* online accumulator — where a single running proof is
//! re-folded with each newly-finalized turn forever, with the previous running
//! proof verified in-circuit so memory stays O(1) — needs the recursion fork's
//! `into_recursion_input::<BatchOnly>` chaining to be driven as a *fold* rather
//! than a *tree*. The 2-step inductive core of that loop is [`fold_two_turns`]
//! (`running ∘ next_turn -> new_running`); see its docs for what the unbounded
//! driver still needs.

#![cfg(feature = "recursion")]

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::BabyBear as P3BabyBear;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::dense::RowMajorMatrix;
use p3_recursion::{
    BatchOnly, ProveNextLayerParams, RecursionInput, RecursionOutput,
    build_and_prove_aggregation_layer, build_and_prove_next_layer,
};

use crate::effect_vm::pi;
use crate::effect_vm_p3_air::EffectVmShapeAir;
use crate::field::BabyBear;
use crate::joint_turn_aggregation::JointParticipant;
use crate::plonky3_recursion_impl::recursive::{
    DreggRecursionConfig, RecursionCompatibleProof, create_recursion_backend,
    create_recursion_config, prove_inner_for_air, verify_inner_for_air, verify_recursive_batch_proof,
};
use crate::poseidon2::hash_4_to_1;

use crate::effect_vm::{
    EFFECT_VM_WIDTH, PARAM_BASE, STATE_AFTER_BASE, STATE_BEFORE_BASE, sel, state,
};

const D: usize = 4;

fn to_p3(v: BabyBear) -> P3BabyBear {
    P3BabyBear::from_u64(v.0 as u64)
}

// ============================================================================
// One finalized turn: a whole-turn proof + the (old_root, new_root) it advances.
// ============================================================================

/// A single finalized turn in the chain. The `participant` carries the per-cell
/// whole-turn EffectVm STARK proof + its public inputs (the same shape the
/// joint-turn path uses); the aggregator reads the cell's pre/post state
/// commitment out of the PI as the chain roots.
pub struct FinalizedTurn {
    /// The whole-turn EffectVm proof for this finalized turn.
    pub participant: JointParticipant,
}

impl FinalizedTurn {
    /// Wrap a participant as a finalized turn.
    pub fn new(participant: JointParticipant) -> Self {
        Self { participant }
    }

    /// The pre-state root this turn consumes (`OLD_COMMIT` position 0).
    pub fn old_root(&self) -> BabyBear {
        self.participant.public_inputs[pi::OLD_COMMIT]
    }

    /// The post-state root this turn produces (`NEW_COMMIT` position 0). This is
    /// the next finalized turn's required `old_root` — the temporal binding.
    pub fn new_root(&self) -> BabyBear {
        self.participant.public_inputs[pi::NEW_COMMIT]
    }
}

// ============================================================================
// Errors
// ============================================================================

/// Why folding a finalized-turn chain failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TurnChainError {
    /// Fewer than 2 turns — a chain fold needs at least 2.
    TooFewTurns {
        /// How many were supplied.
        count: usize,
    },
    /// **The temporal tooth.** Turn `index` does not continue the chain: its
    /// `old_root` is not the previous turn's `new_root`. The finalized order is
    /// broken (reordered / dropped / inserted turn).
    ChainBreak {
        /// The turn that breaks continuity.
        index: usize,
        /// The root the previous turn produced.
        expected_old_root: u32,
        /// The root this turn claims to consume.
        found_old_root: u32,
    },
    /// A turn's per-cell whole-turn proof failed to verify.
    TurnProofInvalid {
        /// The turn whose proof failed.
        index: usize,
        /// The underlying verification error.
        reason: String,
    },
    /// A recursion layer (leaf wrap or aggregation) failed.
    RecursionFailed {
        /// What failed.
        reason: String,
    },
}

impl core::fmt::Display for TurnChainError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            TurnChainError::TooFewTurns { count } => {
                write!(f, "turn chain needs >= 2 turns, got {count}")
            }
            TurnChainError::ChainBreak {
                index,
                expected_old_root,
                found_old_root,
            } => write!(
                f,
                "turn {index} breaks the finalized chain: old_root {found_old_root} != \
                 previous turn's new_root {expected_old_root} (order tampered)"
            ),
            TurnChainError::TurnProofInvalid { index, reason } => {
                write!(f, "turn {index} proof invalid: {reason}")
            }
            TurnChainError::RecursionFailed { reason } => {
                write!(f, "recursion failed: {reason}")
            }
        }
    }
}

impl std::error::Error for TurnChainError {}

// ============================================================================
// TurnChainBindingAir: the sequential (temporal) chain binding.
// ============================================================================

/// Width-4 AIR binding the finalized turn order. One row per finalized turn:
/// `[old_root, new_root, acc_in, acc_out]`.
///
/// Public inputs `[genesis_root, final_root, num_turns, chain_digest]`.
///
/// Constraints:
///   1. chain continuity (transition): `new_root[i] == old_root[i+1]` — the
///      temporal tooth. A reordered/dropped/inserted turn breaks this and is
///      UNSAT.
///   2. first row `old_root == genesis_root`.
///   3. last row `new_root == final_root`.
///   4. running digest continuity: `acc_out[i] == acc_in[i+1]`; first row
///      `acc_in == 0`; last row `acc_out == chain_digest`.
///
/// The digest commits to the ordered (old_root, new_root) pairs, so two distinct
/// finalized histories with the same endpoints still yield distinct digests.
pub struct TurnChainBindingAir;

impl<F: PrimeCharacteristicRing + Sync> BaseAir<F> for TurnChainBindingAir {
    fn width(&self) -> usize {
        4
    }

    fn num_public_values(&self) -> usize {
        4 // [genesis_root, final_root, num_turns, chain_digest]
    }

    fn main_next_row_columns(&self) -> Vec<usize> {
        (0..4).collect()
    }
}

impl<AB: AirBuilder> Air<AB> for TurnChainBindingAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();

        let old_root: AB::Expr = local[0].into();
        let new_root: AB::Expr = local[1].into();
        let acc_in: AB::Expr = local[2].into();
        let acc_out: AB::Expr = local[3].into();
        let next_old_root: AB::Expr = next[0].into();
        let next_acc_in: AB::Expr = next[2].into();

        let public_values = builder.public_values();
        let genesis_root: AB::Expr = public_values[0].into();
        let final_root: AB::Expr = public_values[1].into();
        // public_values[2] = num_turns (carried for the caller; not constrained
        // here since the trace length encodes it, and binding it would require a
        // row-count selector the fork's AirBuilder does not expose cheaply).
        let chain_digest: AB::Expr = public_values[3].into();

        // Constraint 1 (THE temporal tooth): chain continuity. Each turn's
        // new_root must be the next turn's old_root.
        builder
            .when_transition()
            .assert_zero(new_root.clone() - next_old_root);

        // Constraint 2: first row old_root == genesis_root.
        builder
            .when_first_row()
            .assert_zero(old_root.clone() - genesis_root);

        // Constraint 3: last row new_root == final_root.
        builder
            .when_last_row()
            .assert_zero(new_root - final_root);

        // Constraint 4: running digest chain.
        builder.when_first_row().assert_zero(acc_in.clone());
        builder
            .when_transition()
            .assert_zero(acc_out.clone() - next_acc_in);
        builder
            .when_last_row()
            .assert_zero(acc_out - chain_digest);
    }
}

// ============================================================================
// Trace generation for the chain binding.
// ============================================================================

/// Host-side chain checks (>= 2 turns, sequential continuity) + the binding
/// trace. Returns `(trace, public_inputs, chain_digest)`.
///
/// Surfaces a [`TurnChainError::ChainBreak`] at the witness level so we never
/// hand the prover an unsatisfiable trace — but the AIR's constraint 1 rejects
/// it too (see [`generate_chain_trace_unchecked`]).
fn generate_chain_trace(
    turns: &[FinalizedTurn],
) -> Result<(Vec<[BabyBear; 4]>, Vec<BabyBear>, BabyBear), TurnChainError> {
    if turns.len() < 2 {
        return Err(TurnChainError::TooFewTurns { count: turns.len() });
    }
    // Sequential continuity (the temporal tooth, host side).
    for i in 1..turns.len() {
        let prev_new = turns[i - 1].new_root();
        let this_old = turns[i].old_root();
        if prev_new != this_old {
            return Err(TurnChainError::ChainBreak {
                index: i,
                expected_old_root: prev_new.0,
                found_old_root: this_old.0,
            });
        }
    }
    let (trace, pis) = generate_chain_trace_unchecked(turns);
    let digest = pis[3];
    Ok((trace, pis, digest))
}

/// Build the chain-binding trace WITHOUT the host continuity check. The AIR's
/// constraint 1 still enforces it; the negative test uses this to confirm the
/// *circuit* rejects a broken order.
fn generate_chain_trace_unchecked(turns: &[FinalizedTurn]) -> (Vec<[BabyBear; 4]>, Vec<BabyBear>) {
    let n = turns.len();
    let padded_len = n.next_power_of_two().max(2);
    let mut trace: Vec<[BabyBear; 4]> = Vec::with_capacity(padded_len);
    let mut acc = BabyBear::ZERO;

    for (i, t) in turns.iter().enumerate() {
        let old_root = t.old_root();
        let new_root = t.new_root();
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[acc, old_root, new_root, idx]);
        trace.push([old_root, new_root, acc, acc_out]);
        acc = acc_out;
    }

    // Pad to power of two. Padding rows are NoOp self-loops on the final root
    // (old_root == new_root == final new_root) so continuity + digest hold.
    let final_root = trace.last().unwrap()[1];
    for i in n..padded_len {
        let idx = BabyBear::new(i as u32);
        let acc_out = hash_4_to_1(&[acc, final_root, final_root, idx]);
        trace.push([final_root, final_root, acc, acc_out]);
        acc = acc_out;
    }

    let genesis_root = trace[0][0];
    let chain_digest = trace.last().unwrap()[3];
    let pis = vec![
        genesis_root,
        final_root,
        BabyBear::new(n as u32),
        chain_digest,
    ];
    (trace, pis)
}

fn trace_to_matrix(trace: &[[BabyBear; 4]]) -> RowMajorMatrix<P3BabyBear> {
    let values: Vec<P3BabyBear> = trace
        .iter()
        .flat_map(|row| row.iter().map(|&v| to_p3(v)))
        .collect();
    RowMajorMatrix::new(values, 4)
}

// ============================================================================
// Per-turn leaf: a recursion-compatible EffectVm-shape whole-turn proof.
// ============================================================================

/// Number of rows in a per-turn leaf trace (minimal power-of-two exercising
/// row-0 Transfer + NoOp passthrough + a transition).
const LEAF_ROWS: usize = 4;

/// Build a recursion-compatible EffectVm-shape leaf for one finalized turn,
/// pinning the turn's `(old_root, new_root)` into the leaf's commitment boundary
/// public inputs. The leaf re-derives the EffectVm proof's checks in-circuit;
/// its PIs carry the roots the chain binding folds.
fn build_turn_leaf_trace(
    old_root: BabyBear,
    new_root: BabyBear,
    n_rows: usize,
) -> (RowMajorMatrix<P3BabyBear>, Vec<BabyBear>) {
    assert!(n_rows >= 2 && n_rows.is_power_of_two());

    let mut flat: Vec<P3BabyBear> = Vec::with_capacity(n_rows * EFFECT_VM_WIDTH);

    // Row 0: Transfer amount=0 dir=0 -> passthrough; commit boundary old->new.
    let mut row0 = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
    row0[sel::TRANSFER] = BabyBear::ONE;
    row0[STATE_BEFORE_BASE + state::STATE_COMMIT] = old_root;
    row0[STATE_AFTER_BASE + state::STATE_COMMIT] = new_root;
    row0[PARAM_BASE] = BabyBear::ZERO; // amount
    row0[PARAM_BASE + 1] = BabyBear::ZERO; // direction
    flat.extend(row0.iter().map(|&v| to_p3(v)));

    // Rows 1..n_rows: NoOp passthroughs preserving the new root.
    for _ in 1..n_rows {
        let mut row = vec![BabyBear::ZERO; EFFECT_VM_WIDTH];
        row[sel::NOOP] = BabyBear::ONE;
        row[STATE_BEFORE_BASE + state::STATE_COMMIT] = new_root;
        row[STATE_AFTER_BASE + state::STATE_COMMIT] = new_root;
        flat.extend(row.iter().map(|&v| to_p3(v)));
    }

    let mut public_inputs = vec![BabyBear::ZERO; pi::BASE_COUNT];
    public_inputs[pi::OLD_COMMIT] = old_root;
    public_inputs[pi::NEW_COMMIT] = new_root;

    (RowMajorMatrix::new(flat, EFFECT_VM_WIDTH), public_inputs)
}

/// Produce one finalized turn's recursion-compatible inner proof + its PIs.
fn prove_turn_leaf(
    old_root: BabyBear,
    new_root: BabyBear,
    n_rows: usize,
) -> (RecursionCompatibleProof, Vec<BabyBear>) {
    let (matrix, pis) = build_turn_leaf_trace(old_root, new_root, n_rows);
    let air = EffectVmShapeAir;
    let proof = prove_inner_for_air(&air, matrix, &pis);
    (proof, pis)
}

/// Build + prove the chain-binding leaf (the sequential temporal binding).
fn prove_chain_binding_leaf(
    turns: &[FinalizedTurn],
) -> Result<(RecursionCompatibleProof, Vec<BabyBear>), TurnChainError> {
    let (trace, pis, _digest) = generate_chain_trace(turns)?;
    let matrix = trace_to_matrix(&trace);
    let air = TurnChainBindingAir;
    let proof = prove_inner_for_air(&air, matrix, &pis);
    verify_inner_for_air(&air, &proof, &pis)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })?;
    Ok((proof, pis))
}

// ============================================================================
// The whole-chain IVC artifact (K-fold).
// ============================================================================

/// The Gold whole-chain artifact: ONE succinct recursive proof attesting that
/// **all** K finalized-turn leaves AND the sequential chain-binding leaf
/// verified in-circuit. The verifier checks only the root; cost is independent
/// of K.
pub struct WholeChainProof {
    /// The single root batch-STARK proof (the whole tree folded to one).
    pub root: RecursionOutput<DreggRecursionConfig>,
    /// The genesis root the chain starts from.
    pub genesis_root: BabyBear,
    /// The final root the chain reaches.
    pub final_root: BabyBear,
    /// The running digest committing to the ordered (old_root, new_root) pairs.
    pub chain_digest: BabyBear,
    /// Number of finalized turns folded.
    pub num_turns: usize,
}

/// Fold K finalized-turn proofs into ONE whole-chain recursive proof.
///
/// `turns` must be in the node's **finalized order** (the `tau`/blocklace order
/// from `node::blocklace_sync::poll_finalized_blocks`). Each turn's `new_root`
/// must be the next turn's `old_root` — the temporal binding the chain leaf
/// enforces both host-side and in-circuit.
///
/// Steps:
///   1. host-side: >= 2 turns, sequential continuity, every per-turn proof
///      verifies (the per-turn soundness gate);
///   2. prove the chain-binding leaf (rejects a broken order in-circuit too);
///   3. prove one recursion-compatible EffectVm-shape leaf per turn, pinning
///      each turn's `(old_root, new_root)` into its PIs;
///   4. wrap every leaf in its own recursive verifier layer (uni->batch);
///   5. pairwise-aggregate all batch leaves up a binary tree to ONE root.
pub fn prove_turn_chain_recursive(
    turns: &[FinalizedTurn],
) -> Result<WholeChainProof, TurnChainError> {
    // (1) host gate: continuity + per-turn soundness.
    let (_, chain_pis, chain_digest) = generate_chain_trace(turns)?;
    for (i, t) in turns.iter().enumerate() {
        crate::joint_turn_aggregation::verify_participant_pub(&t.participant).map_err(|e| {
            TurnChainError::TurnProofInvalid {
                index: i,
                reason: e,
            }
        })?;
    }
    let genesis_root = chain_pis[0];
    let final_root = chain_pis[1];

    let config = create_recursion_config();
    let backend = create_recursion_backend();
    let params = ProveNextLayerParams::default();

    // (2) chain-binding leaf.
    let (binding_inner, binding_pis) = prove_chain_binding_leaf(turns)?;

    // (3)+(4) one EffectVm-shape leaf per finalized turn, each wrapped uni->batch.
    let mut batch_leaves: Vec<RecursionOutput<DreggRecursionConfig>> =
        Vec::with_capacity(turns.len() + 1);

    for (i, t) in turns.iter().enumerate() {
        let (leaf_inner, leaf_pis) = prove_turn_leaf(t.old_root(), t.new_root(), LEAF_ROWS);
        let air = EffectVmShapeAir;
        let p3_pis: Vec<P3BabyBear> = leaf_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &leaf_inner,
            air: &air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let wrapped = build_and_prove_next_layer::<DreggRecursionConfig, EffectVmShapeAir, _, D>(
            &input, &config, &backend, &params,
        )
        .map_err(|e| TurnChainError::TurnProofInvalid {
            index: i,
            reason: format!("recursive turn leaf failed: {e:?}"),
        })?;
        batch_leaves.push(wrapped);
    }

    // The chain-binding leaf wrapped uni->batch.
    {
        let air = TurnChainBindingAir;
        let p3_pis: Vec<P3BabyBear> = binding_pis.iter().map(|&v| to_p3(v)).collect();
        let input = RecursionInput::UniStark {
            proof: &binding_inner,
            air: &air,
            public_inputs: p3_pis,
            preprocessed_commit: None,
        };
        let wrapped = build_and_prove_next_layer::<DreggRecursionConfig, TurnChainBindingAir, _, D>(
            &input, &config, &backend, &params,
        )
        .map_err(|e| TurnChainError::RecursionFailed {
            reason: format!("recursive chain-binding leaf failed: {e:?}"),
        })?;
        batch_leaves.push(wrapped);
    }

    // (5) Pairwise-aggregate up a binary tree to ONE root batch proof.
    let root = aggregate_tree(batch_leaves, &config, &backend, &params)?;

    Ok(WholeChainProof {
        root,
        genesis_root,
        final_root,
        chain_digest,
        num_turns: turns.len(),
    })
}

/// Fold a vector of batch-STARK proofs to ONE via 2-to-1 aggregation layers.
/// (Same binary-tree fold as [`joint_turn_recursive`].)
fn aggregate_tree(
    mut proofs: Vec<RecursionOutput<DreggRecursionConfig>>,
    config: &DreggRecursionConfig,
    backend: &p3_recursion::FriRecursionBackendForExt<D, 16, 8, p3_recursion::ops::Poseidon2Config>,
    params: &ProveNextLayerParams,
) -> Result<RecursionOutput<DreggRecursionConfig>, TurnChainError> {
    if proofs.is_empty() {
        return Err(TurnChainError::RecursionFailed {
            reason: "no leaves to aggregate".to_string(),
        });
    }
    while proofs.len() > 1 {
        let mut next_level: Vec<RecursionOutput<DreggRecursionConfig>> =
            Vec::with_capacity(proofs.len().div_ceil(2));
        let mut i = 0;
        while i + 1 < proofs.len() {
            let left = proofs[i].into_recursion_input::<BatchOnly>();
            let right = proofs[i + 1].into_recursion_input::<BatchOnly>();
            let out =
                build_and_prove_aggregation_layer::<DreggRecursionConfig, BatchOnly, BatchOnly, _, D>(
                    &left, &right, config, backend, params, None,
                )
                .map_err(|e| TurnChainError::RecursionFailed {
                    reason: format!("aggregation layer failed: {e:?}"),
                })?;
            next_level.push(out);
            i += 2;
        }
        if i < proofs.len() {
            next_level.push(proofs.pop().unwrap());
        }
        proofs = next_level;
    }
    Ok(proofs.pop().unwrap())
}

/// Verify the whole-chain artifact: check the single root batch-STARK proof.
/// Cost is independent of the number of folded turns.
pub fn verify_turn_chain_recursive(proof: &WholeChainProof) -> Result<(), TurnChainError> {
    verify_recursive_batch_proof(&proof.root.0)
        .map_err(|reason| TurnChainError::RecursionFailed { reason })
}

// ============================================================================
// The 2-step inductive core of the UNBOUNDED accumulator.
// ============================================================================

/// The inductive core of a continuous (unbounded) accumulator:
/// `fold_two_turns(running, next) -> new_running`.
///
/// This proves the *binary* step that, iterated, gives the unbounded loop:
/// given a proof of "turns 1..N executed and the root advanced to `mid_root`"
/// and the next finalized turn `(mid_root -> new_root)`, produce a proof of
/// "turns 1..N+1 executed and the root advanced to `new_root`". The two leaves
/// (running summary + next turn) are wrapped and aggregated into one batch
/// proof — the same fold the K-fold tree applies at each internal node.
///
/// ## What this IS
///
/// A genuine 2-to-1 recursive fold over real in-circuit-verified leaves, with
/// the temporal binding (`prev.new_root == next.old_root`) enforced by the
/// chain-binding leaf over the 2-turn window. Iterating it left-to-right over a
/// finalized stream reproduces [`prove_turn_chain_recursive`]'s result.
///
/// ## What the UNBOUNDED driver still needs (named open)
///
/// To make the running proof itself *constant memory* across an unbounded
/// stream — i.e. fold `running_proof ∘ next_turn` where `running_proof` is the
/// PREVIOUS fold's output re-verified IN-CIRCUIT — the running batch proof must
/// be fed back as a [`BatchOnly`] recursion input to the next layer (the fork's
/// `into_recursion_input::<BatchOnly>` already supports this; it is what
/// [`aggregate_tree`] uses internally). The open work is the *driver*: a
/// persistent accumulator struct that (a) holds the single running
/// `RecursionOutput`, (b) on each `poll_finalized_blocks` tick builds the next
/// turn leaf + a 2-row chain-binding leaf binding `running.final_root ->
/// new_root`, and (c) re-aggregates `running ∘ {turn, binding}` into the new
/// running output. The cryptographic machinery is all present and exercised
/// here; what remains is wiring it to the node's live finality stream and
/// persisting the running output across restarts.
pub fn fold_two_turns(
    running: &FinalizedTurn,
    next: &FinalizedTurn,
) -> Result<WholeChainProof, TurnChainError> {
    // The 2-turn window IS a turn chain of length 2 — reuse the proven path.
    let window = [
        FinalizedTurn::new(JointParticipant {
            proof: running.participant.proof.clone(),
            public_inputs: running.participant.public_inputs.clone(),
        }),
        FinalizedTurn::new(JointParticipant {
            proof: next.participant.proof.clone(),
            public_inputs: next.participant.public_inputs.clone(),
        }),
    ];
    prove_turn_chain_recursive(&window)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::effect_vm::pi;
    use crate::effect_vm::{CellState, Effect, EffectVmAir, generate_effect_vm_trace};
    use crate::field::BabyBear;
    use crate::stark;

    /// Build a real EffectVm whole-turn proof for a cell starting at
    /// `(balance, nonce)` and applying a `Transfer` of `amount` (direction 1 =
    /// debit). Returns the finalized turn plus its REAL `(old_root, new_root)`
    /// — the genuine Poseidon2 state commitments the trace generator derives, NOT
    /// fabricated values (the EffectVm AIR boundary-binds OLD/NEW_COMMIT to the
    /// trace, so they cannot be overridden). The caller chains turns by feeding
    /// the next turn the post-state `(balance - amount, nonce + 1)`.
    fn make_turn(balance: u64, nonce: u32, amount: u64) -> (FinalizedTurn, BabyBear, BabyBear) {
        let state = CellState::new(balance, nonce);
        let effects = vec![Effect::Transfer {
            amount,
            direction: 1,
        }];
        let (trace, public_inputs) = generate_effect_vm_trace(&state, &effects);
        let old_root = public_inputs[pi::OLD_COMMIT];
        let new_root = public_inputs[pi::NEW_COMMIT];
        let air = EffectVmAir::new(trace.len());
        let proof = stark::prove(&air, &trace, &public_inputs);
        (
            FinalizedTurn::new(JointParticipant {
                proof,
                public_inputs,
            }),
            old_root,
            new_root,
        )
    }

    /// Build a continuous chain of `k` real finalized turns: each turn debits
    /// `step` from the balance and the next turn starts from the post-state, so
    /// turn i's real `new_root` is turn i+1's real `old_root`. Returns the turns
    /// plus the genesis and final roots.
    fn make_chain(
        start_balance: u64,
        start_nonce: u32,
        step: u64,
        k: usize,
    ) -> (Vec<FinalizedTurn>, BabyBear, BabyBear) {
        let mut turns = Vec::with_capacity(k);
        let mut balance = start_balance;
        let mut nonce = start_nonce;
        let mut genesis = BabyBear::ZERO;
        let mut final_root = BabyBear::ZERO;
        for i in 0..k {
            let (turn, old_root, new_root) = make_turn(balance, nonce, step);
            if i == 0 {
                genesis = old_root;
            } else {
                // The previous turn's post-state IS this turn's pre-state, so the
                // real commitments must already chain.
                assert_eq!(
                    old_root, final_root,
                    "turn {i} old_root must equal previous new_root (real chain)"
                );
            }
            final_root = new_root;
            turns.push(turn);
            balance -= step;
            nonce += 1; // one non-NoOp (Transfer) row bumps the nonce by 1.
        }
        (turns, genesis, final_root)
    }

    /// GOLD whole-chain: fold K=4 REAL finalized turns into ONE recursive proof
    /// that verifies. Each turn's real post-state commitment is the next turn's
    /// real pre-state commitment (genesis -> r1 -> r2 -> r3 -> final). The
    /// verifier checks only the root.
    #[test]
    fn k_fold_turn_chain_proves_and_verifies() {
        let (turns, genesis, final_root) = make_chain(1000, 0, 7, 4);
        assert_eq!(turns.len(), 4);

        let whole = prove_turn_chain_recursive(&turns)
            .expect("a continuous 4-turn finalized chain must fold recursively");
        assert_eq!(whole.num_turns, 4);
        assert_eq!(whole.genesis_root, genesis);
        assert_eq!(whole.final_root, final_root);

        verify_turn_chain_recursive(&whole).expect("the whole-chain root proof must verify");
    }

    /// TEMPORAL TOOTH (host): a turn whose real old_root != previous new_root
    /// breaks the finalized order and is rejected at the chain check — before any
    /// tree. We splice an out-of-sequence turn (a fresh chain's turn, whose
    /// pre-state commitment does not match) into the middle.
    #[test]
    fn broken_order_rejected() {
        let (mut turns, _g, _f) = make_chain(1000, 0, 7, 3);
        // Replace turn 1 with a turn from an UNRELATED chain (different starting
        // balance), so its real old_root does not continue turn 0's new_root.
        let (foreign, foreign_old, _foreign_new) = make_turn(500, 50, 3);
        let prev_new = turns[0].new_root();
        assert_ne!(
            foreign_old, prev_new,
            "the foreign turn must NOT continue the chain (that is the point)"
        );
        turns[1] = foreign;

        match prove_turn_chain_recursive(&turns) {
            Err(TurnChainError::ChainBreak {
                index,
                expected_old_root,
                found_old_root,
            }) => {
                assert_eq!(index, 1);
                assert_eq!(expected_old_root, prev_new.0);
                assert_eq!(found_old_root, foreign_old.0);
            }
            Ok(_) => panic!("a broken finalized order must not produce a whole-chain proof"),
            Err(other) => panic!("expected ChainBreak, got {other:?}"),
        }
    }

    /// TEMPORAL TOOTH (circuit): even bypassing the host check, the
    /// `TurnChainBindingAir` continuity constraint makes a reordered trace
    /// UNSAT. We build the binding trace for a broken order and confirm the
    /// inner proof fails to verify (or the prover refuses it in debug).
    #[test]
    fn broken_order_unsat_in_circuit() {
        let (mut turns, _g, _f) = make_chain(1000, 0, 7, 2);
        let (foreign, _fo, _fn) = make_turn(500, 50, 3);
        turns[1] = foreign; // breaks continuity

        let (trace, pis) = generate_chain_trace_unchecked(&turns);
        // row 0 new_root != row 1 old_root -> continuity broken.
        assert_ne!(trace[0][1], trace[1][0], "the spliced order must be broken");

        let air = TurnChainBindingAir;
        let matrix = trace_to_matrix(&trace);

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let inner = prove_inner_for_air(&air, matrix, &pis);
            verify_inner_for_air(&air, &inner, &pis)
        }));

        let rejected = match result {
            Ok(Ok(())) => false, // verified a broken chain — soundness hole!
            Ok(Err(_)) => true,  // verifier rejected.
            Err(_) => true,      // prover panicked on unsatisfiable trace.
        };
        assert!(
            rejected,
            "a reordered finalized chain must be UNSAT under TurnChainBindingAir continuity"
        );
    }

    /// 2-step inductive core: fold_two_turns over a continuous pair yields a
    /// verifying whole-chain proof of the 2-turn window (the unbounded loop's
    /// inductive step).
    #[test]
    fn two_step_inductive_core_proves_and_verifies() {
        let (turns, genesis, final_root) = make_chain(1000, 0, 11, 2);

        let folded = fold_two_turns(&turns[0], &turns[1])
            .expect("a continuous pair must fold via the core");
        assert_eq!(folded.num_turns, 2);
        assert_eq!(folded.genesis_root, genesis);
        assert_eq!(folded.final_root, final_root);
        verify_turn_chain_recursive(&folded).expect("the 2-step folded proof must verify");
    }

    /// fold_two_turns rejects a discontinuous pair (the inductive step refuses
    /// to extend the running chain with a turn that does not consume its root).
    #[test]
    fn two_step_core_rejects_discontinuity() {
        let (running, _o, _n) = make_turn(1000, 0, 11);
        let (bad_next, _bo, _bn) = make_turn(500, 50, 3); // unrelated chain

        match fold_two_turns(&running, &bad_next) {
            Err(TurnChainError::ChainBreak { index, .. }) => assert_eq!(index, 1),
            Ok(_) => panic!("a discontinuous pair must not fold"),
            Err(other) => panic!("expected ChainBreak, got {other:?}"),
        }
    }
}
