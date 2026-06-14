//! `apply`: lower a DreggDL doc → the per-root **turn sequence** + the
//! **receipt-chain shape**, gated by the static pre-submission check.
//!
//! [`crate::check`] answers *"is this declared authority layout sound?"* over
//! the lowered forest. `apply` is the next step: it turns that lowered forest
//! into the **ordered sequence of `dregg_turn::Turn`s an operator submits** —
//! one turn per root effect-group (births, then funds, then grant trees), in
//! dependency order — and links them into a **receipt chain** the way the live
//! executor will: each turn's [`dregg_turn::Turn::previous_receipt_hash`]
//! points at the prior turn's receipt, so the whole deployment is one causal
//! strand.
//!
//! ## The gate (the load-bearing property)
//!
//! [`plan_apply`] runs the **static assurance first** and **refuses to emit any
//! turn** if it fails. An over-grant — a re-delegation that amplifies the cap
//! it was handed, caught by `dregg-userspace-verify::check_no_amplification` as
//! an in-forest capability amplification — is therefore rejected *before* a
//! single turn is built, before any gas is spent. The plan you get back is
//! exactly the plan that passed the check; there is no path from an amplifying
//! DreggDL to a submittable turn sequence through this function.
//!
//! ```text
//!   Deployment ──lower──▶ CallForest ──analyze──▶ Assurance
//!                                                     │
//!                                          pass? ─────┤── no ─▶ ApplyError::Refused
//!                                                     │              (carries the findings)
//!                                                    yes
//!                                                     ▼
//!                          per-root Turn sequence + receipt-chain shape
//!                          (deploy → birth → fund → grant, chained)
//! ```
//!
//! ## What the receipt chain here IS and is NOT
//!
//! The chain this module computes is the **shape** — the deterministic
//! `previous_receipt_hash` links between the turns, plus a *projected* receipt
//! hash per turn (a function of the turn's own content). It is **not** an
//! executor receipt: it carries no post-state commitment, no executor
//! signature, no `computrons_used` — those are produced by the live executor at
//! submit time and verified against the proof (see
//! `dregg_userspace_verify::boundary`). What the projection gives an operator
//! is the causal skeleton: *which* turn chains to *which*, computed off the
//! artifact alone, so the submitted chain can be checked link-for-link against
//! this plan. A mismatch between the projected chain and the executor's
//! returned receipts is a deviation an auditor can see without trusting the
//! node.

use dregg_turn::turn::{Turn, TurnReceipt};
use dregg_turn::CallForest;
use dregg_types::CellId;

use crate::lower::{Lowered, LowerError};
use crate::schema::Deployment;
use dregg_userspace_verify::Assurance;

/// Errors from [`plan_apply`].
#[derive(Debug, thiserror::Error)]
pub enum ApplyError {
    /// Lowering / name-resolution failed (an unknown name, a bad hex, a
    /// duplicate) — the deployment is malformed before the static check even
    /// runs.
    #[error(transparent)]
    Lower(#[from] LowerError),
    /// The static pre-submission check **refused** the deployment: the declared
    /// authority layout does not conserve, amplifies a capability, or is
    /// ill-formed. No turn sequence is produced. The carried [`Assurance`]
    /// names the precise locus (which node, which effect, which asset / grant
    /// edge) — e.g. an over-grant surfaces as a `no_amplification` finding whose
    /// message contains `amplifies`.
    #[error("deployment refused by the static pre-submission check: {0} finding(s) over the declared authority layout (run `dregg-deploy check` for the loci)", .assurance.all_findings().len())]
    Refused { assurance: Box<Assurance> },
}

/// One turn in the applied deployment plan: the submittable [`Turn`] plus the
/// **projected** receipt hash the executor's receipt for it should match, and a
/// human label of which deployment phase it came from.
#[derive(Clone, Debug)]
pub struct PlannedTurn {
    /// The submittable turn (a single-root call forest, signed and submitted by
    /// the SDK at apply time; the placeholder authorization the lowering put on
    /// the action is re-signed with the real key before submission).
    pub turn: Turn,
    /// The phase tag — `"birth"`, `"fund"`, or `"grant"` — for human-readable
    /// plan output.
    pub phase: &'static str,
    /// The agent (target cell) this turn runs as — the `from` of the root
    /// effect. The receipt chain is keyed per cell, but a deployment is one
    /// operator's causal strand, so we chain across the whole sequence.
    pub agent: CellId,
    /// The turn's own content hash ([`Turn::hash`]) — the stable id the
    /// `previous_receipt_hash` of the *next* turn would point at if receipts
    /// were content-addressed by turn. Exposed so the caller can audit the
    /// chain links.
    pub turn_hash: [u8; 32],
    /// The **projected** receipt hash: what
    /// [`TurnReceipt::receipt_hash`] would yield for this turn IF it committed
    /// against the projected (artifact-only) fields. The next turn's
    /// `previous_receipt_hash` is set to exactly this value, so the plan is a
    /// self-consistent receipt chain. NOT an executor receipt (no post-state
    /// commitment) — the chain *shape*, checkable off the artifact.
    pub projected_receipt_hash: [u8; 32],
}

/// The applied deployment: the ordered, receipt-chained turn sequence that a
/// PASSING DreggDL lowers to, plus the assurance that gated it.
#[derive(Clone, Debug)]
pub struct AppliedPlan {
    /// The federation this deployment binds to (bound at signing time by the
    /// SDK; all-zeros for an `"auto"` deployment).
    pub federation_id: dregg_types::FederationId,
    /// The static assurance that **passed** — every plan returned by
    /// [`plan_apply`] carries a passing assurance by construction (a failing one
    /// is returned as [`ApplyError::Refused`] instead).
    pub assurance: Assurance,
    /// The ordered turn sequence (one per root effect-group), each chained to
    /// the previous via `previous_receipt_hash`. Submitting these in order, each
    /// re-signed with the operator's key, instantiates the whole deployment.
    pub turns: Vec<PlannedTurn>,
}

impl AppliedPlan {
    /// The number of turns in the plan (= the number of root effect-groups).
    pub fn len(&self) -> usize {
        self.turns.len()
    }
    /// `true` iff the plan has no turns (an empty deployment).
    pub fn is_empty(&self) -> bool {
        self.turns.is_empty()
    }
    /// Verify the receipt-chain shape is internally consistent: the first turn
    /// has no predecessor, and each subsequent turn's `previous_receipt_hash`
    /// equals the prior turn's `projected_receipt_hash`. This is the invariant
    /// [`plan_apply`] establishes; re-checking it is what an auditor does to a
    /// plan they were handed.
    pub fn chain_is_linked(&self) -> bool {
        let mut prev: Option<[u8; 32]> = None;
        for pt in &self.turns {
            if pt.turn.previous_receipt_hash != prev {
                return false;
            }
            prev = Some(pt.projected_receipt_hash);
        }
        true
    }
}

/// THE APPLY FLOW: lower a [`Deployment`] → run the static check as the GATE →
/// emit the per-root turn sequence with the receipt-chain shape.
///
/// On a PASS, returns the [`AppliedPlan`]: one [`Turn`] per root effect-group of
/// the lowered forest (births, then funds, then grant trees, in dependency
/// order), chained so each turn's `previous_receipt_hash` is the prior turn's
/// projected receipt hash.
///
/// On a FAIL — including an over-grant caught as in-forest capability
/// amplification — returns [`ApplyError::Refused`] **without producing any
/// turn**. This is the whole point: the static check refuses non-conserving /
/// amplifying specs up front, so an operator never pays to submit a deployment
/// the executor would reject.
///
/// `as_ring`: also gate on the ring-balance check (for a settlement-ring
/// deployment declared as bare funding transfers).
pub fn plan_apply(dep: &Deployment, as_ring: bool) -> Result<AppliedPlan, ApplyError> {
    // (1) lower — name resolution + the checkable forest.
    let lowered = Lowered::from_deployment(dep)?;

    // (2) THE GATE: run the static assurance over the whole declared authority
    // layout. Refuse to emit anything if it does not pass.
    let assurance = dregg_userspace_verify::analyze(&lowered.forest, as_ring);
    if !assurance.pass() {
        return Err(ApplyError::Refused {
            assurance: Box::new(assurance),
        });
    }

    // (3) emit the per-root turn sequence + the receipt-chain shape.
    let turns = build_turn_sequence(&lowered);

    Ok(AppliedPlan {
        federation_id: lowered.federation_id,
        assurance,
        turns,
    })
}

/// [`plan_apply`] from DreggDL TOML text.
pub fn plan_apply_toml(text: &str, as_ring: bool) -> Result<AppliedPlan, crate::DeployError> {
    let dep = crate::parse_toml(text)?;
    Ok(plan_apply(&dep, as_ring)?)
}

/// Split the lowered single-turn-wide forest into one [`Turn`] per root and
/// chain them. The lowered forest already orders roots births → funds → grants
/// and nests re-delegations under their parent grant; we preserve that order
/// and that nesting (each root tree, with its children, becomes one turn).
fn build_turn_sequence(lowered: &Lowered) -> Vec<PlannedTurn> {
    let fed = lowered.federation_id.0;
    let mut out: Vec<PlannedTurn> = Vec::with_capacity(lowered.forest.roots.len());
    let mut prev_receipt: Option<[u8; 32]> = None;

    for (i, root) in lowered.forest.roots.iter().enumerate() {
        let agent = root.action.target;
        let phase = phase_of(&root.action.method);

        // One single-root forest carrying this root tree (children = nested
        // re-delegations) verbatim, so the per-turn forest hash binds the whole
        // sub-tree the checker walked.
        let mut call_forest = CallForest {
            roots: vec![root.clone()],
            forest_hash: [0u8; 32],
        };
        call_forest.forest_hash = call_forest.compute_hash();

        // The turn. nonce = the root's position in the deployment sequence (a
        // deterministic, monotone-per-agent placeholder; the SDK re-stamps the
        // real nonce from the live c-list at submit time). Authorization lives
        // on the action inside the forest, re-signed by the SDK.
        let turn = Turn {
            agent,
            nonce: i as u64,
            call_forest,
            fee: 0,
            memo: Some(format!("dregg-deploy:{phase}")),
            valid_until: None,
            previous_receipt_hash: prev_receipt,
            depends_on: prev_turn_hash(&out).map(|h| vec![h]).unwrap_or_default(),
            conservation_proof: None,
            sovereign_witnesses: Default::default(),
            execution_proof: None,
            execution_proof_cell: None,
            execution_proof_new_commitment: None,
            custom_program_proofs: None,
            effect_binding_proofs: Vec::new(),
            cross_effect_dependencies: Vec::new(),
            effect_witness_index_map: Vec::new(),
        };

        let turn_hash = turn.hash();
        let projected_receipt_hash = project_receipt_hash(&turn, agent, fed, prev_receipt);

        out.push(PlannedTurn {
            turn,
            phase,
            agent,
            turn_hash,
            projected_receipt_hash,
        });
        prev_receipt = Some(projected_receipt_hash);
    }
    out
}

/// The previous turn's content hash, for the `depends_on` causal edge.
fn prev_turn_hash(out: &[PlannedTurn]) -> Option<[u8; 32]> {
    out.last().map(|pt| pt.turn_hash)
}

/// Project the receipt hash for a planned turn off the artifact alone: build a
/// [`TurnReceipt`] with the fields knowable without execution (turn hash,
/// forest hash, effects hash, agent, federation, the chain link) and ZEROED
/// dynamic fields (pre/post-state commitments, computrons, timestamp), then
/// take its `receipt_hash`. The result is a deterministic function of the turn,
/// so the next turn can chain to it and the plan is self-consistent.
///
/// The honest boundary: a zeroed `post_state_hash` means this is the chain
/// SHAPE, not the executor's receipt — the executor fills the real state
/// commitment in at submit time. See module docs + `boundary`.
fn project_receipt_hash(
    turn: &Turn,
    agent: CellId,
    federation_id: [u8; 32],
    previous_receipt_hash: Option<[u8; 32]>,
) -> [u8; 32] {
    let forest_hash = turn.call_forest.compute_hash();
    let effects_hash = effects_hash(&turn.call_forest);
    let receipt = TurnReceipt {
        turn_hash: turn.hash(),
        forest_hash,
        pre_state_hash: [0u8; 32],
        post_state_hash: [0u8; 32],
        timestamp: 0,
        effects_hash,
        computrons_used: 0,
        action_count: turn.call_forest.action_count(),
        previous_receipt_hash,
        agent,
        federation_id,
        routing_directives: Vec::new(),
        introduction_exports: Vec::new(),
        derivation_records: Vec::new(),
        emitted_events: Vec::new(),
        executor_signature: None,
        finality: Default::default(),
        was_encrypted: false,
        was_burn: false,
        consumed_capabilities: Vec::new(),
    };
    receipt.receipt_hash()
}

/// A deterministic digest of every effect in the forest (the artifact-only
/// `effects_hash` projection: a BLAKE3 over each effect's serialized form, in
/// DFS order). Binds the receipt-chain shape to the actual effects, so a turn
/// whose effects were tampered projects a different chain. Uses `serde_json`
/// (already a dep) for the stable per-effect serialization — `Effect` is a
/// fixed serde shape, so the bytes are deterministic for a given effect.
fn effects_hash(forest: &CallForest) -> [u8; 32] {
    let mut hasher = blake3::Hasher::new();
    hasher.update(b"dregg-deploy-effects-v1:");
    for eff in forest.total_effects() {
        if let Ok(bytes) = serde_json::to_vec(eff) {
            hasher.update(&(bytes.len() as u64).to_le_bytes());
            hasher.update(&bytes);
        }
    }
    *hasher.finalize().as_bytes()
}

/// Map the lowered action method symbol back to a human phase tag.
fn phase_of(method: &dregg_turn::action::Symbol) -> &'static str {
    let want_create = dregg_turn::action::symbol("deploy.create_cell");
    let want_fund = dregg_turn::action::symbol("deploy.fund");
    let want_grant = dregg_turn::action::symbol("deploy.grant");
    if *method == want_create {
        "birth"
    } else if *method == want_fund {
        "fund"
    } else if *method == want_grant {
        "grant"
    } else {
        "other"
    }
}
