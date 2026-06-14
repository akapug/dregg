//! # starbridge-swarm-orchestration
//!
//! **A verifiable agent-orchestration swarm** — multi-agent task coordination where the
//! coordination is cap-secured, receipted, and verifiable, run through the REAL verified executor.
//!
//! An agent loop (perceive / plan / act / reflect) lives ABOVE dregg and is the integrator's game.
//! dregg owns the ONE seam that matters — the tool-call / turn boundary — and this app makes that
//! seam legible: every coordinating action is a verified turn leaving a receipt, every dispatch is
//! bounded by a real capability, every spend is metered against a conserved budget, and an
//! over-reaching member is REFUSED by the executor, the no-amplification guarantee firing at the
//! swarm layer exactly as it fires for a transfer.
//!
//! This is the executable surface of two verified Lean developments:
//!
//! | Lean keystone                              | What it guarantees / What this crate enforces |
//! |--------------------------------------------|-----------------------------------------------|
//! | `AgentOrchestrationBudget.dispatchConstraints` | the dispatch-board POLICY as ONE program: budget + provenance + no-replay |
//! | `…affineLe [(1,spentA),(1,spentB)] mandate`    | **atomic budget**: `spent_a + spent_b <= budget` — an over-budget dispatch is UNSAT |
//! | `…immutable budgetF`                           | the mandate, once set, cannot be quietly widened mid-swarm |
//! | `…strictMono epochF`                           | **no replay**: every dispatch strictly advances the epoch |
//! | `…senderInField leadF`                         | signed provenance: a dispatch must come FROM the recorded lead |
//! | `AgentOrchestration.worker_authority_subset_orchestrator` | **non-amplification**: a worker's reach ⊆ the coordinator's (`derive_no_amplify`) |
//! | `AgentOrchestration.workForest_conserves`      | the swarm's value moves conserve (no mint/burn) |
//!
//! ## The two cells (the swarm's substrate)
//!
//! **The COORDINATOR — a dispatch-board cell.** Factory-born, its installed [`CellProgram`] IS the
//! swarm policy, re-checked by the verified executor on EVERY turn that touches it:
//!
//!   * `LEAD`     — the appointed coordinator's identity (the signed-provenance anchor); `WriteOnce`.
//!   * `BUDGET`   — the swarm's spend mandate (the conserved ceiling); `WriteOnce` — never widened.
//!   * `SPENT_A`  — worker-A's cumulative dispatched spend; `Monotonic` — never rolled back.
//!   * `SPENT_B`  — worker-B's cumulative dispatched spend; `Monotonic`.
//!   * `EPOCH`    — the strictly-monotone dispatch counter; `StrictMonotonic` — no replay.
//!
//! and the LIFE-OF-CELL budget gate: `AffineLe { spent_a + spent_b - budget <= 0 }` — the swarm can
//! NEVER collectively dispatch more than its mandate. A dispatch that would breach it is REFUSED by
//! the executor BEFORE it commits (fail-closed, no height advance).
//!
//! **The WORKERS — agent cells.** Each worker holds an ATTENUATED capability: the coordinator hands
//! a worker ONLY its sub-task's authority (a cap reaching exactly the cells the sub-task touches, at
//! exactly the rights it needs). A worker cannot exceed the authority it was handed
//! ([`SwarmError::OutOfMandate`], the executor's c-list gate); and a coordinator cannot hand a
//! worker MORE budget than the swarm's mandate (the `AffineLe` tooth).
//!
//! ## The async notify edge (coordination without synchronization)
//!
//! Workers coordinate via the async notify edge: the coordinator's dispatch carries an
//! `Effect::EmitEvent` targeting a worker, which deposits a pending wake in that worker's inbox; the
//! worker DRAINS it in its OWN, separate, receipted turn (a `SetField` ack). The two receipts are
//! INDEPENDENT on-ledger records — causality (coordinator → worker) is visible, synchronization is
//! NOT forced. The corrected `--wake` model: ASYNC ("recipient drains next turn"), not a joint turn.
//!
//! ## The narration-vs-truth property
//!
//! What the swarm DID is provable, not what it claims. The loop could lie about "I was authorized",
//! "I did X", "I stayed within budget" — but the cap-gate REFUSAL, the executor's receipt + the
//! `EventEmitted` dynamics, and the conserved spend against the mandate are the on-ledger truth.
//! An operator audits a swarm she did not write and could not trust, and is nonetheless never fooled.
//!
//! ## Pre-submission assurance (`dregg-userspace-verify`)
//!
//! Before a dispatch forest is submitted, it is linted by the userspace `analyze()` toolkit —
//! conservation (the value moves net to zero per asset), non-amplification (no in-forest grant
//! exceeds a delegated cap), and well-formedness — so a stranger can pre-flight the swarm's plan and
//! SEE it pass (or see a malformed plan's findings) before spending gas. See `tests/userspace_verify.rs`.

#![forbid(unsafe_code)]

use dregg_app_framework::{
    Action, AppCipherclerk, AuthRequired, CapTarget, CapTemplate, CellId, CellMode, CellProgram,
    ChildVkStrategy, ConstantsModule, Effect, Event, FactoryDescriptor, FieldElement,
    InspectorDescriptor, StarbridgeAppContext, StateConstraint, canonical_program_vk, field_from_u64,
    hex_encode_32, symbol,
};

pub use dregg_app_framework::field_from_bytes;

// =============================================================================
// Slot layout (the coordinator dispatch-board cell) — mirrors the Lean
// `AgentOrchestrationBudget` field names (`leadF`/`budgetF`/`spentAF`/`spentBF`/`epochF`).
// =============================================================================

/// Slot 0 — `LEAD`. The appointed coordinator's identity scalar (the signed-provenance anchor).
/// `WriteOnce`: bound once at board open (from zero), frozen thereafter. The Lean `leadF`.
pub const LEAD_SLOT: u8 = 0;
/// Slot 1 — `BUDGET`. The swarm's spend mandate (the conserved ceiling). `WriteOnce`: bound once at
/// board open, never widened mid-swarm. The Lean `budgetF`.
pub const BUDGET_SLOT: u8 = 1;
/// Slot 2 — `SPENT_A`. Worker-A's cumulative dispatched spend. `Monotonic`: never rolled back to
/// forge head-room. The Lean `spentAF`.
pub const SPENT_A_SLOT: u8 = 2;
/// Slot 3 — `SPENT_B`. Worker-B's cumulative dispatched spend. `Monotonic`. The Lean `spentBF`.
pub const SPENT_B_SLOT: u8 = 3;
/// Slot 4 — `EPOCH`. The strictly-monotone dispatch counter (no replay). `StrictMonotonic`: every
/// dispatch advances it. The Lean `epochF`.
pub const EPOCH_SLOT: u8 = 4;

/// The number of worker spend-meters the board tracks (A and B). The two-meter budget is what no
/// single-field counter sees — it is the affine-sum bound `spent_a + spent_b <= budget`.
pub const WORKER_METERS: usize = 2;

// =============================================================================
// The dispatch policy (the Lean `dispatchConstraints` mirror).
// =============================================================================

/// The swarm orchestration POLICY as a flat conjunction of slot caveats — the Rust transcription of
/// the Lean `AgentOrchestrationBudget.dispatchConstraints`. THIS is the exact predicate the executor
/// installs as the factory-born coordinator's `CellProgram` (`CellProgram::Predicate`) and re-checks
/// on EVERY turn that touches the board. Each clause is a primitive of the integrator wedge; each
/// refusal is a theorem on the Lean side and a real executor refusal here:
///
///   * **atomic budget** (`AffineLe`): `spent_a + spent_b - budget <= 0`, i.e. the swarm's total
///     declared spend never exceeds its mandate. An over-budget runaway is REFUSED; the whole turn
///     aborts (it is ONE predicate). The Lean `affineLe [(1,spentAF),(1,spentBF)] mandate`.
///   * **write-once mandate** (`WriteOnce BUDGET`): the ceiling is bound ONCE at board open (from
///     zero) then frozen — never widened mid-swarm. The Lean `immutable budgetF` (in the
///     birth-compatible form: a factory-born cell is born empty, so `Immutable` would freeze BUDGET
///     AT ZERO and refuse the open turn itself — mirror tool-access-delegation / bounty-board).
///   * **write-once lead** (`WriteOnce LEAD`): the appointed coordinator's identity is bound once at
///     board open then frozen — a rogue cannot recapture the provenance anchor. (Sender-binding to
///     this identity is the §8 crypto portal, the named seam; the slot pins WHO the lead is.)
///   * **monotone meters** (`Monotonic SPENT_A/SPENT_B`): a worker's cumulative spend only
///     accumulates; it can never be rolled back to forge budget head-room.
///   * **no replay** (`StrictMonotonic EPOCH`): every touching turn strictly advances the epoch; a
///     replayed (same / stale epoch) dispatch is REFUSED. The Lean `strictMono epochF`. (The board
///     opens at epoch 1 so the open turn itself strictly advances 0 -> 1; dispatches go 1 -> 2 -> …)
pub fn swarm_constraints() -> Vec<StateConstraint> {
    vec![
        // (3) ATOMIC BUDGET — spent_a + spent_b <= budget (the affine sum, the two-meter bound).
        StateConstraint::AffineLe {
            terms: vec![(1, SPENT_A_SLOT), (1, SPENT_B_SLOT), (-1, BUDGET_SLOT)],
            c: 0,
        },
        // the mandate is bound once at open (from zero) then frozen — never quietly widened.
        StateConstraint::WriteOnce { index: BUDGET_SLOT },
        // the appointed lead's identity is bound once at open then frozen (the provenance anchor).
        StateConstraint::WriteOnce { index: LEAD_SLOT },
        // the per-worker meters only accumulate (never roll back to forge head-room).
        StateConstraint::Monotonic { index: SPENT_A_SLOT },
        StateConstraint::Monotonic { index: SPENT_B_SLOT },
        // (no replay) every touching turn strictly advances the epoch.
        StateConstraint::StrictMonotonic { index: EPOCH_SLOT },
    ]
}

/// The COORDINATOR dispatch-board program — `swarm_constraints` as a `CellProgram::Predicate`,
/// identical to what the factory installs on the born cell (so the program VK names the exact
/// installed predicate).
pub fn coordinator_program() -> CellProgram {
    CellProgram::Predicate(swarm_constraints())
}

/// Canonical child program VK for the coordinator dispatch-board cell.
pub fn coordinator_child_program_vk() -> [u8; 32] {
    canonical_program_vk(&coordinator_program())
}

// =============================================================================
// Factory configuration (the dispatch-board factory).
// =============================================================================

/// The factory VK we publish for the swarm-orchestration coordinator factory.
pub const SWARM_FACTORY_VK: [u8; 32] = *b"starbridge-swarm-orchestr-factry";

/// Default per-epoch creation budget for the coordinator factory.
pub const DEFAULT_CREATION_BUDGET: u64 = 256;

/// Hash an agent identity string to its field-scalar value (the board stores `LEAD` as this scalar
/// — the Rust image of the Lean `leadPk` identity scalar).
pub fn identity_field(agent: &str) -> FieldElement {
    field_from_bytes(agent.as_bytes())
}

/// Build the [`FactoryDescriptor`] for swarm-orchestration coordinator (dispatch-board) cells.
///
/// A factory-born coordinator is born EMPTY; the `open_board` turn binds `LEAD` + `BUDGET` (from
/// zero, under `WriteOnce` — the birth-compatible "fixed at open" form) before any dispatch, and the
/// budget gate + meters + epoch caveats are installed at birth FOR LIFE (mirror
/// privacy-voting/bounty-board/tool-access-delegation: born empty, bound by the first turn, frozen).
pub fn swarm_factory_descriptor() -> FactoryDescriptor {
    FactoryDescriptor {
        factory_vk: SWARM_FACTORY_VK,
        child_program_vk: Some(coordinator_child_program_vk()),
        child_vk_strategy: Some(ChildVkStrategy::Fixed(Some(coordinator_child_program_vk()))),
        allowed_cap_templates: vec![CapTemplate {
            target: CapTarget::SelfCell,
            // The coordinator holds an attenuatable SelfCell cap — the ocap handle the swarm
            // operator dispatches under. Sub-delegation to workers narrows it (no amplification).
            max_permissions: AuthRequired::Signature,
            attenuatable: true,
        }],
        // Born empty: the `open_board` turn binds LEAD + BUDGET from zero under `WriteOnce`.
        field_constraints: vec![],
        // The life-of-cell swarm policy, installed at birth as the born cell's
        // `CellProgram::Predicate` and re-checked by the executor on every touching turn. This is
        // EXACTLY `swarm_constraints()` (and `coordinator_program()`'s predicate), so the advertised
        // program VK names the installed predicate byte-for-byte.
        state_constraints: swarm_constraints(),
        default_mode: CellMode::Sovereign,
        creation_budget: Some(DEFAULT_CREATION_BUDGET),
    }
}

/// All factory descriptors this starbridge-app contributes.
pub fn factory_descriptors() -> Vec<FactoryDescriptor> {
    vec![swarm_factory_descriptor()]
}

// =============================================================================
// The worker meter index (which spend-slot a worker draws against).
// =============================================================================

/// Which of the two worker meters a dispatch advances. The coordinator dispatches a sub-task to
/// exactly one worker; the worker's meter is the column the budget gate sums.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Worker {
    /// Worker A — its cumulative spend lives in `SPENT_A`.
    A,
    /// Worker B — its cumulative spend lives in `SPENT_B`.
    B,
}

impl Worker {
    /// The board slot this worker's cumulative spend accumulates in.
    pub fn spend_slot(self) -> u8 {
        match self {
            Worker::A => SPENT_A_SLOT,
            Worker::B => SPENT_B_SLOT,
        }
    }

    /// A short legible label for the activity feed / event topics.
    pub fn label(self) -> &'static str {
        match self {
            Worker::A => "worker-a",
            Worker::B => "worker-b",
        }
    }
}

// =============================================================================
// The off-ledger budget pre-check (fail-closed BEFORE the turn runs).
// =============================================================================

/// Whether a dispatch advancing `worker`'s meter from `prev_spent` by `cost`, given the OTHER
/// worker's current spend `other_spent`, would stay within `budget`. This is the userspace,
/// artifact-only mirror of the executor's `AffineLe` gate: `prev_spent + cost + other_spent <=
/// budget`. The coordinator checks this BEFORE building the turn (fail-closed — it does not even
/// submit an over-budget dispatch), AND the executor independently re-checks it on commit (the real
/// gate — even if the pre-check is wrong, the over-budget dispatch is refused). Two gates that
/// provably agree (the Lean `affineLe` is the single source of truth).
pub fn dispatch_within_budget(prev_spent: u64, cost: u64, other_spent: u64, budget: u64) -> bool {
    // saturating to avoid wrap; the executor reads the same big-endian u64 sum lifted to i128.
    prev_spent
        .saturating_add(cost)
        .saturating_add(other_spent)
        <= budget
}

// =============================================================================
// Turn builders — OPEN BOARD / DISPATCH / DRAIN.
// =============================================================================

/// **OPEN BOARD** — the swarm operator opens the dispatch board by pinning the `LEAD` identity and
/// the `BUDGET` mandate (`WriteOnce`: bound once from zero, frozen thereafter), the two worker meters
/// born at 0, and the epoch advanced to 1 (so the open turn itself satisfies `StrictMonotonic(EPOCH)`,
/// 0 -> 1). Mirrors the initial board state in the Lean `AgentOrchestrationBudget`.
pub fn build_open_board_action(
    cipherclerk: &AppCipherclerk,
    board: CellId,
    lead: &str,
    budget: u64,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: board,
            index: LEAD_SLOT as usize,
            value: identity_field(lead),
        },
        Effect::SetField {
            cell: board,
            index: BUDGET_SLOT as usize,
            value: field_from_u64(budget),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_A_SLOT as usize,
            value: field_from_u64(0),
        },
        Effect::SetField {
            cell: board,
            index: SPENT_B_SLOT as usize,
            value: field_from_u64(0),
        },
        // open at epoch 1 — the open turn itself strictly advances the epoch 0 -> 1 (so the
        // `StrictMonotonic(EPOCH)` no-replay caveat holds on the very first touch); dispatches then
        // go 1 -> 2 -> 3 -> ….
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(1),
        },
        Effect::EmitEvent {
            cell: board,
            event: Event::new(
                symbol("swarm-board-opened"),
                vec![identity_field(lead), field_from_u64(budget)],
            ),
        },
    ];
    cipherclerk.make_action(board, "open_board", effects)
}

/// **DISPATCH** — the coordinator dispatches a sub-task to `worker`: it advances the worker's
/// cumulative spend meter by `cost`, advances the epoch (no-replay), and (the async notify edge)
/// EMITS a wake targeting the worker cell carrying the sub-task topic. The executor admits this IFF
/// the budget gate holds (`spent_a + spent_b <= budget`), the epoch strictly advances, and the
/// meters are monotone — exactly the Lean dispatch gate.
///
/// `prev_spent` is the worker's current meter value; `new_epoch` is the strictly-greater epoch;
/// `worker_cell` is the worker agent cell the wake targets (the coordination edge); `topic` labels
/// the sub-task.
#[allow(clippy::too_many_arguments)]
pub fn build_dispatch_action(
    cipherclerk: &AppCipherclerk,
    board: CellId,
    worker: Worker,
    worker_cell: CellId,
    prev_spent: u64,
    cost: u64,
    new_epoch: u64,
    topic: &str,
) -> Action {
    let new_spent = prev_spent.saturating_add(cost);
    let effects = vec![
        // advance the worker's cumulative spend meter (Monotonic; summed by the budget gate).
        Effect::SetField {
            cell: board,
            index: worker.spend_slot() as usize,
            value: field_from_u64(new_spent),
        },
        // advance the dispatch epoch (StrictMonotonic — no replay).
        Effect::SetField {
            cell: board,
            index: EPOCH_SLOT as usize,
            value: field_from_u64(new_epoch),
        },
        // the ASYNC NOTIFY EDGE: wake the worker cell with the sub-task topic. The worker drains
        // this in its OWN separate receipted turn — causality visible, synchronization not forced.
        Effect::EmitEvent {
            cell: worker_cell,
            event: Event::new(
                symbol(&format!("dispatch/{}", topic)),
                vec![field_from_u64(cost), field_from_u64(new_epoch)],
            ),
        },
    ];
    cipherclerk.make_action(board, "dispatch", effects)
}

/// **DRAIN (the worker's own ack turn)** — the worker acknowledges a dispatch wake by writing a
/// content-addressed ack into its own cell. This is the async drain: the wake was deposited by the
/// COORDINATOR's committed dispatch; the drain is a WHOLLY INDEPENDENT future turn by the WORKER,
/// with its OWN receipt. `ack_slot` is the worker's ack counter; `wake_digest` is a content address
/// of the dispatch the worker is acknowledging (e.g. the dispatch topic hash). A cell always reaches
/// itself, so the drain is always in-mandate.
pub fn build_drain_action(
    cipherclerk: &AppCipherclerk,
    worker_cell: CellId,
    ack_slot: u8,
    wake_digest: FieldElement,
) -> Action {
    let effects = vec![
        Effect::SetField {
            cell: worker_cell,
            index: ack_slot as usize,
            value: wake_digest,
        },
        Effect::EmitEvent {
            cell: worker_cell,
            event: Event::new(symbol("dispatch-acked"), vec![wake_digest]),
        },
    ];
    cipherclerk.make_action(worker_cell, "drain_dispatch", effects)
}

// =============================================================================
// StarbridgeAppContext mount.
// =============================================================================

/// The canonical web-constants module (slot layout + event topics + factory-vk hex).
pub fn web_constants() -> ConstantsModule {
    ConstantsModule::new("swarm-orchestration")
        .slot("LEAD_SLOT", LEAD_SLOT as u64)
        .slot("BUDGET_SLOT", BUDGET_SLOT as u64)
        .slot("SPENT_A_SLOT", SPENT_A_SLOT as u64)
        .slot("SPENT_B_SLOT", SPENT_B_SLOT as u64)
        .slot("EPOCH_SLOT", EPOCH_SLOT as u64)
        .string("FACTORY_VK_HEX", hex_encode_32(&SWARM_FACTORY_VK))
        .topic("BOARD_OPENED", "swarm-board-opened")
        .topic("ACKED", "dispatch-acked")
}

/// Register the swarm-orchestration starbridge-app on a shared context.
pub fn register(ctx: &StarbridgeAppContext) -> [u8; 32] {
    let factory_vk = ctx.register_factory(swarm_factory_descriptor());

    ctx.register_inspector(InspectorDescriptor {
        kind: "swarm-board".into(),
        descriptor: serde_json::json!({
            "component": "dregg-swarm-board",
            "module": "/starbridge-apps/swarm-orchestration/inspectors.js",
            "uri_prefix": "dregg://cell/",
            "summary_fields": ["lead", "budget", "spent_a", "spent_b", "epoch"],
            "slot_layout": {
                "lead": LEAD_SLOT,
                "budget": BUDGET_SLOT,
                "spent_a": SPENT_A_SLOT,
                "spent_b": SPENT_B_SLOT,
                "epoch": EPOCH_SLOT,
            },
            "factory_vk_hex": hex_encode_32(&factory_vk),
            "child_program_vk_hex": hex_encode_32(&coordinator_child_program_vk()),
            "methods": ["open_board", "dispatch", "drain_dispatch"],
        }),
    });

    factory_vk
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_app_framework::{AgentCipherclerk, Authorization, EmbeddedExecutor};

    fn test_cipherclerk() -> AppCipherclerk {
        AppCipherclerk::new(AgentCipherclerk::new(), [0x5au8; 32])
    }

    fn test_context() -> StarbridgeAppContext {
        let cipherclerk = test_cipherclerk();
        let executor = EmbeddedExecutor::new(&cipherclerk, "default");
        StarbridgeAppContext::new(cipherclerk, executor)
    }

    fn test_cell() -> CellId {
        CellId::from_bytes([7u8; 32])
    }

    // ── the dispatch policy mirrors the Lean dispatchConstraints ─────────────

    #[test]
    fn coordinator_program_has_the_six_policy_clauses() {
        // The board program is a flat predicate (exactly what the factory installs on the born
        // cell), so the advertised program VK names the installed predicate byte-for-byte.
        let CellProgram::Predicate(ks) = coordinator_program() else {
            panic!("coordinator program must be a flat Predicate");
        };
        assert_eq!(ks, swarm_constraints(), "the program IS swarm_constraints");
        // the affine budget gate is present.
        assert!(
            ks.iter().any(|k| matches!(
                k,
                StateConstraint::AffineLe { terms, c: 0 }
                    if terms.contains(&(1, SPENT_A_SLOT))
                        && terms.contains(&(1, SPENT_B_SLOT))
                        && terms.contains(&(-1, BUDGET_SLOT))
            )),
            "the budget gate spent_a + spent_b <= budget must be a clause"
        );
        // write-once mandate + lead (born-empty, bound once, frozen) + monotones + strict-mono epoch.
        assert!(ks.iter().any(|k| matches!(k, StateConstraint::WriteOnce { index } if *index == BUDGET_SLOT)));
        assert!(ks.iter().any(|k| matches!(k, StateConstraint::WriteOnce { index } if *index == LEAD_SLOT)));
        assert!(ks.iter().any(|k| matches!(k, StateConstraint::Monotonic { index } if *index == SPENT_A_SLOT)));
        assert!(ks.iter().any(|k| matches!(k, StateConstraint::Monotonic { index } if *index == SPENT_B_SLOT)));
        assert!(ks.iter().any(|k| matches!(k, StateConstraint::StrictMonotonic { index } if *index == EPOCH_SLOT)));
    }

    // ── the budget pre-check mirrors the executor's AffineLe gate ────────────

    #[test]
    fn dispatch_within_budget_matches_the_affine_bound() {
        // budget 1000; a 600 dispatch to A then a 300 to B fits (900 <= 1000).
        assert!(dispatch_within_budget(0, 600, 0, 1000)); // A: 0 -> 600, B at 0
        assert!(dispatch_within_budget(0, 300, 600, 1000)); // B: 0 -> 300, A at 600 ⇒ 900
        // a 500 to B with A at 600 breaches (1100 > 1000) — the BUDGET TOOTH.
        assert!(!dispatch_within_budget(0, 500, 600, 1000));
        // exactly at the ceiling is admitted (<=).
        assert!(dispatch_within_budget(600, 400, 0, 1000));
        // one over the ceiling is refused.
        assert!(!dispatch_within_budget(600, 401, 0, 1000));
    }

    #[test]
    fn worker_spend_slots_are_distinct_meters() {
        assert_eq!(Worker::A.spend_slot(), SPENT_A_SLOT);
        assert_eq!(Worker::B.spend_slot(), SPENT_B_SLOT);
        assert_ne!(Worker::A.spend_slot(), Worker::B.spend_slot());
    }

    // ── the turn builders carry real effects + a real signature ──────────────

    #[test]
    fn open_board_action_pins_lead_and_budget() {
        let cclerk = test_cipherclerk();
        let action = build_open_board_action(&cclerk, test_cell(), "lead-pk", 1000);
        // lead, budget, spent_a(=0), spent_b(=0), epoch(=0), + event.
        assert_eq!(action.effects.len(), 6);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == LEAD_SLOT as usize && *value == identity_field("lead-pk")
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == BUDGET_SLOT as usize && *value == field_from_u64(1000)
        ));
    }

    #[test]
    fn dispatch_action_advances_meter_epoch_and_emits_wake() {
        let cclerk = test_cipherclerk();
        let worker_cell = CellId::from_bytes([9u8; 32]);
        let action =
            build_dispatch_action(&cclerk, test_cell(), Worker::A, worker_cell, 0, 300, 1, "index");
        // spent_a := 300, epoch := 1, + wake on the WORKER cell.
        assert_eq!(action.effects.len(), 3);
        assert!(matches!(
            &action.effects[0],
            Effect::SetField { index, value, .. } if *index == SPENT_A_SLOT as usize && *value == field_from_u64(300)
        ));
        assert!(matches!(
            &action.effects[1],
            Effect::SetField { index, value, .. } if *index == EPOCH_SLOT as usize && *value == field_from_u64(1)
        ));
        // the wake targets the WORKER cell (the async notify edge), not the board.
        assert!(matches!(
            &action.effects[2],
            Effect::EmitEvent { cell, .. } if *cell == worker_cell
        ));
    }

    #[test]
    fn dispatch_action_carries_a_real_signature() {
        let cclerk = test_cipherclerk();
        let worker_cell = CellId::from_bytes([9u8; 32]);
        let action =
            build_dispatch_action(&cclerk, test_cell(), Worker::B, worker_cell, 0, 1, 1, "t");
        match action.authorization {
            Authorization::Signature(a, b) => assert!(a != [0u8; 32] || b != [0u8; 32]),
            other => panic!("expected Signature, got {other:?}"),
        }
    }

    #[test]
    fn register_installs_factory_and_inspector() {
        let ctx = test_context();
        let vk = register(&ctx);
        assert_eq!(vk, SWARM_FACTORY_VK);
        assert_eq!(ctx.factory_registry().len(), 1);
        assert!(ctx.inspector_registry().get("swarm-board").is_some());
    }
}
