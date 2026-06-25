//! SDK-free delegated tool gateway.
//!
//! The gateway owns the admission, metering, routing, and receipt-envelope logic
//! for tool calls. It deliberately knows only a worker cell plus a turn-acceptor
//! trait. SDK-specific details such as `AgentRuntime`, `SubAgent`, and
//! `HeldToken` stay in the SDK adapter.

use std::collections::{HashMap, VecDeque};
use std::fmt;

use dregg_cell::CellId;
use dregg_cell::program::{CellProgram, StateConstraint, field_from_u64};
use dregg_turn::{
    Action, Authorization, CallForest, CommitmentMode, DelegationMode, Effect, PendingTurnRegistry,
    ResolutionCondition, ResolutionOutcome, TokenKeyRef, Turn, TurnError, TurnReceipt,
};
use dregg_turn::{BrokenReason, action::symbol};

/// The slot index on the worker cell that holds the rate counter `calls_made`.
pub const CALLS_MADE_SLOT: u8 = 4;

/// The grantor's pinned delegation parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolGrant {
    /// The single allowlisted tool / MCP id.
    pub tool_id: i64,
    /// The granted invocation ceiling.
    pub rate_limit: i64,
    /// The expiry height/clock.
    pub deadline: i64,
    /// The executor method verb the worker credential is scoped to.
    pub tool_method: String,
}

/// Byte-faithful mirror of the Lean `delegAdmit g now tool old new` predicate.
pub fn deleg_admit(g: &ToolGrant, now: i64, tool: i64, old: i64, new: i64) -> bool {
    tool == g.tool_id && now <= g.deadline && new == old + 1 && 0 <= old && new <= g.rate_limit
}

/// The executor-side rate backstop installed on the worker cell.
pub fn mandate_program(rate_limit: i64) -> CellProgram {
    let ceiling = if rate_limit < 0 { 0 } else { rate_limit as u64 };
    CellProgram::Predicate(vec![
        StateConstraint::FieldLte {
            index: CALLS_MADE_SLOT,
            value: field_from_u64(ceiling),
        },
        StateConstraint::Monotonic {
            index: CALLS_MADE_SLOT,
        },
    ])
}

/// Why the gateway refused a tool call in-band.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GatewayRefusal {
    /// The presented tool id is not the granted one.
    OutOfScope { presented: i64, granted: i64 },
    /// The call was presented after the granted expiry.
    PastDeadline { now: i64, deadline: i64 },
    /// The rate budget is exhausted.
    OverRate { calls_made: i64, rate_limit: i64 },
}

impl fmt::Display for GatewayRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            GatewayRefusal::OutOfScope { presented, granted } => write!(
                f,
                "tool call out of scope: presented tool {presented}, mandate grants only {granted}"
            ),
            GatewayRefusal::PastDeadline { now, deadline } => write!(
                f,
                "tool call past deadline: presented at height {now}, mandate expired at {deadline}"
            ),
            GatewayRefusal::OverRate {
                calls_made,
                rate_limit,
            } => write!(
                f,
                "tool call over rate: {calls_made} calls already made, mandate grants {rate_limit}"
            ),
        }
    }
}

impl std::error::Error for GatewayRefusal {}

/// A turn-accepting worker that can commit a cap-gated tool turn.
pub trait GatewayTurnAcceptor {
    /// The execution error returned by the underlying worker.
    type Error: fmt::Display;

    /// The worker cell that receives metered tool turns.
    fn cell_id(&self) -> CellId;

    /// Submit one cap-gated turn under `method`.
    fn accept_turn(&self, method: &str, effects: Vec<Effect>) -> Result<TurnReceipt, Self::Error>;

    /// Build the routed call's promise turn.
    ///
    /// This is used only for the pending-registry identity of a routed call; the
    /// actual commit still goes through [`Self::accept_turn`].
    fn build_routed_turn(&self, method: &str, nonce: u64, effects: Vec<Effect>) -> Turn;
}

/// The outcome of an admitted, committed tool invocation.
#[derive(Clone, Debug)]
pub struct ToolReceipt {
    /// The executor receipt for the metered turn.
    pub receipt: TurnReceipt,
    /// The rate counter after this call.
    pub calls_made: i64,
    /// How many calls remain on the mandate.
    pub remaining: i64,
}

/// A delivery witness for a routed tool call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeliveryReceipt {
    /// The content-address of the routed call.
    pub routed_hash: [u8; 32],
    /// The execution environment the call was delivered to.
    pub executor_cell: CellId,
    /// The height the call was enqueued.
    pub enqueued_at: i64,
    /// The height the executor drained and committed it.
    pub delivered_at: i64,
}

/// The terminal result of a routed tool call.
#[derive(Clone, Debug)]
pub struct RoutedResult {
    /// The executor receipt plus meter.
    pub tool_receipt: ToolReceipt,
    /// The delivery witness.
    pub delivery: DeliveryReceipt,
}

/// The status of a routed tool-call promise.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RoutedStatus {
    /// Enqueued, awaiting the executor's drain.
    Pending,
    /// Drained and executed.
    Delivered,
    /// The executor rejected the routed work or it was dropped.
    Broken,
}

/// A non-blocking promise for a routed tool call.
#[derive(Clone, Debug)]
pub struct RoutedHandle {
    /// The hash identifying the routed call in the pending registry.
    pub routed_hash: [u8; 32],
    /// The presented tool id.
    pub tool: i64,
    /// The height the call was enqueued.
    pub enqueued_at: i64,
}

impl RoutedHandle {
    /// The routed work's content-address.
    pub fn routed_hash(&self) -> [u8; 32] {
        self.routed_hash
    }
}

/// Gateway error surface.
#[derive(Debug)]
pub enum ToolCallError<E> {
    /// The delegated policy refused the call in-band.
    Refused(GatewayRefusal),
    /// The underlying turn acceptor rejected execution.
    Execution(E),
    /// A routed result was broken, pending, or unknown.
    Route(String),
}

impl<E: fmt::Display> fmt::Display for ToolCallError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ToolCallError::Refused(r) => write!(f, "mandate refused tool call: {r}"),
            ToolCallError::Execution(e) => write!(f, "tool call execution error: {e}"),
            ToolCallError::Route(reason) => write!(f, "routed tool call error: {reason}"),
        }
    }
}

impl<E> std::error::Error for ToolCallError<E> where E: std::error::Error + 'static {}

/// A mandated tool gateway wrapping a cap-gated turn acceptor.
pub struct ToolGateway<A> {
    grant: ToolGrant,
    acceptor: A,
    worker_cell: CellId,
    calls_made: i64,
    inbox: VecDeque<RoutedWork>,
    pending: PendingTurnRegistry,
    results: HashMap<[u8; 32], Result<RoutedResult, String>>,
}

#[derive(Clone, Debug)]
struct RoutedWork {
    routed_hash: [u8; 32],
    new_count: i64,
    work: Vec<Effect>,
    enqueued_at: i64,
}

impl<A: GatewayTurnAcceptor> ToolGateway<A> {
    /// Create a gateway around an already-admitted turn acceptor.
    pub fn new(grant: ToolGrant, acceptor: A) -> Self {
        let worker_cell = acceptor.cell_id();
        Self {
            grant,
            acceptor,
            worker_cell,
            calls_made: 0,
            inbox: VecDeque::new(),
            pending: PendingTurnRegistry::new(),
            results: HashMap::new(),
        }
    }

    /// The grantor's pinned mandate.
    pub fn grant(&self) -> &ToolGrant {
        &self.grant
    }

    /// The worker cell id.
    pub fn worker_cell(&self) -> CellId {
        self.worker_cell
    }

    /// The underlying turn acceptor.
    pub fn acceptor(&self) -> &A {
        &self.acceptor
    }

    /// The calls made so far under this mandate.
    pub fn calls_made(&self) -> i64 {
        self.calls_made
    }

    /// The calls remaining on the mandate.
    pub fn remaining(&self) -> i64 {
        self.grant.rate_limit - self.calls_made
    }

    /// Admit and submit one inline tool call.
    pub fn invoke(
        &mut self,
        tool: i64,
        now: i64,
        mut work: Vec<Effect>,
    ) -> Result<ToolReceipt, ToolCallError<A::Error>> {
        let old = self.calls_made;
        let new = old + 1;
        if !deleg_admit(&self.grant, now, tool, old, new) {
            return Err(ToolCallError::Refused(
                self.diagnose_refusal(tool, now, old),
            ));
        }

        let mut effects = Vec::with_capacity(work.len() + 1);
        effects.push(Effect::SetField {
            cell: self.worker_cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(new as u64),
        });
        effects.append(&mut work);

        let receipt = self
            .acceptor
            .accept_turn(&self.grant.tool_method, effects)
            .map_err(ToolCallError::Execution)?;
        self.calls_made = new;
        Ok(ToolReceipt {
            receipt,
            calls_made: new,
            remaining: self.remaining(),
        })
    }

    /// Admit and enqueue one non-blocking routed tool call.
    pub fn enqueue(
        &mut self,
        tool: i64,
        now: i64,
        work: Vec<Effect>,
    ) -> Result<RoutedHandle, ToolCallError<A::Error>> {
        let old = self.calls_made;
        let new = old + 1;
        if !deleg_admit(&self.grant, now, tool, old, new) {
            return Err(ToolCallError::Refused(
                self.diagnose_refusal(tool, now, old),
            ));
        }

        self.calls_made = new;
        let mut effects = Vec::with_capacity(work.len() + 1);
        effects.push(Effect::SetField {
            cell: self.worker_cell,
            index: CALLS_MADE_SLOT as usize,
            value: field_from_u64(new as u64),
        });
        effects.extend(work.iter().cloned());
        let routed_turn =
            self.acceptor
                .build_routed_turn(&self.grant.tool_method, new as u64, effects);
        let routed_hash = routed_turn.hash();

        self.pending.submit_pending_at(
            routed_turn,
            ResolutionCondition::AwaitHeight(now.max(0) as u64),
            u64::MAX,
            now.max(0) as u64,
        );
        self.inbox.push_back(RoutedWork {
            routed_hash,
            new_count: new,
            work,
            enqueued_at: now,
        });

        Ok(RoutedHandle {
            routed_hash,
            tool,
            enqueued_at: now,
        })
    }

    /// Drain the routed inbox through the turn acceptor.
    pub fn drive_executor(&mut self, now: i64) -> Vec<[u8; 32]> {
        let mut drained = Vec::new();
        while let Some(item) = self.inbox.pop_front() {
            drained.push(item.routed_hash);

            let mut effects = Vec::with_capacity(item.work.len() + 1);
            effects.push(Effect::SetField {
                cell: self.worker_cell,
                index: CALLS_MADE_SLOT as usize,
                value: field_from_u64(item.new_count as u64),
            });
            effects.extend(item.work.iter().cloned());

            match self.acceptor.accept_turn(&self.grant.tool_method, effects) {
                Ok(receipt) => {
                    let tool_receipt = ToolReceipt {
                        receipt,
                        calls_made: item.new_count,
                        remaining: self.grant.rate_limit - item.new_count,
                    };
                    let delivery = DeliveryReceipt {
                        routed_hash: item.routed_hash,
                        executor_cell: self.worker_cell,
                        enqueued_at: item.enqueued_at,
                        delivered_at: now,
                    };
                    let _events = self.pending.resolve(
                        item.routed_hash,
                        ResolutionOutcome::Resolved(tool_receipt.receipt.clone()),
                    );
                    self.results.insert(
                        item.routed_hash,
                        Ok(RoutedResult {
                            tool_receipt,
                            delivery,
                        }),
                    );
                }
                Err(e) => {
                    if self.calls_made == item.new_count {
                        self.calls_made = item.new_count - 1;
                    }
                    let reason = format!("routed execution rejected: {e}");
                    let _events = self.pending.resolve(
                        item.routed_hash,
                        ResolutionOutcome::Broken(BrokenReason::TurnRejected(
                            TurnError::PreconditionFailed {
                                description: reason.clone(),
                            },
                        )),
                    );
                    self.results.insert(item.routed_hash, Err(reason));
                }
            }
        }
        drained
    }

    /// Poll a routed handle without consuming the result.
    pub fn status(&self, handle: &RoutedHandle) -> RoutedStatus {
        match self.results.get(&handle.routed_hash) {
            Some(Ok(_)) => RoutedStatus::Delivered,
            Some(Err(_)) => RoutedStatus::Broken,
            None => RoutedStatus::Pending,
        }
    }

    /// Resolve and consume a routed result.
    pub fn resolve(
        &mut self,
        handle: &RoutedHandle,
    ) -> Result<RoutedResult, ToolCallError<A::Error>> {
        match self.results.remove(&handle.routed_hash) {
            Some(Ok(result)) => Ok(result),
            Some(Err(reason)) => Err(ToolCallError::Route(reason)),
            None => Err(ToolCallError::Route(format!(
                "routed call {:02x}{:02x}.. not yet delivered (drive the executor first)",
                handle.routed_hash[0], handle.routed_hash[1]
            ))),
        }
    }

    /// The number of routed calls currently enqueued.
    pub fn inbox_depth(&self) -> usize {
        self.inbox.len()
    }

    /// Register a routed dependency in the pending registry.
    pub fn await_routed(&mut self, handle: &RoutedHandle, on: [u8; 32]) {
        self.pending.register_dependent(on, handle.routed_hash);
    }

    fn diagnose_refusal(&self, tool: i64, now: i64, old: i64) -> GatewayRefusal {
        if tool != self.grant.tool_id {
            GatewayRefusal::OutOfScope {
                presented: tool,
                granted: self.grant.tool_id,
            }
        } else if now > self.grant.deadline {
            GatewayRefusal::PastDeadline {
                now,
                deadline: self.grant.deadline,
            }
        } else {
            GatewayRefusal::OverRate {
                calls_made: old,
                rate_limit: self.grant.rate_limit,
            }
        }
    }
}

/// Utility for simple routed-turn identities.
pub fn build_token_routed_turn(
    worker_cell: CellId,
    method: &str,
    nonce: u64,
    cap_token: Vec<u8>,
    issuer_pubkey: [u8; 32],
    effects: Vec<Effect>,
) -> Turn {
    let action = Action {
        target: worker_cell,
        method: symbol(method),
        args: Vec::new(),
        authorization: Authorization::Token {
            encoded: cap_token,
            key_ref: TokenKeyRef::BiscuitIssuer { issuer_pubkey },
            discharges: Vec::new(),
        },
        preconditions: Default::default(),
        effects,
        may_delegate: DelegationMode::None,
        commitment_mode: CommitmentMode::Full,
        balance_change: None,
        witness_blobs: vec![],
    };
    let mut forest = CallForest::new();
    forest.add_root(action);
    Turn {
        agent: worker_cell,
        nonce,
        call_forest: forest,
        fee: 5_000,
        memo: None,
        valid_until: None,
        depends_on: Vec::new(),
        conservation_proof: None,
        sovereign_witnesses: HashMap::new(),
        previous_receipt_hash: None,
        execution_proof: None,
        execution_proof_cell: None,
        execution_proof_new_commitment: None,
        custom_program_proofs: None,
        effect_binding_proofs: Vec::new(),
        cross_effect_dependencies: Vec::new(),
        effect_witness_index_map: Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn demo_grant() -> ToolGrant {
        ToolGrant {
            tool_id: 77,
            rate_limit: 3,
            deadline: 100,
            tool_method: "search".to_string(),
        }
    }

    #[test]
    fn tool_gateway_admit_mirrors_lean_delegadmit() {
        let g = demo_grant();

        assert!(deleg_admit(&g, 50, 77, 0, 1));
        assert!(deleg_admit(&g, 50, 77, 1, 2));
        assert!(deleg_admit(&g, 50, 77, 2, 3));
        assert!(!deleg_admit(&g, 50, 77, 3, 4));
        assert!(!deleg_admit(&g, 50, 99, 0, 1));
        assert!(!deleg_admit(&g, 101, 77, 0, 1));
        assert!(!deleg_admit(&g, 50, 77, 0, 2));
        assert!(!deleg_admit(&g, 50, 77, -1, 0));
    }

    #[test]
    fn mandate_program_carries_rate_and_monotonic() {
        match mandate_program(3) {
            CellProgram::Predicate(cs) => {
                assert_eq!(cs.len(), 2);
                assert!(matches!(
                    cs[0],
                    StateConstraint::FieldLte { index, .. } if index == CALLS_MADE_SLOT
                ));
                assert!(matches!(
                    cs[1],
                    StateConstraint::Monotonic { index } if index == CALLS_MADE_SLOT
                ));
            }
            other => panic!("expected a Predicate program, got {other:?}"),
        }
    }
}
