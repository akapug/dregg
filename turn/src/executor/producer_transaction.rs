//! Transaction boundary for the demoted Rust producer reference.
//!
//! `dregg-exec-lean` runs the Rust executor in place to obtain a differential
//! result and receipt substrate, then installs the verified Lean verdict. A
//! verified rejection must therefore undo more than the `Ledger`: the Rust run
//! may have advanced a receipt head, Stingray budget, rate-limit windows, or
//! executor observation state.
//!
//! The ordinary producer fences note/revocation/reactive effects before its
//! checkpoint. Embedded hosts can instead retain a successful candidate until
//! durable publication: their explicit checkpoint also captures each additional
//! side table the turn can mutate. Ordinary field/transfer turns do not clone
//! unrelated note history or factory registries.

use dregg_cell::nullifier_set::NullifierSet;
use dregg_cell::{CellId, CommitmentSet, FactoryRegistry, RevokedSet, ShieldedNoteSet};
use dregg_cell_crypto::note_bridge::BridgedNullifierSet;

use super::{RateLimitStateSnapshot, TurnExecutor};
use crate::{
    action::Effect,
    pending::{PendingTurnRegistry, ReactiveNullifierSet},
    turn::{ConsumedCapWitness, TurnReceipt},
    umem::{UProjection, UmemTurnWitness},
};

/// Opaque pre-image of side tables reachable from the verified producer's
/// covered set. It is intentionally non-`Clone`: one checkpoint authorizes one
/// rollback, preventing stale pre-images from being replayed later.
pub struct ProducerReferenceCheckpoint {
    rate_limits: RateLimitStateSnapshot,
    budget: Option<BudgetCheckpoint>,
    receipt_agent: CellId,
    previous_receipt_hash: Option<[u8; 32]>,
    last_write_set: Vec<CellId>,
    consumed_cap_witnesses: Vec<ConsumedCapWitness>,
    last_umem_witness: Option<Result<UmemTurnWitness, String>>,
    last_umem_yield: Option<UProjection>,
    embedded: Option<EmbeddedCandidateCheckpoint>,
}

/// Additional pre-images needed when an accepted Rust candidate can still be
/// refused by its publisher. The raw forest journal has already been consumed
/// on success, so its side-table undo information is no longer available.
struct EmbeddedCandidateCheckpoint {
    bridged_nullifiers: Option<BridgedNullifierSet>,
    note_nullifiers: Option<NullifierSet>,
    note_commitments: Option<CommitmentSet>,
    note_revoked: Option<RevokedSet>,
    note_shielded: Option<ShieldedNoteSet>,
    reactive_registry: Option<PendingTurnRegistry>,
    reactive_nullifiers: Option<ReactiveNullifierSet>,
    factory_registry: Option<FactoryRegistry>,
    restore_exact_admission: bool,
}

#[derive(Default)]
struct EmbeddedSideWrites {
    bridged: bool,
    nullifiers: bool,
    commitments: bool,
    revoked: bool,
    shielded: bool,
    reactive: bool,
    factory: bool,
}

impl EmbeddedSideWrites {
    /// Exhaustive over the real effect vocabulary: adding an effect requires
    /// classifying its executor-owned writes at this publication boundary.
    fn include(&mut self, effect: &Effect) {
        match effect {
            Effect::BridgeMint { .. } => self.bridged = true,
            Effect::NoteSpend { .. } => self.nullifiers = true,
            Effect::NoteCreate { .. } => self.commitments = true,
            Effect::RevokeCapability { .. } => self.revoked = true,
            Effect::ShieldedTransfer { .. } => {
                self.nullifiers = true;
                self.shielded = true;
            }
            Effect::Shield { .. } => self.shielded = true,
            Effect::Deshield { .. } => {
                self.nullifiers = true;
                self.commitments = true;
            }
            Effect::Promise { .. } | Effect::Notify { .. } | Effect::React { .. } => {
                self.reactive = true;
            }
            Effect::CreateCellFromFactory { .. } => self.factory = true,
            Effect::ExerciseViaCapability { inner_effects, .. } => {
                for inner in inner_effects {
                    self.include(inner);
                }
            }
            Effect::SetField { .. }
            | Effect::Transfer { .. }
            | Effect::GrantCapability { .. }
            | Effect::EmitEvent { .. }
            | Effect::IncrementNonce { .. }
            | Effect::CreateCell { .. }
            | Effect::SetPermissions { .. }
            | Effect::SetVerificationKey { .. }
            | Effect::SetProgram { .. }
            | Effect::SpawnWithDelegation { .. }
            | Effect::RefreshDelegation { .. }
            | Effect::RevokeDelegation { .. }
            | Effect::Introduce { .. }
            | Effect::PipelinedSend { .. }
            | Effect::MakeSovereign { .. }
            | Effect::Refusal { .. }
            | Effect::CellSeal { .. }
            | Effect::CellUnseal { .. }
            | Effect::CellDestroy { .. }
            | Effect::Burn { .. }
            | Effect::AttenuateCapability { .. }
            | Effect::ReceiptArchive { .. }
            | Effect::Mint { .. }
            | Effect::Custom { .. }
            | Effect::CreateHybridCell { .. }
            | Effect::RotatePqIdentity { .. } => {}
        }
    }
}

struct BudgetCheckpoint {
    spent: u64,
    debit_len: usize,
}

fn retain_observation<T: Clone + Default>(slot: &std::sync::Mutex<T>, take: bool) -> T {
    let mut value = slot.lock().unwrap_or_else(|error| error.into_inner());
    if take {
        std::mem::take(&mut *value)
    } else {
        value.clone()
    }
}

impl TurnExecutor {
    /// Whether this turn can debit factory quota. Used to keep ordinary turns
    /// off the registry-clone path while retaining a whole-turn inverse for
    /// direct and capability-wrapped factory births.
    pub(super) fn turn_mutates_factory_registry(turn: &crate::turn::Turn) -> bool {
        fn effect_mutates_factory(effect: &crate::action::Effect) -> bool {
            match effect {
                crate::action::Effect::CreateCellFromFactory { .. } => true,
                crate::action::Effect::ExerciseViaCapability { inner_effects, .. } => {
                    inner_effects.iter().any(effect_mutates_factory)
                }
                _ => false,
            }
        }
        fn tree_mutates_factory(tree: &crate::forest::CallTree) -> bool {
            tree.action.effects.iter().any(effect_mutates_factory)
                || tree.children.iter().any(tree_mutates_factory)
        }
        turn.call_forest.roots.iter().any(tree_mutates_factory)
    }

    /// Capture the mutable side-state pre-image immediately before a
    /// speculative Rust reference run under the verified producer.
    ///
    /// Only the selected agent's authority-chain entry is copied, and the
    /// Stingray inverse records a length/counter rather than cloning its full
    /// debit history. The producer owns exclusive turn execution while this
    /// checkpoint is live.
    pub fn checkpoint_producer_reference(
        &self,
        receipt_agent: CellId,
    ) -> ProducerReferenceCheckpoint {
        self.checkpoint_reference_state(receipt_agent, false)
    }

    fn checkpoint_reference_state(
        &self,
        receipt_agent: CellId,
        take_observations: bool,
    ) -> ProducerReferenceCheckpoint {
        let rate_limits = self.rate_limit_state_snapshot();
        let budget = self.budget_gate.as_ref().map(|gate| {
            let gate = gate.lock().unwrap_or_else(|error| error.into_inner());
            BudgetCheckpoint {
                spent: gate.slice.spent,
                debit_len: gate.slice.debits.len(),
            }
        });
        let previous_receipt_hash = self.get_last_receipt_hash(&receipt_agent);
        let last_write_set = retain_observation(&self.last_write_set, take_observations);
        let consumed_cap_witnesses =
            retain_observation(&self.consumed_cap_witnesses, take_observations);
        let last_umem_witness = retain_observation(&self.last_umem_witness, take_observations);
        let last_umem_yield = retain_observation(&self.last_umem_yield, take_observations);

        ProducerReferenceCheckpoint {
            rate_limits,
            budget,
            receipt_agent,
            previous_receipt_hash,
            last_write_set,
            consumed_cap_witnesses,
            last_umem_witness,
            last_umem_yield,
            embedded: None,
        }
    }

    /// Capture the owned mutable state of an embedded execution candidate.
    ///
    /// Unlike the verified producer's restricted reference, an embedded turn
    /// can reach the full forest vocabulary and remain provisional after Rust
    /// returns success. Capture only the additional tables that vocabulary can
    /// mutate. Ledger rollback remains the caller's matching restore point.
    pub fn checkpoint_embedded_candidate(
        &self,
        turn: &crate::turn::Turn,
    ) -> ProducerReferenceCheckpoint {
        let mut writes = EmbeddedSideWrites::default();
        for root in &turn.call_forest.roots {
            for tree in root.iter_dfs() {
                for effect in &tree.action.effects {
                    writes.include(effect);
                }
            }
        }
        // These are prior-turn observations, not inputs to execution. Move them
        // into the owned checkpoint: a umem projection can cover the whole
        // ledger, so cloning it here would make every embedded turn O(ledger).
        // Refusal restores them; success replaces them with this turn's result.
        let mut checkpoint = self.checkpoint_reference_state(turn.agent, true);
        checkpoint.embedded = Some(EmbeddedCandidateCheckpoint {
            bridged_nullifiers: writes.bridged.then(|| {
                self.bridged_nullifiers
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone()
            }),
            note_nullifiers: writes.nullifiers.then(|| {
                self.note_nullifiers
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone()
            }),
            note_commitments: writes.commitments.then(|| {
                self.note_commitments
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone()
            }),
            note_revoked: writes.revoked.then(|| {
                self.note_revoked
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone()
            }),
            note_shielded: writes.shielded.then(|| {
                self.note_shielded
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone()
            }),
            reactive_registry: writes.reactive.then(|| {
                self.reactive_registry
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone()
            }),
            reactive_nullifiers: writes.reactive.then(|| {
                self.reactive_nullifiers
                    .lock()
                    .unwrap_or_else(|e| e.into_inner())
                    .clone()
            }),
            factory_registry: writes
                .factory
                .then(|| self.factory_registry.borrow().clone()),
            // If execution was already blocked by an earlier applied/consumed
            // token, refusal must preserve that prior slot rather than treating
            // it as a token consumed by this attempted execution.
            restore_exact_admission: self.exact_fnsp_v3_admission_ready_for_execute().is_ok(),
        });
        checkpoint
    }

    /// Restore the pre-image after the verified producer rejects a turn the
    /// Rust reference speculatively ran. Consuming the checkpoint makes the
    /// inverse single-use.
    pub fn rollback_producer_reference(&self, checkpoint: ProducerReferenceCheckpoint) {
        if let Some(embedded) = checkpoint.embedded {
            if let Some(previous) = embedded.bridged_nullifiers {
                *self
                    .bridged_nullifiers
                    .lock()
                    .unwrap_or_else(|e| e.into_inner()) = previous;
            }
            if let Some(previous) = embedded.note_nullifiers {
                *self
                    .note_nullifiers
                    .lock()
                    .unwrap_or_else(|e| e.into_inner()) = previous;
            }
            if let Some(previous) = embedded.note_commitments {
                *self
                    .note_commitments
                    .lock()
                    .unwrap_or_else(|e| e.into_inner()) = previous;
            }
            if let Some(previous) = embedded.note_revoked {
                *self.note_revoked.lock().unwrap_or_else(|e| e.into_inner()) = previous;
            }
            if let Some(previous) = embedded.note_shielded {
                *self.note_shielded.lock().unwrap_or_else(|e| e.into_inner()) = previous;
            }
            if let Some(previous) = embedded.reactive_registry {
                *self
                    .reactive_registry
                    .lock()
                    .unwrap_or_else(|e| e.into_inner()) = previous;
            }
            if let Some(previous) = embedded.reactive_nullifiers {
                *self
                    .reactive_nullifiers
                    .lock()
                    .unwrap_or_else(|e| e.into_inner()) = previous;
            }
            if let Some(previous) = embedded.factory_registry {
                *self.factory_registry.borrow_mut() = previous;
            }
            if embedded.restore_exact_admission {
                self.restore_exact_fnsp_v3_admission_after_rejection()
                    .expect("the candidate owns any newly applied exact admission token");
            }
        }
        self.restore_rate_limit_state(&checkpoint.rate_limits)
            .expect("an in-memory rate-limit checkpoint is valid");
        if let (Some(gate), Some(previous)) = (&self.budget_gate, checkpoint.budget) {
            let mut gate = gate.lock().unwrap_or_else(|error| error.into_inner());
            gate.slice.spent = previous.spent;
            gate.slice.debits.truncate(previous.debit_len);
        }
        self.restore_last_receipt_hash(checkpoint.receipt_agent, checkpoint.previous_receipt_hash);
        *self
            .last_write_set
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.last_write_set;
        *self
            .consumed_cap_witnesses
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.consumed_cap_witnesses;
        *self
            .last_umem_witness
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.last_umem_witness;
        *self
            .last_umem_yield
            .lock()
            .unwrap_or_else(|error| error.into_inner()) = checkpoint.last_umem_yield;
    }

    /// Advance the authority chain to the exact receipt the verified producer
    /// returned.
    pub fn record_authoritative_receipt_head(&self, agent: CellId, receipt_hash: [u8; 32]) {
        self.record_receipt_hash(agent, receipt_hash);
    }

    /// Re-stamp, re-sign, and atomically advance the authority chain to that
    /// exact final receipt. Keeping those operations in one API prevents the
    /// pre-restamp Rust hash from surviving as the next turn's expected head.
    pub fn restamp_authoritative_committed_receipt(
        &self,
        receipt: TurnReceipt,
        authoritative_post_root: [u8; 32],
    ) -> TurnReceipt {
        let receipt = self.restamp_committed_receipt(receipt, authoritative_post_root);
        self.record_authoritative_receipt_head(receipt.agent, receipt.receipt_hash());
        receipt
    }
}
