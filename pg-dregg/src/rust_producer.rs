//! The **lightweight Rust-executor producer** — the drainer's PRODUCE gate run
//! through the pure-Rust verified `TurnExecutor` (`dregg-turn`), with NO Lean
//! runtime linked.
//!
//! # Where this sits (the middle tier)
//!
//! [`crate::drainer`] runs the four-gate write spine SUBMIT → PRODUCE → CHAIN →
//! MIRROR, where PRODUCE is a [`crate::drainer::Producer`]. There are now THREE
//! producers, in ascending order of weight + guarantee:
//!
//!   1. [`crate::drainer::FoldProducer`] — the deterministic STAND-IN (default,
//!      circuit-free, Lean-free). NO executor: it derives a conserving post-image
//!      by a fold. The gate plumbing is `cargo test`-proven over it.
//!   2. [`RustProducer`] (THIS module, `tier-d-rust`) — the REAL pure-Rust
//!      `TurnExecutor::execute`. A genuine in-Postgres executor: lightweight (no
//!      `libleanshared`, no `libdregg_lean.a`, no Lean toolchain), at parity with
//!      the verified Lean spec (`docs/RUST-LEAN-EXECUTOR-PARITY.md`).
//!   3. [`crate::lean_producer::LeanProducer`] (`tier-d` / `tier-d-lean`) — the
//!      verified Lean executor `execFullForestG`, linked ~150 MB, native-only. The
//!      heavy opt-in for a node that wants the verified guarantee end-to-end.
//!
//! This is the same ship-Rust-default split `sdk-py` took (`3dd988be`): the SDK
//! ships the pure-Rust `TurnExecutor` by default and treats the Lean kernel as the
//! opt-in heavy extra. pg-dregg now gets the same — a real, lightweight,
//! at-parity in-backend executor between the fold stand-in and the heavy Lean tier.
//!
//! # What is faithful here, and the SAME honest residual the Lean tier carries
//!
//! FAITHFUL: the produced post-image's balances and the commit/reject decision are
//! the verified `TurnExecutor`'s — not a Rust fold. The executor enforces
//! conservation, authorization, liveness, and admission in-kernel and fails closed
//! (an overspend / a sealed endpoint / a self-transfer does NOT commit), and the
//! post-balances are read back from the executor's mutated [`dregg_cell::Ledger`].
//! This is the literal "the drainer's PRODUCE runs the REAL `TurnExecutor` in
//! Postgres."
//!
//! RESIDUAL (flagged, not hidden): exactly as [`crate::lean_producer::LeanProducer`],
//! pg-dregg does not (and need not) decode the submitter's postcard `SignedTurn`
//! bytes (`intent.signed_turn`) into the executor's native [`dregg_turn::Turn`] —
//! that marshaller lives in the node. So this producer SYNTHESIZES a conserving
//! transfer (credit the acting agent, debit a float source) as the turn it runs —
//! but, unlike the fold stand-in, it runs that turn through the REAL executor and
//! takes the executor's verdict + post-state as authoritative. Lifting the full
//! `SignedTurn` decode is the same node-side `dregg-turn` work the Lean tier names.
//!
//! The Rust↔Lean parity that justifies trusting this producer's verdict (the
//! differential gauntlet, the audited under-enforcement alignment) is documented
//! in `docs/RUST-LEAN-EXECUTOR-PARITY.md`; a node that wants the verified executor
//! as the authoritative shadow links the Lean tier (`tier-d`).

use crate::drainer::{Producer, SubmitIntent};
use crate::mirror::{MemCell, MirrorBatch};
use crate::workflow::{balance_reg, cell_row, turn_row};
use dregg_cell::permissions::{AuthRequired, Permissions};
use dregg_cell::{Cell, Ledger};
use dregg_turn::{
    Action, Authorization, CommitmentMode, ComputronCosts, DelegationMode, Effect, Preconditions,
    TurnBuilder, TurnExecutor, TurnResult,
};

/// The synthesized transfer's INTERNAL source cell key (the float holder the
/// executor debits). Distinct from the destination key so the two derive to
/// distinct [`CellId`]s; decoupled from the mirror's `source`/`agent` ids exactly
/// as the Lean tier's wire ids are (the executor's internal numbering is its own).
const EXEC_SRC_PK: [u8; 32] = [0x51u8; 32];
/// The synthesized transfer's INTERNAL destination cell key (the acting agent's
/// stand-in inside the executor).
const EXEC_DST_PK: [u8; 32] = [0x52u8; 32];
/// The shared asset class (token id) both internal cells hold — a plain transfer
/// moves balance within one asset class.
const EXEC_TOKEN: [u8; 32] = [0u8; 32];

/// Fully-permissive permissions (every action requires no authorization) — the
/// internal cells the synthesized transfer runs over. The SUBMIT gate has already
/// verified the submitter's REAL capability ([`crate::authz::decide`]) before this
/// runs; the executor's load-bearing job at this seam is conservation + liveness +
/// admission, which it enforces fail-closed regardless of these internal perms.
fn permissive() -> Permissions {
    Permissions {
        send: AuthRequired::None,
        receive: AuthRequired::None,
        set_state: AuthRequired::None,
        set_permissions: AuthRequired::None,
        set_verification_key: AuthRequired::None,
        increment_nonce: AuthRequired::None,
        delegate: AuthRequired::None,
        access: AuthRequired::None,
    }
}

/// The pure-Rust verified-executor producer: each [`Producer::produce`] runs a
/// conserving transfer for the acting agent through the REAL
/// [`dregg_turn::TurnExecutor`] and yields the executor's verified post-image.
///
/// It maintains the SAME per-cell `(balance, nonce)` bookkeeping
/// [`crate::drainer::FoldProducer`] / [`crate::lean_producer::LeanProducer`] do —
/// so successive produced turns are internally consistent across a drain run — but
/// the post-image VALUES and the commit decision come from the executor's mutated
/// ledger, not a fold.
#[derive(Clone, Debug)]
pub struct RustProducer {
    /// The float source cell every synthesized transfer debits (the 32-byte id).
    pub source: [u8; 32],
    /// The unit each synthesized transfer moves.
    pub unit: i64,
    /// The running per-cell `(balance, nonce)` the producer maintains so the turn
    /// it builds each round reflects the executor's prior post-state.
    balances: std::collections::BTreeMap<[u8; 32], (i64, u64)>,
}

impl RustProducer {
    /// A verified-executor producer with `source` funded to `float`, moving `unit`
    /// per turn. Needs NO runtime init — the pure-Rust executor links no Lean.
    pub fn new(source: [u8; 32], float: i64, unit: i64) -> Self {
        let mut balances = std::collections::BTreeMap::new();
        balances.insert(source, (float, 0));
        RustProducer {
            source,
            unit,
            balances,
        }
    }

    /// The producer's notion of a cell's `(balance, nonce)` (for assertions/demos),
    /// kept in lock-step with the verified executor's post-state.
    pub fn balance(&self, id: [u8; 32]) -> i64 {
        self.balances.get(&id).map(|&(b, _)| b).unwrap_or(0)
    }

    /// The Rust executor is ALWAYS available in a `tier-d-rust` build — it links no
    /// archive and needs no runtime init. (Mirrors
    /// [`crate::lean_producer::LeanProducer::runtime_available`] for symmetry; here
    /// it is unconditionally true once the feature is on.)
    pub fn runtime_available() -> bool {
        true
    }
}

impl Producer for RustProducer {
    fn produce(
        &mut self,
        intent: &SubmitIntent,
        ordinal: u64,
        prev_root: [u8; 32],
    ) -> Result<MirrorBatch, String> {
        // A malformed (empty) envelope is refused, exactly as the other producers,
        // so the `refused` outcome path stays real (the executor never sees garbage).
        if intent.signed_turn.is_empty() {
            return Err("empty signed turn (malformed envelope)".to_string());
        }

        // The producer's running pre-state for the source + this agent.
        let (src_bal, src_nonce) = *self.balances.get(&self.source).unwrap_or(&(0, 0));
        if src_bal < self.unit {
            return Err(format!(
                "float exhausted: source holds {src_bal}, unit is {}",
                self.unit
            ));
        }
        let (dst_bal, _) = *self.balances.get(&intent.agent).unwrap_or(&(0, 0));

        // Build a fresh ledger with the two INTERNAL cells funded to the producer's
        // running pre-state, then run a conserving transfer through the REAL Rust
        // executor. `from == action.target` ⇒ no cross-cell capability is needed;
        // the executor still enforces conservation, liveness, and admission.
        let mut src_cell = Cell::with_balance(EXEC_SRC_PK, EXEC_TOKEN, src_bal);
        src_cell.permissions = permissive();
        let src_id = src_cell.id();
        let mut dst_cell = Cell::with_balance(EXEC_DST_PK, EXEC_TOKEN, dst_bal);
        dst_cell.permissions = permissive();
        let dst_id = dst_cell.id();

        let mut ledger = Ledger::new();
        ledger
            .insert_cell(src_cell)
            .map_err(|e| format!("Tier-D-rust: funding the source cell failed: {e:?}"))?;
        ledger
            .insert_cell(dst_cell)
            .map_err(|e| format!("Tier-D-rust: funding the destination cell failed: {e:?}"))?;

        let amount = u64::try_from(self.unit)
            .map_err(|_| format!("Tier-D-rust: negative transfer unit {}", self.unit))?;
        let action = Action {
            target: src_id,
            method: [0u8; 32],
            args: vec![],
            authorization: Authorization::Unchecked,
            preconditions: Preconditions::default(),
            effects: vec![Effect::Transfer {
                from: src_id,
                to: dst_id,
                amount,
            }],
            may_delegate: DelegationMode::None,
            commitment_mode: CommitmentMode::default(),
            balance_change: None,
            witness_blobs: vec![],
        };
        // A fresh ledger per produce ⇒ a genesis (nonce 0, no prior receipt) turn.
        let mut tb = TurnBuilder::new(src_id, 0).fee(0);
        tb.add_action(action);
        let turn = tb.build();

        // Run the turn through the REAL verified Rust executor. Its verdict is
        // authoritative: a rejection (overspend / liveness / admission) is a
        // REFUSAL — fail-closed, no state leaks.
        let executor = TurnExecutor::new(ComputronCosts::zero());
        match executor.execute(&turn, &mut ledger) {
            TurnResult::Committed { .. } => {}
            TurnResult::Rejected { reason, at_action } => {
                return Err(format!(
                    "Tier-D-rust: the verified executor rejected the turn at {at_action:?}: {reason}"
                ));
            }
            TurnResult::Expired => {
                return Err("Tier-D-rust: the verified executor expired the turn".to_string());
            }
            TurnResult::Pending => {
                return Err("Tier-D-rust: the verified executor left the turn pending".to_string());
            }
        }

        // Read the VERIFIED post-balances back from the executor's mutated ledger.
        let new_src_bal = ledger
            .get(&src_id)
            .map(|c| c.state.balance())
            .ok_or_else(|| "Tier-D-rust: executor dropped the source cell".to_string())?;
        let new_dst_bal = ledger
            .get(&dst_id)
            .map(|c| c.state.balance())
            .ok_or_else(|| "Tier-D-rust: executor dropped the destination cell".to_string())?;
        // The mirror's source nonce advances per turn (the running bookkeeping the
        // chaining context folds), exactly as the fold/Lean producers do.
        let new_src_nonce = src_nonce + 1;

        let touched: [([u8; 32], i64, u64); 2] = [
            (self.source, new_src_bal, new_src_nonce),
            (intent.agent, new_dst_bal, 0),
        ];

        // The chaining ledger root, derived bit-identically to the fold + Lean
        // producers (`crate::drainer::fold_chain_root`) so a mixed-producer history
        // still chains (the kernel's in-circuit root is the IVC light client's
        // concern, `.docs-history-noclaude/PG-DREGG.md` §10.2; the CHAIN gate's tooth is structural).
        let post = crate::drainer::fold_chain_root(prev_root, ordinal, &touched);

        let cells = vec![
            cell_row(self.source, new_src_bal, new_src_nonce),
            cell_row(intent.agent, new_dst_bal, 0),
        ];
        let memory: Vec<MemCell> = touched
            .iter()
            .map(|&(id, bal, _)| balance_reg(id, bal))
            .collect();
        // `creator` is the acting agent (the provenance the drainer asserts).
        let turn_hdr = turn_row(ordinal, prev_root, post, intent.agent);
        let batch = MirrorBatch::from_parts(turn_hdr, cells, vec![], memory)
            .map_err(|m| format!("Tier-D-rust: the verified post-image was malformed: {m}"))?;

        // Advance the producer's own bookkeeping to the executor-verified post-state
        // so the next produced turn's pre-state is consistent.
        self.balances
            .insert(self.source, (new_src_bal, new_src_nonce));
        self.balances.insert(intent.agent, (new_dst_bal, 0));
        Ok(batch)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::drainer::Drainer;
    use dregg_auth::credential::{Caveat, Pred, RootKey};

    const SOURCE: [u8; 32] = [0xc0u8; 32];

    fn agent(tag: u8) -> [u8; 32] {
        let mut id = [0x11u8; 32];
        id[0] = tag;
        id
    }

    /// The shared process-wide authz serialization lock (these tests mutate the
    /// global issuer key / revocation set the whole lib-test binary shares).
    #[must_use]
    fn fresh_issuer() -> (std::sync::MutexGuard<'static, ()>, RootKey) {
        let guard = crate::authz::test_serial_lock();
        let issuer = RootKey::from_seed([7u8; 32]);
        crate::authz::set_issuer_pubkey(issuer.public());
        crate::authz::lru_clear();
        crate::authz::revoked_clear();
        (guard, issuer)
    }

    fn submit_token(issuer: &RootKey) -> String {
        issuer
            .mint([
                Caveat::FirstParty(Pred::AttrEq {
                    key: "action".into(),
                    value: "submit".into(),
                }),
                Caveat::FirstParty(Pred::AttrPrefix {
                    key: "resource".into(),
                    prefix: "".into(),
                }),
                Caveat::FirstParty(Pred::NotAfter { at: 1_000_000 }),
            ])
            .encode()
    }

    fn intent(id: u8, agent: [u8; 32], token: &str) -> SubmitIntent {
        SubmitIntent {
            id: [id; 16],
            agent,
            signed_turn: vec![0xab, 0xcd], // non-empty = a well-formed envelope
            token: token.to_string(),
        }
    }

    /// A bare produce (no drainer) drives the REAL Rust executor and yields the
    /// executor-verified post-balances of a conserving transfer.
    #[test]
    fn the_rust_executor_commits_a_conserving_transfer() {
        let p_agent = agent(0x20);
        let mut p = RustProducer::new(SOURCE, 1_000, 30);
        let batch = p
            .produce(
                &intent(1, p_agent, "ignored-here"),
                0,
                crate::workflow::GENESIS_ROOT,
            )
            .expect("the verified Rust executor commits a conserving transfer");

        // The post-image carries the executor-VERIFIED post-balances: source
        // 1000→970, agent 0→30 (the conserved 30-unit move).
        assert_eq!(p.balance(SOURCE), 970, "source debited by the executor");
        assert_eq!(p.balance(p_agent), 30, "agent credited by the executor");
        assert_eq!(batch.turn.creator, p_agent);
        assert_eq!(batch.turn.ordinal, 0);
        let src_cell = batch.cells.iter().find(|c| c.cell_id == SOURCE).unwrap();
        let dst_cell = batch.cells.iter().find(|c| c.cell_id == p_agent).unwrap();
        assert_eq!(src_cell.balance, 970);
        assert_eq!(dst_cell.balance, 30);
    }

    /// An exhausted float is refused before the executor (the conservation-respecting
    /// refusal path is real).
    #[test]
    fn an_overspend_is_refused() {
        let mut p = RustProducer::new(SOURCE, 10, 30);
        let err = p
            .produce(
                &intent(1, agent(0x20), "x"),
                0,
                crate::workflow::GENESIS_ROOT,
            )
            .expect_err("an overspend is refused");
        assert!(err.contains("float exhausted"), "{err}");
    }

    /// An empty envelope is refused as a malformed intent.
    #[test]
    fn an_empty_envelope_is_refused() {
        let mut p = RustProducer::new(SOURCE, 1_000, 1);
        let mut bad = intent(1, agent(0x20), "x");
        bad.signed_turn = vec![];
        let err = p
            .produce(&bad, 0, crate::workflow::GENESIS_ROOT)
            .expect_err("empty envelope is refused");
        assert!(err.contains("empty signed turn"), "{err}");
    }

    /// THE END-TO-END PROOF: a real intent drains pending→executed through the
    /// four-gate spine with the Rust executor as the PRODUCE gate; the chain
    /// advances and the verified post-image is ready to mirror.
    #[test]
    fn an_authorized_intent_drains_through_the_rust_executor() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let mut d = Drainer::new(RustProducer::new(SOURCE, 1_000, 1)).with_clock(1_000);

        assert_eq!(d.next_ordinal(), 0);
        let out = d.drain(&intent(1, agent(0x20), &tok));
        assert!(out.is_executed(), "authorized intent must drain: {out:?}");
        assert_eq!(d.next_ordinal(), 1);
        assert!(d.head().is_some());
        let batch = d.last_batch().expect("executed drain stashed its batch");
        // The post-image is the executor's: agent credited 1, source debited 1.
        let dst = batch
            .cells
            .iter()
            .find(|c| c.cell_id == agent(0x20))
            .unwrap();
        assert_eq!(dst.balance, 1, "agent credited by the verified executor");
        assert_eq!(d.counters().drained, 1);
        assert_eq!(d.counters().refused, 0);
    }

    /// A stream of authorized intents drains; the executor conserves value every
    /// turn (one debit, one credit), so Σ balances is invariant.
    #[test]
    fn draining_a_stream_conserves_value_through_the_rust_executor() {
        let (_g, issuer) = fresh_issuer();
        let tok = submit_token(&issuer);
        let float = 1_000i64;
        let mut d = Drainer::new(RustProducer::new(SOURCE, float, 1)).with_clock(1_000);

        let pending: Vec<SubmitIntent> = (0..16)
            .map(|k| intent(k as u8, agent(0x20 + (k % 4) as u8), &tok))
            .collect();
        let results = d.drain_all(&pending);

        assert_eq!(results.len(), 16);
        assert!(results.iter().all(|(_, o)| o.is_executed()));
        assert_eq!(d.counters().drained, 16);
        assert_eq!(d.next_ordinal(), 16);

        let p = d.producer();
        let agents_total: i64 = (0..4).map(|t| p.balance(agent(0x20 + t))).sum();
        assert_eq!(
            p.balance(SOURCE) + agents_total,
            float,
            "drained stream must conserve value"
        );
    }
}
