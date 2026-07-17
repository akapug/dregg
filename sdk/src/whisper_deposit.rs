//! # THE WHISPER DEPOSIT — the native, cap-gated, APPLY-TIME deposit half of the
//! context channel (the intra-turn cousin of [`dregg_turn::Effect::Notify`]).
//!
//! The [`crate::tool_gateway`] carrier ships a bounded [`WhisperFrame`] on an
//! ADMITTED gate return ([`crate::tool_gateway::ToolReceipt::whisper`]) by draining
//! ONE frame per admitted call from a pluggable
//! [`WhisperSource`](crate::tool_gateway::WhisperSource). The carrier says nothing
//! about WHERE a frame comes from — a host brings its own source (the meld tmpfs
//! hook is one). This module is the NATIVE dregg deposit that replaces that
//! tmpfs-file source: a WRITER's cap-gated turn deposits a cell-attributed frame,
//! addressed to a recipient SEAT, readable at APPLY time by the recipient gateway.
//!
//! ## The deposit primitive, and why THIS shape (the reuse-vs-new decision)
//!
//! A whisper deposit must (1) be a real, cap-gated TURN (so only an authorized
//! writer can whisper to a seat, and the executor — not an out-of-band check — is
//! the gate), (2) land at APPLY time, not finality (the view-polling lesson of
//! `TELEPATHY_DREGG_VERDICT.md`: whispers are apply-time-adjacent, like Notify),
//! (3) be attributable to the writer's cell (`from`), and (4) NOT touch the
//! Lean-mirrored admission crown or the effect grammar it proves.
//!
//! Three native candidates were weighed; this module reuses the cap-gated turn
//! path rather than any of them, ON PURPOSE:
//!
//! * **Literal [`dregg_turn::Effect::Notify`]** — WRONG PAYLOAD + WRONG LIFECYCLE.
//!   `Notify`'s payload is a `wake: Box<Turn>` that mints a nullifier-backed
//!   promise-hole the recipient must later `React` to (one-shot spend). A whisper
//!   carries 200 bytes of text, is read ONCE off a gate return, and is never
//!   reacted to. Smuggling text through a wake-turn memo, then leaving an unspent
//!   reactive hole (with a timeout) on the ledger for every ephemeral line, abuses
//!   the primitive and leaves a durable artifact for a RAM-only channel.
//! * **A new `Effect::WhisperDeposit` kernel variant** — CLEANEST IN THEORY, but it
//!   touches the index-sensitive `postcard` effect codec, needs a `LinearityClass`,
//!   executor dispatch, and (to stay honest) proof-machinery wiring — exactly the
//!   "kernel-adjacent" cost the PR draft flags. It also hands a RAM-resident channel
//!   a durable ledger half. That is a real escalation, justified only once the
//!   channel needs TRUSTLESS routing (see "Honest boundary" below); it is not
//!   needed for the deposit + drain this slice delivers.
//! * **[`dregg_storage::CapInbox`]** — DEPRECATED, and a DURABLE `MerkleQueue`
//!   (quota-bounded, per-message anti-spam deposit). A whisper is ephemeral,
//!   RAM-only, and free; a durable deposit-charged mailbox contradicts every one
//!   of the channel's physics budgets.
//!
//! What fits dregg's grain: the deposit IS a cap-gated turn through the SAME
//! [`SubAgent::execute_method`] gate the gateway's worker rides. The capability is
//! a SEAT-ADDRESSED method verb ([`whisper_method`]): a writer scoped to
//! `whisper.<seat>` may deposit to `<seat>` and ONLY `<seat>` — the executor rejects
//! a deposit under any other seat verb with `TokenInsufficientCapability` (the
//! cap-gate biting, in-executor). The committed deposit turn is the APPLY-TIME
//! event; on commit the attributed frame lands in the recipient's [`WhisperInbox`],
//! whose [`WhisperInbox::source_for`] is exactly a [`WhisperSource`] the recipient
//! gateway installs. Nothing here touches `deleg_admit`, the metering, or the
//! effect grammar.
//!
//! ## Honest boundary (the tradeoff this slice DOES NOT close)
//!
//! The frame TEXT is not yet cryptographically bound into the committed turn — the
//! deposit turn proves the writer holds the seat capability (attribution is real
//! and executor-enforced), but the SDK stamps the frame into the inbox after that
//! commit rather than the executor routing the bytes itself. That is the SAME
//! "not attested (this slice)" residual the carrier already documents: binding
//! `hash(text)` into the metered turn — or promoting the deposit to a native
//! `Effect` the executor routes end-to-end — is the receipt-backed-provenance
//! follow-up. For a same-runtime writer→gateway pair (the shape this slice
//! targets, and the meld consumer's) the cap-gated commit + SDK stamp is the honest
//! equivalent of the tmpfs source it replaces, with a REAL per-seat capability
//! gate the tmpfs file never had.

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};

use dregg_cell::CellId;
use dregg_cell::program::field_from_u64;
use dregg_token::Attenuation;
use dregg_turn::{Effect, TurnReceipt};

use crate::cipherclerk::HeldToken;
use crate::error::SdkError;
use crate::runtime::{AgentRuntime, SubAgent};
use crate::tool_gateway::{WhisperFrame, WhisperSource};

/// The slot on a WRITER cell that holds its monotone whisper sequence counter.
///
/// Each committed deposit advances this slot `seq → seq+1`, giving the deposit a
/// real (non-empty) state transition to commit and an on-ledger, apply-time
/// ordering for the writer's frames. It is the writer's private counter — distinct
/// from the gateway worker cell's [`crate::tool_gateway::CALLS_MADE_SLOT`], which
/// lives on the RECIPIENT cell — so the two never alias.
pub const WHISPER_SEQ_SLOT: u8 = 5;

/// **The seat-addressed capability verb** — the cap-gate's namespace.
///
/// A writer authorized to whisper to `seat` holds a biscuit credential scoped to
/// exactly this method (`whisper.<hex(seat)>`); the executor admits its deposit
/// turn IFF the presented verb is covered, and rejects a deposit to any other seat
/// with `TokenInsufficientCapability`. "Who may whisper to a seat" is therefore
/// "who holds a biscuit for that seat's whisper verb" — a genuine per-seat
/// capability, enforced in-executor, not a courtesy check.
pub fn whisper_method(seat: CellId) -> String {
    let mut verb = String::with_capacity(8 + 64);
    verb.push_str("whisper.");
    for b in seat.0 {
        verb.push_str(&format!("{b:02x}"));
    }
    verb
}

/// **THE RAM-RESIDENT WHISPER MAILBOX** — per-seat pending frames, the deposit's
/// landing zone and the drain [`WhisperSource`]'s backing store.
///
/// Cloneable and `Send` (an `Arc<Mutex<..>>` handle): a [`WhisperWriter`] deposits
/// into it, and the recipient gateway installs a [`WhisperInbox::source_for`]
/// closure that drains it. Frames are per-seat FIFO and CONSUME-ONCE (the drain
/// `pop_front`s), matching the channel's consume-once physics; the gateway drains
/// exactly one per admitted call, so the one-frame-per-boundary budget is the
/// gate's, not the inbox's. Never hits disk (the RAM-only budget).
#[derive(Clone, Default)]
pub struct WhisperInbox {
    seats: Arc<Mutex<HashMap<CellId, VecDeque<WhisperFrame>>>>,
}

impl WhisperInbox {
    /// A fresh, empty mailbox.
    pub fn new() -> WhisperInbox {
        WhisperInbox {
            seats: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// Push a committed deposit's frame onto `seat`'s queue (writer-internal).
    fn push(&self, seat: CellId, frame: WhisperFrame) {
        let mut seats = self.seats.lock().unwrap_or_else(|e| e.into_inner());
        seats.entry(seat).or_default().push_back(frame);
    }

    /// The number of pending (undrained) frames for `seat` — inspection / tests.
    pub fn pending(&self, seat: CellId) -> usize {
        let seats = self.seats.lock().unwrap_or_else(|e| e.into_inner());
        seats.get(&seat).map_or(0, |q| q.len())
    }

    /// **A drain source for `seat`** — a [`WhisperSource`] the recipient gateway
    /// installs via [`crate::tool_gateway::ToolGateway::set_whisper_source`].
    ///
    /// Each call pops the front pending frame for `seat` (consume-once, FIFO), or
    /// `None` when the queue is empty — a non-blocking RAM read, exactly the source
    /// contract the gateway's drain requires. The gateway re-enforces the frame
    /// budgets at intake, so this source is never trusted to have clipped.
    pub fn source_for(&self, seat: CellId) -> WhisperSource {
        let seats = self.seats.clone();
        Box::new(move || {
            let mut seats = seats.lock().unwrap_or_else(|e| e.into_inner());
            seats.get_mut(&seat).and_then(|q| q.pop_front())
        })
    }
}

/// Why a whisper deposit did not land.
#[derive(Debug)]
pub enum WhisperDepositError {
    /// The text clipped to nothing at intake (all-whitespace / all-control) — no
    /// frame, no turn, nothing deposited.
    EmptyFrame,
    /// The cap-gated deposit turn was REFUSED by the executor — the writer's
    /// credential does not cover the target seat's whisper verb
    /// (`TokenInsufficientCapability`), so the deposit is unauthorized. NO frame
    /// lands in the recipient's inbox.
    Refused(SdkError),
}

impl std::fmt::Display for WhisperDepositError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            WhisperDepositError::EmptyFrame => {
                write!(f, "whisper deposit: text clipped to empty, nothing deposited")
            }
            WhisperDepositError::Refused(e) => {
                write!(f, "whisper deposit refused (unauthorized seat): {e}")
            }
        }
    }
}

impl std::error::Error for WhisperDepositError {}

/// The witness of a COMMITTED whisper deposit: the deposit turn's receipt (proof
/// the cap-gated apply-time deposit committed), the attributed frame, and the seat
/// it was deposited to.
#[derive(Clone, Debug)]
pub struct WhisperDeposit {
    /// The committed deposit turn's receipt — proof the writer's cap-gated turn
    /// applied (the APPLY-TIME event the frame is bound to).
    pub receipt: TurnReceipt,
    /// The deposited frame, carrying `from = <writer cell>` (attribution).
    pub frame: WhisperFrame,
    /// The seat the frame was deposited to (the recipient gateway's worker cell).
    pub seat: CellId,
}

/// **A CAP-GATED WHISPER WRITER** — a principal authorized to whisper to a seat.
///
/// Admit one with [`WhisperWriter::admit`]: the grantor delegates a biscuit scoped
/// to exactly [`whisper_method`]`(seat)`, so this writer may deposit to `seat` and
/// only `seat`. [`WhisperWriter::whisper`] deposits a bounded frame to its
/// authorized seat via a cap-gated APPLY-TIME turn; the recipient gateway reads it
/// off the next admitted call's [`crate::tool_gateway::ToolReceipt::whisper`].
pub struct WhisperWriter {
    /// The writer's cap-gated cell — its biscuit covers the seat's whisper verb.
    writer: SubAgent,
    /// The seat this writer is authorized to whisper to (the recipient's worker cell).
    seat: CellId,
    /// The shared mailbox the committed deposit lands in.
    inbox: WhisperInbox,
    /// The writer's monotone whisper sequence (advances on each committed deposit).
    seq: u64,
}

impl WhisperWriter {
    /// Admit a writer authorized to whisper to `seat`.
    ///
    /// The grantor (`runtime`, holding `parent_token`) delegates a freshly spawned
    /// [`SubAgent`] scoped to exactly [`whisper_method`]`(seat)`. The writer's
    /// biscuit credential is the executor-enforced cap: a deposit turn under any
    /// other seat's whisper verb is rejected with `TokenInsufficientCapability`.
    pub fn admit(
        runtime: &AgentRuntime,
        parent_token: &HeldToken,
        seat: CellId,
        inbox: WhisperInbox,
    ) -> Result<WhisperWriter, SdkError> {
        let method = whisper_method(seat);
        let writer = runtime.spawn_sub_agent_scoped(
            &Attenuation::default(),
            parent_token,
            &[method.as_str()],
        )?;
        Ok(WhisperWriter {
            writer,
            seat,
            inbox,
            seq: 0,
        })
    }

    /// This writer's cell id — the `from` its deposited frames carry.
    pub fn writer_cell(&self) -> CellId {
        self.writer.cell_id()
    }

    /// The seat this writer is authorized to whisper to.
    pub fn seat(&self) -> CellId {
        self.seat
    }

    /// **Deposit a whisper to this writer's authorized seat** (the common path).
    ///
    /// Builds a bounded [`WhisperFrame`] (budgets enforced at intake — an empty
    /// clip is [`WhisperDepositError::EmptyFrame`]), then runs the cap-gated
    /// APPLY-TIME deposit turn. On commit the attributed frame lands in the
    /// recipient's [`WhisperInbox`], to be read off the recipient gateway's next
    /// admitted call.
    pub fn whisper(&mut self, text: &str) -> Result<WhisperDeposit, WhisperDepositError> {
        let seat = self.seat;
        self.deposit(seat, text)
    }

    /// Deposit to an ARBITRARY target seat using this writer's credential.
    ///
    /// The one code path both [`whisper`](Self::whisper) and the cap-gate exercise
    /// share: the executor admits the deposit IFF this writer's biscuit covers
    /// [`whisper_method`]`(target)`. A `target` this writer is NOT authorized for
    /// is refused ([`WhisperDepositError::Refused`]) — the cap-gate biting. Public
    /// for genuine multi-seat writers and for exercising the refusal.
    pub fn whisper_to(
        &mut self,
        target: CellId,
        text: &str,
    ) -> Result<WhisperDeposit, WhisperDepositError> {
        self.deposit(target, text)
    }

    /// The cap-gated APPLY-TIME deposit — one path, the cap-gate the only variable.
    fn deposit(
        &mut self,
        target: CellId,
        text: &str,
    ) -> Result<WhisperDeposit, WhisperDepositError> {
        // Build the frame FIRST (budgets enforced at intake), attributed to this
        // writer's cell. An empty clip deposits nothing (no turn spent).
        let seq = self.seq + 1;
        let frame = WhisperFrame::new(text, Some(self.writer.cell_id()), seq)
            .ok_or(WhisperDepositError::EmptyFrame)?;

        // THE CAP-GATE + APPLY-TIME EVENT: run the seat-addressed whisper turn
        // through the SAME executor gate the gateway's worker rides. The turn
        // advances the writer's own monotone whisper-seq slot (a real committing
        // transition; the writer cell's default `CellProgram::None` admits the
        // SetField). The executor admits this turn IFF the writer's biscuit covers
        // `whisper_method(target)`; an unauthorized seat yields
        // `TokenInsufficientCapability` (an Err), so NO frame lands.
        let effects = vec![Effect::SetField {
            cell: self.writer.cell_id(),
            index: WHISPER_SEQ_SLOT as usize,
            value: field_from_u64(seq),
        }];
        let receipt = self
            .writer
            .execute_method(&whisper_method(target), effects)
            .map_err(WhisperDepositError::Refused)?;

        // COMMITTED (apply-time): the attributed frame lands in the recipient's
        // inbox. The writer's tracked seq advances in lock-step with the committed
        // slot; a refused deposit returned above, so neither advances on refusal.
        self.seq = seq;
        self.inbox.push(target, frame.clone());
        Ok(WhisperDeposit {
            receipt,
            frame,
            seat: target,
        })
    }
}
