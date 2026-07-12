//! `envelope` — the **witnessed-nondeterminism envelope**: the execution-audit
//! rail that makes an agent turn *deterministically re-executable*.
//!
//! The run loop ([`AgentCloud::drive_state`](crate::agent::AgentCloud)) is a
//! deterministic orchestration with exactly three live nondeterministic seams,
//! all already behind named traits:
//!
//! 1. the **LLM completion** — [`OpenAICompatCaller::complete`];
//! 2. the **tool outcome** — [`ToolKit::invoke`] / [`ToolKit::run_op`];
//! 3. the **kernel-turn admission** — [`GrainTurnMinter::mint_turn`].
//!
//! This module captures every read from those seams as a [`WitnessedInput`] in an
//! ordered, root-hashed [`WitnessedNondeterminism`] envelope (capture mode), and
//! re-executes a turn by serving each seam from the envelope instead of the world
//! (replay mode) — validating at every entry that the deterministic re-execution
//! asked the SAME question (the [`SeamRequest`] digest). A mismatch is a detected
//! divergence and replay refuses fail-closed.
//!
//! ## The honest ceiling (read this before trusting anything here)
//!
//! **A captured input is asserted by the recorder, never re-derived by replay.**
//! An LLM output is captured-as-input, NOT re-derivable: replay proves *"given
//! these model outputs, the orchestration admitted/refused/receipted exactly
//! this"* — it can never prove the model produced them. Live tool outcomes are
//! the same (the [`WitnessedRun`](crate::agent::WitnessedRun) re-execution oracle
//! in `agent.rs` is the partial strengthening for the re-runnable subset). And
//! the recorder is the HOST: a lying host can capture a fabricated input and the
//! envelope will replay it faithfully. Replay also never recommits kernel turns —
//! a recorded `turn_hash` is an echo of the record, checked against the real
//! committed-turn manifest elsewhere (the grain-verify R2 tooth).
//!
//! The BYO api key is never captured: it is not a field of any record and not an
//! input to any digest (it transits only the transport auth header, exactly as
//! before).
//!
//! Design + built/not-built ledger: `docs/DESIGN-witnessed-nondeterminism-envelope.md`.
//! Wiring these wrappers into the product run paths (`Session` / `live.rs`) is
//! design, not built; this module is the envelope mechanics and the three seam
//! welds, each implemented against the real trait it wraps.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use serde::{Deserialize, Serialize};
use serde_json::Value;

use crate::agent::{GrainTurnMinter, ToolCall, ToolKit, ToolOutcome};
use crate::brain::OpenAICompatCaller;
use crate::receipt::BodyHasher;

// ── domain separators ────────────────────────────────────────────────────────

const ENTRY_DOMAIN: &[u8] = b"dregg-agent-envelope-entry-v1";
const ROOT_DOMAIN: &[u8] = b"dregg-agent-envelope-root-v1";
const LLM_REQ_DOMAIN: &[u8] = b"dregg-agent-envelope-llm-request-v1";
const TOOL_INVOKE_DOMAIN: &[u8] = b"dregg-agent-envelope-tool-invoke-v1";
const TOOL_OP_DOMAIN: &[u8] = b"dregg-agent-envelope-tool-op-v1";
const TURN_MINT_DOMAIN: &[u8] = b"dregg-agent-envelope-turn-mint-v1";
const CLOCK_DOMAIN: &[u8] = b"dregg-agent-envelope-clock-v1";
const RNG_DOMAIN: &[u8] = b"dregg-agent-envelope-rng-v1";
const CELLS_DOMAIN: &[u8] = b"dregg-agent-envelope-cells-v1";

/// A deterministic digest of the agent's committed cell heap at a seam (the
/// context a tool ran under). `BTreeMap` iterates sorted, so the fold is
/// order-canonical by construction.
fn cells_digest(cells: &BTreeMap<String, String>) -> [u8; 32] {
    let mut h = BodyHasher::new(CELLS_DOMAIN);
    for (k, v) in cells {
        h.field(k.as_bytes()).field(v.as_bytes());
    }
    h.finalize()
}

// ── the vocabulary: which seam, what question, what answer ──────────────────

/// Which nondeterministic seam an envelope entry belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SeamKind {
    /// One [`OpenAICompatCaller::complete`] call (the model's answer).
    LlmCompletion,
    /// One [`ToolKit::invoke`] call (a flat / priced service verdict).
    ToolInvoke,
    /// One [`ToolKit::run_op`] call (a rich operator-tool verdict).
    ToolOp,
    /// One [`GrainTurnMinter::mint_turn`] call (the executor's admission).
    TurnMint,
    /// A host-side wall-clock read ([`witness_clock`]). RESERVED vocabulary —
    /// `drive_state` itself reads no clock today (block heights ride the handle).
    Clock,
    /// A host-side randomness read ([`witness_rng`]). RESERVED vocabulary — the
    /// receipt-chain secret is provisioned before the turn, not read mid-turn.
    Rng,
}

/// **The replay-validation identity of one seam read** — the deterministic
/// question the orchestration asked, digested. Recomputed identically by a
/// faithful re-execution; a mismatch against the recorded digest is a DETECTED
/// divergence (changed code, wrong envelope, or a spliced record) and replay
/// refuses fail-closed. The digest inputs never include the api key.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SeamRequest {
    /// The seam this read belongs to.
    pub kind: SeamKind,
    /// The domain-separated blake3 digest of the deterministic request side.
    pub request_digest: [u8; 32],
}

impl SeamRequest {
    /// The LLM-completion seam identity: `blake3(domain ‖ endpoint ‖ request-JSON)`.
    /// The api key is NOT an input (it rides the transport auth header only).
    /// `request.to_string()` is deterministic for one build of the constructing
    /// code (the brain builds the JSON the same way on capture and replay).
    pub fn llm(endpoint: &str, request: &Value) -> SeamRequest {
        let mut h = BodyHasher::new(LLM_REQ_DOMAIN);
        h.field(endpoint.as_bytes())
            .field(request.to_string().as_bytes());
        SeamRequest {
            kind: SeamKind::LlmCompletion,
            request_digest: h.finalize(),
        }
    }

    /// The tool-invoke seam identity over `(service, amount_cents, cells)`.
    pub fn tool_invoke(
        service: &str,
        amount_cents: Option<i64>,
        cells: &BTreeMap<String, String>,
    ) -> SeamRequest {
        let mut h = BodyHasher::new(TOOL_INVOKE_DOMAIN);
        h.field(service.as_bytes());
        match amount_cents {
            Some(a) => {
                h.u64(1).u64(a as u64);
            }
            None => {
                h.u64(0);
            }
        }
        h.field(&cells_digest(cells));
        SeamRequest {
            kind: SeamKind::ToolInvoke,
            request_digest: h.finalize(),
        }
    }

    /// The operator-op seam identity over `(call, cells)`.
    pub fn tool_op(call: &ToolCall, cells: &BTreeMap<String, String>) -> SeamRequest {
        let call_json = serde_json::to_string(call).expect("a ToolCall serializes (strings only)");
        let mut h = BodyHasher::new(TOOL_OP_DOMAIN);
        h.field(call_json.as_bytes()).field(&cells_digest(cells));
        SeamRequest {
            kind: SeamKind::ToolOp,
            request_digest: h.finalize(),
        }
    }

    /// The kernel-turn seam identity — exactly [`GrainTurnMinter::mint_turn`]'s
    /// arguments `(label, cost, consumed_after, cell_root)`.
    pub fn turn_mint(
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> SeamRequest {
        let mut h = BodyHasher::new(TURN_MINT_DOMAIN);
        h.field(label.as_bytes())
            .u64(cost as u64)
            .u64(consumed_after as u64)
            .field(&cell_root);
        SeamRequest {
            kind: SeamKind::TurnMint,
            request_digest: h.finalize(),
        }
    }

    /// The clock seam identity. Domain-constant: a clock read carries no request
    /// data, so its identity is its POSITION in the envelope (order is identity).
    pub fn clock() -> SeamRequest {
        SeamRequest {
            kind: SeamKind::Clock,
            request_digest: BodyHasher::new(CLOCK_DOMAIN).finalize(),
        }
    }

    /// The rng seam identity over the requested byte count.
    pub fn rng(len: usize) -> SeamRequest {
        let mut h = BodyHasher::new(RNG_DOMAIN);
        h.u64(len as u64);
        SeamRequest {
            kind: SeamKind::Rng,
            request_digest: h.finalize(),
        }
    }
}

/// **One witnessed nondeterministic input** — the answer the world gave at a
/// seam, captured verbatim so a re-execution can consume it instead of the world.
/// Every variant is an ASSERTION BY THE RECORDER (see the module honest-ceiling
/// note): replay serves it, it never re-derives it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WitnessedInput {
    /// The provider's raw response JSON text (or the transport's error string) for
    /// one [`OpenAICompatCaller::complete`] call. Stored as the exact text so
    /// hashing needs no JSON canonicalization; replay re-parses it. The api key is
    /// NEVER part of this record.
    LlmCompletion {
        /// `Ok(response-JSON-text)` or `Err(transport error)` — both are outcomes
        /// a faithful replay must reproduce.
        response: Result<String, String>,
    },
    /// The [`ToolOutcome`] one [`ToolKit::invoke`] returned (verdict, summary, and
    /// any [`WitnessedRun`](crate::agent::WitnessedRun) execution binding).
    ToolInvoke {
        /// The captured verdict, replayed verbatim.
        outcome: ToolOutcome,
    },
    /// The [`ToolOutcome`] one [`ToolKit::run_op`] returned.
    ToolOp {
        /// The captured verdict, replayed verbatim.
        outcome: ToolOutcome,
    },
    /// The executor's answer to one [`GrainTurnMinter::mint_turn`]: the committed
    /// `turn_hash`, or the refusal reason. On replay this is an ECHO — replay does
    /// NOT recommit kernel turns; checking the hash names a real committed turn is
    /// the R2 manifest check, outside this rail.
    TurnMint {
        /// `Ok(turn_hash)` or `Err(refusal reason)`, exactly as the executor answered.
        result: Result<[u8; 32], String>,
    },
    /// A host-side wall-clock read (reserved; see [`SeamKind::Clock`]).
    Clock {
        /// The witnessed reading, unix milliseconds.
        unix_millis: i64,
    },
    /// A host-side randomness read (reserved; see [`SeamKind::Rng`]).
    Rng {
        /// The witnessed bytes.
        bytes: Vec<u8>,
    },
}

impl WitnessedInput {
    /// The seam this input answers.
    pub fn kind(&self) -> SeamKind {
        match self {
            WitnessedInput::LlmCompletion { .. } => SeamKind::LlmCompletion,
            WitnessedInput::ToolInvoke { .. } => SeamKind::ToolInvoke,
            WitnessedInput::ToolOp { .. } => SeamKind::ToolOp,
            WitnessedInput::TurnMint { .. } => SeamKind::TurnMint,
            WitnessedInput::Clock { .. } => SeamKind::Clock,
            WitnessedInput::Rng { .. } => SeamKind::Rng,
        }
    }
}

/// One envelope line: the deterministic question ([`SeamRequest`]) and the
/// witnessed answer ([`WitnessedInput`]), at its position `seq`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessedEntry {
    /// The 0-based position in the envelope (consumed strictly in order).
    pub seq: u64,
    /// The replay-validation identity of the read.
    pub request: SeamRequest,
    /// The captured answer.
    pub input: WitnessedInput,
}

impl WitnessedEntry {
    /// The entry's domain-separated blake3 hash. SCAFFOLD CAVEAT (named in the
    /// design doc): the preimage is the entry's `serde_json` form — deterministic
    /// for one build of this code (declaration-ordered structs), but the hardening
    /// step before this root is ever bound into a signed record is a canonical
    /// binary encoding (postcard).
    pub fn entry_hash(&self) -> [u8; 32] {
        let json = serde_json::to_string(self).expect("witnessed entries serialize");
        let mut h = BodyHasher::new(ENTRY_DOMAIN);
        h.field(json.as_bytes());
        h.finalize()
    }
}

/// **The witnessed-nondeterminism envelope of one turn** — the ordered record of
/// every nondeterministic input the turn consumed. Given the turn's initial state
/// and this envelope, the orchestration re-executes deterministically for audit.
///
/// The envelope makes the turn RE-EXECUTABLE; it does not make the captured
/// inputs TRUE (see the module honest-ceiling note).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WitnessedNondeterminism {
    /// The entries, in consumption order. Order is identity: replay serves them
    /// with a strict cursor, never by lookup.
    pub entries: Vec<WitnessedEntry>,
}

impl WitnessedNondeterminism {
    /// Append one witnessed read; returns its assigned `seq`.
    pub fn record(&mut self, request: SeamRequest, input: WitnessedInput) -> u64 {
        let seq = self.entries.len() as u64;
        self.entries.push(WitnessedEntry {
            seq,
            request,
            input,
        });
        seq
    }

    /// The number of witnessed reads.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// `true` iff nothing was witnessed.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The envelope root: the prev-linked fold `root' = blake3(domain ‖ root ‖
    /// entry_hash)` over the entries in order. Order-sensitive — a reordered,
    /// spliced, or tampered envelope moves the root. The zero envelope's root is
    /// all-zero. Binding this root into the signed receipt record is a NAMED
    /// design step, not yet built (design doc §8.2).
    pub fn root(&self) -> [u8; 32] {
        let mut acc = [0u8; 32];
        for e in &self.entries {
            let mut h = BodyHasher::new(ROOT_DOMAIN);
            h.field(&acc).field(&e.entry_hash());
            acc = h.finalize();
        }
        acc
    }
}

// ── replay errors ────────────────────────────────────────────────────────────

/// Why a capture or replay step refused. Every variant is fail-closed: no seam
/// read is ever silently invented or silently mismatched.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplayError {
    /// `record` was called on a replayer (a replayed turn must not extend the record).
    NotCapturing,
    /// `resupply` was called on a recorder (a captured turn must run its real effects).
    NotReplaying,
    /// The re-execution asked for more nondeterminism than the envelope holds —
    /// the code path diverged (it took extra steps) or the envelope is truncated.
    Exhausted {
        /// The entry index the re-execution asked for.
        at: u64,
    },
    /// The re-execution asked a different KIND of seam than the record holds at
    /// this position — a control-flow divergence.
    SeamMismatch {
        /// The entry index.
        at: u64,
        /// What the re-execution asked.
        expected: SeamKind,
        /// What the envelope recorded.
        recorded: SeamKind,
    },
    /// The re-execution asked the same kind of question with DIFFERENT content —
    /// the deterministic request digest diverged (changed code, wrong envelope,
    /// or a spliced record).
    RequestDivergence {
        /// The entry index.
        at: u64,
        /// The digest the re-execution derived.
        expected: [u8; 32],
        /// The digest the envelope recorded.
        recorded: [u8; 32],
    },
    /// The envelope served an input whose shape does not match its seam (a
    /// corrupt record; unreachable when entries were built by [`Recorder`]).
    WrongShape {
        /// The seam the consumer needed.
        expected: SeamKind,
    },
}

impl std::fmt::Display for ReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReplayError::NotCapturing => {
                write!(
                    f,
                    "replay hook is replaying; it refuses to extend the record"
                )
            }
            ReplayError::NotReplaying => {
                write!(
                    f,
                    "replay hook is capturing; it refuses to serve recorded inputs"
                )
            }
            ReplayError::Exhausted { at } => write!(
                f,
                "replay diverged at entry {at}: the envelope is exhausted (the re-execution took \
                 more nondeterministic steps than were witnessed)"
            ),
            ReplayError::SeamMismatch {
                at,
                expected,
                recorded,
            } => write!(
                f,
                "replay diverged at entry {at}: the re-execution asked a {expected:?} read but \
                 the envelope recorded a {recorded:?} read"
            ),
            ReplayError::RequestDivergence {
                at,
                expected,
                recorded,
            } => write!(
                f,
                "replay diverged at entry {at}: request digest {} does not match the recorded {} \
                 (changed code, wrong envelope, or a spliced record)",
                hex::encode(expected),
                hex::encode(recorded)
            ),
            ReplayError::WrongShape { expected } => write!(
                f,
                "corrupt envelope: the served input does not have the {expected:?} shape"
            ),
        }
    }
}

impl std::error::Error for ReplayError {}

// ── the replay hook: one trait, two modes ────────────────────────────────────

/// Which side of the audit a hook is on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TapMode {
    /// Perform the real effects; witness every result into the envelope.
    Capture,
    /// Perform NO effects; serve every seam read from the envelope, validated.
    Replay,
}

/// **The replay hook** — the one seam-side object the enveloped wrappers thread
/// every nondeterministic read through. [`Recorder`] implements the capture side,
/// [`Replayer`] the replay side; both are fail-closed on the mode they are not.
pub trait ReplayHook {
    /// The mode this hook runs the turn under.
    fn mode(&self) -> TapMode;

    /// CAPTURE: append one witnessed read (the real effect already ran; `input`
    /// is its result). A refusal here must fail the wrapped call — an unwitnessed
    /// input never steers the run.
    fn record(&mut self, request: &SeamRequest, input: &WitnessedInput) -> Result<(), ReplayError>;

    /// REPLAY: serve the next recorded input, validating that `request` matches
    /// the recorded seam kind and request digest at the cursor. A mismatch is a
    /// detected divergence and must poison the replay.
    fn resupply(&mut self, request: &SeamRequest) -> Result<WitnessedInput, ReplayError>;

    /// A snapshot of the envelope this hook holds (recorded-so-far for a
    /// [`Recorder`]; the full record for a [`Replayer`]).
    fn snapshot(&self) -> WitnessedNondeterminism;
}

/// The one shared-hook handle the wrappers hold. `Rc<RefCell<…>>` because the
/// run loop is synchronous and the caller/toolkit/minter of ONE turn must
/// interleave into ONE ordered envelope.
pub type SharedHook = Rc<RefCell<dyn ReplayHook>>;

/// The capture-side [`ReplayHook`]: appends every witnessed read, in order.
#[derive(Debug, Default)]
pub struct Recorder {
    envelope: WitnessedNondeterminism,
}

impl Recorder {
    /// A fresh, empty recorder.
    pub fn new() -> Recorder {
        Recorder::default()
    }

    /// The envelope recorded so far.
    pub fn envelope(&self) -> &WitnessedNondeterminism {
        &self.envelope
    }

    /// Consume the recorder into its envelope.
    pub fn into_envelope(self) -> WitnessedNondeterminism {
        self.envelope
    }
}

impl ReplayHook for Recorder {
    fn mode(&self) -> TapMode {
        TapMode::Capture
    }

    fn record(&mut self, request: &SeamRequest, input: &WitnessedInput) -> Result<(), ReplayError> {
        self.envelope.record(*request, input.clone());
        Ok(())
    }

    fn resupply(&mut self, _request: &SeamRequest) -> Result<WitnessedInput, ReplayError> {
        Err(ReplayError::NotReplaying)
    }

    fn snapshot(&self) -> WitnessedNondeterminism {
        self.envelope.clone()
    }
}

/// The replay-side [`ReplayHook`]: a strict cursor over a recorded envelope.
/// Validates every read's seam kind + request digest; the FIRST divergence
/// poisons the replayer (every later read refuses with the same error), so a
/// diverged replay cannot limp onward consuming misaligned entries.
#[derive(Debug)]
pub struct Replayer {
    envelope: WitnessedNondeterminism,
    cursor: usize,
    poisoned: Option<ReplayError>,
}

impl Replayer {
    /// A replayer over `envelope`, cursor at the start.
    pub fn new(envelope: WitnessedNondeterminism) -> Replayer {
        Replayer {
            envelope,
            cursor: 0,
            poisoned: None,
        }
    }

    /// How many entries have been served.
    pub fn replayed(&self) -> usize {
        self.cursor
    }

    /// `true` iff every recorded entry was consumed (a faithful replay must end
    /// here — leftover entries mean the re-execution took FEWER steps: also a
    /// divergence, checked by the auditor after the run).
    pub fn fully_consumed(&self) -> bool {
        self.cursor == self.envelope.entries.len()
    }

    /// The divergence that poisoned this replay, if any.
    pub fn divergence(&self) -> Option<&ReplayError> {
        self.poisoned.as_ref()
    }
}

impl ReplayHook for Replayer {
    fn mode(&self) -> TapMode {
        TapMode::Replay
    }

    fn record(
        &mut self,
        _request: &SeamRequest,
        _input: &WitnessedInput,
    ) -> Result<(), ReplayError> {
        Err(ReplayError::NotCapturing)
    }

    fn resupply(&mut self, request: &SeamRequest) -> Result<WitnessedInput, ReplayError> {
        if let Some(e) = &self.poisoned {
            return Err(e.clone());
        }
        let at = self.cursor as u64;
        let Some(entry) = self.envelope.entries.get(self.cursor) else {
            let err = ReplayError::Exhausted { at };
            self.poisoned = Some(err.clone());
            return Err(err);
        };
        if entry.request.kind != request.kind {
            let err = ReplayError::SeamMismatch {
                at,
                expected: request.kind,
                recorded: entry.request.kind,
            };
            self.poisoned = Some(err.clone());
            return Err(err);
        }
        if entry.request.request_digest != request.request_digest {
            let err = ReplayError::RequestDivergence {
                at,
                expected: request.request_digest,
                recorded: entry.request.request_digest,
            };
            self.poisoned = Some(err.clone());
            return Err(err);
        }
        let input = entry.input.clone();
        self.cursor += 1;
        Ok(input)
    }

    fn snapshot(&self) -> WitnessedNondeterminism {
        self.envelope.clone()
    }
}

// ── seam weld #1: the LLM transport ──────────────────────────────────────────

/// [`OpenAICompatCaller`] enveloped: capture mode performs the inner call and
/// witnesses its raw response (or transport error); replay mode NEVER touches
/// the inner caller (or any key) and serves the envelope, digest-validated.
///
/// Slots in as [`OpenAICompatBrain`](crate::brain::OpenAICompatBrain)'s `C` with
/// zero brain changes (the brain has exactly one `complete` call site). The api
/// key transits ONLY the inner call's auth-header argument — it is never recorded
/// and never a digest input.
pub struct EnvelopedCaller<C> {
    inner: C,
    hook: SharedHook,
}

impl<C> EnvelopedCaller<C> {
    /// Wrap `inner` with `hook` (a [`Recorder`] to capture, a [`Replayer`] to replay).
    pub fn new(inner: C, hook: SharedHook) -> EnvelopedCaller<C> {
        EnvelopedCaller { inner, hook }
    }

    /// The shared hook (e.g. to snapshot the envelope after a captured run).
    pub fn hook(&self) -> &SharedHook {
        &self.hook
    }

    /// The wrapped caller.
    pub fn inner(&self) -> &C {
        &self.inner
    }
}

impl<C: OpenAICompatCaller> OpenAICompatCaller for EnvelopedCaller<C> {
    fn complete(
        &mut self,
        endpoint: &str,
        api_key: &str,
        request: &Value,
    ) -> Result<Value, String> {
        let req = SeamRequest::llm(endpoint, request);
        let mode = self.hook.borrow().mode();
        match mode {
            TapMode::Replay => {
                // Serve from the envelope; the inner caller (and the key) are
                // never touched on replay.
                let input = self
                    .hook
                    .borrow_mut()
                    .resupply(&req)
                    .map_err(|e| e.to_string())?;
                match input {
                    WitnessedInput::LlmCompletion { response } => match response {
                        Ok(json) => serde_json::from_str::<Value>(&json).map_err(|e| {
                            format!("envelope-recorded LLM response failed to re-parse: {e}")
                        }),
                        Err(e) => Err(e),
                    },
                    other => Err(ReplayError::WrongShape {
                        expected: SeamKind::LlmCompletion,
                    }
                    .to_string()
                        + &format!(" (served {:?})", other.kind())),
                }
            }
            TapMode::Capture => {
                let live = self.inner.complete(endpoint, api_key, request);
                // Witness the raw outcome — the response TEXT (or the error), never
                // the key. A capture refusal fails the call (fail-closed): an
                // unwitnessed model output must not steer the run.
                let witnessed = WitnessedInput::LlmCompletion {
                    response: live.as_ref().map(|v| v.to_string()).map_err(|e| e.clone()),
                };
                self.hook
                    .borrow_mut()
                    .record(&req, &witnessed)
                    .map_err(|e| e.to_string())?;
                live
            }
        }
    }
}

/// A fail-closed stand-in caller for pure replay: if a replayed turn ever falls
/// through to a live model call, that is a bug — this errors instead. No key, no
/// network, ever.
pub struct NoCaller;

impl OpenAICompatCaller for NoCaller {
    fn complete(
        &mut self,
        _endpoint: &str,
        _api_key: &str,
        _request: &Value,
    ) -> Result<Value, String> {
        Err("NoCaller: a replayed turn must be served from the envelope, never live".to_string())
    }
}

// ── seam weld #2: the toolkit ────────────────────────────────────────────────

/// [`ToolKit`] enveloped: capture mode runs the inner tool and witnesses its
/// [`ToolOutcome`]; replay mode serves the envelope and NEVER runs the tool.
///
/// `op_cap` forwards to the inner toolkit in BOTH modes — it is a pure function
/// of workdir config (the cap-gate consumes it before any effect), so the
/// preferred replay shape is to wrap the SAME real toolkit type: its effects are
/// never invoked on replay, and cap resolution stays faithful. [`NoToolKit`]
/// stands in when the toolkit cannot be reconstructed (its default `op_cap` may
/// then diverge from a workdir-resolving toolkit's — a divergence the request
/// digests surface rather than hide).
///
/// The [`ToolKit`] trait has no error channel, so an envelope refusal here
/// surfaces as a FAIL-CLOSED failing outcome (summary prefixed
/// `ENVELOPE DIVERGENCE` / `ENVELOPE CAPTURE REFUSED`) — and, on replay, the
/// [`Replayer`] is poisoned, so the divergence is also visible structurally via
/// [`Replayer::divergence`], not only in the outcome text.
pub struct EnvelopedToolKit<T> {
    inner: T,
    hook: SharedHook,
}

impl<T> EnvelopedToolKit<T> {
    /// Wrap `inner` with `hook`.
    pub fn new(inner: T, hook: SharedHook) -> EnvelopedToolKit<T> {
        EnvelopedToolKit { inner, hook }
    }

    /// The shared hook.
    pub fn hook(&self) -> &SharedHook {
        &self.hook
    }
}

impl<T: ToolKit> ToolKit for EnvelopedToolKit<T> {
    fn invoke(
        &self,
        service: &str,
        amount_cents: Option<i64>,
        cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        let req = SeamRequest::tool_invoke(service, amount_cents, cells);
        let mode = self.hook.borrow().mode();
        match mode {
            TapMode::Replay => match self.hook.borrow_mut().resupply(&req) {
                Ok(WitnessedInput::ToolInvoke { outcome }) => outcome,
                Ok(other) => ToolOutcome::fail(format!(
                    "ENVELOPE DIVERGENCE (fail-closed): expected a ToolInvoke input, envelope \
                     served {:?}",
                    other.kind()
                )),
                Err(e) => ToolOutcome::fail(format!("ENVELOPE DIVERGENCE (fail-closed): {e}")),
            },
            TapMode::Capture => {
                let outcome = self.inner.invoke(service, amount_cents, cells);
                if let Err(e) = self.hook.borrow_mut().record(
                    &req,
                    &WitnessedInput::ToolInvoke {
                        outcome: outcome.clone(),
                    },
                ) {
                    return ToolOutcome::fail(format!(
                        "ENVELOPE CAPTURE REFUSED (fail-closed): {e}"
                    ));
                }
                outcome
            }
        }
    }

    fn op_cap(&self, call: &ToolCall) -> String {
        // Pure config resolution — runs live in BOTH modes (see the type doc).
        self.inner.op_cap(call)
    }

    fn run_op(&self, call: &ToolCall, cells: &BTreeMap<String, String>) -> ToolOutcome {
        let req = SeamRequest::tool_op(call, cells);
        let mode = self.hook.borrow().mode();
        match mode {
            TapMode::Replay => match self.hook.borrow_mut().resupply(&req) {
                Ok(WitnessedInput::ToolOp { outcome }) => outcome,
                Ok(other) => ToolOutcome::fail(format!(
                    "ENVELOPE DIVERGENCE (fail-closed): expected a ToolOp input, envelope \
                     served {:?}",
                    other.kind()
                )),
                Err(e) => ToolOutcome::fail(format!("ENVELOPE DIVERGENCE (fail-closed): {e}")),
            },
            TapMode::Capture => {
                let outcome = self.inner.run_op(call, cells);
                if let Err(e) = self.hook.borrow_mut().record(
                    &req,
                    &WitnessedInput::ToolOp {
                        outcome: outcome.clone(),
                    },
                ) {
                    return ToolOutcome::fail(format!(
                        "ENVELOPE CAPTURE REFUSED (fail-closed): {e}"
                    ));
                }
                outcome
            }
        }
    }
}

/// A fail-closed stand-in toolkit for pure replay: every effect path fails with a
/// clear message (a replayed turn served from the envelope never reaches it).
/// Its `op_cap` is the default [`ToolCall::default_cap`] — see the
/// [`EnvelopedToolKit`] doc for why wrapping the real toolkit is preferred.
pub struct NoToolKit;

impl ToolKit for NoToolKit {
    fn invoke(
        &self,
        service: &str,
        _amount_cents: Option<i64>,
        _cells: &BTreeMap<String, String>,
    ) -> ToolOutcome {
        ToolOutcome::fail(format!(
            "NoToolKit: a replayed turn must be served from the envelope, never live \
             (service `{service}`)"
        ))
    }
}

// ── seam weld #3: the kernel-turn minter ─────────────────────────────────────

/// [`GrainTurnMinter`] enveloped: capture mode commits the real kernel turn and
/// witnesses the executor's answer; replay mode serves the recorded answer and
/// commits NOTHING — a replayed turn is a simulation for audit, and the recorded
/// `turn_hash` is an ECHO (checking it names a real committed turn is the R2
/// manifest check, outside this rail).
pub struct EnvelopedMinter<M> {
    inner: M,
    hook: SharedHook,
}

impl<M> EnvelopedMinter<M> {
    /// Wrap `inner` with `hook`.
    pub fn new(inner: M, hook: SharedHook) -> EnvelopedMinter<M> {
        EnvelopedMinter { inner, hook }
    }

    /// The shared hook.
    pub fn hook(&self) -> &SharedHook {
        &self.hook
    }

    /// The wrapped minter (e.g. to reach `committed_turns` after a captured run).
    pub fn inner(&self) -> &M {
        &self.inner
    }
}

impl<M: GrainTurnMinter> GrainTurnMinter for EnvelopedMinter<M> {
    fn mint_turn(
        &mut self,
        label: &str,
        cost: i64,
        consumed_after: i64,
        cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        let req = SeamRequest::turn_mint(label, cost, consumed_after, cell_root);
        let mode = self.hook.borrow().mode();
        match mode {
            TapMode::Replay => {
                let input = self
                    .hook
                    .borrow_mut()
                    .resupply(&req)
                    .map_err(|e| e.to_string())?;
                match input {
                    WitnessedInput::TurnMint { result } => result,
                    other => Err(format!(
                        "{} (served {:?})",
                        ReplayError::WrongShape {
                            expected: SeamKind::TurnMint,
                        },
                        other.kind()
                    )),
                }
            }
            TapMode::Capture => {
                let live = self.inner.mint_turn(label, cost, consumed_after, cell_root);
                self.hook
                    .borrow_mut()
                    .record(
                        &req,
                        &WitnessedInput::TurnMint {
                            result: live.clone(),
                        },
                    )
                    .map_err(|e| e.to_string())?;
                live
            }
        }
    }
}

/// A fail-closed stand-in minter for pure replay.
pub struct NoMinter;

impl GrainTurnMinter for NoMinter {
    fn mint_turn(
        &mut self,
        _label: &str,
        _cost: i64,
        _consumed_after: i64,
        _cell_root: [u8; 32],
    ) -> Result<[u8; 32], String> {
        Err("NoMinter: a replayed turn must be served from the envelope, never live".to_string())
    }
}

// ── the reserved seams: clock + rng witnesses ────────────────────────────────

/// Witness one wall-clock read through `hook`: capture calls `live` and records
/// its reading; replay serves the recorded reading and never calls `live`.
/// RESERVED for hosts that read a clock mid-turn — `drive_state` itself does not.
pub fn witness_clock(hook: &SharedHook, live: impl FnOnce() -> i64) -> Result<i64, ReplayError> {
    let req = SeamRequest::clock();
    let mode = hook.borrow().mode();
    match mode {
        TapMode::Replay => match hook.borrow_mut().resupply(&req)? {
            WitnessedInput::Clock { unix_millis } => Ok(unix_millis),
            _ => Err(ReplayError::WrongShape {
                expected: SeamKind::Clock,
            }),
        },
        TapMode::Capture => {
            let now = live();
            hook.borrow_mut()
                .record(&req, &WitnessedInput::Clock { unix_millis: now })?;
            Ok(now)
        }
    }
}

/// Witness one randomness read of `len` bytes through `hook`: capture calls
/// `live` and records the bytes; replay serves the recorded bytes and never calls
/// `live`. RESERVED — the receipt-chain secret is provisioned before the turn,
/// so `drive_state` itself performs no mid-turn rng read.
pub fn witness_rng(
    hook: &SharedHook,
    len: usize,
    live: impl FnOnce() -> Vec<u8>,
) -> Result<Vec<u8>, ReplayError> {
    let req = SeamRequest::rng(len);
    let mode = hook.borrow().mode();
    match mode {
        TapMode::Replay => match hook.borrow_mut().resupply(&req)? {
            WitnessedInput::Rng { bytes } => Ok(bytes),
            _ => Err(ReplayError::WrongShape {
                expected: SeamKind::Rng,
            }),
        },
        TapMode::Capture => {
            let bytes = live();
            hook.borrow_mut().record(
                &req,
                &WitnessedInput::Rng {
                    bytes: bytes.clone(),
                },
            )?;
            Ok(bytes)
        }
    }
}

// ── tests ────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::brain::RecordedOpenAICaller;
    use serde_json::json;

    #[test]
    fn llm_capture_then_replay_is_deterministic_validated_and_keyless() {
        // CAPTURE: a live-standing recorded model behind the enveloped caller.
        let live = RecordedOpenAICaller::new(vec![
            json!({"choices":[{"message":{"content":"alpha"}}]}),
            json!({"choices":[{"message":{"content":"beta"}}]}),
        ]);
        let recorder = Rc::new(RefCell::new(Recorder::new()));
        let hook: SharedHook = recorder.clone();
        let mut captured = EnvelopedCaller::new(live, hook);
        let r1 = json!({"model":"m","messages":[{"role":"user","content":"one"}]});
        let r2 = json!({"model":"m","messages":[{"role":"user","content":"two"}]});
        let endpoint = "https://api.example/v1/chat/completions";
        let a1 = captured.complete(endpoint, "sk-super-secret", &r1).unwrap();
        let a2 = captured.complete(endpoint, "sk-super-secret", &r2).unwrap();
        let envelope = recorder.borrow().snapshot();
        assert_eq!(envelope.len(), 2);

        // The api key is NEVER captured: not in any record, not in any digest input.
        let envelope_json = serde_json::to_string(&envelope).unwrap();
        assert!(
            !envelope_json.contains("sk-super-secret"),
            "the api key must never enter the envelope"
        );

        // REPLAY: the inner caller is a fail-closed NoCaller — every response must
        // come from the envelope, digest-validated, no key needed.
        let replayer = Rc::new(RefCell::new(Replayer::new(envelope.clone())));
        let rhook: SharedHook = replayer.clone();
        let mut replayed = EnvelopedCaller::new(NoCaller, rhook);
        let b1 = replayed.complete(endpoint, "", &r1).unwrap();
        let b2 = replayed.complete(endpoint, "", &r2).unwrap();
        assert_eq!(a1, b1);
        assert_eq!(a2, b2);
        assert!(replayer.borrow().fully_consumed());
        assert!(replayer.borrow().divergence().is_none());

        // A divergent request (the re-execution asked something else) is REFUSED
        // fail-closed and poisons the replayer.
        let replayer2 = Rc::new(RefCell::new(Replayer::new(envelope)));
        let rhook2: SharedHook = replayer2.clone();
        let mut replayed2 = EnvelopedCaller::new(NoCaller, rhook2);
        let divergent = json!({"model":"m","messages":[{"role":"user","content":"OTHER"}]});
        let err = replayed2.complete(endpoint, "", &divergent).unwrap_err();
        assert!(err.contains("diverged"), "{err}");
        assert!(replayer2.borrow().divergence().is_some());
    }

    #[test]
    fn envelope_root_detects_tampering_and_reordering() {
        let mut env = WitnessedNondeterminism::default();
        env.record(
            SeamRequest::clock(),
            WitnessedInput::Clock { unix_millis: 1111 },
        );
        env.record(
            SeamRequest::clock(),
            WitnessedInput::Clock { unix_millis: 2222 },
        );
        let root = env.root();

        let mut tampered = env.clone();
        tampered.entries[1].input = WitnessedInput::Clock { unix_millis: 9999 };
        assert_ne!(root, tampered.root(), "a tampered entry must move the root");

        let mut reordered = env.clone();
        reordered.entries.swap(0, 1);
        assert_ne!(
            root,
            reordered.root(),
            "a reordered envelope must move the root"
        );
    }

    #[test]
    fn toolkit_capture_then_replay_serves_outcomes_without_running_tools() {
        struct EchoKit;
        impl ToolKit for EchoKit {
            fn invoke(
                &self,
                service: &str,
                amount_cents: Option<i64>,
                _cells: &BTreeMap<String, String>,
            ) -> ToolOutcome {
                ToolOutcome::pass(format!("ran {service} amount={amount_cents:?}"))
            }
        }

        let recorder = Rc::new(RefCell::new(Recorder::new()));
        let hook: SharedHook = recorder.clone();
        let kit = EnvelopedToolKit::new(EchoKit, hook);
        let cells = BTreeMap::new();
        let captured = kit.invoke("run_tests", None, &cells);
        assert!(captured.ok);
        let envelope = recorder.borrow().snapshot();

        // REPLAY behind a fail-closed NoToolKit: a PASSING replayed outcome proves
        // the envelope answered (NoToolKit can only fail).
        let replayer = Rc::new(RefCell::new(Replayer::new(envelope)));
        let rhook: SharedHook = replayer.clone();
        let rkit = EnvelopedToolKit::new(NoToolKit, rhook);
        let replayed = rkit.invoke("run_tests", None, &cells);
        assert_eq!(captured, replayed);
        assert!(replayed.ok);
        assert!(replayer.borrow().fully_consumed());

        // A step past the record is refused fail-closed (and poisons the replayer).
        let extra = rkit.invoke("verify_deploy", None, &cells);
        assert!(!extra.ok);
        assert!(
            extra.summary.contains("ENVELOPE DIVERGENCE"),
            "{}",
            extra.summary
        );
        assert!(replayer.borrow().divergence().is_some());
    }

    #[test]
    fn minter_capture_then_replay_echoes_turn_results_without_committing() {
        struct FixedMinter;
        impl GrainTurnMinter for FixedMinter {
            fn mint_turn(
                &mut self,
                _label: &str,
                _cost: i64,
                _consumed_after: i64,
                _cell_root: [u8; 32],
            ) -> Result<[u8; 32], String> {
                Ok([7u8; 32])
            }
        }

        let recorder = Rc::new(RefCell::new(Recorder::new()));
        let hook: SharedHook = recorder.clone();
        let mut minted = EnvelopedMinter::new(FixedMinter, hook);
        let h = minted
            .mint_turn("invoke:run_tests", 1, 1, [0u8; 32])
            .unwrap();
        assert_eq!(h, [7u8; 32]);
        let envelope = recorder.borrow().snapshot();

        // REPLAY behind a fail-closed NoMinter: the recorded answer is an ECHO —
        // nothing is recommitted, and an Ok here proves the envelope served it.
        let replayer = Rc::new(RefCell::new(Replayer::new(envelope)));
        let rhook: SharedHook = replayer.clone();
        let mut replay = EnvelopedMinter::new(NoMinter, rhook);
        let rh = replay
            .mint_turn("invoke:run_tests", 1, 1, [0u8; 32])
            .unwrap();
        assert_eq!(rh, [7u8; 32]);
        assert!(replayer.borrow().fully_consumed());
    }

    #[test]
    fn clock_witness_capture_then_replay_never_reads_the_live_clock() {
        let recorder = Rc::new(RefCell::new(Recorder::new()));
        let hook: SharedHook = recorder.clone();
        let t = witness_clock(&hook, || 1234).unwrap();
        assert_eq!(t, 1234);
        let envelope = recorder.borrow().snapshot();

        let replayer = Rc::new(RefCell::new(Replayer::new(envelope)));
        let rhook: SharedHook = replayer.clone();
        let rt = witness_clock(&rhook, || panic!("replay must not read the live clock")).unwrap();
        assert_eq!(rt, 1234);
    }
}
