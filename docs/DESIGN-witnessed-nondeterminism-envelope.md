# DESIGN — execution auditing: the agent loop as deterministic replay under a witnessed-nondeterminism envelope

Status: DESIGN + first scaffold (`dregg-agent/src/envelope.rs`). 2026-07-12.
Scope: the `dregg-agent` run loop (`agent::AgentCloud::drive_state` and everything it drives).

## 1. The claim the audit rail sells — and its exact limit

A hosted agent turn should be **re-executable by an auditor**: given (a) the turn's
initial state and (b) a sealed record of every nondeterministic input the turn
consumed, a re-execution reproduces every admission, every refusal, every meter
draw, and every receipt **byte-for-byte**. That is the audit rail: a dispute about
"what did the agent do and why" is settled by replay, not by trusting the host's
narrative log.

The exact limit, stated up front because the whole design is worthless if it is
fudged: **an LLM output is captured-as-input, NOT re-derivable.** Replay proves
*"given these model outputs, the orchestration admitted/refused/receipted exactly
this"*. It can never prove the model actually produced those outputs, and no
amount of envelope machinery changes that. The same holds for live tool outcomes
(a shell run, an HTTP fetch). See §6 for the full honest ceiling.

## 2. Ground truth: the loop is already almost deterministic

Read against `dregg-agent/src/agent.rs` (`drive_state`, agent.rs:1633–1853), the
pipeline per decided action is:

1. **cap-gate** — `Credential::verify(&root_pub, &cap_context(&cap, block))`: a
   pure function of the credential bytes, the cap string, and `handle.block`
   (which is fixed in the `AgentHandle`, not a clock read).
2. **kernel-turn admission** — `GrainTurnMinter::mint_turn(label, cost,
   consumed_after, cell_root) -> Result<[u8; 32], String>`: **external** (the
   executor decides; its answer is a nondeterministic input to this loop).
3. **meter draw** — `ReplenishingMeter::draw(&MeterKey::new(id, seq), amount,
   block)`: pure arithmetic over the draw history, keyed exactly-once per
   `(agent, seq)`.
4. **run** — `ToolKit::invoke` / `ToolKit::run_op`: **external** (a real shell /
   fs / http / Stripe effect; its `ToolOutcome` is a nondeterministic input).
5. **receipt seal** — `ReceiptChain::seal(body_hash, seq, turn_hash)`: ed25519
   over a `BodyHasher` (blake3, domain-separated) body hash. ed25519 signing is
   deterministic (RFC 8032), so given the same chain secret, prev head, and body,
   the sealed receipt is byte-identical on replay.

The brain side: `OpenAICompatBrain<C>` constructs each chat-completions request
**deterministically** from its conversation state (goal + prior observations) and
calls the ONE transport seam, `OpenAICompatCaller::complete(endpoint, api_key,
request)` (brain.rs:687–688 is the single call site). The model's response is a
nondeterministic input; the request is a deterministic function of prior inputs.

Notably ABSENT from the loop: wall-clock reads (block heights ride the handle;
`ToolGatewayMinter.now` is a constant presentation stamp) and mid-turn RNG (the
receipt-chain secret is provisioned before the turn, `SessionState::from_secret`).
So clock/rng envelope entries are RESERVED vocabulary for hosts that add such
reads, not a current requirement of `drive_state`.

Conclusion: the loop is a deterministic orchestration with exactly **three** live
nondeterministic seams, all already behind named traits. That is why this design
is a weld, not a rewrite.

## 3. The nondeterminism inventory (the envelope's vocabulary)

| Seam | Real API | Captured record | Replay-validation identity (request digest) | Never captured |
|---|---|---|---|---|
| LLM completion | `brain::OpenAICompatCaller::complete` | the provider's raw response JSON text, or its error string (`Result<String, String>`) | blake3(domain ‖ endpoint ‖ request-JSON) | **the api_key** — excluded by construction (it is not a digest input and not a record field) |
| Tool invoke | `agent::ToolKit::invoke` | the full `ToolOutcome` (ok, summary, `Option<WitnessedRun>`) | blake3(domain ‖ service ‖ amount-marker ‖ amount ‖ cells-digest) | — |
| Operator op | `agent::ToolKit::run_op` | the full `ToolOutcome` | blake3(domain ‖ tool-call-JSON ‖ cells-digest) | — |
| Kernel-turn admission | `agent::GrainTurnMinter::mint_turn` | `Result<turn_hash, refusal-reason>` | blake3(domain ‖ label ‖ cost ‖ consumed_after ‖ cell_root) | — |
| Clock (reserved) | host-side | `unix_millis` | domain-constant (order carries identity) | — |
| RNG (reserved) | host-side | the bytes | blake3(domain ‖ requested-len) | — |

The **request digest** is the teeth of replay: on replay the deterministic core
re-derives each seam's request and the replayer checks it against the recorded
digest. A mismatch is a **detected divergence** (the code changed, the wrong
envelope was presented, or the envelope was spliced) and replay refuses
fail-closed — it never silently serves an answer to a different question. This is
the same history-plus-validation discipline duroxide-style durable execution
uses; here it is applied at the agent-turn level for audit.

## 4. The envelope

`envelope::WitnessedNondeterminism` is an ordered list of `WitnessedEntry { seq,
request: SeamRequest, input: WitnessedInput }`.

- **Entry hash**: blake3 via the existing `receipt::BodyHasher`, domain
  `dregg-agent-envelope-entry-v1`, over the entry's serialized form.
- **Envelope root**: a prev-linked fold `root' = blake3(domain ‖ root ‖
  entry_hash)` — order-sensitive, so a reordered or spliced envelope moves the
  root. One 32-byte commitment names the whole turn's consumed nondeterminism.
- **Ordering is identity**: entries are consumed strictly in order by a cursor;
  there is no keyed lookup an adversarial host could permute.

Scaffold caveat, named: entry hashing serializes with `serde_json` over
declaration-ordered structs — deterministic for one build of this code, but the
hardening step is a canonical binary encoding (`postcard`, already a crate dep)
before the root is ever bound into anything signed.

## 5. Capture and replay

One trait, two modes (`envelope::ReplayHook`, `TapMode::{Capture, Replay}`):

- `Recorder` — capture mode: each wrapper performs the real effect, then appends
  the witnessed record. A record that cannot be appended **fails the call**
  (fail-closed: an unwitnessed effect result never reaches the brain — the effect
  itself may already have happened, which is the irreducible cost of capturing
  after the fact; what is guaranteed is that no unwitnessed input steers the run).
- `Replayer` — replay mode: each wrapper **never performs the effect**; it serves
  the next recorded entry after validating seam kind + request digest, and
  poisons itself on first divergence (`Replayer::divergence()`), so a diverged
  replay cannot limp onward consuming misaligned entries.

The welds (all implemented in the scaffold, against the real traits):

- `EnvelopedCaller<C: OpenAICompatCaller>` — implements `OpenAICompatCaller`;
  slots in as the brain's `C` with zero brain changes. In replay the inner caller
  is never touched and no key is needed (`NoCaller` stands in, erroring if ever
  reached).
- `EnvelopedToolKit<T: ToolKit>` — implements `ToolKit`; `op_cap` forwards to the
  inner toolkit **in both modes** (it is a pure function of workdir config, and
  the cap-gate consumes it), while `invoke`/`run_op` are intercepted in replay.
  Preferred replay shape: wrap the SAME real toolkit type — its effects are never
  invoked in replay mode, and cap resolution stays faithful. `NoToolKit` exists
  for when the toolkit cannot be reconstructed (with the stated caveat that its
  default `op_cap` may diverge from a workdir-resolving toolkit's — a divergence
  the request digests will then surface).
- `EnvelopedMinter<M: GrainTurnMinter>` — implements `GrainTurnMinter`. On
  replay, the recorded `Result<turn_hash, reason>` is served: **replay does NOT
  recommit kernel turns**. The turn hash is a witnessed input; a replayed turn is
  a simulation for audit, not a second on-ledger execution.

Replay procedure (the auditor's side): reconstruct the turn's genesis —
`AgentHandle` (it is `Serialize`), `SessionState::restore_from_report` /
`from_secret` with the persisted chain secret, `AgentCloud::from_seed` +
`precharge_meter` for the meter — then run the same goal through
`run_goal_minted` with all three seams wrapped in `Replayer` mode, and compare
the produced `AgentRunReport` (receipts byte-for-byte, log, counts) against the
original. Equality = the host's report is exactly what this code does on these
inputs. **This wiring is design, not built** (§8) — note the auditor needs the
chain secret to reproduce signatures, which makes byte-exact receipt replay a
HOST-side or escrowed-secret audit; a third party without the secret replays
everything except the signatures and checks the originals with the existing
`verify_agent_run` instead.

## 6. The honest ceiling

1. **Captured-as-input, not re-derivable.** The LLM response, the shell/http
   outcome, the executor's admission — each is a fact the envelope asserts, not
   one replay re-establishes. Replay verifies the ORCHESTRATION (gating,
   metering, receipting, feedback into the brain's next request), nothing more.
2. **The recorder is the host.** A lying host can capture a fabricated tool
   outcome and the envelope will replay it faithfully. The envelope is R2-grade
   in the sense grain-turn's "Honest scope (R2, not R3)" note uses: it removes
   "trust the host's story about the loop" and leaves "trust the host's record of
   the inputs". Partial strengthenings that already exist and compose here:
   - `WitnessedRun` + `verify_witnessed_qa` (agent.rs): for the re-runnable
     subset of tool outcomes (`run_tests`/`verify_deploy`), a re-execution oracle
     checks the recorded `(exit, output_digest)` — a fabricated QA verdict is
     caught for that subset.
   - the zkOracle attestation slot (`grain-turn::ATTESTATION_SLOT`): binds "which
     brain drove this" onto the committed turn — orthogonal to, and composable
     with, the envelope.
3. **No cross-turn kernel truth from replay.** Replayed turn hashes are echoes of
   the record. Checking that a `turn_receipt_hash` names a REAL committed turn
   remains the R2 manifest check (`ToolGatewayMinter::committed_turns`), outside
   this rail.
4. **Secret-holding.** Byte-exact receipt reproduction requires the receipt-chain
   secret (§5). The envelope adds no new secret and never captures the BYO api
   key (excluded by construction at the one seam it transits).

## 7. Dreggic fit

Per-grain: one envelope per session/grain, living beside its receipt chain —
never a global log. Owner-anchored: the envelope's future commitment binding
(§8.2) rides the SAME owner-anchored receipt chain / grain turn-cell the session
already owns. Bilateral: an audit is auditor↔host over one grain's artifacts; no
federation-wide consensus entity is introduced, no quorum is asked to attest an
envelope. Conserving: no Transfer semantics are touched — the envelope is
witness-only. Fail-closed throughout: capture refusal fails the call, replay
divergence poisons the replayer, the `No*` stand-ins error rather than pass.

## 8. Built vs design (the ledger)

**Built (this scaffold, `dregg-agent/src/envelope.rs` — compiles against the real
traits, unit-tested in-module):**
- the envelope types (`WitnessedNondeterminism`, `WitnessedEntry`,
  `WitnessedInput`, `SeamRequest`, `SeamKind`), entry hashing, the prev-linked
  envelope root;
- the replay hook trait (`ReplayHook`) + `Recorder` / `Replayer` (cursor,
  digest validation, divergence poisoning, fail-closed error surface);
- the three seam wrappers (`EnvelopedCaller`, `EnvelopedToolKit`,
  `EnvelopedMinter`) + fail-closed stand-ins (`NoCaller`, `NoToolKit`,
  `NoMinter`) + the reserved clock/rng witnesses (`witness_clock`,
  `witness_rng`);
- tests: capture→replay determinism at each seam, request-divergence refusal,
  envelope-root tamper detection, api-key non-capture.

**Design only (NOT built — do not represent otherwise):**
1. Wiring capture into the product run paths (`Session`, `live.rs`, the `attach`
   bin): constructing the wrappers per turn and persisting one envelope per goal.
2. Binding the envelope root into the signed record — either a new
   `AgentReceipt` field folded into `body_hash` (a receipt-format version bump)
   or an envelope-root slot on the grain turn-cell alongside `ATTESTATION_SLOT`.
   Until this lands, envelope↔chain association is by custody, not signature.
3. Envelope persistence + the auditor entrypoint (`dregg-agent replay <envelope>
   <report>`), including the reconstruction recipe of §5.
4. Canonical (postcard) entry encoding before (2) ever ships.
5. Brain-request capture policy: digests suffice for validation; full request
   capture (for divergence DIAGNOSIS, not correctness) is an opt-in flag to keep
   envelopes small and free of prompt-embedded user data by default.

## 9. Relation to existing primitives

- `brain::RecordedOpenAICaller` — replays canned responses but validates
  nothing about the requests (by design; it is a test double). `EnvelopedCaller`
  in replay mode is its audit-grade successor: same seam, plus request-digest
  validation, ordering, and a sealed root. The test double stays.
- `turn/src/reversible.rs` + the time-travel demo — KERNEL-side history: reverse
  and re-apply committed cell state. Complementary axis: reversible turns move
  state backward; the envelope re-derives orchestration decisions forward. An
  audit can use both (rewind the grain, replay the turn).
- duroxide / `hosted-durable` — durable-execution WORKFLOWS (a kept product
  layer, per HORIZONLOG). The envelope borrows its history+validation replay
  discipline but is not a workflow engine and does not replace it.
- `grain-verify` R2 tooth — checks receipts against the committed-turn manifest;
  the envelope adds the WHY behind each receipt. The two compose into one audit:
  manifest says the turns are real, envelope says the loop was faithful.
