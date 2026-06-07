# DREGG — Ground-Truth Ontology, Functional Correctness, and Product Layer

> Canonical, brutally-honest map synthesized from 5 deep code reviews of both the
> Lean (`metatheory/Dregg2/…`) and Rust (`turn/`, `cell/`, `sdk/`, `node/`,
> `starbridge-apps/`, `storage/`) sides. Read this before asking "what is a turn",
> "is the cell program correct", or "is the orchestration/toolcalling/storage stuff real".
> Trust this over the marketing in the older docs; trust the code over this.

---

## PART 1 — THE ONTOLOGY (what the structures actually are)

### The crux: "Turn" is overloaded. There are THREE distinct things.

1. **`Exec.Turn`** (Lean, `Dregg2/Exec/Kernel.lean:45`) — a TINY struct
   `{ actor src dst : CellId; amt : ℤ }`. **This is NOT the protocol turn.** It is the
   per-effect **receipt / clock log row**. `fullReceiptA` (`TurnExecutorFull.lean:4479`)
   maps every executed effect to one of these (most are self-rows
   `{actor, src:=cell, dst:=cell, amt:=0}`; transfers carry the real move; mint/burn/
   bridgeMint carry ±amt). The executor's state `RecChainedState = { kernel :
   RecordKernelState; log : List Turn }` (`RecordKernel.lean:905`) appends one of these
   rows per committed effect. **The Lean "receipt chain" is a list of these clock rows.**

2. **The PROTOCOL turn** = a credentialed **call-forest**. In Lean this is `FullForestG`
   (`FullForestAuth.lean:277`); in Rust it is `Turn { call_forest, … }`
   (`turn/src/turn.rs:241`). This is the actual transaction an agent submits.

3. **The commitment-layer `Receipt`** (Lean `Receipt.lean:45`,
   `{ prevHash oldCommit newCommit effectsHash : Nat }`) / Rust `TurnReceipt`
   (`turn.rs:597`) — binds pre/post-state Merkle roots + effects hash + (devnet) STARK
   proof. **This is a different, richer object than the `Exec.Turn` log rows**, and the
   two receipt notions are NOT yet unified (see Gaps).

When this doc says "turn" unqualified, it means **#2, the protocol turn / call-forest**.

---

### Structure reference

#### Turn (protocol) — the credentialed call-forest

| Side | Type | Fields / role |
|------|------|---------------|
| Lean | `FullForestG` (`FullForestAuth.lean:277`) | `{ auth : NodeAuth; action : FullActionA; children : List FullChildA }` — a TREE. The **gated/production** forest. |
| Lean | `FullForestA` (`FullForest.lean:82`) | `{ action : FullActionA; children : List FullChildA }` — the ungated structural forest. `FullForestG` = this + per-node `auth` decoration. |
| Rust | `Turn` (`turn/src/turn.rs:241`) | `{ agent; nonce; call_forest : CallForest; fee; memo; valid_until; previous_receipt_hash; depends_on; conservation_proof; sovereign_witnesses; execution_proof; effect_binding_proofs; … }`. The wire transaction. |
| Lean | `WTurn` (`FFI.lean`) | `{ agent nonce fee validUntil prevHash root : FullForestG }` — the wire form the FFI parses, lifting to `FullForestG`. |

The Rust `Turn` ⟷ Lean `WTurn`/`FullForestG`. **Neither maps to `Exec.Turn`.**

#### Action — a node of the forest

- Lean `FullActionA` (`TurnExecutorFull.lean:3245`): ~43 constructors. **One node = ONE effect.** Authorization lives on the separate `NodeAuth` decoration, not on the action.
- Rust `Action` (`turn/src/action.rs:68`): `{ target; method; args; authorization; preconditions; effects : Vec<Effect>; may_delegate; commitment_mode; balance_change; witness_blobs }`. **One node = a VEC of effects, and the authorization lives ON the action.**

This structural mismatch (Rust multi-effect+auth-on-action vs Lean single-effect+auth-on-decoration) is bridged by the marshaller **by convention, not by a proven bijection** (see Gaps).

#### Effect — the atomic state mutation

- Lean: each `FullActionA` constructor IS an effect (~43): `balanceA`, `delegate`, `revoke`, `mintA`, `burnA`; 5 pure-state (`setFieldA`/`emitEventA`/`incrementNonceA`/`setPermissionsA`/`setVKA`); 6 authority (`introduceA`/`delegateAttenA`/`attenuateA`/`dropRefA`/`revokeDelegationA`/`validateHandoffA`); `exerciseA` (inner recursion); supply (`createCellA`/`createCellFromFactoryA`/`spawnA`/`bridgeMintA`); escrow/obligation/committed-escrow legs; note (`noteSpend`/`noteCreate`); 3 bridge legs; seal/sovereign/refusal/receipt-archive; 4 queue + batch/pipeline; 4 swiss; 4 lifecycle/refresh.
- Rust `Effect` enum (`action.rs:760`): ~43 variants (`SetField`, `Transfer`, `GrantCapability`, `RevokeCapability`, `EmitEvent`, `IncrementNonce`, `CreateCell`, `NoteSpend`/`NoteCreate`, `CreateSealPair`/`Seal`/`Unseal`, `SpawnWithDelegation`, `RefreshDelegation`, `RevokeDelegation`, `BridgeMint`/`Lock`/`Finalize`/`Cancel`, `Introduce`, `PipelinedSend`, `CreateObligation`/`Fulfill`/`Slash`, `CreateEscrow`/`Release`/`Refund` + committed variants, `ExerciseViaCapability`, `MakeSovereign`, `CreateCellFromFactory`, `Queue*`, `ExportSturdyRef`, …).

Mapped **1:1-ish** Lean ⟷ Rust. The marshaller (`lean_shadow.rs`) actually projects only ~20 of ~43 (see Product/Gaps).

#### Cell — the stateful object an effect mutates

- Lean `RecordKernelState` (`RecordKernel.lean:442`): **18 fields** — `accounts` (Finset), `cell` (CellId→Value, content-addressed record carrying a balance field), `caps`, `escrows`, `nullifiers`, `revoked`, `commitments`, `bal` (CellId→AssetId→ℤ per-asset ledger), `queues`, `swiss`, `slotCaveats`, `factories`, `lifecycle`, `deathCert`, `delegate`, `delegations`, `sealedBoxes`. Conserved measure: `recTotal` (Σ balOf over accounts); `recTotalAssetWithEscrow` (bal+escrows per-asset).
- Rust `Cell` (`cell/src/cell.rs:184`): `{ id; public_key; state : CellState; permissions; verification_key; delegate; delegation; token_id; capabilities : CapabilitySet; program : CellProgram; mode; lifecycle }`. `CellState` (`state.rs:45`): 8 `fields[FieldElement;8]` + `field_visibility` + `commitments` + `nonce` + `balance` + `proved_state` + `delegation_epoch` + `swiss_table_root` + `refcount_table_root`.

#### CellProgram — the per-cell transition validator (NOT a computation)

- Rust `CellProgram` (`cell/src/program.rs:53`): `None | Predicate(Vec<StateConstraint>) | Cases(Vec<TransitionCase>) | Circuit{circuit_hash}`. Checked on every state-modifying effect.
- Lean analog: `slotCaveats` + `stateStepGuarded` (the installed caveat program), AND the model-level `RecordProgram` (`Program.lean`) the user DSL elaborates to.

**Key fact: a cell program is an ADMISSIBILITY PREDICATE, not a function.** It accepts/rejects candidate `(old, new)` pairs; it does not compute `new`. The computation is done by a separate, tiny, total op language (`RecOp` = `setScalar`/`addScalar`, `RecordCell.lean`; Rust effect-apply). See Part 2.

#### Receipt — TWO things, not unified

- **Clock-row log**: `RecChainedState.log : List Exec.Turn` — one `{actor,src,dst,amt}` row per committed effect. The audit log.
- **Commitment receipt**: Lean `Receipt { prevHash oldCommit newCommit effectsHash }` (`Receipt.lean:45`, `wellLinked` chain) / Rust `TurnReceipt` (`turn.rs:597`: `turn_hash, forest_hash, pre_state_hash, post_state_hash, effects_hash, computrons_used, …`) / `WitnessedReceipt` (`witnessed_receipt.rs:246`, wraps with STARK `proof_bytes` + public inputs + witness bundle). The proof-bearing receipt.

#### Cap / Auth — the authority lattice

`Authority/Positional.lean:37,49`: `Auth = read | write | grant | call | reply | reset | control` (lift of l4v auth); `Cap = null | endpoint(target, rights) | node(target)` (lift of l4v cap), with `capAuthConferred` verbatim from l4v `Access.thy`.

#### Authorization — the 10-variant WHO

Lean `Authorization` (`FullForestAuth.lean:102`) / Rust (`action.rs:206`): `Signature`, `Proof`, `Breadstuff`, `Bearer`, `Unchecked`, `CapTpDelivered`, `Custom`, `OneOf`, `Stealth`, `Token`. `portalVerify` (`:145`) routes crypto arms through `CryptoKernel.verify`; `Unchecked` fail-closes; `Breadstuff` returns true (c-list read deferred to the WHAT leg); `OneOf` recurses.

---

### DATA-FLOW DIAGRAM (what flows around, per turn)

```
  Turn (protocol / wire)
    │  Rust: turn/src/turn.rs:241    Lean: WTurn → liftForestG → FullForestG
    │  carries: agent, nonce, fee, prevHash, + a CallForest / forest root
    ▼
  CallForest  =  tree of nodes (CallTree / FullForestG)
    │  Rust: forest.rs:31 (Merkle BLAKE3 of action_hash‖children_hash)
    │  Lean: FullForestG { auth, action, children }
    │  walked DEPTH-FIRST, ALL-OR-NOTHING
    ▼
  per node:  ┌─────────────────────────────────────────────────────────┐
             │ GATE                                                     │
             │  Rust: verify_authorization + preconditions + CellProgram│
             │  Lean: gateOK = credentialValidG  (WHO, portalVerify)    │
             │              ∧ capAuthorityG       (WHAT, authModeAdmits) │
             │              ∧ caveatsDischarged   (state-reading)        │
             │              ∧ revocationGate      (nullifier ∉ revoked)  │
             └─────────────────────────────────────────────────────────┘
             │  fail → whole forest aborts (none)
             ▼
  Action  (target, method, authorization, preconditions, effect(s))
    │  Rust: Vec<Effect>   Lean: ONE FullActionA
    ▼
  Effect  → dispatched to a chained kernel step
    │  Rust: apply against Ledger of Cells (mutate CellState.fields/balance/
    │        nonce + capabilities + side tables); meter computrons; journal
    │  Lean: execFullA dispatches FullActionA → mutate RecordKernelState (18 fields)
    ▼
  Cell mutation  +  append ONE receipt row (Exec.Turn) to the log
    │
    ▼
  children: run under EXECUTED delegation handoff
    │  Lean: recCDelegateAtten (delegator := targetOf parent action; t := capTarget
    │        parentCap); fail-closed if delegator holds no cap to t  (no amplification)
    ▼
  on success: emit commitment Receipt / TurnReceipt
    │  pre/post-state Merkle roots + effects_hash + receipt-chain link
    │  + (devnet) STARK proof_bytes  (WitnessedReceipt)
    ▼
  DONE  (any node returning none ⇒ entire forest rolled back)
```

**The live engine is `TurnExecutor::execute` (`turn/src/executor/execute.rs:114`).**
The Lean mirror is `execFullForestG` via `@[export] dregg_exec_full_forest_auth`
(`FFI.lean:3487`).

---

## PART 2 — FUNCTIONAL CORRECTNESS (the honest line)

### Verdict: the SECURITY ENVELOPE is verified. FULL FUNCTIONAL SEMANTICS are NOT (except the transfer beachhead).

There is a clean, structural reason, and it is the single most important fact about
dregg's verification story:

> **A cell program is a CONSTRAINT, not a function.** `RecordProgram.admits :
> Method → Value(old) → Value(new) → Bool` (and `CellProgram.admits : KernelState →
> Turn → Bool`) accept/reject candidate `(old,new)` pairs. They do **not** name or
> derive the intended `new`. The actual next state is computed by a separate, tiny,
> total op language — `applyOp` over `setScalar`/`addScalar` (`RecordCell.lean`) —
> **which has NO declarative spec it is proven to refine.**

So the architecture is: *op computes a candidate → program is a fail-closed FILTER on
that candidate.* Nothing pins the **uniquely-correct** next state; a program may admit
many predicate-satisfying next-states.

### What IS verified (real, sorry-free, `#assert_axioms`-pinned to the 3 kernel axioms)

**The envelope / Hoare-postconditions:**
- `recExec_admitted` — every committed transition was admitted by the program (the gate is load-bearing, never bypassed).
- `recExec_commits_applyOp` + `setField_scalar_self` — a commit commits **exactly** `applyOp`'s candidate (no silent rewrite); reading a field you just set returns what you set.
- `recExec_some_iff_admits` — full ⇔ characterization of when the arrow fires.
- `recExec_mono_holds` — for `monotonic "count"`, a committed transition genuinely has `new.count ≥ old.count`, recovered as an honest `Int` inequality.
- `recCexec_attests` / `recReplay_preserves_sumEquals` — across a whole replay, a `sumEquals` program keeps `Σ new[fields] = c`.
- `denote_conserves` / `denote_run_conserves` / `system_refines_kernel` — a `CellProgram` cannot bypass kernel conservation or produce a transition `exec` wouldn't.
- DSL elaboration correctness (`counter_eq_counterProgram`, `escrow_eq_expected`, ~11 atom smoke-tests, by `rfl`) — the eDSL surface elaborates to **exactly** the intended verified catalog term.
- Queue handlers: per-effect `conserves`/`auth_gated`/`admission_gated`; P0-1 binding-attack rejection (`#guard`).
- Executor envelope on the forest: `execFullForestA_eq_execFullTurnA` (tree = pre-order fold), `recCexec_attests` (conservation ∧ authority ∧ chain-link), `recChained_run_conserves`, `gateOK_revoked_fails` (revoked nullifier rejected — non-vacuous teeth, reads committed state).

### What is NOT verified

- **No `applyOp_spec` / no functional-refinement theorem.** Nothing proves that running program `P` on input `X` yields the **semantically-correct** answer `Y`. Only that whatever got through satisfies the developer's predicate (count went up; sum = c; status moved along an allowed edge).
- The full-state soundness triangle (all 18 `RecordKernelState` fields pinned per effect, with an anti-ghost tooth that a wrong output is rejected) exists for the **transfer beachhead only**, not uniformly across the ~43 effects.
- Crypto soundness (`CryptoKernel.collisionHard`), foreign-chain finality (bridges), §8 STARK extractability — **named portal hypotheses**, not Lean-discharged.

### Where exactly the line is

| Claim | Status |
|-------|--------|
| "The result satisfies my declared predicate" (constraints hold on the committed state) | **VERIFIED** |
| "The committed value is exactly what the op produced" (no silent rewrite) | **VERIFIED** |
| "The program can only tighten the kernel; conservation/authority can't be bypassed" | **VERIFIED** |
| "The eDSL elaborates to the verified term I think it does" | **VERIFIED** (`rfl`) |
| "**The result IS the function I meant**" (output uniqueness + correctness) | **NOT VERIFIED** (transfer only) |
| "All 18 state fields are pinned per effect with anti-ghost teeth" | **NOT VERIFIED** (transfer only) |

This is **l4v-style refinement of the ENVELOPE** (Hoare postconditions = the
constraints), **not** l4v-style functional refinement against an abstract spec
function. The honest answer to "is cell-program functional correctness verified" is:
**the security semantics are; the functional semantics are not.**

**Shortest push to real functional correctness:** introduce an independent declarative
reference per cell-program family (e.g. `escrowSpec : Method → State → State` in plain
Lean) and prove a refinement triangle with an anti-ghost tooth:
`recExec escrowProgram method old op = some new ↔ new = escrowSpec method old`
(output uniqueness + correctness, not just `admits old new`). Also widen `RecOp` beyond
the 2-constructor toy so the spec has real computational content to refine.

---

## PART 3 — THE PRODUCT LAYER (what exists, how real)

Ratings: **RUNNING** (built binary, runs end-to-end on the live Rust engine) ·
**VERIFIED-MODEL** (proved in Lean over a toy/abstract ledger, disjoint from the
running path) · **SEED** (architecturally present, key wire missing).

The recurring structural truth across all four products: **the Rust runtime runs, the
Lean proofs are real, and the two are largely DISJOINT** — the verified executor is a
shadow/producer behind env flags over only ~20 of ~43 marshallable effects, not yet the
universal engine, and the load-bearing security gates frequently run as out-of-band
advisory checks rather than inline executor admission.

### 3a — Agent orchestration apps — **RUNNING demo + VERIFIED-MODEL (disjoint)**

- **Rust (runs):** `sdk/src/runtime.rs` `AgentRuntime` / `SubAgent` genuinely spawn least-privilege sub-agents: real macaroon/biscuit `token.attenuate`, a fresh `AgentCipherclerk` identity, a signature-bound `LocalDelegation`, all on a shared `dregg_cell::Ledger`. Built binaries (`demo-agent/examples/`): `orchestration_demo.rs` (690 lines — spawn/execute/overreach-deny/budget/revocation/ZK/audit), `agent_network.rs` (1013 lines, 8-cell coordination via `Pipeline`/`EventualRef`), `ai_agent_mcp_workflow.rs` (503 lines, simulated MCP). Real deny/budget/revoke are genuine `Err` returns, not theater.
- **Lean (verified, toy):** `Dregg2/Apps/AgentOrchestration.lean` (458 lines) proves non-amplification (`derive_no_amplify`), per-asset conservation, fail-closed out-of-scope mint, `gate-committed ⇒ credential ∧ caveats` — but on its **own 2-asset toy ledger**.
- **The load-bearing gap:** `SubAgent::execute` builds turns with **`Authorization::Unchecked`** and does **not** pass the attenuated token into the executor. Capability enforcement is an **out-of-band `cap.verify()`** the demo calls alongside — the token gates the **narration**, not the executor's admission of the worker's `SetField`. `Authorization::Token` is constructed **nowhere** in `sdk`/`app-framework`/`demo-agent`/`starbridge-apps`. The verified Lean executor is **off the critical path** (`SubAgent::execute` bypasses the `run_turn` producer seam entirely; producer mode is `feature(lean-producer)` + `DREGG_LEAN_PRODUCER` gated and only on `AgentRuntime::execute`).
- **Push-next:** make `SubAgent::execute` carry `Authorization::Token` (the attenuated `HeldToken`) and have `TurnExecutor` enforce it **inline** (the `Token` arm + Datalog evaluator already exist). Converts "narrated security" → "executor-enforced security" and makes the existing Lean theorems the actual semantics of the running path.

### 3b — Decentralized toolcalling permissions — **RUNNING at executor / SEED at MCP surface**

- **Executor layer (real, decentralized, enforced):** `Authorization::Token { encoded, key_ref, discharges }` (`action.rs:422`) is a first-class biscuit (`eb2_`)/macaroon (`em2_`) credential. `verify_token_authorization` (`authorize.rs:1527`) decodes, trust-checks the issuer against the **target cell's own key** (the cell is its own granting authority), then runs the **real upstream `biscuit_auth` crate** (`biscuit_backend.rs:141`) against a Datalog policy (`dregg.rs:289`): `allow if service($svc,$actions), request_service, request_action, $actions.contains($act)` + terminal `deny if true`. Attenuation is real append-only `inner.append(block)` — cryptographically narrow-only, offline-verifiable, transferable. Unit tests prove replay/wrong-action/untrusted-issuer/expired/tampered all reject. **This is a genuine, working decentralized object-capability primitive.**
- **Lean (verified envelope):** `Authority/Caveat.lean` proves the attenuation **lattice** is sound and non-vacuous (`attenuate_narrows`; `#guard` windowed token admits height 150, rejects 50/250; third-party caveat suspends until discharged). But `Ctx` is only instantiated as `Height` — Lean proves the meet/narrowing law, **not** that the Rust Datalog correctly maps real `(action,resource)` to scope. Crypto (no-forgery, HMAC) is explicitly **ASSUMED** (`ThirdPartyDischarge.lean`).
- **The gap (MCP surface):** `node/src/mcp.rs` `handle_tools_call → dispatch_tool` (`6605 → 1360`) is a flat match over ~45 tools with **ZERO per-tool capability gate** — only a single global `s.unlocked` bit. Once unlocked, any client invokes any tool. No MCP tool constructs `Authorization::Token`; they build `Unchecked`/`Bearer`/`CapTpDelivered`. **The capability machinery exists and the executor enforces it; the wire from MCP tool dispatch to a presented scope-bound token is missing.**
- **Push-next:** (1) tool→required-scope table; (2) require each `tools/call` to carry an `Authorization::Token`, build the root action's method/target from the tool's declared scope; (3) reuse `verify_token_authorization` unchanged. Integration, not new crypto.

### 3c — Storage gateway mandates (SGM) — **VERIFIED-MODEL + thin RUNNING demo; policy not load-bearing at runtime**

- **Lean (verified):** `sgmAdmitM` (`StorageGatewayMandate/Core.lean:111`) is a real fail-closed authorizer: `opAllowed ∧ prefix(PUT) ∧ clearance(GET) ∧ volume-budget` (`Slice.tryDebit`). Proved teeth (each violation class → `none`), `sgm_volume_legal_forever` (spent ≤ ceiling under every adversarial schedule), conservation, gated rejection, and the hard-won 53-arm executor frame `execFullForestA_progLive_preserved`.
- **Runs (thin):** `teasting/tests/cross_app_mandate_storage_e2e.rs` composes identity + CWM + SGM through one `EmbeddedExecutor` (Rust `dregg-turn` + `dregg-cell`), 7 signed turns, single causal receipt chain, replay-determinism. The installed `CellProgram` `StateConstraints` (immutable anchor/ceiling/prefix, monotonic volume, `spent ≤ ceiling`) are enforced each turn.
- **The gap:** the rich admission logic (op-allowlist / prefix-on-PUT / clearance-on-GET) lives **only in the off-line `sgmAdmitM` predicate the executor never calls**. The installed `StateConstraints` can't express allowlist/prefix/clearance, so a turn setting `last_op=GET` without clearance, or a non-prefix `object_key`, is **NOT rejected** by the executor. No verified refinement ties Rust `sgm_admit` ⟺ Lean `sgmAdmitM` (hand-written unit tests only). `sgmWF` carries only "cell live + caveat program installed" — the literal anchor/volume VALUE conjuncts are explicitly **not** carried. The `dregg-storage` crate (queues/relay/inbox) is `#[deprecated]` and **disconnected** — the mandate stores no bytes; `volume_spent` is a free-floating counter.
- **Push-next:** prove the value-carrying second cell-record frame — the executor's per-turn step on the mandate cell COMMITS **iff** `sgmAdmitM` admits (only reachable `volume_spent` transitions are the admitted ones). Concurrently teach the installed `CellProgram` a guard that actually enforces op-allowlist/prefix/clearance, and route the e2e through the SWAP/Lean executor.

### 3d — Workflow mandates (CWM, compartment-workflow) — **VERIFIED-MODEL + thin RUNNING demo; same not-load-bearing gap as SGM**

- **Lean (verified):** `cwmAdvanceM` (`CompartmentWorkflowMandate/Core.lean:209`) advances a cursor iff `stepAdmissible` (all DAG `needs` ⊆ `completed`, not already done) ∧ `stepClearanceOK` (per-step compartment clearance). Canonical 3-step review→redact→sign charter. Proved teeth (`cwm_illegal_dag_rejected`, `cwm_clearance_violation_rejected`), `cwm_step_legal_forever`, conservation, gated rejection, same 53-arm frame.
- **Runs (thin):** `starbridge-apps/compartment-workflow-mandate/src/lib.rs` (453 lines) with an explicit Lean-theorem → Rust-admission-check mapping table (`stepAdmissible`/`cwmAdvanceM` → `step_admissible`/`cwm_advance_admits` + `MonotonicSequence` slot caveat). Runs in the same e2e as SGM (final `step_cursor=3`, immutable anchors, replay-determinism).
- **The gap:** the app's own word is **"scaffold"** — `step_clearance_ok` is partial, Stingray debit wiring is a follow-on, and the gated production theorems (SenderAuthorized + revocation witness on `advance_step`) are **not yet wired**. Same as SGM: DAG-prereq/clearance enforcement is the off-line predicate; the installed `StateConstraints` only express monotonic-cursor/immutable-anchor; no predicate↔executor refinement.
- **Push-next:** same as SGM (commit-iff-admit value frame + an executor-side guard that enforces DAG/clearance), then drive review→redact→sign through real `SubAgent`s over the app-framework HTTP server with token-gated turns — the first capability-secured multi-agent workflow that runs AND matches a Lean theorem.

---

## ONE-SCREEN SUMMARY

- **"Turn" is overloaded.** Protocol turn = credentialed call-forest (`FullForestG` / Rust `Turn{call_forest}`); `Exec.Turn` is just a 4-field receipt log row; the commitment `Receipt`/`TurnReceipt` (Merkle roots + STARK) is a third, separate thing.
- **An effect** is one `FullActionA` constructor / Rust `Effect` variant (~43, mapped 1:1-ish) mutating an 18-field `RecordKernelState` (Rust: a Ledger of `Cell`s).
- **A cell program is a predicate, not a function** — it filters `(old,new)` candidates; the next state is computed by a separate tiny op language with no spec it refines.
- **Verified = the envelope** (conservation, authority, chain-link, non-amplification, revocation/caveat teeth) — real sorry-free theorems. **Not verified = full functional semantics** (output-uniqueness), proved only for the transfer beachhead.
- **Product:** orchestration & toolcalling **RUN** end-to-end on the Rust engine (real attenuation, real biscuit caps, real receipts) but the capability gate is **out-of-band/advisory** (`Authorization::Token` wired nowhere agent-facing; MCP tools un-gated behind one global unlock); storage-gateway & workflow mandates are **verified Lean policy models + thin runnable demos** whose rich admission logic is **not enforced by the executor at runtime**. Every gap is one integration/refinement step, not a missing primitive.
