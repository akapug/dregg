# Submit Path — how an external HTTP turn reaches the blocklace DAG + finalizes cross-node

Scope: the ingress → consensus wiring in `node/src/api.rs` and `node/src/blocklace_sync.rs`.
Grounded file:line at HEAD. This doc began as a READ-ONLY diagnosis that found a design gap
("no path carries a fresh external client's OWN turn into the DAG"); the fix design in §5
is implemented, so the doc now teaches the wired path. The traced maps remain the reference
for how each ingress reaches consensus.

Companion lane: the n=3 **finality-gate** diagnosis covers turns that are ALREADY in the
DAG (does `tau` super-ratify + does `execute_finalized_turn` fire). This doc covers the
step *before* that: how an externally-submitted (HTTP) turn ENTERS the DAG.

---

## Short answer

An external HTTP turn reaches the blocklace DAG through **`POST /turns/submit`** (the
caller-signed rich-client path), and a **fresh** client's first turn finalizes cross-node:

- **`POST /turns/submit`** carries the client's own cell, binds the client's receipt to the
  client's **own** chain (not the node operator's), injects to the blocklace on commit
  (`api.rs:3729-3737`), and relies on finalization as the sole authoritative application in
  multi-party mode. `execute_finalized_turn` **provisions the turn's actor cell
  deterministically** (`provision_signer_actor_cell`, `blocklace_sync.rs:4536`) alongside
  transfer destinations, so "cell not found" no longer blocks a first turn.

- **`POST /turn/submit`** (thin client) is the **operator-only** path by design: the
  confused-deputy hardening rewrites the request's `agent` to the node's OWN operator cell
  (`api.rs:3075-3084`), so it can only ever author operator turns. It is not, and cannot
  be, a client-turn path while the hardening stands (correctly — see §2a).

- **`POST /api/faucet`** acts as the genesis-provisioned faucet cell and was the original
  template for finalization-driven provisioning (`api.rs:7045-7074`).

Remaining gate downstream of this doc's scope: staged turns only drain into round blocks
when rounds can advance (`plan_round_block` supermajority) — the n=3 finality-gate lane's
territory (§6).

---

## 1. The three external ingress endpoints

All three are `protected_routes`, gated by `require_auth` (`api.rs:1397`, layered at
`api.rs:1884`).

| Endpoint | Handler | Agent the turn acts as |
|---|---|---|
| `POST /turn/submit` | `post_submit_turn` (`api.rs:3053`) | node operator's own cell — body `agent` **ignored** |
| `POST /turns/submit` | `post_submit_signed_turn` (`api.rs:3414`) | the caller's signer default cell (must match) |
| `POST /api/faucet` | `post_faucet` (`api.rs:6961`) | the genesis faucet cell |

---

## 2. Traced submit path — where each commits, where each injects to the DAG

### 2a. `POST /turn/submit` (thin HTTP, operator-only)

```
post_submit_turn (api.rs:3053)
  ├─ rate-limit + unlocked gate
  ├─ CONFUSED-DEPUTY HARDENING: ignore req.agent, derive the
  │  operator's own cell from s.cclerk.public_key()             (api.rs:3075-3084)
  ├─ build CallForest signed by the operator cipherclerk
  ├─ execute_via_producer(...) against s.ledger                 (api.rs:3192)
  └─ match exec_result:
       Committed  → append_receipt onto s.cclerk (LOCAL chain)  (api.rs:3232)
                  → gossip_turn
                  → blocklace.submit_turn(...)  ← DAG injection  (api.rs:3352-3360)
       Rejected   → return; NO blocklace injection
```

The DAG injection is only reached on the `Committed` branch. Because the turn acts on the
operator's own cell, it commits **only when that cell exists**:

- Clean-boot genesis node: the operator agent cell is provisioned at boot
  (`node/src/lib.rs:855-870` — "clean boot → agent cell present with the operator key").
- Refused-launch-then-relaunch node: the operator cell is **absent** (`lib.rs:855-870`
  documents exactly this recovery-path trap) → `execute_via_producer` returns
  `Rejected("cell not found")` and the handler never calls `blocklace.submit_turn`.

A *client's own* turn is unreachable here by design: the body `agent` is discarded, so the
endpoint can only ever author operator turns. This is correct — the hardening prevents the
operator signature being pointed at a victim c-list. Client turns route through the
caller-signed `/turns/submit`.

### 2b. `POST /turns/submit` (caller-signed SignedTurn — THE external client path)

```
post_submit_signed_turn (api.rs:3414)
  ├─ verify signer signature over turn hash                     (api.rs:3435)
  ├─ HYBRID perimeter: a present-but-invalid ML-DSA half REJECTS (api.rs:3454-3467)
  ├─ REQUIRE turn.agent == derive_raw(signer, "default")        (api.rs:3469-3483)
  ├─ is_operator_agent split                                    (api.rs:3502)
  │    operator agent → previous_receipt_hash gated on the NODE
  │                     head (s.cclerk)                         (api.rs:3510-3525)
  │    FOREIGN client → NO node-head gate; binds to ITS OWN
  │                     claimed previous_receipt_hash
  │                     (None for a first turn)                 (api.rs:3558-3564)
  ├─ provision_signer_actor_cell + provision_transfer_destinations
  │    (the IDENTICAL provisioning the finalized path applies)  (api.rs:3580-3581)
  ├─ execute_via_producer(...) IN PLACE under the write lock    (api.rs:3582-3587)
  │    MULTI-PARTY: journal rolled back — the run is an
  │    optimistic ack; finalization is the sole authoritative
  │    application. SOLO keeps the commit.                      (api.rs:3592-3598)
  └─ Committed → append_receipt onto s.cclerk ONLY for the
              operator's own agent (or solo)                    (api.rs:3633-3634)
              → gossip_turn
              → blocklace.submit_turn / submit_turn_bundle      (api.rs:3729-3737)  ← DAG injection
```

The two structural couplings the original diagnosis flagged are closed here:

1. **Actor provisioning.** `provision_signer_actor_cell` (`blocklace_sync.rs:8243`) inserts
   `derive_raw(signer, "default")` as a zero-balance stub when absent — at ingress
   (`api.rs:3580`) for the local receipt, and authoritatively at finalization
   (`blocklace_sync.rs:4536`) on every node. A brand-new client cell no longer yields
   `Rejected("cell not found")`.
2. **Chain decoupling.** Only the node operator's own agent binds to the `s.cclerk` head;
   a foreign client's `previous_receipt_hash` is its OWN chain's (None for a first turn),
   and in multi-party mode the local run is rolled back so clients are not serialized
   through, or appended onto, the node-owned chain.

### 2c. `POST /api/faucet`

`post_faucet` (`api.rs:6961`) transfers from the **genesis faucet cell**, present
authoritatively on every node. In multi-party mode all provisioning + execution runs
against a **scratch clone** for the HTTP receipt, leaving authoritative state to
finalization (`api.rs:7045-7074`), then injects to the blocklace like the others
(`api.rs:7425`). It is the original template for the finalization-authoritative posture
`/turns/submit` now shares.

---

## 3. Traced internal turn → DAG → finalize path (what every ingress relies on)

Once a payload reaches `blocklace.submit_turn`, the machinery is uniform:

```
BlocklaceHandle::submit_turn (blocklace_sync.rs:427)
  → submit_turn_payload (blocklace_sync.rs:536)
       n>1: STAGE into pending_payloads, return (receipt, Local)   (blocklace_sync.rs:558-561)
       n=1: add_block immediately (solo finalizes trivially)       (blocklace_sync.rs:568)

cadence_tick_round_driven (blocklace_sync.rs:3716)  [round-driven producer loop]
  → round_cadence_decision → DrainTurns                            (blocklace_sync.rs:3466)
  → pop_front pending_payloads → produce_round_block(payload)      (blocklace_sync.rs:3787-3797)
  → produce_round_block (blocklace_sync.rs:501):
       plan_round_block gate — advance ONLY on a supermajority of
       distinct creators at the current round                      (blocklace_sync.rs:3341)
       else RoundPlan::Wait → None → re-stage the payload          (blocklace_sync.rs:514)

finality executor → tau super-ratifies → execute_finalized_turn    (blocklace_sync.rs:4287)
  → verify the turn signature carried in the block                 (blocklace_sync.rs:4308-4316)
  → provision_signer_actor_cell (the turn's ACTOR)                 (blocklace_sync.rs:4536)
  → provision_transfer_destinations (Transfer destinations)        (blocklace_sync.rs:4541)
  → execute_via_producer on every node, uniform post-state
```

Two facts from this path matter to the external story:

- **The block producer carries exactly one queued payload per round block** and only when
  `plan_round_block` reaches a supermajority (`blocklace_sync.rs:3341`). If rounds cannot
  advance, staged turns never drain and `block_height` stays at genesis — the
  round-advancement / finality-gate concern the n=3 lane owns (S5-1, documented at
  `blocklace_sync.rs:470-500`).
- **`execute_finalized_turn` provisions the turn's actor cell AND transfer destinations**
  (`blocklace_sync.rs:4536-4541`). Provisioning is byte-deterministic: `SignedTurn.signer`
  is carried in the block and its signature is verified at `blocklace_sync.rs:4308-4316`,
  so every node inserts the identical stub — the same uniformity argument
  transfer-destination provisioning relies on
  (`provision_transfer_destinations_is_deterministic_and_idempotent`,
  `blocklace_sync.rs:6729`).

---

## 4. The path's design (formerly the "fix design" — implemented)

The external-turn path = **caller-signed turn → deterministic actor provisioning at
finalization → uniform cross-node execution**, decoupled from the node operator's chain.

1. **`/turns/submit` is THE external client path, decoupled from the node chain.** The
   `previous_receipt_hash` gate and `append_receipt` apply only to the operator's own
   agent (`api.rs:3502-3525`, `:3633-3634`). A foreign-agent turn's local run is an
   optimistic ack (multi-party rolls the journal back, `api.rs:3592-3598`); the
   finalization pass is the sole authoritative application — the posture the faucet
   pioneered with its scratch clone.

2. **The ACTOR cell is provisioned at finalization, deterministically.**
   `provision_signer_actor_cell` (`blocklace_sync.rs:8243`) runs in
   `execute_finalized_turn` before `execute_via_producer` (`blocklace_sync.rs:4536`),
   inserting `derive_raw(SignedTurn.signer, "default")` as a zero-balance stub if absent.
   A fresh client's FIRST turn finalizes cross-node instead of `cell not found`.

3. **`/turn/submit` stays an operator-only endpoint.** The confused-deputy hardening
   (`api.rs:3075-3084`) stands — do NOT relax it; client turns go through the
   caller-signed path.

Net: a client builds a `SignedTurn` over its own cell, `POST /turns/submit` injects it to
the blocklace, the round producer carries it, and `execute_finalized_turn` provisions the
actor + applies it uniformly on every node.

---

## 5. Interaction with the n=3 finality-gate lane

The pipeline has two sequential gates; this doc's gate (submit → DAG) is wired, and the
second is the n=3 lane's territory:

```
external client turn
   │  [submit → DAG]          — /turns/submit + actor provisioning (wired, §2b/§4)
   ▼
blocklace DAG (staged in a round block)
   │  [finality-gate]         — plan_round_block supermajority / tau super-ratify
   ▼                             (blocklace_sync.rs:3341, cadence at :3716)
execute_finalized_turn fires on every node   (blocklace_sync.rs:4287)
```

A staged turn still finalizes only when rounds advance (`plan_round_block` supermajority;
the S5-1 round-synchronous-shape analysis, `blocklace_sync.rs:470-500`) — that gate is a
performance/liveness concern tracked by the n=3 finality-gate lane, not a gap in the
submit wiring.
