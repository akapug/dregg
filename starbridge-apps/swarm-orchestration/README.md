# starbridge-swarm-orchestration — a verifiable agent-orchestration swarm

Multi-agent task coordination where the **coordination itself** is cap-secured,
receipted, and verifiable — run through the **real verified executor**, not a
mock. An agent loop (perceive / plan / act / reflect) lives ABOVE dregg and is
the integrator's game; dregg owns the ONE seam that matters — the
tool-call / turn boundary — and this app makes that seam legible.

> *four small lies a loop might tell — `authorized, did, paid, am` — four
> receipts the ledger keeps; the swarm cannot pretend.*

## What it is

A **COORDINATOR** dispatch-board cell holds a conserved **budget** + a
**mandate** and dispatches sub-tasks to **WORKER** agent cells. The board is a
factory-born cell whose installed `CellProgram` IS the swarm policy, re-checked
by the verified executor on every turn:

| Slot       | Caveat            | Guarantee |
|------------|-------------------|-----------|
| `LEAD`     | `Immutable`       | the appointed coordinator's identity (the signed-provenance anchor) is pinned |
| `BUDGET`   | `Immutable`       | the spend mandate — never widened mid-swarm |
| `SPENT_A`  | `Monotonic`       | worker-A's cumulative spend never rolls back to forge head-room |
| `SPENT_B`  | `Monotonic`       | worker-B's cumulative spend |
| —          | `AffineLe { spent_a + spent_b − budget ≤ 0 }` | **atomic budget**: the swarm collectively spends at most its mandate |
| `EPOCH`    | `StrictMonotonic` | **no replay**: every dispatch strictly advances the epoch |

## The five things a stranger watches fire

1. **COORDINATE (the wake).** The coordinator dispatches a sub-task to worker-A;
   the async notify edge (`EmitEvent`) deposits a pending wake; worker-A
   **DRAINS** it in its OWN separate receipted turn. **Two distinct receipt
   hashes** — causality (coordinator → worker) is visible, synchronization is
   NOT forced. The corrected `--wake`: async, not a joint turn.
2. **CONSERVE (the budget).** A second dispatch to worker-B stays within the
   mandate; the swarm spent exactly its dispatches (`spent_a + spent_b ≤ budget`).
3. **REFUSE the breach.** A dispatch that would breach the mandate is **REFUSED
   by the executor** (the `AffineLe` budget gate) — fail-closed, no commit. The
   conservation guarantee firing at the swarm layer.
4. **REFUSE the over-grant.** A worker reaching a NON-mandated cell is **REFUSED**
   — the no-amplification guarantee firing; a worker cannot exceed the authority
   it was handed.
5. **PRE-FLIGHT.** The whole dispatch plan is linted by
   `dregg-userspace-verify::analyze()` BEFORE submission — conservation,
   non-amplification, well-formedness — so the stranger sees GREEN before paying
   gas (and sees the toolkit CATCH a malformed plan).

## Run it

```sh
# the runnable demo — watch all five fire, every frame a real verified turn
cargo run --release -p starbridge-swarm-orchestration --example swarm_demo

# the end-to-end executor tests (the two refusal teeth + conservation + the wake)
cargo test  --release -p starbridge-swarm-orchestration --test factory_birth

# the pre-submission assurance (dregg-userspace-verify analyze())
cargo test  --release -p starbridge-swarm-orchestration --test userspace_verify
```

(`--release`: the embedded verified executor is slow in debug.)

## The verified Lean development this mirrors

- **`metatheory/Dregg2/Apps/AgentOrchestrationBudget.lean`** — the dispatch-board
  POLICY as ONE `RecordProgram`: the six primitives buildr/builders/sig/simbi each
  hand-roll UNGATED (cap-gated authority + signed provenance via `senderInField`,
  atomic budget via `affineLe [(1,spentA),(1,spentB)] mandate`, actor-bound baton
  handoff, no-replay `strictMono` epoch, immutable mandate, capped async notify
  wake) — every refusal a theorem (`over_budget` / `replayed_dispatch` /
  `worker_cannot_widen_reach` / … UNSAT vs `honest_dispatch_admits`).
- **`metatheory/Dregg2/Apps/AgentOrchestration.lean`** — the swarm run through the
  KERNEL EXECUTOR: an orchestrator spawns least-privilege workers, delegates each
  an ATTENUATED slice (`worker_authority_subset_orchestrator` =
  `derive_no_amplify`: the worker's authority is a strict subset of the
  orchestrator's), and the whole work-forest conserves
  (`workForest_conserves`).

This crate is the **executable surface**: the policy is the factory descriptor's
`state_constraints` installed as the born cell's `CellProgram`, and every refusal
is a REAL executor refusal — not app bookkeeping.

## The honest static/dynamic boundary

`dregg-userspace-verify::analyze()` is the **static, pre-submission** half: it
reads the dispatch forest (never executes it) and certifies the
userspace-decidable shape — per-asset conservation, in-forest delegation-edge
attenuation, well-formedness. The **dynamic** half — whether the signer actually
HELD the cap (the live c-list lookup), whether balances suffice, the whole-state
commitment — is the executor's job, exercised end-to-end in
`tests/factory_birth.rs`. The two together are the full assurance; neither alone.
