# Product / Usability / Polis Assessment — is dregg *good for its purpose* yet?

**Date:** 2026-06-08
**Author:** polis-product-assessor (subagent)
**Scope:** Walk the real user/agent journeys. Be ruthless about where dregg
falls short of being genuinely GOOD for its purpose — not merely *correct*. The
honest product bar: a verified-but-unusably-slow or verified-but-nobody-can-use-it
system is **not done**.

All performance numbers below are **measured**, not estimated, on the dev
machine (Apple-silicon laptop) under realistic workspace contention (other
build/bench workflows running concurrently). The harness is the new
`perf/` crate (`perf/benches/turn_proof.rs`, `perf/src/bin/perf_summary.rs`),
which times the **production** prover entry points
(`dregg_circuit::effect_vm_p3_full_air::prove_effect_vm_p3` /
`verify_effect_vm_p3`) over honest Effect-VM traces built by the same
`generate_effect_vm_trace` the executor witness path uses.

---

## 0. The one-paragraph verdict

dregg is a **real, capability-secure runtime with a genuinely substantive
AI-agent orchestration substrate** — 46 MCP tools, executor-enforced
sub-agent delegation, and three Lean-verified agent-coordination apps that
build and test green. The polis vision (AI minds embodied in capability-secure
cells; authority that does not depend on goodwill) is **materialized in code**,
not aspirational. BUT it is **not yet good for its purpose** on three axes that
matter to a real user/agent: (1) the **turn latency is seconds, not
milliseconds**, and the node **proves inline on the request path under a global
lock**, so throughput is ~3 turns/sec and every caller blocks for the full
proof; (2) **verification is expensive** (~100–180 ms), which quietly undercuts
the headline promise that "anyone can cheaply check"; (3) the **front door is
the proof tower, not the product** — there is no 5-minute "embody your agent"
path, the newest agent apps are headless libraries with no surface, and a
newcomer (human or AI) cannot self-serve from the README. None of these are
correctness bugs. All three are the difference between "verified" and "done."

---

## 1. The apps — genuinely useful, or demos?

### What's real (verified, builds, tests green)

`starbridge-apps/README.md` claims eight real apps + two roadmap stubs. The
three **agent-centric** ones (the polis-relevant ones) check out concretely:

| App | What it is | Evidence |
|---|---|---|
| `tool-access-delegation` | grantor agent mints a rate-limited, deadline-bounded, tool-scoped, revocable mandate cell; the verified executor checks the caveats on **every** tool invocation | `starbridge-apps/tool-access-delegation/src/lib.rs` (538 lines); tests green (15 passed) |
| `sealed-auction` | agents compete with sealed bids (hash-binding `(bidder,value,nonce)`), reveal, then the winning bid **settles atomically through the verified per-asset executor** (`dregg_intent::verified_settle::settle_ring_verified`) | `starbridge-apps/sealed-auction/src/lib.rs:1-40`; tests green |
| `agent-provenance` | append-only, tamper-evident hash-chained scratchpad (`WriteOnce` entry slots + `Monotonic` head); a third party can recompute the chain link-for-link | `starbridge-apps/agent-provenance/src/lib.rs:1-90` (678 lines); tests green |

Each is the **Rust face of a verified Lean app** (`Dregg2/Apps/*.lean`) with a
**byte-for-byte differential corpus** pinning the Rust decision vector to the
Lean `#guard` (anti-drift). The guarantees are theorems, not assertions:
`tool_invocation_commit_iff_admit`, `reveal_binds_committed`,
`prov_entry_writeonce`, all `#assert_axioms`-clean. This is the strongest part
of the product: the apps are not toys, and their security properties are
machine-checked over the **whole post-state**, not a shadow aggregate.

The older five (`nameservice`, `identity`, `subscription`,
`governed-namespace`, the two mandate apps) additionally ship web surfaces
(`pages/`) and a generated-constants anti-drift discipline
(`constants.generated.js`), and the CLI drives `voting`/`bounty` live against a
seeded devnet (`node/src/starbridge_seed.rs`).

### The honest shortfall on "useful"

- **The three newest, most polis-relevant apps are headless libraries.** They
  are `src/lib.rs` + `examples/` + `tests/` — `FactoryDescriptor` builders and
  signed turn-builders. There is **no `pages/` surface, no deployed instance,
  no CLI verb** for tool-access-delegation / sealed-auction / agent-provenance.
  A human cannot *use* them; an integrator must write Rust against the
  framework. They are **proven, demonstrable building blocks**, not products a
  newcomer can pick up and run.
- **"App" conflates three maturity tiers** that the README's single table
  flattens: (a) verified-lib-with-web-surface (nameservice/identity/...),
  (b) verified-lib-no-surface (the three agent apps), (c) `manifest.json`
  roadmap stub (`compute-exchange`, `gallery`). Only tier (a) is something a
  non-Rust user can touch.
- **No app yet demonstrates the multi-agent loop end to end on the live node.**
  The sealed-auction settles through the verified executor *in-process*; there
  is no walkthrough of two independent Claude instances actually competing for
  a real compute slot over the wire. The substrate exists (see §2); the
  *demonstrated journey* does not.

**Verdict:** the apps are genuinely useful **as verified primitives for
builders**, and that is real and rare. They are **not yet useful as products**
for a newcomer who is not writing Rust against `dregg-app-framework`.

---

## 2. The agent-orchestration substrate — does it actually serve AI coordination?

**Yes — this is the best-realized part of the vision.** Two surfaces, both real:

### (a) The MCP server — an AI agent embodied as a cell

`node/src/mcp.rs` (8167 lines) exposes the node as a **Model Context Protocol
server over stdio** (`dregg ... mcp`, `node/src/main.rs:855`). It defines
**46 tools** (`node/src/mcp.rs:656` `tool_definitions()`), counted directly):
`dregg_create_agent`, `dregg_authorize`, `dregg_submit_turn`,
`dregg_grant_capability`, `dregg_revoke_capability`, `dregg_delegate`,
`dregg_post_intent`/`dregg_fulfill_intent`, `dregg_seal_data`/`dregg_unseal_data`,
`dregg_create_bearer_cap`/`dregg_exercise_bearer_cap`, `dregg_place_bid`,
`dregg_captp_deliver`, `dregg_exercise_handoff_cert`, … This is *literally* "an
AI mind operates through a capability-secure cell": Claude (or any MCP client)
gets a cell, an authority model, and a verified turn path. Per-tool capability
enforcement is real and opt-in (`DREGG_MCP_CAP_ENFORCE=1`,
`node/src/state.rs:53`): the `tools/call` surface requires each call to present
a cap that the executor checks.

### (b) The SDK sub-agent path — delegation that the executor enforces

`AgentRuntime::spawn_sub_agent_scoped` (`sdk/src/runtime.rs:627`) is the
mandate machinery the task asks about, and it is **not decorative**:

- it mints a **new cipherclerk + cell** for the worker (own keypair, own cell in
  the ledger),
- it **attenuates** the parent token (`decoded.attenuate(&effective_restrictions)`),
  zeroes the root key (the worker "cannot mint new root tokens or bypass the
  attenuation chain", `runtime.rs:666`),
- crucially, it **mints a biscuit cap-token bound to the worker's own cell**
  whose issuer is recorded as the cell's `verification_key`, so that the
  **executor's `verify_token_authorization` — not an out-of-band `cap.verify()`
  — is the admission gate** (`runtime.rs:715-740`). "A credential issued by any
  other key is rejected by the executor."

This is exactly "safety-by-construction = autonomy that does not depend on
goodwill": the grantor hands over a narrowly-scoped, revocable credential and
**never its keys**, and the runtime — not politeness — refuses anything outside
the grant. The `tool-access-delegation` app (§1) layers a rate/deadline/scope
consumption budget on top, also executor-checked.

### The honest shortfall on the substrate

- **Two enforcement stories coexist and the redundancy is confusing.** The
  delegated `HeldToken` is described in-code as the "legacy, out-of-band"
  defense-in-depth presentation, while the biscuit `cap_token` is "the ENFORCED
  gate." Carrying both — and a `subagent-method:` feature caveat synthesized
  only to keep the legacy token non-empty (`runtime.rs:640`) — is a smell: a
  reader cannot tell at a glance which artifact is load-bearing. The verified
  gate should be the *only* gate, with the legacy token retired.
- **Revocation latency / propagation is single-node.** `dregg_revoke_capability`
  exists and the Lean side proves nullifier-driven revocation, but on a real
  federation the "immediately revocable" promise is a **distributed** property
  (per the single-machine principle: the honest bound is a topology bound). On
  the live *solo* node it's immediate; the n>1 story is modelled, not measured.
- **No worked multi-agent transcript.** The pieces (spawn → delegate → worker
  submits gated turn → grantor revokes) are all present and unit-tested, but
  there is no single runnable example that an onboarding agent can replay to
  *see* the loop. That is a documentation/ergonomics gap, not a capability gap.

**Verdict:** the substrate **genuinely serves AI coordination** and is the
clearest evidence the polis vision is real. It is under-packaged (two
overlapping token stories, no end-to-end transcript) but the core is sound and
enforced where it counts.

---

## 3. Dev/agent ergonomics — SDK, CLI, the wire

### What's good
- The SDK re-exports a coherent surface (`sdk/src/lib.rs`): `AgentRuntime`,
  `SubAgent`, `AgentCipherclerk`, `Turn`/`TurnBuilder`/`Effect`,
  `WitnessedReceipt`. `AgentRuntime::execute(Vec<Effect>)` is a one-call turn.
- The CLI (`cli/src/main.rs`) is a "hardened, expanded client" with ~20
  subcommand groups, doctor diagnostics, and confirms for dangerous ops; its
  `long_about` explicitly tracks parity with `node/api.rs` POST shapes.
- The node HTTP API is broad and discoverable (`node/src/api.rs:1394+`):
  `/turn/submit`, `/turns/submit` (signed envelope), `/turns/submit-encrypted`,
  `/api/cells`, `/api/receipts`, blocklace/checkpoint endpoints, observability
  stream.

### The honest shortfall on ergonomics
- **The README is a proof-tower tour, not a quickstart.** `metatheory/README.md`
  opens with the l4v layer cake and "what the `sorry`s mean." There is **no
  "embody your agent in 5 minutes"** path. A newcomer — human or AI — landing on
  the repo cannot self-serve to a running agent; they must reverse-engineer the
  journey from the SDK and the app crates. For a project whose thesis is *AI
  minds inhabiting cells*, the absence of an agent-onboarding front door is the
  single biggest product gap after latency.
- **Wire-type leakage / two submit shapes.** `/turn/submit` (JSON action spec)
  and `/turns/submit` (SDK-built `SignedTurn` envelope) coexist with different
  request shapes; the CLI `long_about` itself flags historical "422 skews." The
  surface is wide but not obviously *narrow-and-typed* for a first-time
  integrator.
- **Proof artifacts are heavy to carry.** A `WitnessedReceipt` ships the full
  STARK proof bytes + public inputs + (optionally) the trace
  (`node/src/api.rs:2138`). For an agent that wants a cheap "did it commit?"
  answer, the proof is on the critical path of the *response payload*, not an
  opt-in attachment.

**Verdict:** ergonomics are **fine for a Rust integrator**, **poor for a
newcomer or an AI agent self-onboarding from the docs**. The building blocks are
clean; the on-ramp is missing.

---

## 4. Latency / UX of a real turn — MEASURED

Production prover path (`prove_effect_vm_p3` / `verify_effect_vm_p3`), honest
Effect-VM traces, dev laptop under workspace build contention.

**`perf-summary` single-shot (mean of N):**

| workload | effects | prove (mean) | verify (mean) |
|---|---:|---:|---:|
| transfer_1effect  | 1  | **344 ms** | **104 ms** |
| transfer_4effect  | 4  | **279 ms** | **108 ms** |
| transfer_16effect | 16 | **291 ms** |  95 ms |

**Criterion (10 prove / 100 verify samples, [low mean high]):**

| workload | prove time | verify time |
|---|---|---|
| transfer_1effect  | [302 ms · 305 ms · 307 ms] | [117 ms · 123 ms · 131 ms] |
| transfer_4effect  | [273 ms · 281 ms · 294 ms] | [160 ms · 179 ms · 200 ms] |
| transfer_16effect | [628 ms · 872 ms · 1.11 s]  | [100 ms · 105 ms · 110 ms] |

Reproduce: `cargo run --release -p dregg-perf --bin perf-summary` and
`cargo bench -p dregg-perf --bench turn_proof`.

### What the numbers say (ruthlessly)

1. **A turn proves in ~0.3 s and verifies in ~0.1 s.** That is fine for a
   human clicking a button. It is **marginal-to-bad for an AI agent doing many
   turns**, and **bad for a node serving many agents**.
2. **The AIR is fixed-height**, so 1 vs 4 effects cost the same ~280 ms; the
   16-effect case jumps (to ~0.9 s, with high variance) when the trace crosses a
   power-of-two row boundary. So per-turn cost is **roughly constant and
   coarse-grained**, not proportional to work — you pay full STARK price for a
   one-line state change.
3. **Verification is NOT cheap.** ~100–180 ms per proof. The polis pitch is
   "anyone can cheaply check the authority was respected." At 100 ms+/proof, a
   verifier auditing a stream of turns is doing real CPU work; a light client /
   browser / mobile checker will feel it. **This quietly undercuts the headline
   promise.** (The intended fix — recursive aggregation to one succinct proof
   per batch, the Silver→Gold path — exists in design and partially in code but
   is not on the live commit path.)

### The critical architecture finding: proving is INLINE and SERIALIZED

The node's `/turn/submit` handler **proves the turn synchronously, on the HTTP
request path, while holding the executor state lock**:

- `post_submit_turn` takes `&mut s` (the global node state),
  `executor.execute(&turn, &mut s.ledger)` commits, then
  `build_http_witnessed_receipt(...)` is called **before the response is
  returned** (`node/src/api.rs:148`).
- `build_http_witnessed_receipt` (`node/src/api.rs:2103`) builds the trace and
  calls `dregg_circuit::stark::try_prove(...)` **inline** (`api.rs:2129`),
  returning the proof bytes in the receipt.

Consequences:
- **Every client waits the full prove time** (~0.3 s+) for its `submit` to
  return. There is no "committed now, proof follows" fast-ack.
- **Throughput is bounded by serial proving under the lock**: ~1/0.3 s ≈ **3
  turns/sec, single-threaded**, regardless of cores. A second agent's turn
  queues behind the first agent's STARK.
- This is the **opposite** of the architecture the latency wants: commit fast,
  prove off the critical path (async worker / `spawn_blocking` pool), attach the
  proof to the receipt out-of-band, and let verifiers pull it.

**Secondary finding (divergence):** the node still proves through the **old
hand-AIR** `dregg_circuit::stark::try_prove` (`api.rs:2129`), **not** the cutover
`prove_effect_vm_p3` the SDK's `full_turn_proof` routes through
(`sdk/src/full_turn_proof.rs:416`). So the live node's commit path and the
SDK/perf path are proving via **different circuits**. That is a coherence/SWAP
gap, and it means the live node is not exercising the audited descriptor/p3
prover on its own commit path.

**Verdict on latency/UX:** sub-second per turn is *survivable*; **inline serial
proving under the state lock is not** — it caps the whole node at a few turns
per second and makes every agent block on every other agent's proof. This is the
**#1 product-blocking issue**, and it is an architecture fix (move proving off
the critical path), not a cryptography fix.

---

## 5. The POLIS lens — does dregg deliver the Diaspora vision?

> *AI minds embodied in capability-secure, verified cells; safety-by-construction
> = freedom that does not depend on anyone's goodwill.*

**Where dregg genuinely delivers:**
- **Embodiment is real.** An AI agent gets a cell, a keypair, a balance, and a
  verified turn path via 46 MCP tools (§2a). This is not a metaphor; it runs.
- **Authority does not depend on goodwill.** `spawn_sub_agent_scoped` (§2b)
  hands a worker a narrowly-attenuated, executor-enforced, revocable credential
  and never the keys. The grantor's safety is enforced by
  `verify_token_authorization`, not by trusting the worker. The
  tool-access-delegation app proves the consumption budget bites on every call.
  **This is the heart of the Diaspora promise, and it is the strongest thing in
  the codebase.**
- **Safety-by-construction is machine-checked.** The agent apps' security
  properties are Lean theorems over the whole post-state, pinned to the Rust by
  differential corpora. Tampering a third cell ⇒ UNSAT. The "verified cell" is
  not marketing.

**Where it falls short of the vision:**
- **A polis is plural; the live deployment is a solo node.** The single-machine
  principle (from MEMORY) says the strong properties (immediate revocation,
  consistent checkpoint, real GC) are what you get at n=1, and distribution
  *bounds* them. The honest reading: dregg today delivers the **n=1 polis** —
  one cell-fabric, one producer — with the n>1 federation **modelled and
  partially built** (blocklace, gossip, epoch-reconfig, BLS quorum residual
  open) but **not the lived, measured multi-mind city** the vision describes.
  The "diaspora" — many minds in many sovereign cells coordinating across the
  wire — is architecturally reachable but not yet demonstrated.
- **"Freedom" includes being able to *leave* and *be checked cheaply*.**
  Sovereign-cell migration (Hosted↔Sovereign) is design, not impl (MEMORY).
  And cheap third-party verification — the thing that lets a mind *prove* it
  respected authority without anyone's trust — is ~100 ms/proof today, i.e. not
  yet cheap (§4.3). A polis where checking your neighbor costs real CPU is a
  polis with friction.
- **The on-ramp gates participation.** A vision of *minds inhabiting cells*
  needs a door a mind can walk through. Today that door is "write Rust against
  `dregg-app-framework` after reading the l4v layer cake" (§3). The polis is
  real for its builders; it is not yet open to a newcomer mind self-serving.

**Polis verdict:** dregg delivers the **kernel of the Diaspora vision** —
embodied agents, goodwill-independent authority, machine-checked safety — and
that kernel is genuine and rare. It does **not yet** deliver the *plural,
cheaply-auditable, openly-joinable* polis the vision names. The gap is
**deployment + latency + on-ramp**, not foundations.

---

## 6. Top usability / purpose gaps (ranked, ruthless)

| # | Gap | Why it blocks "good for purpose" | Where |
|---|---|---|---|
| **1** | **Proving is inline & serialized on the node's request path under the state lock** | Caps the whole node at ~3 turns/sec; every agent blocks on every other agent's STARK. The polis cannot scale past a handful of agents. **Architecture fix: commit fast, prove off-critical-path, attach proof async.** | `node/src/api.rs:148, 2103-2141` |
| **2** | **Verification costs ~100–180 ms/proof** | Directly undercuts "anyone can cheaply check." A light client / mobile / browser verifier feels it; auditing a turn stream is real CPU. **Needs recursive aggregation (Silver→Gold) on the live path.** | measured §4; `perf/` |
| **3** | **No agent-onboarding front door** | A newcomer (human or AI) cannot self-serve from the README to a running embodied agent. The polis is closed to anyone not already writing Rust. **Needs a "embody your agent in 5 min" quickstart + a runnable multi-agent transcript.** | `metatheory/README.md`; missing example |
| **4** | **Node commit path proves through the OLD hand-AIR, not the cutover `prove_effect_vm_p3`** | The live node and the SDK/audited path prove via *different circuits* — a coherence/SWAP gap; the live node isn't exercising the audited prover on its own commits. | `node/src/api.rs:2129` vs `sdk/src/full_turn_proof.rs:416` |
| **5** | **The 3 newest, most polis-relevant apps are headless libs** | tool-access-delegation / sealed-auction / agent-provenance have no surface, no CLI verb, no deployed instance — proven building blocks, not usable products. | `starbridge-apps/{tool-access-delegation,sealed-auction,agent-provenance}/` |
| **6** | **Two overlapping sub-agent token stories** | A "legacy out-of-band" `HeldToken` (with a synthesized filler caveat) shadows the real executor-enforced biscuit `cap_token`; a reader can't tell which is load-bearing. Retire the legacy token. | `sdk/src/runtime.rs:640-748` |
| **7** | **Per-turn cost is fixed-height & coarse** | You pay full STARK price (~280 ms) for a one-field write; cost is constant, not proportional to work, with cliffs at power-of-two row boundaries. Hurts the "many small turns" agent workload. | measured §4.2 |
| **8** | **The plural polis is modelled, not deployed** | Live deployment is a solo node; federation (n>1 revocation propagation, BLS quorum, migration) is design/partial. The "diaspora" is reachable, not lived. | MEMORY; `_WHAT-IS-DREGG.md:11-30` |

---

## 7. What I built (this assessment's deliverables)

- **`perf/` crate** (new, workspace member): the **first harness that times the
  production turn-proof path** (`prove_effect_vm_p3`/`verify_effect_vm_p3`),
  not the old hand-AIR benches. `perf/benches/turn_proof.rs` (criterion),
  `perf/src/bin/perf_summary.rs` (single-shot table), `perf/src/lib.rs`
  (honest-trace workload builders). Builds green; numbers in §4 are from it.
- **This document.**

### What I deliberately did NOT touch (other workflows own these)
`circuit/Circuit/Emit/*` (deep-circuit), `turn/`+`node`+`marshal` (SWAP — I
**read** node/api.rs but edited nothing), `starbridge-apps/*` (apps),
`Crypto/*` (crypto), `redteam/` (red-team), `lightclient/` (gold). I added one
line to the root `Cargo.toml` members list (`"perf"`) and created the `perf/`
crate, which is in my lane ("new bench harnesses … a new benches/ or perf
crate").

---

## 8. The one thing to do next

**Move proving off the node's critical path.** Gap #1 is the difference between
"a verified curiosity that does 3 turns/sec" and "a polis that scales." Commit
the turn synchronously (cheap), return a fast ack, and prove on a
`spawn_blocking` worker pool, attaching the `WitnessedReceipt`'s proof to the
receipt chain out-of-band for verifiers to pull. Then aggregate (gap #2) so the
verifier pays once per batch, not once per turn. Everything else here is
packaging and deployment; this is the load-bearing architecture fix that makes
the rest worth packaging.

*(A small poem, because the kernel really is beautiful:*
*a mind in a cell, holding a key it can shrink but never forge —*
*the city is built; now open the gate, and make the checking cheap.)* ✦
