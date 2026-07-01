# DreggNet — the agent in the world

*The reach vision: an autonomous agent that does not just run inside a sandbox but
**reaches out** — acquires real compute, moves real money, calls real services,
reads and writes real data, and composes with other agents — and gives you back a
**proof of everything it did** and a **hard bound on everything it could have done**.*

*Read this for the SHAPE. Status language matches the repo's grading: **LIVE** =
code-proven here (mostly the local / in-process path), **PARTIAL** = core wired with
a named seam, **GAP** = designed not built. Verify any LIVE/PARTIAL claim against
HEAD before relying on it. Companion grounding: `docs/VISION.md` (the category),
`docs/VISION-NEXT-PRODUCT.md` (the wedge), `docs/RECEIPT-CONTRACT.md`,
`docs/REPLENISHING-BUDGET.md`, and on the substrate side `~/dev/breadstuffs`
(`sdk/src/service_economy.rs`, `bridge/`, `captp/`, `dregg-merge/`,
`metatheory/Dregg2/Deos/`).*

---

## 0. The thesis — autonomy and safety are the same primitive

Every agent platform today buys autonomy and safety from different shelves. The
model is autonomous because you handed it tools and a loop; it is "safe" because of
a system prompt, a moderation pass, an allow-list of tool names, and a human who
reads the logs *after*. The leash and the audit do not travel with the authority —
they live in the harness, and the moment the agent's action leaves the harness (an
API key in an env var, a wallet the tool can sign with, a shell that can `curl`
anything), the bound is gone and the record is whatever the host chose to write.

dregg collapses that split. The same three things that let an agent *act* are the
same three things that *bound and prove* it:

1. **a budget cell** — its allowance. Every action draws from it; an exhausted
   budget refuses the next action **in-band**, so a runaway is rate-bounded *by
   construction*, not by a watchdog. The un-drawn headroom is a hard ceiling on
   everything the agent could still have done.
2. **a capability** — its reach, narrowly. An attenuable `dga1_` credential (the
   powerbox) names exactly which services it may invoke, which cells it may touch,
   which destinations it may reach. A sub-agent can only ever get a *narrower* cap.
3. **a receipt chain** — its record. Every admitted action seals into a prev-hash-
   linked, signed record that a non-witness re-verifies without trusting the host.

This is already a runnable braid, not a slide. `exec/src/agent.rs` is the whole
loop in one file: `AgentCloud::run` drives a brain's decided `AgentAction`s and for
each one **(1)** cap-gates it against the bundle (`Credential::verify`,
`agent.rs:1013`), **(2)** draws the cost from the replenishing-budget cell
(`Meter::draw`, `agent.rs:1036`), **(3)** runs it, **(4)** seals a chained
`AgentReceipt` (`agent.rs:1114`). `verify_agent_run` (`agent.rs:624`) re-witnesses
the chain, confirms consumption stayed under the ceiling, and confirms the proof
and the bound agree — *needs only the report, trusts no host.*

> The pitch made concrete: **give an autonomous agent a budget and a capability;
> get back a proof of everything it did and a hard bound on everything it could have
> done.** Autonomy is what the cap *grants*; safety is what the same cap *withholds*.
> They are one object.

The rest of this doc is what happens when that object stops pointing at a mock tool
and starts pointing at the world.

---

## 1. Acquiring resources — an agent that provisions itself

An autonomous agent's first real-world act is usually *getting something it needs*:
more compute, storage, a paid API, or a sub-agent to do part of the job. In dregg
each of these is a **turn against a cell, drawn from the budget, gated by a cap, and
receipted** — so an agent can provision itself and you can read back exactly what it
leased and what it spent.

- **Compute** — the execution lease is the unit. A funded dregg `execution-lease`
  authorizes a workload (lessee · cap-grade · asset · budget); DreggNet's bridge
  maps the cap-grade → a polyana sandbox tier and runs the workload, ticking a meter
  against the lease budget (`bridge/src/lib.rs`, the 5-step weld). On the substrate
  side the same shape is `ExecutionLease::open/fund/run`
  (`breadstuffs/sdk/src/service_economy.rs:328`): `open` spawns a cap-scoped worker
  and installs a `FieldLte ∧ Monotonic` meter program on the lease cell; `fund` moves
  value in with a conserving `Effect::Transfer`; `run` advances a durable checkpoint
  the executor gates — *a run past `max_steps` is rejected by the executor, not by
  the runtime's good behavior.* **LIVE** on the local/in-process path.
- **The compute market is autonomous.** `control/src/orchestrator.rs` is a real
  daemon (`run_until_shutdown`) that, every tick, watches funded leases → picks a
  healthy backend (failover-aware, `control/src/fleet.rs`) → dispatches the durable
  metered workload over the mesh → settles each metered period as one **conserving,
  exactly-once** `Effect::Transfer` lessee → backend → reaps a lapsed lease. So an
  agent that holds a funded lease genuinely *rents compute from a fleet it does not
  own*, and the provider gets paid per proven period. **LIVE** (loop, pick, dispatch,
  settle); **PARTIAL** for reading leases off a *live* dregg node (the `dregg-verify`
  decode is real; the light-client RPC transport is the named seam).
- **Storage / data** — a workload reads and writes its own committed cell heap
  mid-execution: `cell_read` / `cell_write` over the host-API
  (`exec/src/host_api.rs:545`), each a `filesystem:read` / `filesystem:write` effect
  the cap-gate must admit. State is umem (universal memory) — portable, witnessed,
  committed to a root that a write moves. **LIVE** in-process.
- **A service** — `invoke(service, args)` calls a gateway-registered service through
  the ToolGateway rail (below). Acquiring the *right* to call it is just holding the
  `invoke:<service>` cap; *exercising* it spends budget and (if priced) moves value.
- **A sub-agent** — `AgentCloud::deploy_subagent` (`agent.rs:916`) opens a child
  budget cell attenuated off the parent (the meter **refuses** a child that asks for
  a larger ceiling or faster refill) and a child credential genuinely attenuated off
  the parent's real cap chain. A child cap the parent never held is refused up front
  (`AgentError::Widen`) and is unreachable on the wire even if it weren't. **LIVE.**

The common shape: **the budget cell is the allowance, the cap is the reach, and
every acquisition is a receipted turn.** You can hand an agent a wallet-sized budget
and a tightly-scoped cap and let it provision its own stack — and the run report
tells you, line by line, what it leased and what headroom it never touched.

---

## 2. Acting in the world — real money, real services, real data, all provable

This is the part the sandbox alone cannot give you. Fly Machines and Cloudflare
Workers can *isolate* your code; what they structurally cannot give you is a guest
that, **from inside the sandbox, mid-execution**, calls a verified service, moves
value, reaches a real endpoint, and leaves a receipt for each move. That inner
affordance is `exec/src/host_api.rs` — the workload as a **transacting agent**.

### 2.1 Move real money — the value bridges

An agent moves real value across the dregg boundary through the breadstuffs bridge
rails. Each rail ties an off-dregg settlement to an on-dregg conserving effect
(`Σδ=0`) with a global double-spend nullifier, so a mint cannot be replayed and the
mirrored supply can never exceed what was actually locked/paid.

| Rail | Direction | Mechanism | Trust grade | Maturity |
|------|-----------|-----------|-------------|----------|
| **Solana** | inbound | lock → federation Ed25519 attestation → conserving mint; `live_supply ≤ locked` (`bridge/src/solana_mirror.rs`) | trusted oracle (or consensus-verified lock path) | **production-shaped**; SPL `$DREGG`, finalized-only relayer, TLS-required |
| **Stripe** | inbound | payment → HMAC-SHA256 webhook → conserving mint; `live_supply ≤ paid` (`bridge/src/stripe_mirror.rs`) | trusted oracle (Stripe signature) | **production-shaped**; real webhook verification, 5-min replay window |
| **Ethereum** | inbound | finalized deposit log → JSON-RPC observation → conserving mint (`bridge/src/ethereum_relayer.rs`) | `StructureOnly` (RPC finality) | **production-shaped off-chain**; in-circuit beacon-LC route is horizon |
| **Ethereum** | outbound | recursive STARK → Groth16 wrap → Solidity verifier (`bridge/src/ethereum.rs`) | SNARK | **GAP** — scaffold complete (calldata, public-input binding, state machine), the STARK-verifier Groth16 circuit is out-of-repo |
| **Mina** | settlement | BLAKE3 binding-commitment + relay/finality observation (`bridge/src/mina.rs`) | binding-commitment only | **demo/scaffold** — no in-circuit STARK verify yet |

So an agent that holds a value cap can, **today**, accept a customer's Stripe
payment or a Solana deposit as a dregg-side credit, then spend that credit on
compute leases and paid service calls — and the whole money-in → work → money-out
flow is one re-witnessable receipt log. Outbound EVM settlement and proof-carrying
Mina are the named horizon (they wait on a SNARK wrapper / an audited in-circuit
verifier, not on dregg-specific design).

A subtlety worth stating plainly: bridge mints are **not** metered separately — an
agent's authority gates the *authorization* (the macaroon's `action_allowed` /
`budget` / `revocable` facts, `bridge/src/authorize.rs`) and the *payment*
(execution-lease budget), and the conserving effect rides the executor. Value moves
only inside a turn the cap admitted.

### 2.2 Call real services — the ToolGateway rail, cap-gated to real APIs

`invoke` is the agent economy's "pay to call agent B's tool" shape, realized as a
real metered, cap-gated, conserving, receipted call (`host_api.rs:418` `dispatch`):

- **cap-gated** — the effect *class* runs through dregg's proven monotone
  attenuation law `gate_effect_set` (`host_api.rs:442`); a lease without the
  `tool-call` class genuinely cannot invoke, and a finer per-service allow-set scopes
  *which* services below the class. A service that is *implemented* on the broker but
  not *authorized* by the lease is still refused `not-an-attenuation`.
- **metered + paid** — an over-budget call is refused before it runs; a priced call
  moves the provider's per-call `price` from the consumer to the provider as a
  conserving `Σδ=0` value move riding the same call, and an insolvent or
  over-value-budget call is refused **`402` before the call runs** (`host_api.rs:494`),
  so no value moves and no work happens.
- **receipted** — a committed call chains a `TurnShadowReceipt` naming the service
  *and* the amount paid, so the run is a re-witnessable audit of
  *who-called-what / paid-whom / wrote-which-cell*. **LIVE** (proven from a real
  CPython/Node guest mid-execution, `host_api.rs:1152`).

The "real API" reach is the cap-gated egress wall, `exec/src/egress.rs` — **deny by
default**. A workload reaches *nothing* on the network unless a cap named the
destination (`egress:api.openai.com:443`, `egress:*.internal:8080`,
`egress:10.0.0.0/8:*`). Attenuation can only *remove* an `egress:` cap, so a
sub-agent's reach is a subset of its parent's. The policy projects into the real
wasmtime WASI network policy (deny-all → `allow_tcp(false)`; a grant →
`socket_addr_check` admitting *only* the named pairs, proven against polyana's own
projection at `egress.rs:982`), and egress is **metered like bandwidth** — a mining
/ DDoS / exfil loop hits a hard `402` ceiling, and every grant exercised or refused
is logged. So "the agent may call OpenAI and Stripe and nothing else" is a *cap*,
not a hope, and the audit shows exactly what it reached. **LIVE** in-process
(wasmtime); **PARTIAL** for the firecracker live-netns enforcement (the allowlist is
computed, the host tap/route install is the named seam; until then the microVM boots
with *no* network interface unless the allowlist is non-empty).

### 2.3 Read/write real data and publish

The agent's real "hands" are the toolkit (`exec/src/agent_toolkit.rs`): `run_tests`,
`verify_deploy`, `check_health`, `verify_receipts`, `run_workload` — each behind the
same `invoke` rail, so each is cap-gated, metered, and its **verdict is bound into
the signed receipt**: the agent *cannot claim a green test it did not run*. Better,
the compute-tier tools bind a `WitnessedRun` — `(command · code_root · result)` —
and `verify_witnessed_qa` (`agent.rs:754`) re-executes the bound and rejects a
verdict the execution does not reproduce, *and* checks the tested code root equals
the deployed `content_root`. So a self-deploying agent's "I built it, tested it, and
shipped it" is a proof that *these tests ran on the deployed code with this result*,
not a runtime's say-so. Publishing (static-site hosting where a site IS a cell
carrying a `content_root` commitment, `webapp/src/hosting.rs`) is the same: served
bytes re-witness against the committed root. **LIVE** on the local path; the honest
residual is that re-execution still runs in the same substrate — full
operator-independence wants the tier run attested by the federation light client
(the in-circuit witness, the circuit-soundness lane).

**The whole of §2 in one line:** the agent does *real things* — moves money, calls
services, reaches endpoints, writes data, ships sites — and you get a proof of
everything it did and a bound on everything it could.

---

## 3. Composing with other agents — cap-secured ecosystems

A single bounded agent is useful; a *market* of them is the prize. dregg's
composition primitives already exist on the substrate, and they compose with each
other.

- **Delegate an attenuated cap.** The cap algebra is a subset lattice with a
  structural proof: `is_attenuation`/`attenuate_in_place`
  (`breadstuffs/cell/src/capability.rs`) narrows permissions (an `AuthRequired`
  lattice), the effect mask (a bitwise subset over 26 effect types — TRANSFER, MINT,
  GRANT_CAPABILITY, …), and the expiry (can only move *earlier*), and **rejects any
  widening**. Macaroon caveats only ever *add* constraints (the HMAC chain,
  `macaroon/src/macaroon.rs`). So a sub-agent provably **cannot exceed what you
  granted** — the no-amplify property is enforced by the structure, re-checked on the
  wire, and (in DreggNet's onramp) enforced again on the budget axis
  (`deploy_subagent`). **LIVE / proven.**
- **Hire a sub-agent on bonded work.** The house capacities give you pay-on-proof.
  **Sealed escrow** (`metatheory/Dregg2/Deos/SealedEscrow.lean`, Rust
  `cell/src/escrow_sealed.rs`) is a 2-of-2 atomic swap: each party locks a leg,
  settlement flips *both* legs to `Consumed` atomically, a re-settle of a consumed
  leg is **rejected**, and the leg status is bound in the committed heap root (a forge
  cannot masquerade). **Standing obligation**
  (`metatheory/Dregg2/Deos/StandingObligation.lean`) is a recurring duty with a
  strictly-monotone cursor: discharged once per period, on schedule — early
  discharge, over-discharge, and replay are each rejected. So "agent A escrows the
  fee, agent B does the work, settlement releases on proof, and a retainer pays B
  per period" is enforced by the executor and machine-checked in Lean, not by trust.
  **LIVE / proven** (the executor tooth is load-bearing; the *circuit* tooth — a
  light client witnessing it, not just a re-executing validator — is the named weld,
  `HOUSE-CAPACITIES-WELD-PLAN.md`).
- **Coordinate offchain — the merge runtime.** Most multi-agent coordination should
  never touch consensus. `dregg-merge` (`breadstuffs/dregg-merge/`) is a CRDT
  join-semilattice: two agents apply ops to their own copies partition-tolerantly,
  then merge deterministically with a re-witnessable `MergeReceipt` and **no chain op
  per merge**. The gate is a dichotomy machine-checked in Lean: an **I-confluent**
  operation (a G-Set grow) merges *free*; a non-confluent one (a balance that could
  overdraft) **escalates to settle** at the federation boundary. So a swarm
  coordinates at memory speed for the common case and only pays for consensus when
  the operation actually needs it. **LIVE / proven** abstractly + Rust executor;
  circuit-weld is phase-C.
- **Compose remote action — CapTP promise pipelining.** `captp/src/pipeline.rs`
  batches a multi-step cross-federation action graph into one round-trip: a sender
  queues `PipelinedMessage`s targeting an unresolved promise, each carrying its own
  `authorization` proof, and the registry drains them in order on resolve (a broken
  upstream promise breaks the dependent results — fork-join). So an agent can express
  "ask B for X, call a method on X, feed the result to C" as one authorized,
  pipelined graph instead of three round-trips, and every hop is cap-checked.
  **LIVE / Lean-gated** resolve.

Put together: an agent **hires** a sub-agent by handing it a narrowed cap (delegate),
**bonds** the work with escrow / a retainer (house capacities), **coordinates** the
fan-out offchain (merge), and **composes** the remote calls in one pipelined graph
(CapTP) — and the whole ecosystem inherits the no-amplify guarantee: no agent
anywhere in the graph can exceed the authority that flowed into it.

---

## 4. Why this is the thing the big agent platforms structurally lack

OpenAI's and Anthropic's agent platforms are excellent at the *loop* — planning,
tool-calling, memory, reflection. What they do not have, and cannot bolt on without
a substrate like this, is **a cryptographic leash and audit that travels with the
authority**:

- their bound lives in the harness (a tool allow-list, a rate limiter) — *outside*
  the authority, so it does not survive the authority leaving the harness;
- their audit is whatever the host logged — *trust the operator*, not verify;
- their delegation is ad hoc — a sub-agent gets the same API key, no provable
  narrowing;
- their spend is reconciled *after* — no in-band ceiling that refuses the action that
  would breach it.

dregg's version is the inversion of each: the bound *is* the cap and the budget cell
(travels with the grant, attenuates with delegation, refuses in-band); the audit *is*
the receipt chain (re-witnessed by a non-witness, host untrusted); the delegation *is*
attenuation (provably narrower); the spend ceiling *is* the meter (refuses before the
breach, not after). **You can hand an agent real-world authority precisely because
you can bound and audit it cryptographically** — and the bound and the audit are not
extra machinery, they are the same primitive that grants the authority.

---

## 5. The killer scenarios

1. **The agent that runs a business.** It accepts customers' payments over the
   Stripe / Solana bridges (money in, conserving mint), leases compute from the fleet
   to serve them (the orchestrator's lease market), calls paid third-party services
   through the ToolGateway rail (pay-per-call, conserving), hires sub-agents for spiky
   work on escrowed bonds (pay-on-proof), and publishes its product as a content-
   committed site. Every dollar in, every dollar out, every service call, every
   deploy is one re-witnessable receipt log — *and the headroom report proves the
   ceiling it never crossed.* You can audit the business by re-witnessing it, not by
   trusting its books. **Reachable** on the inbound rails + local path today; the
   public-edge operation and outbound settlement are the named gaps.
2. **A cap-bounded swarm composing real work.** A coordinator deploys a fan-out of
   sub-agents, each on an attenuated cap and a slice of the budget, coordinating
   offchain through the merge runtime (free for the I-confluent common case),
   composing their remote calls via CapTP pipelining, and escalating to settlement
   only where an operation genuinely conflicts. The whole swarm's authority is a
   provable subset of the coordinator's — no agent can reach past what flowed into it,
   and the merge receipts re-witness the convergence. **Reachable / proven** on the
   substrate; the at-scale operated deployment is the build-out.
3. **Authority you can actually hand over.** The reason you would *never* give a
   today-agent your AWS root, your treasury wallet, or your prod deploy key is that
   you cannot bound or audit what it does with them. dregg makes that a *quantitative*
   decision: grant a cap scoped to `egress:api.stripe.com:443` + `invoke:deploy` +
   a 50-`$DREGG` budget that refills at 10/day, and you have *named and bounded* the
   blast radius — and the receipt chain tells you, verifiably, exactly what it did
   inside that box. The leash is the grant.

---

## 6. Reachable vs horizon (the honest ledger)

**Reachable now (LIVE on the local / in-process path, proven here):**

- the cap-gated + metered + receipted agent loop, with re-witness + the could-have
  bound (`exec/src/agent.rs`);
- the transacting host-API: `invoke` (cap-gated, conserving-paid, receipted) +
  `cell_read`/`cell_write`, driven from a real Python/Node guest mid-execution
  (`exec/src/host_api.rs`);
- deny-by-default cap-gated egress, projected into the real wasmtime sandbox + metered
  like bandwidth (`exec/src/egress.rs`);
- the autonomous compute-lease market (watch → schedule → dispatch → meter → settle
  exactly-once → reap, `control/src/orchestrator.rs`);
- sub-agent attenuation on *both* the cap and the budget axes (`deploy_subagent`);
- the substrate primitives — cap algebra, escrow/obligation, merge runtime, CapTP
  pipelining — proven in Lean and exercised in Rust;
- inbound value: Solana + Stripe (production-shaped), Ethereum-inbound (StructureOnly).

**Named seams (PARTIAL — core wired, one honest gap each):**

- reading funded leases from a *live* dregg node (the verified decode is real; the
  light-client RPC transport is the seam);
- firecracker live-netns egress enforcement (allowlist computed; host tap/route
  install pending — until then microVMs boot networkless);
- the circuit weld of the house capacities (the executor tooth is load-bearing; a
  *light client* witnessing escrow/obligation/merge — not just a re-executing
  validator — is the named weld);
- value-moving host methods `transfer` / `subturn` (deliberately deferred from the
  safe-autonomous host-API batch pending a wider value-authority review).

**Horizon (GAP — designed, not built):**

- outbound EVM settlement (needs the STARK-verifier Groth16 circuit / a SP1·RISC0
  wrapper);
- proof-carrying Mina (needs an audited in-circuit STARK verifier);
- the live public edge + real `$DREGG` billing operated on an open network;
- full operator-independence of the witnessed-QA re-execution (the in-circuit
  federation witness).

The honest line, carried from `docs/VISION.md`: nearly everything LIVE is proven
*built + locally*, not yet *operated on a public edge*. But the **shape** — an agent
as a first-class, cap-bounded, metered, receipted, composable real-world actor — is
not a hope here; it is wired, and every reach above names the primitive it stands on.

---

## 7. The one-paragraph version

dregg turns an AI agent into a **provable real-world actor**: a budget cell is its
allowance, an attenuable capability is its reach, and a receipt chain is its record —
and those same three things are what bound and prove it. With them an agent acquires
compute and sub-agents, moves real money across the value bridges, calls real
services through a cap-gated paid-and-receipted rail, reaches exactly the endpoints
its caps name and nothing else, reads and writes committed state, and composes with
other agents — hiring on bonded escrow, delegating provably-narrower caps,
coordinating offchain through the merge runtime, pipelining remote action through
CapTP. The result is the thing centralized agent platforms cannot offer by
construction: **autonomy and safety as one primitive** — you hand an agent
real-world authority *because* you can bound and audit it cryptographically, and the
leash is the grant.

---

*( ⌐■_■ ) the agent steps out of the box — but the box is a cap, and the cap travels
with it. a small poem for the road:*

> *a budget is an allowance,*
> *a cap is how far it can roam,*
> *a receipt is the trail it leaves —*
> *and all three follow it home.*
