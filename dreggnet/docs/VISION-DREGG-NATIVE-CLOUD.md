# DreggNet, the dregg-native resource cloud

*"Hosting. Resources available."*

*The un-myopic vision. Where `VISION.md` paints the product and `VISION-NEXT-TECH.md`
composes the real primitives, this document recovers the BIGGER frame that scrolled
out of context while the swarm built the generic version: **DreggNet is not a fly.io
clone with a verifiable veneer — it is dregg's own primitives (cell, umem, capability,
the house economy) extended OUTWARD through dregg into the real world, so that every
resource is a first-class dregg object, not reimplemented infrastructure.***

*Read for the SHAPE. Every claim names the primitive it stands on; the honesty grading
(REACHABLE-FROM-HEAD vs HORIZON) is at the foot of each section and verifiable against
`~/dev/breadstuffs` HEAD and the DreggNet crates.*

---

## 0 · The correction — resources, not infrastructure

The swarm built a competent generic cloud: polyana sandbox tiers, a WireGuard mesh, an
object store, a metering pipeline, invoices. It is real and it works on the local path.
But it is built the way *every* cloud is built — machines, registries, and a mesh as
**in-memory generic state with dregg cap-gates bolted on top** (`storage/src/registry.rs`
in-memory; `control/src/mesh.rs` pure WireGuard with no dregg primitive; `storage/src/
bucket.rs:60` content root an FNV stand-in, not a umem root). The verifiability is a
*veneer*: receipts and attestations wrapped around infrastructure that is, underneath,
the same containers-and-Postgres everyone else runs.

That is the myopic version. It answers "can we be a cloud provider?" It does not answer
the question dregg actually poses, which is bigger:

> **What is a cloud when the resources themselves are dregg objects — when a running
> workload IS a cell, a database IS a umem, a service IS a capability, and the economy
> IS the resource layer rather than a billing system stapled to its side?**

dregg's one-sentence through-line is *"a turn is the exercise of an attenuable
proof-carrying token over owned state, leaving a verifiable receipt."* A cloud built on
that sentence does not *manage* resources on your behalf and bill you for them. It hands
you **resources as proof-carrying tokens over owned state** — objects you snapshot, fork,
pass, compose, merge, prove, and attenuate, exactly as you do any other cell. The
infrastructure underneath (real CPUs, real GPUs, real money, real bandwidth) is what the
token is *redeemed against*, not what the abstraction is *made of*.

This is the difference between "we run a Postgres for you" and "your database is a
sovereign umem cell you own, that happens to be materialized on our disks." The first is a
service relationship. The second is **dregg reaching into the real world** — the cell
model, unbroken, all the way down to the metal.

---

## 1 · Compute — a workload is a cell, not a container we manage

### The primitive

A cell is "an isolated agent execution context" (`cell/src/cell.rs:249`) holding four
substances — value, state, authority, evidence. A umem is a witnessed `(domain,key)→value`
store whose committed root is its boundary (`turn/src/umem.rs`, `docs/reference/umem.md`),
and the umem keystone `boundary_init_root_bound` (`UniversalMemory.lean:475`,
`#assert_axioms`-clean) makes a umem **a value you hand off and resume: the receiver
inherits the producer's pin.** On that keystone dregg already built:

- **time-travel** — restore a past image by an O(1) inverse fold over a captured umem
  boundary, *the boundary IS the state* (`turn/tests/umem_time_travel.rs`, `b1bd3305`);
- **continuations as passable umems** — a suspended turn resumes into the running ledger
  rather than re-executing from pre-state (`turn/src/continuation.rs`, `087a4cd7`);
- **composable umem-refs** — a value that IS another umem's boundary root, opened through
  two disjoint init-bindings (`open_through_umem_ref`, `umem.rs:691`).

### The vision

A running workload is **a cell whose state is a umem.** Not "a container we schedule" —
a live dregg object with the cell's whole grammar available to it:

- **Snapshot** is `checkpoint_ledger` / a captured umem boundary — a 32-byte root that
  *is* the entire machine image. You do not ask the provider to snapshot a VM; you take a
  boundary root of your own cell.
- **Fork** is `SpawnWithDelegation` over that boundary — two workloads that share a
  pinned init image and diverge, each sovereign. Fork-a-running-process becomes a kernel
  verb, not a hypervisor trick.
- **Time-travel** is the inverse fold already shipped — roll a workload back to any past
  boundary, fail-closed if the reified image doesn't reproduce the recorded root.
- **Pass** is a `Transfer` of the workload-cell or a `GrantCapability` over it — hand a
  live, mid-execution workload to another agent or human, who resumes it from the
  inherited pin. The continuation machinery already does this for suspended turns.
- **Compose** is the call-forest — a workload that spawns sub-workloads as children of one
  atomic turn, all-or-nothing.

The materialization onto real silicon already exists and is genuinely dregg-native at the
authorization seam: the **execution-lease** (`sdk/src/service_economy.rs:305`,
`starbridge-apps/execution-lease`). A lease cell carries a meter program
`FieldLte{step ≤ max_steps} ∧ Monotonic{step}` (`service_economy.rs:267`) the executor
binds into every committed transition — a rewind to forge head-room is *refused on the
verified commit path*, not by a watchdog. The DreggNet `bridge` crate maps a funded lease's
`CapGrade` → a polyana `CapTier` and runs the workload on real sandboxes
(`bridge/src/lib.rs`): wasmi → wasmtime+fuel → seccomp+Landlock `Caged` → Firecracker
`MicroVm` → GPU passthrough, refusing any silent downgrade (`exec/src/lib.rs`). Metering is
a **conserving `Transfer`** with exactly-once durable settlement (`durable/`,
`control/src/settle_ledger.rs`), so a crash resumes *within the same budget* and never
double-charges.

### The cap grants real seconds — the budget cell IS the scheduler

A capability is not a key in a table — *you hold it iff you can produce its witness*
(`docs/reference/auth.md`). The resource-capability is the budget cell
(`exec/src/budget.rs`, the seL4-MCS scheduling-context shape) which is, at once, a
quantity, a rate (`budget/period`), an authority (attenuable: a child sub-budget provably
cannot over-draw the parent, `budget.rs:523`), AND a schedule (the admission test
`headroom_at(now) ≥ amount` is *"may you run next,"* not just *"may you pay"*). So a cap
that grants 1000 GPU-seconds is not a billing entry — **the cell that decides dispatch is
the same cell that produces the invoice.** Metering and scheduling are one decision on one
object, and multi-tenant fairness is literally the attenuation tree.

> **What no cloud can do:** fork a *running* GPU job into two at a verified snapshot, hand
> one to another agent who resumes it from the inherited pin, and prove to a light client
> holding one root that both forks descend from the same authorized image within the same
> conserved budget — re-executing nothing.

**REACHABLE-FROM-HEAD:** lease → cap-tier → polyana with conserving metered settlement is
wired and runs (`bridge/`, `exec/`, `durable/`). Snapshot/fork/time-travel exist as umem
primitives in breadstuffs (`umem_time_travel.rs`, `continuation.rs`). The PoC is welding
them: a workload-cell whose checkpoint is a umem boundary, forked by `SpawnWithDelegation`.

**HORIZON:** the umem **checkpoint/resume kernel-effect** (Stage B, `UMEM-STAGE-B-DESIGN.md`)
is designed-not-built — a first-class effect emitting a umem-ref and one consuming one. Live
GPU is hardware-gated. A workload's working-set as a load-bearing portable umem is a
prototype (`3911af58c`), not yet production.

---

## 2 · Storage & databases — state is a umem cell, not a Postgres we run

### The primitive

The umem (§1) is dregg's persistent-state primitive, and it is already the substrate of
real stored objects: a per-cell heap is a umem whose boundary equals the committed
`heap_root` (`PerCellUmem.lean`, `f0372f22`); a sovereign **document** rides the heap as a
`DocHeapCell` bound by one committed root (`dregg-doc/src/doc_heap.rs`, `bf5e0154b`); the
receipt chain *is* the persistence layer (`docs/reference/persist.md` — "the database is
the cache, the receipt chain is the truth") with crash-recovery `recover = checkpoint ⊕
overlay` verified (`CrashRecovery.lean`, four `#assert_axioms`-clean theorems). On top sits
the **merge runtime** (`dregg-merge/`): an I-confluent CvRDT join gated by a *proven*
classifier (`Confluence.lean`) that emits a re-witnessable `MergeReceipt` — free merge when
confluent, settle-at-the-boundary when a conserved quantity or a retraction participates
(`SettlementSoundness.lean`).

### The vision

A "database" is **a umem cell you own** — witnessed, portable, composable, mergeable —
*not* a Postgres instance the provider runs and you rent.

- **Witnessed.** Every read is an opening against the boundary root; a tampered value flips
  the root (order-canonical, injective, anti-vacuous — `cell/src/state.rs`). The store
  cannot lie about what it holds; a light client checks the root and learns the whole
  history of every write was authorized and correctly committed, re-executing nothing.
- **Portable.** The umem keystone makes the store a value you hand off and resume. You move
  your database between providers by passing its boundary root; the new host materializes it
  and inherits the producer's pin. No export/import, no dump/restore — the *identity* of the
  database is its root, provider-independent.
- **Composable.** A `UVal::UmemRef` is a value that IS another umem's root (`umem.rs:324`),
  so a database can reference another database and a verifier opens through both via two
  disjoint init-bindings — joins across sovereign stores without trusting either host.
- **Mergeable → multiplayer.** This is the part no managed database has. Two replicas edit
  offline, exchange grow-set deltas **over IPFS by CID** (`dregg-ipfs`: `CID ==
  content_root`, no re-hash), and merge locally with a `MergeReceipt`. The gate decides per
  merge: a collaborative document's edits merge *freely* (confluent, no coordination), while
  a balance overdraft is *refused* and collapses to one netted settle at the boundary. So a
  single cell can carry **both** a grow-only collaborative table **and** a conserved balance
  and know, per write, which is coordination-free and which must settle — the distinction
  CRDT systems cannot express because they forbid linear value outright.

The DreggNet storage face today is a bucket-as-cell with cap-gated receipted mutations
(`storage/src/bucket.rs`) and a zero-trust verified GET. The named debt is exactly the gap
between veneer and primitive: the `content_root` is an **FNV stand-in** (`bucket.rs:60`),
not the Poseidon2 umem root, and the bucket registry is in-memory. Closing that — flip the
root to the real umem `heap_root`, persist the registry as an on-chain cell — turns "an
object store with receipts" into "a sovereign witnessed umem you own."

> **What no cloud can do:** branch your production database like a git repo, let two agents
> write to both branches offline with no coordination, merge them with a proof that says
> exactly which rows merged freely and which conserved quantity had to settle, and hand the
> merged store to a third party who verifies the whole lineage from one root.

**REACHABLE-FROM-HEAD:** bucket-as-cell with verified GET and cap-gated PUT is live
(`storage/`); umem heaps, doc-on-heap, crash-recovery, and the merge runtime + IPFS
round-trip each exist in breadstuffs. The "missing half" (per `ARCHITECTURE-CRITIQUE`) is the
**write/merge runtime** wiring — the `delta_cid` transport adapter + a two-replica driver,
days from HEAD because each half is proven.

**HORIZON:** the FNV→umem-root flip (`dregg-verify`) is reviewed-go, not live; full
on-chain durable registries (R-1 blocker) replace the in-memory `HashMap`s; multi-writer
multiplayer over IPFS at scale is the branch-and-stitch frontier
(`project-distributed-houyhnhnm-frontier`).

---

## 3 · Network & services — a service is a capability you invoke, not a load balancer

### The primitive

A cell already does method dispatch; **cells-as-service-objects** gives that a first-class
typed shape *above* the effect-VM, with no kernel effect (`docs/reference/services.md`).
`invoke()` is the **command** front door (`app-framework/src/invoke.rs`): resolve the
descriptor, route through the verified DFA router (unknown method → fail-closed), cap-gate on
`auth_required`, desugar to an ordinary `Action`. `Reactor` is its **reactive twin**
(`app-framework/src/reactor.rs`): a service declares a `ReceiptFilter` of what cells/ops it
watches and reacts to an on-chain commit with its own receipted turn — *the chain is the
message bus* (the discord-bot exemplar, `7e5c40b9`). And **CapTP promise pipelining**
(`captp/src/pipeline.rs`, `docs/reference/captp.md`) carries a send to a promise that has not
yet resolved — queued, delivered when it settles — with the proven invariant that
*pipelining buys latency, not authority*: every delivered send is re-checked by the same
fail-closed executor (`drainAll_preserves_caps`, `pipelining_preserves_seam`).

### The vision

A service is **a capability you exercise**, and a service *graph* is **promise-pipelined
cap composition** — not a load balancer routing opaque traffic.

- **Invoke = cap-mediated method call.** You don't open a socket to a service; you exercise
  a cap over its cell, and the kernel witnesses the effects. The service cannot do anything
  your cap doesn't grant, and you cannot reach it without producing the witness.
- **Reactor = autonomous on-chain services.** A service that watches the ledger and reacts is
  an agent loop with no poll, no webhook, no trust — the trigger is a committed receipt, the
  reaction is a receipted turn. Compose services by having them watch each other's cells.
- **Promise pipelining = composable service graphs without round-trips.** Build a chain where
  each step targets the previous step's result promise (`pipeline_chain`), across federations,
  and the whole graph executes at the speed of one round-trip — but every edge is re-authorized
  on delivery and a broken promise cascades, installing nothing. This is CapTP's deep idea
  (E, Agoric) braided down into a *witnessed* substrate: a service composition you can prove
  was authority-faithful end to end.
- **The inner host-API → workloads that transact.** A workload running on the lease (§1) is
  itself a cell that can invoke other services and transact — so a hosted process is not a
  sandboxed leaf but a first-class participant in the service graph, cap-bounded.

The DreggNet networking layer today is the honest gap: `control/src/mesh.rs` is pure
WireGuard with *no* dregg primitive — generic overlay routing. The dregg-native reframing is
that **service reachability is a capability, not an IP route**: a workload reaches another
service iff it holds the cap, and the mesh is the transport that *materializes* an exercised
cap edge, not an addressing scheme of its own.

> **What no cloud can do:** wire ten services into a pipelined graph that spans three
> independent providers, execute the whole graph at one-round-trip latency, and prove that
> no service in the chain exercised any authority its caller did not hold — and that when one
> link broke, every downstream effect was un-installed atomically.

**REACHABLE-FROM-HEAD:** `invoke()`, `Reactor`, and CapTP pipelining are all built and tested
in breadstuffs (userspace, no kernel effect). The service-economy SDK already buys/invokes
services over the verified rail (`sdk/src/service_economy.rs`).

**HORIZON:** the `Serviced` cross-cell-read **receipt carrier** (so a light client re-checks a
service *answer*, not just the turn) and the CapTP `InterfaceDescriptor` handshake on
`CapHello` are named-not-built (`cell/src/interface.rs:38`). Reframing the DreggNet mesh as
cap-materialized routing is design work, not yet wired.

---

## 4 · Economy — the house capacities ARE the resource relationships

### The primitive

dregg's "house" is six Lean-verified economic capacities, each a heap-committed cell program
+ invariant + forge-detector, all `#assert_axioms`-clean with a Rust `invariant_matches_lean_rung`
tooth (`project-house-capacities`, `HOUSE-CAPACITY-FRAMEWORK.md`). They sit on two proven reuse
bases — the cap-lattice `attenuate_subset` and the committed-heap-root `root_binds_get`. Under
them is the supply model: per-asset-well `Σδ = 0` (`Σ(holders) + well = 0`,
`.docs-history-noclaude/SUPPLY-MODEL.md`), with cap-gated `Mint` (well → holder, requires a
mint-cap, not bare ownership) and permissionless self-`Burn` (holder → well), conserved across
four independent domains (balance, note, gas, cross-cell — no pay-gas-with-notes attack,
`Conservation.lean:372`).

### The vision

The economy is **not billing bolted onto the resource layer — it IS the resource layer.** Each
house capacity is a real cloud relationship, already proven:

| Capacity | dregg invariant (Lean rung) | The cloud relationship it IS |
|---|---|---|
| **escrow** (sealed) | atomic 2-of-2 swap, one-shot, over-claim rejected (`SealedEscrow.lean`) | **bonded compute market** — a provider posts collateral to prove capacity; the consumer claims settlement when the workload completes; neither leg settles without the other |
| **obligation** (standing) | strict-monotone `next_due` cursor, one discharge/period (`StandingObligation.lean`) | **SLA / subscription** — "deliver N turns/day," cursor-gated to exactly one settlement per period; early/double/skip all refused |
| **vault** | deposit-no-dilution, immune to ERC-4626 inflation (`9fd370c5`) | **tenant value custody** — hold a tenant's balance provably without dilution |
| **membrane** | authority composes by meet, no-amplification enforced twice (`Membrane.lean`) | **sub-tenant isolation** — wrap a sub-tenant in a membrane that provably narrows authority |
| **derived** | value MUST equal f(sources), stale-after-change refused (`DerivedCell.lean`) | **computed allowance / metered view** — a sub-agent's budget as a read-only `FilteredSum` over sources |
| **hatchery** | user-defined verified KINDs, `HpresProof::Attested` a forever-crown (`Hatchery.lean`) | **issuance policy** — define contract-backed resource classes (a "verified GPU-hour," a credential-as-asset) |

And the keystone reframing: **a unit of real resource is an asset well.** A computron, a
GPU-hour, a gigabyte-month, an LLM token — each is an asset with exactly one issuer well; the
genesis mints supply, consumption burns it, conservation holds per-well. The budget cell (§1)
is a holder's balance in that asset, and a `Transfer` *moves computational authority itself*.
So the entire economy — pricing, metering, fairness, bonds, SLAs, custody — is the *same*
conserved-value machinery the protocol already proves, not a separate subsystem. DreggNet's
`StandingObligation` meter and conserving-`Transfer` settlement (`control/src/hosting_meter.rs`,
`settle_ledger.rs`) are already exactly this; the vision is to recognize that the *resources
themselves* are the assets, so there is nothing left to "bill" — using the resource and
conserving the value are one effect.

> **What no cloud can do:** run a permissionless compute market where providers bond escrow
> to advertise real capacity, consumers pay through a cursor-gated obligation, a sub-tenant is
> wrapped in a membrane that provably cannot exceed its grant, and every dollar/GPU-hour/token
> is a conserved asset whose `Σδ=0` a light client checks — an economy that is *proven*, not
> *reconciled.*

**REACHABLE-FROM-HEAD:** all six capacities have Lean rungs + Rust teeth in breadstuffs; the
supply model with cap-gated Mint/Burn is in the executor (`apply_burn`/`apply_mint`); DreggNet's
metering+settlement spine is already conserving-`Transfer` over `StandingObligation`. Modeling
DreggNet's compute/storage/bandwidth as asset wells is a re-grounding, not new crypto.

**HORIZON:** the per-effect in-circuit `budget` field (so a light client witnesses the meter,
not just a re-executing validator) is a named follow-up; the house-capacity **VK weld** (binding
each invariant into the EffectVM) is the one honest seam per capacity
(`HOUSE-CAPACITIES-WELD-PLAN.md`). A real price floor (DreggNet is subsidized today,
`hosting_meter.rs:99`) is a product decision, not a primitive gap.

---

## 5 · The real-world bridge — dregg primitives extended outward

The whole point is that these are not abstractions floating free — they **redeem against real
infrastructure.** dregg reaches the world at four seams, each already partly built:

- **Real compute.** The `bridge` crate is the funded-lease → real-sandbox weld
  (`bridge/src/lib.rs`): a dregg cap-grade authorizes a polyana cap-tier, the workload genuinely
  runs (wasmi/wasmtime/seccomp/Firecracker/GPU), and the meter charges a conserving `Transfer`.
  The authorization is dregg; the silicon is real; the settlement is proven. *This is the
  template for every resource:* a dregg token redeemed against a metered real backend with
  exactly-once durable accounting.
- **Real money.** Value crosses in as a bridged `$DREGG` mirror asset — an ordinary `AssetId`
  you `pay` with (`sdk/src/service_economy.rs`), so paying in real currency desugars to the same
  conserving `Transfer` as any internal move. The `bridge/` crates carry cross-federation note
  proofs (`BridgeMint`) and the foreign-finality light-client seam.
- **Real storage transport.** `dregg-ipfs` makes a dregg blake3 content commitment *be* an IPFS
  CIDv1 (`CID == content_root`) — so the decentralized any-node transport is free and a stored
  object's dregg identity and its network address are the *same* 32 bytes.
- **Real services & identity.** `webauth` cap-accounts are attenuable credentials; the agent
  toolkit produces signed witnessed-execution receipts binding `(command, code_root, result)`
  to a tier (`exec/src/agent_toolkit.rs`), so "this real machine ran this code and got this
  result" is a re-verifiable fact, not an operator's word.

The unifying move: **the dregg object is the source of truth; the real backend is its
materialization.** A workload-cell is materialized on a Firecracker VM; a umem-database is
materialized on redb/IPFS; a service-cap is materialized over the WireGuard mesh; a $DREGG
balance is materialized against a real bank rail. In every case the *abstraction is the cell*
and the infrastructure is interchangeable underneath — which is precisely why your workload,
database, and service are portable between providers: you own the object, not the instance.

---

## 6 · The killer capabilities — what a resource-cloud-as-protocol can do

Compose the five primitives and capabilities fall out that **no centralized host and no
chain-only system can assemble**, because each needs all of {ocap lattice, conservation law,
content-addressed identity, witnessed merge, proof ladder} under one substrate — and dregg is
the only place they coexist.

1. **Fork a running resource.** Snapshot a live GPU job to a 32-byte boundary root, fork it
   into two sovereign workloads via `SpawnWithDelegation`, and prove both descend from the same
   authorized image. The cloud equivalent of `fork()` — for *real, running, metered* compute.

2. **Pass a resource between agents and humans.** A `Transfer` or `GrantCapability` hands a
   live, mid-execution workload — or a whole database, or a service — to another party, who
   resumes it from the inherited umem pin. Resources are first-class objects you *give*, not
   accounts you share credentials to.

3. **Merge resources.** Branch a production database, write to both branches offline with no
   coordination, and merge with a `MergeReceipt` that proves exactly which writes were
   coordination-free and which conserved quantity had to settle. Multiplayer state with a
   conservation law — which CRDTs cannot carry and chains cannot do offline.

4. **Prove a resource to a stranger.** A light client holding one root learns the whole
   history — every workload run authorized, every byte stored correctly committed, every
   GPU-hour conserved — *re-executing nothing, trusting no operator.* Witnessed execution
   (`(command, code_root, result)` bound to a tier) makes "this machine ran this" a fact, not a
   claim. Provenance — for data, compute, and cost together — is a receipt chain, not trusted
   metadata.

5. **Attenuate a resource.** Hand out a sub-budget that provably cannot over-draw the parent
   (`budget.rs:523`), a membrane-wrapped sub-tenant that cannot exceed its grant, a service-cap
   narrowed to one method. Delegation without staying in the loop, and without trusting the
   delegate — the authority *is* the bound.

6. **An agent that acquires and composes real resources, autonomously and provably.** This is
   the synthesis. An agent loop is the braid of **budget + cap + receipt**
   (`exec/src/agent.rs`): every decided action metered from a budget cell, cap-gated by an
   attenuable credential, sealed into a re-verifiable receipt. Give that agent a budget cell and
   it can — on its own, within a conserved ceiling it cannot exceed — lease compute, open a
   umem database, bond an escrow into a compute market, compose a pipelined service graph across
   providers, and leave a receipt chain proving *every resource it touched was authorized, paid,
   conserved, and correctly used.* An autonomous economic actor in the real world whose entire
   footprint is witnessed. No cloud offers a resource an agent can hold as a proof-carrying
   token; dregg offers nothing else.

The through-line: **other clouds give you infrastructure and ask you to trust them. DreggNet
gives you resources as objects you own, fork, pass, merge, prove, and attenuate — and a light
client holding one root verifies the whole thing.** Hosting. Resources available. As dregg
objects, extended into the real world.

---

## 7 · The honest ledger — reachable vs horizon

**Reachable from HEAD (the weld, not new crypto):**

- Compute-as-leased-cell with conserving metered settlement on real polyana tiers (`bridge/`,
  `exec/`, `durable/`) — *live on the local path.*
- Snapshot/fork/time-travel/continuation as umem primitives (breadstuffs) — *built, to be
  welded onto the workload-cell.*
- Storage-as-umem-cell with verified GET / cap-gated PUT (`storage/`) — *live; FNV→umem-root
  flip is the gap.*
- Services as `invoke`/`Reactor`/CapTP-pipelining (breadstuffs app-framework + captp) — *built,
  userspace, no kernel effect.*
- The economy as house capacities + per-asset-well `Σδ=0` (breadstuffs) — *Lean-proven, Rust
  teeth; DreggNet's meter/settle spine already conserving-`Transfer`.*
- Real-world bridges: funded-lease→sandbox, $DREGG mirror asset, `CID==content_root`,
  witnessed-execution receipts — *partly live.*

**Horizon (named seams, each with a closure lane):**

- The umem **checkpoint/resume kernel-effect** (Stage B, designed-not-built) — unlocks
  first-class snapshot/fork/pass of running workloads.
- The **write/merge runtime** wiring (the "missing half") — unlocks multiplayer databases over
  IPFS.
- **Durable + on-chain registries** (R-1) — replace in-memory `HashMap`s so the verifiability
  story closes end to end across restart.
- The **house-capacity VK weld** + per-effect in-circuit `budget` — so a *light client*, not
  just a re-executing validator, witnesses the economic invariants.
- The `Serviced` **receipt carrier** + CapTP handshake — so a light client re-checks a service
  *answer*.
- Live **GPU** and a real **price floor** — hardware and product, not primitive, gaps.

None of these is a wall. Each is a weld between two things that already exist and are proven —
which is exactly the shape of the un-myopic vision: *not new engines, but dregg's own
primitives recognized as the resources, and extended outward through dregg into the world.*

---

*Grounding: `~/dev/breadstuffs/docs/reference/{cells,umem,services,captp,turns,persist,auth}.md`
and the memory topics `project-house-capacities`, `project-umem-as-primitive-epoch`,
`project-partial-turn-promises`, `project-distributed-houyhnhnm-frontier`. DreggNet:
`bridge/`, `exec/`, `control/`, `storage/`, `durable/`, `billing/`, `sdk/src/service_economy.rs`,
and the companion `VISION.md` / `VISION-NEXT-TECH.md`. Verify every LIVE/PARTIAL claim against
HEAD before relying on it.*
