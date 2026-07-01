# The bigger DreggNet — is dregg pulling its weight?

*The synthesis of four scholar-visionary docs into one answer to ember's question:
**are we building the small thing or the big thing, and is dregg actually load-bearing
or decorative?** This document leads with the verdict, then the bigger vision, the
honest current state, the ranked re-dregg roadmap, and the one-line through-line.*

*Dated 2026-06-30, DreggNet `dev`. Read for the SHAPE. Every claim names the primitive
or `file:line` it stands on; honesty grading (REACHABLE-FROM-HEAD vs HORIZON) is
explicit. Sources synthesized: `DREGG-PRIMITIVE-VOCABULARY.md` (the toolbox),
`VISION-DREGG-NATIVE-CLOUD.md` (resources as cells), `VISION-AGENT-WORLD.md` (the
provable agent), `MYOPIA-AUDIT.md` (the honest gap). Verify against HEAD before
betting on a specific line.*

---

## 1 · The answer

**Yes — and no, and the "no" is the most useful thing in this document.**

dregg is pulling its weight on **one axis** and sitting decoratively on **the other**,
and the two axes have opposite verdicts. This is the honest two-axis finding, and it
is more interesting than a flat yes or a flat no:

| Axis | What it is | Verdict |
|---|---|---|
| **Authorization + audit spine** | the `dga1_` cap algebra (attenuate=append, no-amplify), the prev-hash receipt chain, the `ReplenishingBudget` ceiling, the Poseidon2 `content_root` | **genuinely dregg, load-bearing, real** — not naming. ed25519 caveat chains, real attenuation semantics, real Poseidon2 heap roots (the FNV scar is dead — `storage/src/bucket.rs:122` is the REAL wide-8-felt root on every build). The fix here is *twin→proof*, not *generic→native*. |
| **Resource substrate** | the thing being hosted/stored/run: the durable, *witnessed*, *forkable*, *snapshottable*, *mergeable*, *time-travelable* state | **generic** — every resource (server, site, bucket, secret, domain, grain, org, log) is a serde struct in a `Mutex<…map>`, persisted (if at all) through a from-scratch JSON-lines log (`dreggnet-store`) that **reimplements exactly what a committed umem heap already gives**. `umem` is used in **zero** surfaces. |

**The reframe — why it looks decorative, and why that is good news.** dregg looks
decorative *for hosting* not because the hat is fake, but because **we built generic
hosting** — fly-machines + S3 + Vercel + Vault + CloudWatch as in-memory registries —
and then bolted the real dregg spine on top. The resources can't fork, merge, snapshot,
time-travel, or transact, because they were never carved out of umem cells. So the
superpowers that would *distinguish* a dregg cloud from `fly.io + S3 + Vercel` are
absent — not because dregg lacks them (it has them, proven, one repo over in
`breadstuffs`), but because the cloud's resource layer doesn't *use* them.

The crucial corollary, and the reason this is a vision and not a postmortem: **the
dregg-native version is simpler, sounder, and strictly more capable.** It is *less*
code (`SOUNDNESS-TWINS-CENSUS` proves the fixes delete a whole crate and ~10
registries), *sounder* (the machine-checked proofs replace hand-rolled twins), and
*strictly more capable* (it unlocks fork/merge/snapshot/time-travel/transact, which no
`Mutex<BTreeMap>` can ever do). We are not choosing between "ship the small thing" and
"chase the big thing." The big thing is the small thing minus the reimplementation.

---

## 2 · The bigger vision — the non-myopic DreggNet

### The one-primitive thesis

The myopic reading: "a verified blockchain that can host a static site." The toolbox
says something far larger. dregg supplies, as **proven or deployed primitives, the
entire vocabulary of a cloud** — accounts, objects, databases, volumes, snapshots,
currencies, billing, payments, escrow, subscriptions, pooled funds, IAM, access
tokens, sandboxes, the operations API, atomic transactions, serverless triggers,
microservices, async RPC, collaborative documents, multiplayer sessions, federation,
identity, remote desktop, an app store — **with one property none of them have
elsewhere: every one re-witnesses against a committed root on a light-client-unfoolable
rail, so the host cannot lie about what it stored, served, charged, or authorized.**

And it does so from **one primitive, eight ways**. The thesis is collapse, not breadth:

> **A unit of resource is a conserved, verified cell.** Compute, storage, services,
> economy, and identity are not five subsystems with a billing layer stapled on — they
> are five *readings* of the same object. The cell IS the workload (state = a umem
> heap), IS the database (a witnessed `(domain,key)→value` store), IS the service (a
> cap you invoke), IS the account (signed-balance `Σδ=0` value + attenuable authority),
> IS the identity (login = receiving your root capability). *Using the resource and
> conserving its value are one effect.*

This is the heart of `VISION-DREGG-NATIVE-CLOUD.md`: a cloud built on dregg's own
sentence — *"a turn is the exercise of an attenuable proof-carrying token over owned
state, leaving a verifiable receipt"* — does not *manage* resources and bill you. It
hands you **resources as proof-carrying tokens over owned state**: objects you
snapshot, fork, pass, compose, merge, prove, and attenuate exactly as you do any cell.
The real CPUs, GPUs, money, and bandwidth are what the token is *redeemed against*, not
what the abstraction is *made of*. "We run a Postgres for you" becomes "your database
is a sovereign umem cell you own, that happens to be materialized on our disks."

### The killer capabilities

Compose the primitives and capabilities fall out that **no centralized host and no
chain-only system can assemble** — each needs all of {ocap lattice, conservation law,
content-addressed identity, witnessed merge, proof ladder} under one substrate, and
dregg is the only place they coexist:

1. **Fork a running GPU job at a verified snapshot.** Checkpoint a live workload to a
   32-byte umem boundary root, fork it into two sovereign workloads via
   `SpawnWithDelegation`, and prove to a light client holding one root that both forks
   descend from the same authorized image within the same conserved budget —
   re-executing nothing. `fork()`, for real, running, metered compute.
2. **Pass a live workload between agents and humans.** A `Transfer`/`GrantCapability`
   hands a mid-execution workload (or a whole database, or a service) to another party,
   who resumes it from the inherited umem pin. Resources are first-class objects you
   *give*, not accounts you share credentials to.
3. **Branch+merge a production database with a settlement proof.** Branch it like a git
   repo, let two agents write to both branches offline with *no coordination*, and merge
   with a `MergeReceipt` that proves exactly which rows merged freely (I-confluent) and
   which conserved quantity had to settle at the boundary. Multiplayer state *with a
   conservation law* — which CRDTs cannot carry and chains cannot do offline.
4. **An agent that runs a business within a budget it cannot exceed, leaving a proof of
   everything it did.** Accept customers' Stripe/Solana payments (conserving mint), lease
   compute from a fleet it doesn't own, call paid third-party services (pay-per-call,
   conserving), hire sub-agents on escrowed bonds (pay-on-proof), publish a
   content-committed site — every dollar in/out, every call, every deploy one
   re-witnessable receipt log, **and a headroom report proving the ceiling it never
   crossed.** Autonomy and safety are *one primitive*: the same budget+cap that lets it
   act is the same budget+cap that bounds and proves it. The leash lives in the
   authority, not the harness.

### Why nobody else can build it — the substrate

Other clouds give you infrastructure and ask you to trust them. The three things that
are uniquely dregg's, that no competitor can assemble:

1. **The unit of compute, account, and authority are the same verified object** — a
   workload transacts, pays, holds caps, and proves it stayed in its box.
2. **Coordination is mostly-offchain** (the merge runtime) — globally distributed
   without serializing on a chain, anchoring only when authority crosses a boundary.
3. **Authority is bounded and audited cryptographically and inline** — give an agent a
   budget and a cap, get a proof of everything it did and a hard bound on everything it
   *could* have done.

The big agent platforms (OpenAI, Anthropic) are excellent at the *loop* and
structurally lack exactly this: their bound lives in the harness (dies when the
authority leaves it), their audit is whatever the operator logged, their delegation is
an ad-hoc shared API key, their spend is reconciled *after*. dregg inverts each — the
bound *is* the cap, the audit *is* the receipt chain, delegation *is* attenuation, the
ceiling *is* the meter that refuses before the breach. You can hand an agent real-world
authority *because* you can bound and audit it cryptographically.

---

## 3 · The honest current state

Split cleanly, file:line-grounded from the audit. **Don't undersell the spine; don't
oversell the body.**

### Genuinely dregg-native already (the real spine — load-bearing, not naming)

- **The agent loop** — `exec/src/agent.rs` is the whole braid in one file:
  cap-gate (`Credential::verify`, `:1013`) → draw from a replenishing-budget cell
  (`Meter::draw`, `:1036`) → run → seal a chained `AgentReceipt` (`:1114`);
  `verify_agent_run` (`:624`) re-witnesses the chain and confirms consumption stayed
  under the ceiling, trusting no host. The could-have bound is real.
- **Roles/sessions/orgs as attenuations** — `org/cap.rs:62` `attenuate_to_role`
  appends a permission caveat; the no-amplify proof (`cap.rs:157`) shows a viewer can't
  self-promote. RBAC-as-cap-attenuation, real cap-verify refusal, not a trusted flag.
- **The verifiable invoice** — `billing/` traces each line to its settled meter
  receipts (`verify_against_receipts`); a padded/forged line fails. Genuinely credited.
- **Real Poseidon2 `content_root`** — hosting and storage commit the **REAL** wide-8-felt
  (~124-bit) sorted-Poseidon2 cell-heap root on every build (`storage/src/bucket.rs:122,134`,
  `webapp/src/hosting.rs`), via `dregg_circuit::heap_root` — the **FNV stand-in scar is
  dead** (post-`0b2457d`; the lingering "FNV" note in `VISION-DREGG-NATIVE-CLOUD §2` is
  now stale). A host cannot lie about served/stored bytes; the per-asset opening is a
  genuine trustless leaf-fold read.
- **The account-identity re-anchor** — `webauth/account_id.rs:61` derives the account
  id as the **real substrate `CellId::derive_raw`** via `dregg_types` (post-`0372685`);
  `webauth/cred.rs` is a wire-byte-identical port of `dregg-auth::credential`. This is
  the one crate that depends on breadstuffs, and the `dga1_` cap the whole front office
  rests on is real attenuation.
- **The durable pg_dregg conservation tooth** — `durable/src/verified.rs` imports the
  **REAL** `pg_dregg::mirror` verified hash chain (`RootChain`/`MirrorBatch`/`verify_chain_step`,
  `:50`), so tamper/reorder/replay of a settlement row is caught for real; exactly-once
  `(lease,period)` settlement with write-ahead+fsync (`settle_ledger.rs`) is the
  product's high-water mark.
- **`exec/` honestly delegates** — `run_workload` is a thin seam over polyana's real
  polyglot engine (`exec/src/lib.rs:1`, Apache-2.0, co-developed); the cap-grade→tier→provider
  floor check (no silent downgrade) is the right dregg-shaped boundary. Not a clone.

### The generic body (the myopia — what's NOT dregg yet)

- **`umem` is used in ZERO surfaces.** It appears in the cloud's executable code only
  as doc-comments (the aspirational seam) plus one SHA-256 `BTreeMap` stand-in in
  `sandstorm-bridge/src/cell.rs:27` — explicitly *"the prototype's stand-in for
  turn/src/umem.rs."* No kernel umem cell anywhere.
- **No surface issues a real kernel turn/`Effect`.** The only `Effect::` in the
  data/compute crates is a doc-comment describing a *future* `Effect::Transfer`
  (`durable/src/verified.rs:69`).
- **Every resource is a serde struct in a `Mutex<…map>`** — sites
  (`webapp/src/hosting.rs:576`), buckets (`storage/src/registry.rs:52`), domains,
  secrets (`dregg-secrets/src/store.rs:46`), servers (`control/src/server.rs:529`),
  mesh nodes, machines, workloads, logs — persisted (if at all) through the from-scratch
  JSON-lines `dreggnet-store::RegistryLog`.
- **The economy reaches deepest but still twins.** `durable` depends on real
  `pg_dregg::mirror`, **but** the per-turn root is a **blake3 stand-in** (`verified.rs:27`)
  and the conservation arithmetic is the in-process `ConservingLedger` **twin**, not the
  proven `dregg-payable::Payable`.

So even the "native" front office is **native-in-authorization, generic-in-substrate**:
the spine gates generic resources. The resources cannot fork/merge/snapshot/time-travel/
transact — the exact superpowers that distinguish a dregg cloud.

---

## 4 · The re-dregg roadmap — from bolted-together to one-primitive

Ranked by *biggest gap × highest payoff*. Each: the move, what it deletes, what it
unlocks, reachable-vs-horizon, and the named substrate seam (the swarm's work).

### #1 — Compute as a forkable umem cell (MOST MYOPIC, HIGHEST PAYOFF)

- **Move.** A server IS a checkpointable umem cell carrying a cap-bounded workload; its
  running image is a committed heap. **sleep = checkpoint** to the committed umem heap,
  **wake = restore**, **scale = fork** (cell branch via `SpawnWithDelegation`), **pay
  only while awake** (checkpoint releases the lease, bills only storage). Today
  `stop`/`wake` is a lifecycle enum (`control/src/server.rs:72`) that releases/re-provisions
  a `VmProvider` machine — the fly.io model, not the umem model.
- **Deletes.** The `ServerRecord`-as-fly-Machine generic; collapses "a container we
  manage" into "a cell that forks."
- **Unlocks.** Genuine pay-only-while-awake, live migration/fork as a heap pass,
  time-travel debugging of a crashed server, and a workload that **transacts from inside
  the sandbox** (the §2 agent-world superpower). The single change that most converts
  "verifiable fly.io" into "the cloud whose unit of compute is a unit of account and
  authority."
- **Reachable vs horizon.** The lease→cap-tier→polyana weld with conserving metered
  settlement is **REACHABLE — live on the local path** (`bridge/`, `exec/`, `durable/`);
  snapshot/fork/time-travel/continuation exist as **proven umem primitives in
  breadstuffs**. The PoC is welding them onto the workload-cell.
- **Substrate seam (the swarm's).** The umem **checkpoint/resume kernel-effect** (Stage
  B, `UMEM-STAGE-B-DESIGN.md`) — a first-class effect emitting a umem-ref and one
  consuming it — is designed-not-built. Live GPU is hardware-gated.

### #2 — The registries → umem cells (the substrate myopia, deletes a whole crate)

- **Move.** Make each `Mutex<…map>` registry (sites, buckets, domains, secrets, logs,
  servers) a thin view over a real umem cell; route mutations (`publish`/`put`/`delete`)
  through real cap-gated `Effect::Write` turns whose receipt is the kernel `TurnReceipt`;
  the durable state is the committed umem heap.
- **Deletes.** The entire `dreggnet-store` crate (`store/src/lib.rs` — *"a careful,
  well-built reimplementation of exactly what a committed umem heap provides"*) and the
  ~10 in-memory registries it persists behind. Per `SOUNDNESS-TWINS-CENSUS §1`, the fix
  removes code.
- **Unlocks.** fork/merge/time-travel across **hosting + storage + domains at once**;
  atomic preview/branch deploys (fork the site cell, serve the fork, stitch or discard);
  instant rollback; the in-circuit light-client witness that the served root is the
  genuine committed state.
- **Reachable vs horizon.** **REACHABLE** for the runtime swap (umem heaps, doc-on-heap,
  crash-recovery all exist in breadstuffs); the **HORIZON** is full on-chain durable
  registries replacing the in-memory `HashMap`s end-to-end across restart (the R-1
  blocker).
- **Substrate seam.** The real turn / `Effect::Write` / light-client witness, uniformly
  deferred today to "the circuit swarm's VK-epoch."

### #3 — Unblock the merge runtime (structurally blocked until #1/#2)

- **Move.** Once resources ARE umem cells, the I-confluent write/merge path has
  somewhere to live: two replicas of a bucket/database edit offline, exchange grow-set
  deltas (over IPFS by CID — `CID == content_root`, no re-hash), and merge locally with
  a `MergeReceipt`; the proven `classify_merge` gate decides per write — free merge when
  confluent, settle-at-the-boundary when a conserved quantity participates.
- **Deletes.** Nothing directly — it's a *precondition unlock*. But it retires the
  "mostly-offchain coordination" claim's vacuity.
- **Unlocks.** The cloud's **defining superpower** (`VISION` Bet #2): globally
  distributed coordination at memory speed, anchoring only when authority crosses a
  boundary. A single cell carrying *both* a grow-only collaborative table *and* a
  conserved balance, knowing per-write which is coordination-free — the distinction
  CRDTs cannot express.
- **Reachable vs horizon.** The merge runtime laws + dichotomy are **proven
  (`#assert_axioms`-clean) and the Rust executor exists** in breadstuffs; the "missing
  half" is the **write/merge runtime wiring** — the `delta_cid` transport adapter + a
  two-replica driver, **days from HEAD because each half is proven** — but it is
  *structurally blocked* until §2 makes resources cells. **HORIZON:** multi-writer
  multiplayer at scale (the branch-and-stitch frontier).
- **Substrate seam.** The Lean⟷Rust in-circuit **merge write-half refinement** — the
  named seam for the circuit swarm.

### #4 — The economy twins → real dregg deps (smallest move, deepest surface)

- **Move.** Depend on `dregg-payable::Payable::pay` for the conserving `Effect::Transfer`
  (delete the `ConservingLedger` twin); swap the blake3 per-turn root for the Poseidon2
  one; flip the tier-c proof verifier. Model compute/storage/bandwidth/tokens as **asset
  wells** — each a unit of resource with exactly one issuer well; genesis mints supply,
  consumption burns it, `Σδ=0` per well. Then *using the resource and conserving the
  value are one effect* — there is nothing left to "bill."
- **Deletes.** The `ConservingLedger` twin (`control/src/settle.rs`); the blake3 stand-in.
- **Unlocks.** The house capacities AS the resource relationships: escrow = bonded
  compute market, obligation = SLA/subscription, vault = tenant custody, membrane =
  sub-tenant isolation, derived = metered view, hatchery = issuance policy — all already
  Lean-proven, riding `dregg-payable` + Poseidon2.
- **Reachable vs horizon.** **REACHABLE** — all six capacities have Lean rungs + Rust
  teeth in breadstuffs; DreggNet's meter/settle spine is *already* conserving-`Transfer`
  over `StandingObligation`. Modeling resources as asset wells is a re-grounding, not new
  crypto.
- **Substrate seam.** The per-effect in-circuit `budget` field + the house-capacity **VK
  weld** (`HOUSE-CAPACITIES-WELD-PLAN.md`) — so a *light client*, not just a re-executing
  validator, witnesses the economic invariants. A real price floor (subsidized today,
  `hosting_meter.rs:99`) is a product decision, not a primitive gap.

### #5 — The remaining firewall dissolutions

- **Move.** Identity port → dependency (`webauth/cred.rs` → a `dregg-auth` dependency,
  closing the rotation/recovery gap); the `exec` `ReplenishingBudget` twin → land the
  widening in breadstuffs at `cell/src/budget.rs` and depend (twin→proof); give the
  polyana workload a cell handle so it can pay/attenuate from inside the cage; reframe
  the `control/src/mesh.rs` WireGuard overlay as **cap-materialized routing** (service
  reachability is a capability, not an IP route).
- **Deletes.** The remaining twins; the standalone non-dregg mesh addressing.
- **Unlocks.** End-to-end soundness (the proofs one repo over become the ones running);
  the `Serviced` cross-cell-read **receipt carrier** so a light client re-checks a service
  *answer*, not just the turn.
- **Reachable vs horizon.** Mostly **REACHABLE** small moves (now unblocked since the AGPL
  firewall dissolved — `FIREWALL-DISSOLUTION.md`); the `Serviced` receipt carrier + CapTP
  `InterfaceDescriptor` handshake and the cap-materialized mesh are **HORIZON** design work.
- **Substrate seam.** The `Serviced` receipt carrier (`cell/src/interface.rs:38`); the
  firecracker live-netns egress install (allowlist computed, host tap/route the seam);
  outbound EVM settlement (the STARK-verifier Groth16 wrapper, out-of-repo).

---

## 5 · The through-line

When DreggNet is the big thing, it is not a verifiable veneer over `fly.io + S3 +
Vercel`. It is **dregg's own primitives — cell, umem, capability, the house economy —
recognized as the resources themselves and extended outward through dregg into the real
world**, so that a workload IS a cell, a database IS a umem, a service IS a capability,
the economy IS the resource layer, and an agent holds each as a proof-carrying token it
can fork, pass, merge, prove, and attenuate. Other clouds give you infrastructure and
ask you to trust them; DreggNet gives you resources as objects you own, and a light
client holding one root verifies the whole thing — re-executing nothing, trusting no
operator.

> **One unit of resource is a conserved, verified cell — and using it, paying for it,
> proving it, and bounding it are one effect. Hosting. Resources available. As dregg
> objects.**

The spine is already real. The body just needs to be carved out of umem — which is
*less* code, *sounder*, and *strictly more capable*. The hat is real; now the server
learns to fork.

---

*Synthesis of `DREGG-PRIMITIVE-VOCABULARY.md`, `VISION-DREGG-NATIVE-CLOUD.md`,
`VISION-AGENT-WORLD.md`, `MYOPIA-AUDIT.md`. Companion grounding:
`docs/VISION.md`, `docs/ARCHITECTURE-CRITIQUE.md`, `docs/SOUNDNESS-TWINS-CENSUS.md`,
`docs/FIREWALL-DISSOLUTION.md`, and `~/dev/breadstuffs/docs/reference/`. Read-only on
code; verify every `file:line` / LIVE-vs-HORIZON claim against HEAD before relying on
it. ( ⌐■_■ )*
