# DreggNet — the vision

*The bold next direction, grounded in what is actually built. Read this for the
SHAPE; verify any LIVE/PARTIAL/stand-in claim against HEAD before relying on it.
Status language matches the repo's own grading: LIVE = code-proven here (mostly on
the local / in-process / LocalProvider path), PARTIAL = core wired with a named
seam, GAP = designed not built. The companion grounding docs are
`docs/PERMISSIONLESS-CLOUD-PLAN.md`, `docs/LIFTOFF-SURPASS-MATRIX.md`,
`docs/ARCHITECTURE-CRITIQUE.md`, `docs/SERVICES.md`,
`docs/SANDSTORM-INTEGRATION-PLAN.md`, and `docs/REPLENISHING-BUDGET.md`.*

---

## 0. Where we stand (the honest what-is)

DreggNet is the operated layer over dregg, the open verified ocap substrate
(`~/dev/breadstuffs`, AGPL). dregg says *what was promised, paid, and owed*,
verifiably; DreggNet *delivers it* and bills for it. The split is real and
load-bearing: the substrate is the trustless rail, the infrastructure is the moat.

What is genuinely here today, grounded to code:

- **The serving spine.** The full Elide `httpe` gateway + its dep closure build
  green for Linux (`net/`), the WireGuard/Tailscale mesh between control and fleet
  (`control/src/mesh.rs`), and **polyana** — the polyglot execution engine (34
  language families; sandbox tiers from `wasmtime`/`v8` to `Caged`
  seccomp+Landlock and `MicroVm` Firecracker; durable replay).
- **The lease economy.** A funded dregg `execution-lease` authorizes a workload;
  the bridge maps cap-grade → sandbox tier, runs it on polyana, ticks a
  `StandingObligation` meter, and settles each charge as a real conserving
  `Effect::Transfer` — exactly-once, crash-safe, re-witnessable
  (`control/src/{orchestrator,settle_ledger,node_api}.rs`, `durable/`).
- **The product surfaces (LIVE on the local path).** Static site hosting where a
  site IS a cell carrying a `content_root` commitment (`webapp/src/hosting.rs`),
  trustless object storage (`storage/`, `verified_get`), durable crash-resume
  execution (`durable/`), agent-served web APIs that refuse over-budget with `402`
  before the handler runs (`webapp/router.rs`, `LeasedRouter`), the fly-machines
  API (`gateway/`), `webauth` attenuable `dga1_` cap-accounts, the auto-deploy
  build-as-durable-workflow (`dregg-deploy`), custom-domain bindings as cells
  (`dregg-domains`), and the Sandstorm grain=cell / powerbox=cap prototype
  (`sandstorm-bridge/`).
- **The federation.** An n=4 devnet heading to 5; the self-hostable
  `dreggnet-provider` (anyone runs their own against their own cells + machines).

The honest line, carried from `docs/LIFTOFF-SURPASS-MATRIX.md`: nearly everything
LIVE is proven *built + locally*, not yet *operated on a public edge*. The live
`example.com` edge, real cert issuance, the on-chain `Effect::Write` that replaces
the FNV `content_root` stand-in with the real Poseidon2 heap root, the Firecracker
guest plane + a GPU tier, and real `$DREGG` billing are reviewed-go / operational
gaps. The vision below is reached *from these primitives*, and every reach names
the primitive it stands on.

One more honest input shapes the whole vision: `docs/ARCHITECTURE-CRITIQUE.md`
found that the product layers drifted toward *eager per-op on-chain settlement* and
*five bespoke bridge relayers at sub-light-client trust*, while the **I-confluent
merge runtime** — the offchain coordinator the thesis says is the *common case* —
is essentially unbuilt. The vision treats that not as a wound but as the **largest
unclaimed superpower in the building**, and bet #2 is to claim it.

---

## 1. The superpowers — what a verifiable, cap-secured, mostly-offchain cloud unlocks that nothing else can

These are not features to polish; they are properties a centralized trusted host
cannot offer *by construction*. Each is already real or near in this repo.

1. **You verify the operated result, not just the storage.** Fleek/IPFS verify
   *what was stored*; Arweave verifies *content addresses*. DreggNet verifies the
   *operation*: a served byte, a compute step, and a billing charge each
   re-witness against a committed cell, anchored to a finalized committee
   checkpoint on a light-client-unfoolable rail (`verifyBatch accept ⟹ ∃ genuine
   kernel transition`). The host *cannot* lie about what it served or charged.
   Grounding: `webapp/src/hosting.rs` `content_root`, the trustless
   `deos-view::render_trustless_cell_document` projection the portal already uses,
   `control/src/settle_ledger.rs` conserving `Transfer`, breadstuffs
   `CircuitSoundness.lean`.

2. **Workloads that transact.** A running container is not a dumb VM — it is a
   cell, and a cell holds caps, owns assets, pays, settles, and coordinates. The
   compute substrate and the economic substrate are *the same substrate*. A
   workload can pay for its own next period, mint a receipt, hold an escrow leg,
   or hand a sub-capability to a peer — inside the sandbox, witnessed. No other
   cloud makes the unit of compute also a unit of account and a unit of authority.
   Grounding: `bridge/` (lease⟷workload), `webapp/router.rs` (`LeasedRouter`),
   the host-API `invoke`/`cell_read`/`cell_write` spine, breadstuffs `Payable`.

3. **Attenuable cap-accounts instead of API keys.** "No KYC, wallet = account" is
   the floor. The real power is that the account is an *attenuable, offline-
   verifiable, revocable* `dga1_` credential: a tenant hands a CI runner a
   deploy-only, one-site, time-boxed sub-capability without sharing the root key,
   and a third party can witness exactly what authority was delegated, to whom,
   when. Grounding: `webauth/`, breadstuffs `cipherclerk` + the cap-reshape crown.

4. **Cross-operator verification (federation without a shared chain).** Two
   operators verify the *same* history independently — the receipt stream root is
   bound into an attested root, so a federation does not need a common ledger to
   agree. This is the structural basis for a permissionless provider network where
   the moat is the network, not the code (`dreggnet-provider`,
   breadstuffs `BridgeReceipt`/`AttestedRoot`).

5. **The merge runtime (the unclaimed one).** The thesis is *mostly-offchain
   coordination*: agents and operators accumulate I-confluent (CRDT) deltas
   coordination-free and settle on-chain only at a real cross-boundary commitment,
   where revocation is non-monotone (`SettlementSoundness.lean`, proven). The read
   face exists (`dregg-query`), the formal gate is proven (`Confluence.lean`), but
   the *write/merge* runtime is the missing half — and it is the thing that turns a
   collection of providers into one coherent, globally-distributed, chain-free
   cloud. See bet #2.

6. **Pay-only-while-awake.** A grain/cell sleeps when idle, checkpoints to its
   committed umem heap, releases the lease, and bills only storage — so a tenant
   holds hundreds of objects and pays compute only for the awake ones. A trusted
   always-on host cannot match this cost model cheaply
   (`docs/SANDSTORM-INTEGRATION-PLAN.md` §3, `durable/`, umem).

7. **Agents that are cap-bounded, receipted, and provable.** An agent is a cell:
   it spins up, holds its cap, attenuates a sub-cap to a sub-agent, pays for its
   compute, and *every action it takes leaves a witnessed receipt*. You can give
   it real money and real authority because you can bound exactly what it may do,
   prove exactly what it did, and revoke it instantly. This is the compounding one
   — it is the 10x frontier.

---

## 2. The 10x frontier — the killer capability: the Verifiable Agent Cloud

The single capability that makes a developer go *"I have to use this"* is not a
better static host. It is this:

> **Give an autonomous agent a budget and a capability. Get back a proof of
> everything it did, and a hard bound on everything it could do.**

Every other cloud asks you to trust an agent with an API key and a credit card and
hope. DreggNet makes the agent a **cap-bounded, receipted, provable tenant**:

- it deploys itself (`dregg-cloud deploy`), gets a cap-account (`webauth`) and a funded
  **replenishing budget** that meters *actual* consumption against a rate ceiling
  that refills lazily — a runaway agent is *rate-bounded by construction*, not by a
  watchdog (`docs/REPLENISHING-BUDGET.md`, the seL4-MCS shape over
  `cell/src/allowance.rs`);
- it runs as a persistent grain at the cap-tier its lease authorizes — never
  weaker — sleeping when idle and billing only storage
  (`docs/COMPUTE-TIERS.md`, `bridge/`);
- it serves an API (`webapp/router.rs`) and **transacts**: pays per request, holds
  an escrow leg, and hands a strictly-attenuated sub-cap to a sub-agent through the
  **provable powerbox** — the first delegation where a third party can witness that
  an agent holds *exactly* the authority granted and no more (confused-deputy
  immunity *with a proof*, `docs/SANDSTORM-INTEGRATION-PLAN.md` §4);
- it coordinates with peer agents over branch/stitch — each coordination turn a
  receipted, settlement-sound merge (breadstuffs branch-and-stitch);
- and the whole run produces a **receipt chain a light client re-verifies** with
  no trust in the operator.

Why this is 10x and not incremental: the industry is racing to give agents
autonomy, and the blocker is *trust* — you cannot safely hand an autonomous agent
spend authority and tool access without a way to bound and audit it. DreggNet is
the substrate where that bound and that audit are *cryptographic and inline*, not
policy-and-hope. It is the cloud built for the thing everyone is about to need:
**software you did not write, running with money and authority you granted, that
you can prove stayed inside its box.**

It compounds the primitives that are already here — agent-web-apps + the lease
economy + the powerbox + the replenishing budget + branch/stitch + the trustless
read — into one category nobody else can assemble, because nobody else has the
verified ocap substrate underneath.

---

## 3. The bold bets — three directions that compound the primitives into a category

### Bet 1 — The Verifiable Agent Cloud (the killer capability, productized)

Make §2 the headline product. The pieces are mostly LIVE in isolation; the bet is
to *braid them into one onramp*: `dregg-cloud agent deploy` → a cap-account + a funded
replenishing budget + a persistent grain + a served API + a sub-cap delegation
ceremony + a downloadable receipt-chain proof. The differentiators are not
slideware — each is a file in this tree. The new work is the *integration surface*
and the developer story: "deploy an agent, give it $X and cap C, get a proof." Sub-
agents become a first-class shape (an agent attenuates a budget and a cap to a
child, the Stingray split in `docs/REPLENISHING-BUDGET.md` §3 makes N children of
one cap settle without contending the parent). This is the bet with the shortest
distance from HEAD to a thing a developer cannot get anywhere else.

### Bet 2 — Claim the merge runtime (the mostly-offchain cloud, finally built)

`docs/ARCHITECTURE-CRITIQUE.md` is right: we over-built the rare boundary (five
chain relayers at sub-light-client trust) and under-built the common case (offchain
coordination). The bold re-grounding is to **build the DREGG3 §2.4 `merge`
interpretation as a production path** and make it the defining property of the
network:

- two providers (or two replicas of one provider, or two agents) accumulate
  I-confluent deltas coordination-free, gated by the proven `ConfluenceClassifier`,
  and **reconcile at a boundary** — lease-close, dispute, revocation — settling the
  accumulated outbox as *one* netted conserving Transfer, not one per period;
- settlement becomes *reconcile-at-boundary*, not per-op-eager: the `SettleReceipt`
  becomes the artifact two parties hold *between* settlements (the `BridgeReceipt`
  two-phase pattern applied to leases), with an on-ledger Transfer only at the
  non-monotone event;
- the bridge collapses to **one `ForeignFinalitySource` abstraction** with a
  burn-down to the witnessed bar (Fork-X folds foreign finality into the EffectVM so
  a light client, not a re-executing validator, witnesses a cross-chain mint).

The payoff is a cloud that is *globally distributed without serializing on a chain*
— providers and agents coordinate offchain at memory speed and anchor only when
authority crosses a boundary. This is the architecture that makes "permissionless
cloud" mean something stronger than "decentralized billing." Grounding: the read
face (`dregg-query`) + the proof (`Confluence.lean`, `SettlementSoundness.lean`)
exist; the write/merge runtime + the boundary cadence is the build.

### Bet 3 — The verifiable app store (Sandstorm × verify)

Run the hundreds of `.spk` apps (Etherpad, Wekan, Gitea, Davros, …) dregg-native:
a grain = a cell, the powerbox = a provable cap delegation, the sandbox = a
DreggNet compute tier, metered in `$DREGG`, served trustlessly. The result is a
third category — not a better Liftoff, not a revived Sandstorm: **an agent-native
object-capability cloud with Sandstorm's app catalog and dregg's proofs**, where
every app is an object you verify (its data, its served bytes, its bill all
re-witnessable), cross-app delegation is provable, and you pay only for what's
awake. The prototype is green (`sandstorm-bridge/`, the manifest parser + grain
lifecycle + powerbox ceremony); the build is the `.spk` reader, the descriptor↔Pred
matcher, and the http-bridge shim. This is the consumer/prosumer face of the same
substrate — and it is also where *agents acquire tools*: a catalog app is a cap an
agent can be granted through the same provable powerbox.

*(A fourth, optional compounding direction — cross-org compute markets on the
escrow bond: the Hellas marketplace shape over `SealedEscrow` + `StandingObligation`
in `docs/REPLENISHING-BUDGET.md` §4, where a provider bonds slashable stake and a
consumer's posting rate is cap-bounded. It is the trust-minimized B2B face of bet
#1 and rides the same primitives; build on demand.)*

---

## 4. The honest path — the nearest reachable epic vs the horizon

### The reachable epic (devnet-ready, from HEAD)

The nearest thing that is genuinely *epic* and genuinely *reachable* is **the
Verifiable Agent Cloud, end-to-end on the devnet path** — because every piece
exists and the work is the braid, not new engines:

1. **The agent onramp.** `dregg-cloud agent deploy` over the existing `dregg-deploy`
   durable build + `webauth` cap-account + the persistent-server grain shape — an
   agent deploys itself, gets a budget, runs, serves, and produces a receipt chain.
2. **The replenishing budget as the meter.** Land `cell/src/budget.rs` (the widen
   of `allowance.rs`) and put metering + the sub-agent split on it — closing the
   SRV-3 "bill measured consumption, not ticks" half on principle. This is a near-
   pure reuse with a copyable Lean rung (`StandingObligation.lean`).
3. **Make verifiable hosting real, not a stand-in.** The single highest-leverage
   operational flip: the on-chain `Effect::Write` that replaces the FNV
   `content_root` with the real Poseidon2 committed heap root, so the trustless
   re-witness checks the genuine commitment. The property is already proven; this
   wires the carrier (reviewed-go: the `dregg-verify` AGPL link-isolation + a live
   node).
4. **The merge runtime's first production path** (bet #2, rung 1): two providers
   reconcile a lease at the boundary as one netted Transfer, behind the existing
   `Settlement` seam — the smallest real instance of reconcile-at-boundary,
   provable on the local path.
5. **Sustained finality on the 5-node federation** + the WireGuard two-node
   handshake — the operational floor the whole cloud serves on.

That set, green and demonstrated on the devnet, *is* the epic: a developer hands an
agent a budget and a cap, it runs in the cloud, transacts, delegates, and hands
back a proof — on a network multiple operators verify independently. Nothing else
can do that today.

### The horizon (the further reaches)

- **GPU agent fleets + heavy compute** — the Firecracker guest plane + a GPU
  cap-tier (`exec/`, `docs/COMPUTE-TIERS.md`), making DreggNet a place to run
  cap-bounded, receipted *training and inference*, not just CPU handlers.
- **Cross-chain agent commerce, witnessed** — the bridge's burn-down to the
  light-client bar (Fork-X), so an agent can pay and be paid across Solana/ETH/
  Midnight with the mint *witnessed*, not RPC-trusted.
- **Confidential agent workloads** — the M2 shielded-transfer rail, so a tenant's
  values, payments, and (eventually) compute can be private *and* verified — ZK
  hosting with no analog elsewhere.
- **The global verifiable edge** — many operators, real anycast, the federation as
  a true permissionless network; the honest trade is verifiability now, raw edge
  maturity closed incrementally on real hardware.
- **The deos desktop as a cloud** — the reflective, multiplayer cockpit
  (breadstuffs) hosted as a DreggNet surface: a live, malleable, cap-secured
  workspace that *is* its own IDE/inspector, served and metered like any grain. The
  cloud you do not just deploy to, but *inhabit*.

---

## 5. The through-line

Liftoff is a KYC-free host you trust; DreggNet is a permissionless host you verify.
But the vision is larger than surpassing one host: it is that **the unit of
compute, the unit of account, and the unit of authority are the same verified
object** — a cell — so the cloud becomes a place where autonomous software runs
with money and authority you granted, coordinates mostly offchain, and proves it
stayed inside its box. The static-site race is the on-ramp; the destination is the
verifiable agent cloud, built on a merge runtime, with a provable app catalog —
three faces of one substrate that nobody else has underneath.

Build the agent onramp; claim the merge runtime; make the proofs real. The rest is
horizon, and the horizon is reachable from here.

---

*Dated 2026-06-30. Bold by intent, grounded by discipline: every reach above names
the primitive it stands on. Verify file:line and LIVE/PARTIAL/stand-in claims
against HEAD before relying on any specific one.*
