# Architecture critique — receipts, chain-relaying, and the dilution of mostly-offchain coordination

*A read-only senior-architecture review across `~/dev/breadstuffs` (the dregg core) and
`~/dev/DreggNet` (the cloud). Written adversarially: the working assumption is that we
drifted, and each claim is either proved or disproved against code at HEAD. Honest both
ways — what is coherent with the vision is named as such.*

## 0 · The thesis we are grading against

The dregg vision is **mostly-offchain coordination**: a turn is the exercise of an
attenuable proof-carrying token over owned state, *leaving a verifiable receipt*. Agents
coordinate off-chain by exchanging receipts + capabilities + the I-confluent (CRDT) merge,
and **settle/anchor on a chain only at a real cross-boundary commitment** — the one place
revocation is non-monotone (`SettlementSoundness.lean`). Proving is OFF the commit path: a
fidelity ladder (Symbolic → Full → witness-bundle → recursive → aggregated), where proofs
are *additive attestation, not permission* (`paper2/04-receipts.md` §4.3: "turns flow as
signed receipts and nobody waits on a prover").

The grade, in one line: **the kernel still embodies this thesis; the two product surfaces
we have been building on top of it — the bridge crate and the DreggNet cloud — quietly
invert it.** The bridge makes *external chains* the coordinator; the cloud makes *eager
per-op on-chain settlement* the coordinator. Both reach for a chain where a receipt +
periodic reconciliation was the design.

---

## 1 · The receipt model — a coherent core wrapped in a degraded periphery

### 1.1 What is coherent (the core is real)

The kernel receipt is load-bearing and exactly the offchain-coordination primitive the
vision promised:

- **`TurnReceipt`** (`breadstuffs/turn/src/turn.rs:844`), the receipt *chain*
  (`Dregg2.Exec.Receipt`, `chain_tamper_evident`) — "the DB is the cache; the chain is the
  truth." `previous_receipt_hash` makes it append-only and forgery-resistant; an
  `executor_signature` (Ed25519) lets a party who was *not there* verify the step. It is
  bound into `AttestedRoot.receipt_stream_root`, so two federations verify the *same*
  history independently, with no shared chain. This is offchain coordination done right.
- **`BridgeReceipt` / `BridgeReceiptEnvelope`** (`breadstuffs/cell-crypto/src/note_bridge.rs:352`,
  `:589`) — a genuine 2-/4-phase offchain protocol (Locked → Witnessed → Finalized),
  chained by `previous_phase_receipt_hash`, signed by a BLS `ThresholdQC`. Two federations
  mint across a boundary *by exchanging signed receipt envelopes*, the committees registered
  out of band, no common ledger. `federation/tests/cross_federation_bridge_receipt.rs` is
  the load-bearing demonstration. **This is the high-water mark** — it is what every other
  receipt in the system *should* aspire to.
- The **read side** is also receipt-shaped and honest: `dregg-query`'s `RangeCertificate`
  over an MMR root (`breadstuffs/dregg-query/src/attested.rs`) is a *non-omission* receipt —
  a query answer that proves it hid nothing. And the **store-and-forward relay** carries a
  `DequeueProof` (`breadstuffs/storage/src/queue.rs:88`) plus a bonded/slashable operator
  (`dregg-storage-templates/src/relay_operator.rs`): a sender hands a message to a relay and
  the delivery receipt is the coordination artifact. Both are coherent with the thesis.

So at the kernel/protocol layer there is **one discipline** — an append-only, prev-hash-
chained, signature-or-QC-bearing record that a non-witness can verify — and it is
load-bearing.

### 1.2 What drifted (the periphery is N incoherent notions)

Above the kernel the discipline fragments. A census finds **~10 distinct "receipt" types in
three semantic classes**, and most of the new ones are *post-hoc logs*, not *a priori
coordination artifacts*:

| Receipt | Where | Class | Offchain-coordinating? |
|---|---|---|---|
| `TurnReceipt` / `WitnessedReceipt` | `breadstuffs/turn/` | attestation, chained | **yes** (load-bearing) |
| `BridgeReceipt(Envelope)` | `breadstuffs/cell-crypto/note_bridge.rs` | 2-/4-phase, QC | **yes** (load-bearing) |
| `DequeueProof` / `RangeCertificate` | `breadstuffs/storage`, `dregg-query` | delivery / non-omission | **yes** |
| `SettleReceipt` | `DreggNet/durable/src/settle.rs:105` | exactly-once sidecar | partial — *on-chain*-coordinated |
| `HostingReceipt` | `DreggNet/control/src/hosting_meter.rs:186` | wrapper over `SettleReceipt` | no (metadata) |
| `TurnShadowReceipt` | `DreggNet/polyana/.../dregg_turn_shadow.rs` | chained workload attestation | weak — produced, barely consumed |
| metering `Receipt` | `DreggNet/polyana/src/core/.../capability_spec.rs:263` | log | **no** — and *misshapen* (below) |
| `DeployReceipt` / `BindReceipt` / `PublishReceipt` | `DreggNet/dregg-deploy`, `dregg-domains`, `webapp/hosting.rs:247` | logs | no (stand-ins) |
| `BucketReceipt` / `PutReceipt` / `DeleteReceipt` | `DreggNet/storage/src/registry.rs:302` | logs | no |

Two findings sharpen the drift:

1. **A receipt that lies about what it carries.** The polyana metering `Receipt`
   (`DreggNet/polyana/src/core/src/capability_spec.rs:217-226`) declares a `grant_chain`
   field for capability lineage that is *shaped but never populated or verified* — the
   comment admits it is "ALWAYS `None`, and nothing downstream checks it for authority."
   This is the inverse of the kernel receipt: a record that *looks* like it binds authority
   and binds nothing. That is not a receipt; it is a struct wearing the word.

2. **Even within one subsystem the model is not unified.** polyana carries *two* receipt
   notions at once — a decent chained `TurnShadowReceipt` (`exec/src/host_api.rs:561`,
   prev-hash-linked, gated by `EffectIntent`) *and* the degraded metering `Receipt` above.
   There is no single `Q`-type, no shared verifier, across the product surface; each crate
   rolls its own and most never get verified by anyone.

**Verdict (receipts):** the core receipt model is coherent and load-bearing; `BridgeReceipt`
is exactly the offchain-coordination primitive the thesis wants. But the product layers have
**not adopted that discipline** — they emit logs named "receipt." A `DeployReceipt` /
`PublishReceipt` records *that a chain op happened*; it does not let two parties coordinate
off-chain and reconcile later. The receipt degraded from *coordination primitive* to
*audit log* the moment it crossed out of the kernel.

---

## 2 · Chain-relaying — the bridge crate over-relays, at sub-bar trust

The recent work added live relayers/observers for **Solana, Ethereum (in + out), Midnight,
Mina**, plus a **Stripe** fiat mirror (`breadstuffs/bridge/src/`: `solana_relayer.rs`,
`ethereum_relayer.rs`, `midnight_observer.rs`, `mina_observer.rs`, `stripe_mirror.rs`).
Each is a *watch-finality → verify → mint/settle* loop. Three criticisms.

### 2.1 The mint is unified; the *coordinator* moved to the external chain

The mint side is genuinely conserving and sound: every inbound path funnels into
`bridge_mint_against_lock`, whose **consume-once nullifier + per-asset Σδ=0 ledger are the
global double-mint authority** — "the relayer is *not* the soundness root"
(`solana_relayer.rs:30-35`). Good. That is the part that honors the vision: a bridge is a
real boundary, and the conservation law is dregg's, not the chain's.

But the *coordination of truth* has nonetheless moved off dregg and onto the foreign chain.
The relayer's whole job is to treat **the external chain's finalized state as the source of
truth** and mirror it inward. That is legitimate *for a bridge* — a bridge is precisely
where you cross a boundary you do not control. The drift is one of **proportion and
placement**: we now carry five bespoke "the-other-chain-is-truth" ingest pipelines, and
they are the loudest, most-recently-built surface in the repo. The I-confluent merge — the
*offchain* coordinator that is supposed to be the common case — is comparatively starved
(see §4.3).

### 2.2 Five chains, three inbound shapes — the bridge has no single abstraction

The watch/verify side is *not* unified the way the mint side is:

- `solana_relayer` / `ethereum_relayer` → verify finality + escrow binding, then **mint
  directly** via the committed nullifier path.
- `midnight_observer` → parse the event and **submit to dregg federation consensus**
  (`midnight_observer.rs:15,50`) — a different inbound model (consensus, not direct mint).
- `stripe_mirror` → a signed webhook from a **trusted oracle (Stripe)** stands in for chain
  finality (`stripe_mirror.rs:1-9`).
- the **cross-federation** path is yet a fourth shape (the phased `BridgeReceiptEnvelope`).

So there are at least three or four distinct "how does an external fact become a dregg mint"
mechanisms. Each new chain has been a fresh file with its own finality model, its own trust
seam, and its own submission path. There is a shared `JsonRpcTransport` byte-pipe and a
shared `bridge_mint_against_lock` sink, but no shared *bridge* abstraction in between. This
is N-notions drift, the same disease as §1.2, on the ingest side.

### 2.3 The bridges are LIVE at a trust grade *below* dregg's own bar

This is the sharpest finding. Every relayer is deployed at **`LockProofTrust::StructureOnly`**
— "a *re-executing validator that trusts the RPC's finalized commitment* accepts it"
(`solana_relayer.rs:26-44`; identical language in `ethereum_relayer.rs`, `mina_observer.rs`).
The fully-trustless path — folding the foreign chain's consensus + inclusion proof into the
EffectVM so a **dregg light client (not a re-executing validator) can witness the mint is
backed** — is explicitly deferred to "the circuit swarm's VK-epoch" in *every* relayer's
header, and is unbuilt at HEAD.

The whole point of dregg is light-client unfoolability (`CircuitSoundness.lean`,
`lightclient_unfoolable`). The bridges ship that guarantee's *negation* as their operating
posture: to believe a bridged mint you must re-execute and trust an RPC. We have built and
gone *live* with the chain-heavy mirror while the witnessed version — the version that is
the entire reason dregg exists — is a perpetual "owned by the circuit swarm." That is the
clearest instance of building the on-chain-ish thing eagerly and leaving the offchain-
verifiable thing as a named seam.

**Verdict (chain-relaying):** the conservation/nullifier spine is coherent; the bridge *as a
boundary* is the right idea. But we **over-relay** (five bespoke ingest pipelines, no single
abstraction) and we ship them at **re-execution/RPC trust**, below dregg's own light-client
bar, with the witnessed weld indefinitely deferred. The bridge has become the headline
surface; it should be the rare boundary.

---

## 3 · The cloud — per-op eager settlement is the quiet inversion

DreggNet's `ARCHITECTURE.md` states the loop plainly: "Tick the lease meter
(`StandingObligation`) each period; settle via `Payable`" (lines 113-117), and "DreggNet
bills for real execution … settled over dregg's open `Payable` rail" (lines 192-197).

The good news first: it is **not** chain-heavy toward *external* chains, and there *is* an
accumulation buffer. "On-chain" here means **dregg's own node ledger** (`POST
/api/turns/submit`, `control/src/node_api.rs`), not Solana/ETH. Meter ticks accrue into a
`dreggnet_meter` outbox keyed `(lease, period)` with `ON CONFLICT DO NOTHING`
(`durable/src/lib.rs`), and the bandwidth counter accrues unbilled bytes behind a billing
cursor (`webapp/src/hosting.rs`, commit 2440d72). So the *offchain accumulation* half of the
thesis is present.

The drift is the **cadence and the proof posture**:

1. **Settlement is per-op, not per-boundary.** `settle_meter_outbox`
   (`durable/src/settle.rs:317`) and the orchestrator's `settle_placement`
   (`control/src/orchestrator.rs:371-397`) settle **each metered period as one conserving
   `Effect::Transfer`** the instant dispatch completes. `NodeApiSettlement`
   (`control/src/node_api.rs`) submits **one Transfer turn per `(lease, period)`** to the
   node. There is **no batch, no reconciliation window, no boundary trigger** — the design
   is "settle-per-operation through the `Settlement` trait" (`settle.rs:179`), with the
   trait abstracting *only* the backend (in-process `ConservingLedger` today,
   `NodeApiSettlement` when reviewed-go flips), never the *cadence*. The thesis wanted
   accumulate-off-chain → reconcile-at-a-boundary; the cloud built accumulate-into-an-outbox
   → settle-every-period.

2. **The S3-gated endgame collapses the verification-mode lattice.** The verified store's
   target (`durable/src/verified.rs:65-73`) is that "each settled period becomes a **proof-
   attested on-chain dregg `Payable`**." Taken to the live edge, that is *Full-prove + settle*
   for **every metering tick** — exactly the rung-collapse the fidelity ladder exists to
   avoid. Proving is supposed to be *off* the commit path and *additive*; here it is being
   wired *onto* the settlement of every period. With bandwidth metering this is acutely
   wrong: a high-traffic site is "1M ticks/day → 1M on-chain transfers/day" if the per-op
   model is taken literally (the agent census flagged this; the bandwidth roll-up exists
   precisely because per-byte settlement is absurd — but the *compute/uptime* paths have no
   such roll-up).

3. **There is no offchain reconciliation path at all.** No CRDT, no vector-clock merge, no
   I-confluent accumulation in the cloud — settlement is strictly per-op through one
   `Settlement` trait. The cloud never asks "can these charges merge coordination-free and
   settle once at lease close?"

**Verdict (cloud):** not externally chain-heavy, and the outbox is the right primitive —
but the **settle cadence is per-op-eager**, the **proof posture (S3) collapses the ladder
to Full-prove-everything**, and there is **no reconcile-at-boundary** model. The vision's
"settle only when revocation is non-monotone at the boundary" became "settle every period,
and aspire to prove each one."

---

## 4 · Diagnosis — what went wrong with mostly-offchain coordination

The kernel never lost the thesis. The blocklace bridge still classifies most turns as
**`ExecutionTier::Sovereign`** — "executes immediately at the submitter's node without
waiting for consensus" — and only escalates `Ordered` turns to total order
(`breadstuffs/blocklace/src/dregg_bridge.rs:31-46`). The CALM split, the receipt chain, the
settlement-soundness boundary are all intact. So the dilution is **entirely in the layers we
bolted on top**, and it has three roots:

### 4.1 We reached for *a* chain because the chain was the easy correctness story

Every product question — "how do two providers agree a lease was paid?", "how does a bridge
believe a foreign lock?" — was answered by *settle/mint a turn on the dregg ledger* (or
mirror a foreign one) rather than *exchange a receipt and reconcile*. `settle.rs:30-50` is
candid: the design is "settle-per-operation through an abstracted `Settlement`," and the
only abstraction is *which ledger*, never *whether to defer*. The chain handles atomicity
and ordering for free, so it became the default coordinator even where a `BridgeReceipt`-
style bilateral receipt would do. **The receipt became proof-we-did-a-chain-op rather than
the-thing-that-lets-us-avoid-one.**

### 4.2 We shipped the chain-heavy half and deferred the witnessed half

The bridges are live at `StructureOnly` trust; the in-circuit witnessed weld is "the VK-
epoch, owned elsewhere." The cloud settles eagerly now; the proof-attested store is "S3-
gated." In both cases the **chain-coordinated version ships and the offchain-verifiable
version is a named seam** — the exact pattern the standing feedback warns against ("a named
seam is not a hole," but also: do not ship the easy on-chain 60% and park the hard
witnessed core). We did the easy half loudly.

### 4.3 The offchain substrate is under-built relative to the chain surface

The I-confluent *write* path — the rhizomatic `merge` interpretation (DREGG3 §2.4:
interp=executor, compile=circuit, **merge=CRDT-sync NOT yet built**) — is still essentially
unbuilt as a coordination mechanism. The *read* face exists (`dregg-query` classify + MMR
attest), and the formal gate is proven (`Confluence.lean`, `SemanticConvergence.lean`), but
there is **no production path where two cloud providers, or two agents, accumulate
coordination-free deltas and merge them without a settling turn.** Meanwhile we built five
chain relayers. The ratio is upside-down: the rare boundary (bridges) is over-served; the
common case (offchain merge) has no runtime.

---

## 5 · Re-grounding — recover the mostly-offchain thesis

Constructive, in priority order. None of these touch the kernel's soundness; they re-place
coordination where the thesis put it.

### 5.1 Promote the receipt to ONE coordination type, demote the logs

- Adopt the `BridgeReceipt`/`TurnReceipt` discipline as the **single product-wide receipt
  contract**: append-only, prev-hash-chained, signature-or-QC-bearing, *verifiable by a
  non-witness*. Make `DeployReceipt`/`PublishReceipt`/`BindReceipt`/storage receipts either
  *be* that (sign + chain them so a client can verify a deploy without trusting the host) or
  stop calling them receipts (they are logs).
- **Kill the lying field**: either populate and verify polyana's `Receipt.grant_chain`
  (`capability_spec.rs:217`) or delete it. A receipt that shapes authority it never binds is
  worse than none.
- Unify polyana on the chained `TurnShadowReceipt`; retire the parallel metering `Receipt`.

### 5.2 Make settlement reconcile-at-boundary, not per-op

- Introduce a **reconciliation cadence** into the `Settlement` seam, not just a backend
  choice. The natural boundaries are **lease-close, dispute, and revocation** (the non-
  monotone events) — settle the *accumulated* outbox as **one** conserving Transfer (or one
  netted multi-leg ring via the existing `intent`/`verified_settle` ring machinery) at those
  points, not one Transfer per period.
- The meter outbox + `SettleReceipt`'s exactly-once key is already the right offchain
  accumulator. The fix is downstream: a `SettleReceipt` should be the artifact two parties
  hold *between* settlements, with an on-ledger Transfer only at the boundary. This is the
  `BridgeReceipt` 2-phase pattern applied to leases.
- **Do NOT wire proving onto every tick.** Keep the S3 proof-attested `Payable` as the
  *boundary* artifact (a whole-lease or whole-epoch witnessed settlement), honoring the
  ladder: Symbolic/receipt during the lease, one Full/aggregated proof at close.

### 5.3 Give the bridge a single abstraction and a path to the witnessed bar

- Factor the five ingest pipelines behind **one `ForeignFinalitySource` + one inbound
  policy** (direct-mint vs federation-consensus is a *parameter*, not a per-chain rewrite).
- Treat `StructureOnly` as a **temporary, labelled trust floor with a burn-down**, not a
  shipping posture. The `bridge_leaf_adapter.rs` / `custom_leaf_adapter.rs` Fork-X work is
  the path to fold foreign finality into the EffectVM so a light client witnesses the mint —
  that is the bridge's actual completion, and it should be on the critical path, not "the
  circuit swarm's."

### 5.4 Build the offchain merge runtime (close the ratio)

- Stand up the DREGG3 §2.4 `merge` interpretation as a **production path**: two providers /
  agents accumulate I-confluent deltas (the `Sovereign`/grow-only fragment, gated by the
  proven `ConfluenceClassifier`) and merge coordination-free, escalating to a settling turn
  **only** when the classifier says the merge crosses the conservation/authority boundary.
  The read face (`dregg-query`) and the formal gate (`Confluence.lean`,
  `SemanticConvergence.lean`) already exist; the write/merge runtime is the missing half.
- This is the structural fix for §4.3: it gives the *common case* (offchain coordination) a
  runtime as real as the *rare case* (the bridge), and restores the intended proportion.

---

## Appendix · one-line scorecard

| Surface | Coherent with thesis? | Why |
|---|---|---|
| `TurnReceipt` chain, `BridgeReceipt`, `DequeueProof`, MMR attest | **Yes** | offchain-verifiable, chained/signed |
| blocklace `ExecutionTier` (Sovereign default) | **Yes** | most turns never touch consensus |
| Verification-mode ladder in the kernel | **Yes** | proving off the commit path (`prove_pool` drops-on-full) |
| polyana metering `Receipt`, deploy/publish/storage receipts | **Drift** | logs named "receipt"; one carries unbound authority |
| Bridge ingest (5 chains, `StructureOnly`) | **Drift** | over-relayed, no single abstraction, sub-light-client trust |
| Cloud settlement cadence | **Drift** | per-op eager Transfer; no reconcile-at-boundary |
| S3 proof-attested per-period `Payable` | **Drift** | collapses the fidelity ladder to Full-prove-everything |
| Offchain I-confluent *write*/merge runtime | **Missing** | read face + proofs exist; no production merge path |
