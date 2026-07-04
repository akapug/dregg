# The technical frontier — what the primitives unlock once composed

*A visionary-but-grounded companion to `docs/VISION.md`. Where `VISION.md` paints
the **product** (the Verifiable Agent Cloud, the merge runtime, the app store),
this paints the **technical** direction: the novel capabilities that fall out of
**composing the primitives that are now real**, not building new engines. Every
reach below names the primitive it stands on and the nearest buildable PoC. Read
for the shape; verify file:line and LIVE/PARTIAL claims against HEAD.*

---

## 0 · The primitives, real (the parts we compose)

Five things crossed from design into code, and each is a *primitive* — small,
general, attenuable, witnessed — not a feature:

- **The replenishing-budget cell + the `Meter` trait** (`exec/src/budget.rs`,
  `exec/src/meter.rs`). A `(budget, period, refill-queue)` object — the seL4-MCS
  scheduling-context shape — realized as a forge-detectable dregg cell that meters
  *actual* consumption against a ceiling that refills lazily up to `now`. It is
  **attenuable**: `attenuate(sub_budget ≤ budget, …)` mints a child that provably
  cannot over-draw the parent (`budget.rs:523`). It generalizes breadstuffs
  `cell/src/allowance.rs`.
- **The merge runtime** (breadstuffs `dregg-merge/`): an I-confluent CvRDT join
  (`MergeState::join`) gated by `classify_merge` (the Rust face of
  `Confluence.lean`), emitting a re-witnessable `MergeReceipt` that composes into
  the read face's MMR. Free merge when confluent; **settle at the boundary** when
  a bounded resource or a retraction participates.
- **`dregg-ipfs`** (`dregg-ipfs/`): a dregg blake3 content commitment *is* an IPFS
  CIDv1 (no re-hash). `CID == content_root` for a raw blob; a `dregg-merge` delta's
  `content_id` *is* its CID. The content-addressed merge-transport.
- **The agent loop** (`exec/src/agent.rs`, `exec/src/agent_toolkit.rs`): the braid
  of **budget + cap + receipt** — every decided action is metered (drawn from a
  budget cell), cap-gated (a `dga1_` caveat-chain credential), and sealed into a
  prev-hash-chained, signed receipt a non-witness re-verifies. The brain is a seam
  (`AgentBrain`); the toolkit wraps capabilities as cap-gated metered receipted
  tools.
- **The verification-mode lattice + the single-machine principle** (breadstuffs
  `turn/src/collapse.rs`; `project-dregg4-vision`): proving is *off* the commit
  path, on a ladder (Symbolic → Full → witness-bundle → recursive → aggregated);
  and dregg's honest bounds are **distributed** bounds — at `n=1` they collapse to
  strong-local properties (consistent checkpoint, immediate revocation, instant
  finality).

The thesis of this document: these compose into capabilities **no centralized
host and no chain-only system can assemble**, because the composition needs all of
{ocap lattice, conservation law, content-addressed identity, witnessed merge,
proof ladder} under one substrate — and dregg is the only place they coexist.

---

## 1 · The resource-capability — the budget cell as a universal resource primitive

**The composition.** A budget cell is, at once, four things the rest of computing
keeps as four separate subsystems:

1. **a quantity** — how much of an asset (dollars, CPU-seconds, bytes, tokens,
   memory pages) may be outstanding in a window;
2. **a rate** — `budget/period` is a sporadic-server bandwidth ceiling over a
   *sliding* window (the MCS reframing: `period` is granularity, not a wall-clock
   sale);
3. **an authority** — it is a *cell*, so it is attenuable down the cap lattice:
   `attenuate` mints a child sub-budget that *cannot* widen (`budget.rs:523`), so a
   parent hands out spend-rights without staying in the loop;
4. **a schedule** — because it *is* the seL4-MCS scheduling-context shape, the
   admission test `headroom_at(now) ≥ amount` is not only "may you pay" but "may
   you run next." Metering and scheduling are the same decision on the same cell.

So one cell is the **biller, the rate-limiter, the fair-share node, the escrow
bond, the agent leash, and the dispatcher** — `Meter`'s docstring already names
five hand-rolled meters it collapses; the deeper reach is the sixth, *scheduling*.
A QoS class is a budget; a priority is a period; backpressure is headroom; an SLA
is a budget cell; multi-tenant fairness is the attenuation *tree* (each tenant a
child, the lattice is the fair-share hierarchy); the Stingray non-contention split
(N settlers, each a child budget) is the same move as N sub-agents of one cap.

**Why this is novel / hard elsewhere.** Everywhere else these are distinct
substrates: cgroups/k8s for scheduling, a metering pipeline for billing, an escrow
contract for bonds, a token-bucket for rate. seL4 had the unifying insight —
*the scheduling context is a capability* — but confined it to one kernel on one
machine. dregg lifts it into a **portable, distributed, forge-detectable,
witnessed cell**: a "resource-capability" that is simultaneously *authority +
quantity + rate*, attenuable, and re-witnessable by a third party. That object
does not exist anywhere else. It is what lets the same primitive bound a runaway
agent, fund an escrow bond, split a hot account without locking it, and decide who
runs next — with one verification template and (per the house-capacity discipline)
one named VK seam.

**Nearest buildable PoC.** `dregg-sched`: a tiny work-conserving scheduler whose
*only* state is N budget cells (one per tenant/agent). Admission = `Meter::draw`;
the cell that has matured headroom runs next. Demonstrate three things on the
local path with the cells we have: (a) a runaway tenant is rate-bounded *by
construction*, not by a watchdog; (b) a child sub-agent provably never starves its
parent (the attenuation `sub_budget ≤ budget`); (c) the *same* cells that decided
dispatch produce the invoice — one object, the scheduler *and* the bill,
re-witnessable. This is days from HEAD because `budget.rs`/`meter.rs` already
expose `draw`/`attenuate`/`headroom_at`; the new code is the dispatch loop.

---

## 2 · Confluent decentralized verifiable state — merge runtime ⋈ IPFS ⋈ the gate

**The composition.** N parties each hold a copy of a cell. Each applies
**I-confluent** ops to its own copy *offchain, partition-tolerant, no consensus*.
They exchange their delta grow-sets **over IPFS by CID** — dedup is free (a G-Set
union is idempotent; re-fetching a CID is a no-op), a delta's `content_id` *is* its
IPFS address (`dregg-ipfs::delta_cid`), and a retraction's target is a Merkle link
that resolves to the delta it retracts. They **merge locally**: `MergeRuntime::merge`
consults `classify_merge`; a confluent merge runs the CvRDT join and emits a
chained `MergeReceipt` (re-witnessable, MMR-composing) with **no chain op**; a
non-confluent merge is **refused** with `Escalation::MustSettle` — routed through
one settling turn at the boundary, the only place revocation is non-monotone
(`SettlementSoundness.lean`).

**Why this is novel / hard elsewhere.** Local-first/CRDT systems (Automerge, Yjs,
the rhizomatic G-Set) converge — but they cannot express a *bounded* invariant
(`balance ≥ 0`, a conservation law): two locally-valid withdrawals merge to an
overdraft, so those systems simply forbid linear value. dregg's distinguishing
asset is the **gate**: a *proven* classifier (`Confluence.lean`'s
`cardLeOne_not_iconfluent` keystone) that draws the line precisely — free-merge
the confluent writes, settle the non-monotone ones — so dregg can carry *both* a
grow-only collaborative document *and* a conserved balance in the same cell and
know, per merge, which path is legal. The second asset nobody else has: the merge
is **witnessed** — a `MergeReceipt` a non-witness re-verifies, composing into the
read face's non-omission MMR. CRDTs converge silently; dregg's merges leave a
verifiable trace. IPFS supplies the decentralized any-node transport for free
because the identity already aligns (`CID == content_root`).

The apps this unlocks — collaborative docs, offline-first multi-device sync,
multiplayer (branch-and-stitch), distributed agent memory (the rhizomatic Chorus
shape: converge-by-union, retroactive distrust) — are all **verifiable** and all
*know exactly which writes are coordination-free and which must settle*. That is
the architecture-critique's prescribed re-grounding (§5.4) made into a capability.

**Nearest buildable PoC.** A two-device offline-first collaborative cell synced
*only* over IPFS: edit both offline, exchange grow-sets by CID, merge with
receipts. Demonstrate the gate doing real work — a grow-set of document edits
merges *freely* (confluent), while a balance-overdraft merge is *refused* and
collapses to one netted settle at the boundary. `dregg-merge`'s
`offchain_coordination.rs` test plus the `dregg-ipfs` round-trip already prove each
half; the PoC is the wiring (the `delta_cid` transport adapter + a two-replica
driver) — the architecture-critique calls this exactly "the write/merge runtime,
the missing half."

---

## 3 · Verifiable data / compute pipelines — provenance as a receipt chain

**The composition.** Chain agents + toolkit tools + merges into a DAG where every
node is receipted. A stage takes a cap-gated input (a dataset addressed by its
**CID**), runs a metered toolkit workload (`run_tests`/`run_workload` over a
compute tier), and emits an output whose receipt **binds the output commitment to
the input commitment, the code's CID, the cap exercised, and the budget drawn**.
Fan-in stages combine intermediate results through the merge runtime. The whole
pipeline's output carries a receipt chain a consumer re-verifies with
`verify_chain` + content-address checks — a *provable provenance graph*. The
verification-mode lattice rides on top: a cheap Symbolic receipt for the bulk
steps, a Full/recursive proof at the gate stage where assurance is worth paying
for.

**Why this is novel / hard elsewhere.** ML/data lineage today is trusted metadata
(MLflow tags, lineage annotations); supply-chain attestation (SLSA, Sigstore)
proves the *build artifact's* provenance but not the *data*, not the *cost*, not
*cap-bounded execution*. dregg makes the lineage a **receipt chain**: you can prove
a result came from *exactly* these (committed) datasets, through *this* (CID'd)
code, *within* this budget, by *this* cap-bounded agent — because compute, data
identity, authority, and cost are the same witnessed objects. A forged "trained on
the licensed data only" breaks a signature, not a policy.

**Nearest buildable PoC.** A three-stage pipeline — fetch a dataset by CID →
transform via a toolkit workload → emit a result — whose final artifact carries the
end-to-end receipt chain, re-verified by `verify_chain` plus the content-address
check on each input. The toolkit, the receipt chain, and the IPFS CID exist; the
build is the DAG combinator that threads one stage's output commitment into the
next stage's input cap.

---

## 4 · The single-machine principle, taken to the agent cloud

**The composition.** A provider node running many agent-cells *is* an `n=1` system
over those cells, and at `n=1` the distributed bounds collapse
(`project-dregg4-vision`): a **consistent global checkpoint** of all agent state
(the same EROS/KeyKOS snapshot mechanism the pay-only-while-awake sleep already
uses), **immediate revocation** of a misbehaving agent's caps (no recency floor),
**synchronous atomic cross-cell commit** (a swarm of sub-agents commits or aborts
together, no 2PC blocking), **instant finality** of inter-agent transfers, and real
mark-sweep GC. The bounds reappear *only* when agents cross a provider boundary —
which is exactly where §2's merge gate + settlement-soundness already live.

So the agent cloud is a **lattice of `n=1` strong-local islands** joined by
settle-at-boundary merges: each provider gives its agents strong properties for
free; only cross-provider coordination pays the distributed tax. This is the
topology-parametrized bound made into an architecture — never pay the distributed
price for a non-distributed workload.

**Why this is novel / hard elsewhere.** The whole industry builds "agent clouds" on
a distributed-by-default stack (k8s + an eventually-consistent store, or a chain)
and pays the tax everywhere: no clean snapshot, slow revocation, no atomic
multi-agent transaction. dregg's insight is that *most* agent work is single-machine
and should get single-machine properties; you go distributed only at the boundary,
and there the proven gate handles it. The capabilities that fall out are ones a
distributed-by-default cloud structurally cannot offer: **time-travel debugging of
a whole agent fleet** (consistent snapshot + RCCS reversibility), **atomic swarm
transactions**, an **instant cap kill-switch** (revoke and the next receipt is
refused — provably dead), and **checkpoint/restore/fork of a live agent** (the umem
continuations revolution).

**Nearest buildable PoC.** A single-provider agent-node that (a) takes a consistent
snapshot of all running agent-cells, (b) revokes one agent's caps and shows the
next action refused in-band (provably dead, not "scheduled for termination"), and
(c) forks an agent from a checkpoint. Then stand up a second node and merge at a
boundary — the *only* place the distributed bound appears. The snapshot/sleep
mechanism (`durable/`, umem) and the cap-revocation path exist; the PoC is the
strong-local control surface over them.

---

## 5 · The verification-mode lattice as a product knob — pay for the assurance you need

**The composition.** The rungs are real (`collapse.rs` `WitnessMode`,
`recursive_witness_bundle.rs`, the IVC fold) and proving is *off* the commit path.
Exposed as a **per-read knob**, assurance becomes something the *consumer* chooses:
Symbolic for snappy local/dev, Full for publishing, a witness-bundle for a
re-executing validator who will replay (cheaper — no ZKP verify), a recursive O(1)
proof for a light client who will not, an aggregated proof for cross-chain settle.
The same turn, a different rung, a different price/latency — and climbing a rung
*never* blocks the write path, because proofs are additive attestation, not
permission.

**Why this is novel / hard elsewhere.** Every other verifiable system picks one
point on this axis and bakes it in (a zk-rollup proves everything; a plain chain
proves nothing extra). dregg makes assurance a **dial** because its proof system is
decomposed into a ladder where each rung is independently sound and the cheap rung
is producible without the expensive one. A consumer says "I'm a light client, give
me the recursive proof"; another says "I'll re-execute, give me the bundle" — and
pays accordingly.

**Nearest buildable PoC.** A `verify --mode {symbolic|full|bundle|recursive}` knob
over a single served artifact, surfacing the size/latency/trust trade per rung: one
cell read, four assurance levels, four prices. This is the orchestration layer over
the existing rungs — the "rung-selection policy" the mode-lattice memo names as
greenfield.

---

## 6 · The two deepest bets — and why they are one architecture

Of the five, two are *primitive unifications* (the rest compose on top of them):

> **Bet I — the resource-capability (§1):** authority + quantity + rate + schedule
> in one attenuable, witnessed cell. The intra-node unifier: what runs, what is
> owed, what may be delegated — all the same object, all strong-local.
>
> **Bet II — confluent decentralized verifiable state (§2):** CRDT local-first that
> *knows its confluence boundary* (the proven gate) and *proves its merges* (the
> receipt/MMR), transported over IPFS by content identity, settling only at
> non-monotone boundaries. The inter-node unifier: how copies converge.

These are not two bets — they are the two halves of **one topology-parametrized
architecture**, and the **single-machine principle (§4) is the bridge**:

- *Inside* a node (`n=1`), budget cells (Bet I) give resource control its
  strong-local form — a budget *is* the scheduler, the bill, and the leash, with
  instant revocation and a consistent snapshot.
- *Across* nodes (`n>1`), the merge gate (Bet II) carries the coordination-free
  common case and pays the distributed price *only* at the boundary — exactly where
  a budget's settlement and a cell's revocation become non-monotone.

So the deep technical direction is: **make resource and authority the same
attenuable cell (Bet I), make state convergence confluence-gated and witnessed
(Bet II), and let deployment topology — not a fixed assumption — decide which
bounds apply (the single-machine principle).** §3 (verifiable pipelines) is then a
DAG of budget-metered cap-gated stages whose lineage is the receipt chain; §5 (the
assurance dial) is the knob on every read. Two unifications, one bridge, three
capabilities riding on top.

Nothing here is a new engine. Every piece named is a file in this tree or its
breadstuffs sibling. The frontier is the *composition* — and it is reachable from
HEAD.

---

*Dated 2026-06-30. Bold by intent, grounded by discipline: the budget cell, the
merge runtime, `dregg-ipfs`, the agent loop, the mode lattice, and the
single-machine principle are real; the capabilities above are what they unlock when
composed. Verify file:line and LIVE/PARTIAL claims against HEAD before relying on
any specific one.*
