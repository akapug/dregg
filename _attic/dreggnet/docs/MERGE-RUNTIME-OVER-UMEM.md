# The merge runtime over umem registries — the #3 re-dregg move

*The production realization of `breadstuffs/dregg-merge` over real cloud resources: two
replicas of a umem registry reconcile **offchain** — confluent writes merge free, a
conserved quantity settles at the boundary, and every free merge leaves a re-witnessable
trace. This is the I-confluent write/merge path the offchain-coordination thesis named, now
with a home. Companion: `docs/REGISTRIES-AS-UMEM.md §4`, `docs/THE-BIGGER-DREGGNET.md §4
#3`, `docs/ARCHITECTURE-CRITIQUE.md §4.3/§5.4`.*

---

## 1 · The unblock

The architecture critique's deep finding was structural, not cosmetic: the
offchain-coordination thesis (`VISION` Bet #2 — *"mostly off-chain coordination, settle only
at the boundary"*) was blocked **because no resource was a umem cell**. The merge runtime
(`dregg-merge`) and its formal gate (`Dregg2.Confluence` / `SemanticConvergence.lean`)
already existed; the read face (`dregg-query`) already existed. But the I-confluent
write/merge path had **nowhere to live** — a `Mutex<BTreeMap>` + JSON-lines log is not a
content-addressed CvRDT, so there was no registry-shaped object to merge.

The #2 move fixed that: `dreggnet-umem`'s [`UmemRegistry`] (`umem/src/lib.rs`) is a real
`dregg_cell::CellState` whose `(collection,key) -> value` heap holds the records and whose
boundary is the kernel's sorted-Poseidon2 `compute_heap_root`. Its heap leaf-set **is** a
`dregg_merge::GrowSet`. This document is move #3: the merge runtime built **on that object**
(`umem/src/merge.rs`).

## 2 · The driver

A registry's live records are adapted into a `GrowSet`: **each record is one content-
addressed `Assert` delta** on a shared logical cell id, carrying the record's canonical JSON
(the same bytes the umem heap lays in), authored by a fixed registry tag so two replicas
that independently `append` the byte-identical record produce the **same** delta — the union
deduplicates them (idempotence). The driver adds two methods to `UmemRegistry<R>`:

- **`grow_set(cell)`** — the CvRDT view of this replica's records. A third party can rebuild
  it to re-witness a merge.
- **`merge(other, cell, runtime)`** — the two-replica driver. It consults the confluence
  gate `dregg_merge::classify_merge`:
  - **Confluent → FREE.** Disjoint (or identical) record-sets merge by set union —
    commutative, associative, idempotent, order-independent — and the other replica's
    records are folded in. Returns a chained, re-witnessable `MergeReceipt`. **No consensus,
    no chain op.** Two replicas, each merging the other, converge to one record-set.
  - **Conserved → SETTLE.** When the replicas diverge on the *same* logical key (a single-
    writer register written with two different values — the "billing balance leaf" /
    bounded-resource shape), reconciling it requires **retracting the loser**, a non-monotone
    op. The driver injects exactly that retraction so the **gate** (not a hand-rolled branch)
    renders the `Escalation::NonMonotoneOp` verdict, returns `RegistryMergeError::Settle`,
    and **leaves the replica unchanged**. The write must go through a settling turn at the
    boundary — the one place revocation is non-monotone (`SettlementSoundness.lean`).

## 3 · The mergeable receipt

Every free merge emits a `MergeReceipt`: the merged GrowSet commitment, the per-delta
provenance (which replica contributed each delta — `A`/`B`/`Both`), and a prev-hash chain.
A third party who holds the two input GrowSet views calls `MergeReceipt::rewitness` —
recompute the join, check the commitment — and is convinced the merge is the genuine CvRDT
join of exactly those inputs, **with no chain op**. The offchain coordination leaves a
verifiable trace; a forged merged commitment fails the re-witness (a tamper tooth).

## 4 · The teeth (`umem/tests/two_replica_merge.rs` + `umem/src/merge.rs`)

1. **confluent-free + deterministic** — two operators add disjoint domains offline → merge
   is free → each gains the other's records → both replicas converge to the same record-set
   (equal GrowSet commitments); `join` is commutative (order-independent merged commitment)
   and re-merging is idempotent (a no-op).
2. **conserved-conflict-settles** — two replicas claim the same key with different bindings →
   the gate refuses → `Settle{ NonMonotoneOp, conflicts: [key] }` → the replica is unchanged
   (no record crosses the boundary on a settle). Plus the literal bounded-resource shape: a
   `BoundedCounter` (a balance) is refused `NonIConfluentKind` by `classify_merge`.
3. **the merge receipt verifies** — a genuine receipt re-witnesses over the input views; a
   forged merged commitment fails.

## 5 · How this realizes the offchain-coordination thesis

Two operators each hold a replica of a domain (or site) registry. Each registers domains
*offline, partition-tolerant, with no coordination* — these are grow-only adds, the
I-confluent shape, so they need no consensus. When the two replicas exchange leaf-deltas and
`join` locally, confluent writes merge **free**: the merge is a *local* operation neither
side has to be told is legal (BEC Thm 3.1 — concurrent invariant-preserving versions merge
invariant-safely). The chain is touched **only** when a conserved quantity participates — a
divergent single-writer register, a balance — and then exactly at the settling boundary.
That is "mostly off-chain coordination, settle only at the boundary," made real over the
registries that run the cloud.

## 6 · The named in-circuit seam — `MergeRefinesConfluence`

The merge here is **executor-grade**: a re-witnessing peer who holds the two input GrowSet
views is convinced. That a *light client* — not a re-executing peer — sees the merge
preserved the invariant, i.e. that this driver's `join` **IS** the `⊔` the Lean gate
(`Dregg2.Confluence`) reasons about, **witnessed in-circuit**, is the **`MergeRefinesConfluence`
weld**: the swarm's VK-epoch, the same shape the registry's committed-boundary witness
(`CommitBindsMMR`) already names. The off-chain half (the CvRDT join, the gate's dichotomy,
the re-witnessable receipt) is closed here; the in-circuit tooth is its named shadow. This
module adds no Lean theorem — the CRDT laws and the gate's dichotomy are already machine-
checked over the abstract lattice (`Confluence.lean`, `SemanticConvergence.lean`, axiom-clean,
both polarities witnessed); `merge.rs` is their executable realization over real registries.

## 7 · The honest boundary on convergence

The merge's canonical, order-independent commitment is the **GrowSet commitment** (the
`MergeReceipt.merged` field) — it commits the sorted set of delta ids, so it is identical on
both replicas after they converge, regardless of merge order. The umem cell's Poseidon2
`heap_root` is a per-replica **storage** root: it depends on the heap's collection-assignment
layout, which can differ between replicas that appended in different orders even when they
hold the identical record-set. So convergence is asserted at the content level (the GrowSet
commitment / the receipt), not claimed for the per-replica Poseidon2 layout root. A canonical
(sorted) re-lay that makes the storage roots converge byte-identically is a clean,
non-load-bearing follow-up — the merge's verifiable identity is already the content
commitment.
