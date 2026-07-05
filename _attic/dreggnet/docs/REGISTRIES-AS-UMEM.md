# Registries as umem cells — re-dregg the substrate (the #2 move)

*The design for move #2 of `docs/{MYOPIA-AUDIT,THE-BIGGER-DREGGNET}.md`: re-anchor the
DreggNet registries on the **real umem heap** so persistence is a committed boundary
root (not a from-scratch JSON-lines log), and the registries gain **fork / merge /
time-travel** — the superpowers a `Mutex<…map>` + `dreggnet-store` can never give.*

*Dated 2026-06-30, DreggNet `dev`. DESIGN-FIRST; the BUILD lands the cleanest 1–2
registries (sites + domains) and NAMES the seam for the rest. Verify `file:line`
against HEAD before betting on it.*

---

## 0 · The one-paragraph thesis

Today ~10 registries (sites `webapp/src/hosting.rs`, buckets `storage/src/registry.rs`,
domains `dregg-domains/src/lib.rs`, mesh `control/src/mesh.rs`, the front-office stores)
are serde structs in `Mutex<…map>`s, persisted (where at all) through `dreggnet-store`
(`store/src/lib.rs`) — a from-scratch append-only JSON-lines log with torn-tail recovery,
compaction, and a blake3 `content_root`. **`dreggnet-store` re-implements, byte for byte,
exactly what a committed umem heap already gives** (its own doc says so:
*"a careful, well-built reimplementation of exactly what a committed umem heap
provides"*). The re-dregg move: **a registry IS a umem cell** — a committed heap keyed
`(collection, key) → value`, whose durable persistence + reconstruction IS the heap
commit/restore, whose boundary root IS the real sorted-Poseidon2 `compute_heap_root`
(the same boundary the compute-as-cell and account-recovery lanes depend on). This
DELETES `dreggnet-store` as registries move off it, and unlocks fork/merge/time-travel
across hosting + storage + domains at once.

---

## 1 · A registry IS a umem cell

### The shape

A registry maps `resource-id → record` (site name → `SiteCell`, domain → `DomainBinding`).
A umem cell carries a heap: a `BTreeMap<(u32 collection, u32 key), FieldElement>` (where
`FieldElement = [u8; 32]`) whose **boundary** is `dregg_cell::compute_heap_root` — the
Rust shadow of the Lean `Substrate.Heap.root`, a sorted-Poseidon2 binary Merkle tree over
`hash[hash[coll, key], value]` leaves, pinned by the proven `root_binds_get`
(`breadstuffs/cell/src/state.rs:409`).

The map is direct: **each record is a collection in the cell's heap.** A record's canonical
bytes (its JSON) are laid into the heap as length-delimited 32-byte leaves:

```
  collection c (one per record)        leaf (c, 0) = byte length (u64, LE)
  ────────────────────────────         leaf (c, 1) = JSON bytes [0..32]
  store_key  "blog"                     leaf (c, 2) = JSON bytes [32..64]
  record     SiteCell{ … }              …
                                        leaf (c, n) = JSON bytes [last chunk, zero-padded]
```

- **Persistence** = the umem heap commit: reseal `heap_root` (`reseal_heap_root`), the
  32-byte boundary root, and durably materialize the heap leaves. **Not** a JSON-lines log.
- **Reconstruction** = restore from the committed heap: load the leaves, **re-derive the
  root and check it matches the sealed root** (the `root_binds_get` boundary check — fail
  closed on tamper), then reassemble each collection's JSON and deserialize the record.
  The record is rebuilt FROM the heap; the heap IS the store.
- **The boundary root** replaces `dreggnet-store`'s blake3 `content_root` with the kernel's
  real Poseidon2 heap root — the commitment a dregg light client understands.

### Why this is faithful, not a re-skin

`dregg_cell::compute_heap_root` is the *kernel's own* heap boundary (not a DreggNet hash):
the same function the substrate commits a cell's umem heap with, the one
`UMEM-PRIMITIVE.md §2` and `dregg-doc/src/doc_heap.rs` ("the document IS a cell with a
umem-heap") ride. Depending on it is the move the firewall dissolution unblocks
(`FIREWALL-DISSOLUTION.md` — ember owns the substrate; DreggNet is AGPL): **depend on the
real substrate, don't re-implement it.**

---

## 2 · The payoffs `dreggnet-store` can never give

A JSON-lines append-log is a flat sequence of records. A umem heap is a *committed,
content-addressed state object*. That difference IS the three superpowers:

### Fork — a tenant forks their whole hosting namespace
A registry's durable form is its heap. **Fork = copy the heap** into a second registry over
its own path: now two divergent copies descend from one root. A tenant forks their entire
`SiteRegistry` (every published site at once), serves the fork, and stitches or discards it
— a preview/branch deploy of a whole namespace. A `Mutex<BTreeMap>` + append-log has no
"copy the committed state and diverge" operation; the heap does (`UmemRegistry::fork`).

### Merge — collaborative, multi-writer registries with a conservation law
Because a registry is now a cell with a content-addressed leaf-set, the **merge runtime
(`breadstuffs/dregg-merge`) applies directly** (see §4). Two replicas of a registry each add
records offline; the heap leaf-set is a **grow-only set** (`dregg_merge::GrowSet`,
`asserted: BTreeMap<Hash, Delta>`, `join = ∪`); `classify_merge` decides per write — free
merge when I-confluent, settle at the boundary when a conserved quantity participates. This
is the structural unblock: a serde-struct registry has nowhere for the I-confluent
write/merge path to live; a umem-cell registry IS that home.

### Time-travel — "my domains as of yesterday"
Each commit tags a snapshot by its boundary root. **Restore an earlier root** → the
registry at that point. A tenant rolls their hosting/domain namespace back to a prior
committed state (instant rollback, time-travel debugging). The append-log only ever grows
forward (compaction *destroys* history); the root-addressed heap snapshot retains it
(`UmemRegistry::checkpoint` / `restore`).

---

## 3 · The map — each `Mutex`-map registry onto a umem cell

| Registry | File (HEAD) | Record | Re-dregg disposition |
|---|---|---|---|
| **Sites** | `webapp/src/hosting.rs:575` `Mutex<BTreeMap<String, SiteCell>>` | `SiteCell` (name, owner, content_root, content) | **MOVED** — `UmemRegistry<SiteCell>`, this PR |
| **Domains** | `dregg-domains/src/lib.rs:408` `Mutex<BTreeMap<String, DomainBinding>>` | `DomainBinding` (domain, site, owner, state) | **MOVED** — `UmemRegistry<DomainBinding>`, this PR |
| **Buckets** | `storage/src/registry.rs` | `BucketCell` (name, owner, content_root, content) | **MOVED** — `UmemRegistry<BucketCell>`; the bucket-store cell commits to a Poseidon2 boundary root, gains namespace fork/checkpoint/restore |
| **Mesh nodes** | `control/src/mesh.rs` | `MeshNode` | **MOVED** — `UmemRegistry<MeshNode>`; the mesh registry forks + time-travels |
| **Servers** | `control/src/server.rs` | `ServerRecord` | **MOVED** — `ServerStore` now wraps `UmemRegistry<ServerRecord>` (the record store; the per-server STATE cell is the adjacent compute-as-cell lane #1). The terminal-record sweep is a real umem `remove` — the swept record is provably gone from the committed heap |
| **Secrets / orgs / logs** | `dregg-secrets`, `org`, `dreggnet-logs` | versions / memberships / log lines | NAMED SEAM — front-office stores; same primitive |

**`dreggnet-store` is DELETED.** With sites + domains (this doc's #2 PR) and now buckets +
servers + mesh moved onto the real umem heap, the from-scratch JSON-lines log crate has
zero consumers and was removed (the `store/` crate dir gone, the workspace member line
gone). The whole durable-registry reimplementation is replaced by the committed umem heap —
the substrate myopia carved out, root and branch.

**Sites + domains were the cleanest first** (content-addressed, owner-keyed, already
cap-gated + receipted, already real-Poseidon2 `content_root` on the site) so the umem swap
is purely a *backend* change behind an unchanged registry API; buckets + servers + mesh
took the identical swap.

---

## 4 · How this unblocks the merge runtime (the #3 move)

`docs/THE-BIGGER-DREGGNET.md §4 #3` ("unblock the merge runtime") is **structurally
blocked until resources are umem cells** — *"because no resource is a umem cell, the
I-confluent write/merge path has nowhere to live."* Registries-as-umem-cells is exactly
the precondition it names:

- A `UmemRegistry`'s heap is a `(collection, key) → value` leaf-set. The natural CvRDT over
  it is `dregg_merge::GrowSet` — a record = an asserted delta keyed by content id, `join`
  is set union (`breadstuffs/dregg-merge/src/state.rs:76`), and the gate
  `classify_merge` (`gate.rs:84`) decides: two tenants each publish disjoint sites offline
  → **I-confluent, free local merge** (no consensus); a conserved quantity (e.g. a billing
  balance leaf) participating → `Escalation::MustSettle` at the boundary.
- The transport is content-addressed by the boundary root (a registry's root IS its CID),
  so two replicas exchange leaf-deltas and `join` locally — the "mostly-offchain
  coordination" superpower (`VISION` Bet #2) lands the moment the registry is a cell.

So this PR's `UmemRegistry` is the object move #3 builds the two-replica driver over: the
heap leaf-set → `GrowSet` adapter + `classify_merge` gate is a *days-from-HEAD* weld once
the registry is a cell, because each half is already proven in breadstuffs. **Before this
PR the merge runtime had no registry-shaped cell to merge; after it, it does.**

---

## 5 · The build — what lands, what is named

### Lands (this PR)
- **`dreggnet-umem`** (new crate, `umem/`): `UmemRegistry<R: Record>` — the umem-cell-backed
  registry primitive. Depends on the real `dregg-cell` (the same breadstuffs git rev
  `webapp` already pins for `dregg-circuit`), holds a `dregg_cell::CellState` as the
  registry's umem cell, and exposes a `RegistryLog`-compatible API (`open`/`append`/`all`/
  `get`/`keys`/`len`/`contains`/`path`) **plus** the umem superpowers (`boundary_root`,
  `fork`, `checkpoint`/`restore`). The `Record` trait is the same shape `dreggnet-store`
  uses, so existing `impl Record for SiteCell / DomainBinding` move over unchanged.
- **`SiteRegistry`** (`webapp`): `store: Option<UmemRegistry<SiteCell>>`; `with_durable_store`
  opens the umem cell; `publish` commits to the heap. Callers unchanged; the existing
  `durable_sites_restart.rs` round-trip test passes against the umem backend.
- **`DomainRegistry`** (`dregg-domains`): same swap for `DomainBinding`.
- **Tests**: umem round-trip (publish → commit to a boundary root → drop → restore →
  reconstructed exactly-once, owned correctly), fork (two divergent copies from one root),
  time-travel (restore an earlier root).
- **`dreggnet-store` shrinks**: `webapp` and `dregg-domains` drop the `dreggnet-store`
  dependency. The crate remains only for `storage` + `control/mesh` (the not-yet-moved
  registries) — visibly on the path to deletion.

### Named seams (honest)
- **The durable materialization of the heap.** In production the dregg **node's committed
  heap** is the durable store (the on-chain `Effect::Write`, the circuit swarm's VK-epoch).
  Here `UmemRegistry` materializes the cell's heap leaves to a local content-addressed
  snapshot keyed by the boundary root — the node's job, stood in locally. This is the ONE
  seam: the heap-snapshot file is where a real node's committed heap goes. It is **not** a
  re-implementation of registry semantics (that was `dreggnet-store`); it is blob
  persistence of umem leaves with a fail-closed boundary check.
- **The remaining registries** (buckets, mesh, secrets, orgs, logs) keep `dreggnet-store`
  until they take the identical swap. `dreggnet-store` is not deleted in this PR — it is
  *shrunk* (two of its users gone) and named for deletion once the rest move.
- **The in-circuit witness** that the boundary root is the genuine committed state (a light
  client, not just a re-executing validator, sees the commit) remains the circuit swarm's
  VK-epoch — the same seam the site `content_root` already names. The OFF-chain half (real
  Poseidon2 boundary, re-derivable + fail-closed on restore) is closed here.

---

## 6 · The through-line

`dreggnet-store` was the substrate myopia in miniature: a whole crate built to give
registries the durable, content-addressed, witnessed state that *a committed umem heap
already is*. Re-anchoring the registries on the real umem heap is **less code** (the crate
deletes as its users move), **sounder** (the kernel's proven `compute_heap_root` boundary
replaces a hand-rolled blake3 log), and **strictly more capable** (fork/merge/time-travel,
which no `Mutex<BTreeMap>` + append-log can do). The hat was real; this carves the body —
the registry — out of umem, and it learns to fork.

---

*Companion: `docs/MYOPIA-AUDIT.md §7` (the `dreggnet-store` finding), `THE-BIGGER-DREGGNET.md
§4 #2/#3`, `FIREWALL-DISSOLUTION.md` (depend-on-substrate unblock), and
`~/dev/breadstuffs/cell/src/state.rs` (`compute_heap_root`, the umem heap) +
`~/dev/breadstuffs/dregg-merge` (the merge runtime #2 unblocks). ( ⌐■_■ )*
