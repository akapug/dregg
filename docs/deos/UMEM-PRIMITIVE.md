# umem as a general primitive

A *umem* is **a witnessed key→value store whose committed root is its boundary**: a
`(domain, key) → value` address space, a Blum memory-checking trace of the accesses to it,
and a sorted-Poseidon2 root over its final present cells that any verifier can bind to. Today
dregg has exactly ONE umem — the whole world's state, in five domains
(`turn/src/umem.rs:90`, `metatheory/Dregg2/Crypto/UniversalMemory.lean:75`). This doc designs
umem as a **reusable primitive**: per-cell heaps, transient working memories, *passable*
intermediate states, and composed umems — all the same construct.

The enabler this doc assumes (landing in parallel): **the boundary-binding keystone** —
`boundary_init_root_bound` / `boundary_init_root_derived`
(`metatheory/Dregg2/Crypto/UniversalMemory.lean:463,475`) welded into the circuit so a umem's
*init* image is pinned to a committed root supplied as a public input, the same way the *final*
image already is (`boundary_root_from_memcheck`, line 429). With both edges bound, a umem
becomes a value you can **hand off and resume**: the receiver re-pins the init root and inherits
soundness. That is what unlocks uses 2–4.

## 1. What a umem IS (the one construct)

Three parts, all already present:

| part | what it is | where, today |
|------|-----------|-------------|
| **address space** | `(domain, key) → Option value`, domains disjoint by tag | `UDomain`/`UKey`/`UVal` `turn/src/umem.rs:90,115,250`; Lean `UAddr κ := Domain × κ` `UniversalMemory.lean:86` |
| **access trace** | Blum `(kind, addr, val, prev_val, prev_serial)` ops; ONE balance certifies consistency of every domain projection | `UMemOp` `turn/src/umem.rs:413`; `UMemOpSpec` `circuit/src/descriptor_ir2.rs:363`; `universal_memory_sound` `UniversalMemory.lean:197` |
| **boundary** | sorted-Poseidon2 root over final present cells = the committed commitment | `boundaryCells`/`boundary_root_derived` `UniversalMemory.lean:320,416` |

The load-bearing properties, all `#assert_axioms`-clean (`UniversalMemory.lean:772`):

- **Tag isolation** — `(d,a)=(d,b) ↔ a=b` is wire-literal; a write in one domain can never
  cancel a claim in another (`consistentFrom_filter`, `consistentFrom_strip`, lines 118/154).
  This is the property that lets *many* umems coexist in *one* trace without aliasing.
- **Final-column pinning** — the prover's claimed final cells ARE the genuine fold
  (`memcheck_pins_final`, line 281), so the derived root is trustworthy, not prover-chosen.
- **Boundary = today's roots** — the derived root equals the existing map root by canonicity,
  no crypto in the derivation (`boundary_root_derived`, line 416).
- **No-chip-table cost** — a umem write+read-back is 67.6 KiB vs 128.7 KiB as a boundary map
  op (`descriptor_ir2.rs:75`); freshness is ONE read row returning `none`, Merkle-path-free
  (`nullifier_fresh_sound`, line 554).

The key design realization: **the five `Domain` values are not the alphabet — they are an
*instance*.** The construct is parametric in `κ` (the in-domain key) and the domain tag is just
"which umem / which plane". A per-cell heap, a service's scratch, a checkpointed computation are
all "another disjoint slice of the same `Domain × κ` algebra". Everything below is *naming a new
slice*, never a new table.

---

## 2. Per-cell umems (heaps)

**The model.** A cell's heap IS its own umem. The address space is `(collection_id, key)`; the
boundary is `heap_root`; the prover-side store is `heap_map`. A cross-cell read is *reading
another cell's umem boundary* — you bind that cell's committed `heap_root` and open the key.

**Reusable (already built).** This is the most-grown embryo:

- `CellState.heap_root` (committed, folded into the canonical commitment v6→v7) + `heap_map`
  (`(u32,u32) → FieldElement` prover store) — `cell/src/state.rs:210,224`; `compute_heap_root`
  over a `(collection_id, key) → value` map, with `collection_id_binds_heap_root` proving
  collections don't alias (`cell/src/state.rs:403,1289`).
- The unbounded `fields_map`/`fields_root` (keys ≥ 16) is the *same shape* one plane up —
  `cell/src/state.rs:181,190`. It is "the embryo" the owner named: an unbounded, root-committed
  per-cell map, exactly a umem domain restricted to one cell.
- The projection already lands every per-cell plane at `Field{cell,slot}`, `HeapRoot(cell)`,
  etc. under `Heap` domain (`turn/src/umem.rs:274`). The per-cell view is *a filter of the
  global umem by `UKey::cell()`* (`turn/src/umem.rs:213`).

**Gaps (new).**
- Today `heap_root` is committed but NOT yet projected as accessible umem cells — `umem.rs:68`
  deliberately drops `fields_root` (derived) and never enters `heap_map` entries into the
  trace. To make the per-cell heap a *first-class* umem you add a `Heap` collection
  `Heap{cell, collection, key}` whose values come from `heap_map`, and a domain code so a heap
  access emits a `umem_op` row.
- A cross-cell read needs the *other* cell's heap as a bound init image. Today reads stay within
  one turn's projection. The keystone gives this directly: bind cell B's committed `heap_root`
  as an init boundary, open key — `boundary_init_root_bound` (line 475) makes a tampered image
  fail the published root.

**First step.** Add a `Heap` `UKey` collection projecting `CellState.heap_map` entries (one
`UVal::Bytes32` per `(collection,key)`), and emit a `umem_op` on `JournalEntry` heap writes.
This is purely additive (the same recursion-gated witness path, `umem.rs:28`) and gives the
per-cell heap genuine umem rows + a derived `heap_root` that already equals `boundary_root`.

---

## 3. Working-memory umems

**The model.** A service-cell's (or the interpreter's, or a long-running effect's) *transient*
working memory is a umem in a new domain whose **boundary is never committed** unless explicitly
checkpointed. Reads/writes are ordinary umem ops; because the trace rides the ONE balance, the
working memory is consistent for free — but its root never enters the state commitment, so it
costs nothing on the consensus path.

**Reusable.** This is precisely the `registers` domain's design: "per-proof VM transients, never
persistent state — EMPTY in the persistent projection by design" (`umem.rs:91`,
`UniversalMemory.lean:73`). The mechanism for "a domain that participates in the trace but not
the boundary" already exists and is proven sound: `universal_memory_sound` certifies *every*
domain projection regardless of whether its root is materialized; only domains that *publish* a
root pay the boundary cost (`boundary_root_from_memcheck` is per-domain, line 429). The
no-chip-table measurement (`descriptor_ir2.rs:75`) is what makes transient scratch cheap.

**Gaps (new).**
- A general "working" domain (or a per-service tag) distinct from `registers`, so the
  interpreter and service cells get their own non-aliasing scratch.
- A *checkpoint* operation: derive the boundary root of the working domain on demand
  (`boundary_root_derived` already does this for any domain) — see §4.

**First step.** Reuse `Domain::registers` as-is for the interpreter's scratch (it already
projects to nothing and its trace is already certified). No new code — this use is *unlocked by
recognizing it's the register domain's contract*. A dedicated service-working domain is a later
additive `Domain` value.

---

## 4. Passable intermediate states (the exciting one)

**The model.** A umem becomes a **portable, witnessed value**: a triple
`(declared addresses, committed init root, op trace so far)` whose *boundary at hand-off time*
is the witness of what it was. The boundary-binding keystone is exactly the handoff seal — both
edges of the umem are pinned to committed roots, so:

- to **checkpoint** a computation's intermediate state: derive its boundary root (the present
  final cells, `boundaryCells`, line 320) — `memcheck_pins_final` (line 281) makes that root
  the genuine fold, not prover-chosen. This root IS the umem-ref.
- to **hand it off**: pass the umem-ref (the root + declared-address list, or a sturdyref to
  the prover-side store). The root is the handoff witness.
- to **resume** in another cell: re-pin the umem-ref as the *init* boundary
  (`boundary_init_root_bound`, line 475) and continue the trace. A tampered intermediate state
  produces a different sorted-Poseidon2 leaf list → a different root → the pin refuses.
- to **prove what it was**: the root binds the whole content under the named `Poseidon2SpongeCR`
  floor (`Heap.root_injective`).

**This is the key move:** a umem-ref is a *content-addressed checkpoint*. Resumption is sound
because the init binding makes the receiver inherit the producer's final pin. No new soundness
machinery — the keystone's two edges (init-bound + final-pinned) ARE checkpoint + resume.

**Connecting to existing machinery.** A pending turn's intermediate state is *already* a
partially-witnessed value:

- **Partial-turn / promises** (`turn/src/{eventual,conditional,pending}.rs`). An `EventualRef`
  (`eventual.rs:23`) names a not-yet-existing value by `(source_turn, output_slot)`; a
  `PendingEntry` (`pending.rs`) holds a `Turn` + a `ResolutionCondition` awaiting a receipt. A
  pending turn's accumulated state IS a umem-in-progress: its op trace so far, with holes. The
  fit: an `EventualRef`'s resolution can carry a **umem-ref** (the boundary root of the producer
  turn's relevant domain slice) instead of an opaque output slot — the consumer re-pins it as
  init and continues. The promise-hole = nullifier insight already in MEMORY (a hole-fill binds
  δ in-circuit) extends cleanly: the fill *is* a boundary handoff.
- **CapTP pipelining** (`captp/src/pipeline.rs`). The FIFO drain (`verified_drain_reorder`,
  `pipeline.rs:50`, riding `pipeline_fulfill_drains_fifo`) ships queued messages to an
  unresolved promise. Pass a **umem-ref down the pipe**: a pipelined message can carry the
  boundary root of the state it operates on, so the far end resumes against a bound init image
  rather than re-fetching state — promise pipelining inherits light-client unfoolability because
  the umem-ref is the witnessed value, not a trusted blob.
- **The membrane** (`starbridge-v2/src/shared_fork.rs`). A `SharedFork` hands a confined
  sub-world across instances (`shared_fork.rs:1`, three consent tiers over a real
  `ConditionalTurn`). Carry a umem across the membrane: the fork's culled subgraph IS a umem
  slice (the cells + caps it exposes); its boundary root is what the guest binds. The branch
  /stitch merge-back (`crate::branch_stitch`) becomes a umem reconciliation — the stitched
  result re-derives a boundary that pins what merged.

**What witnesses a handoff.** The **boundary at hand-off-time**: the sorted-Poseidon2 root over
the umem's present cells at the checkpoint. It is (a) *trustworthy* — `memcheck_pins_final`
forces it to the genuine fold; (b) *injective* — `Heap.root_injective` under the CR floor, so
the root names exactly one content; (c) *re-bindable* — `boundary_init_root_bound` makes the
receiver's init pin refuse any tampered image. Checkpoint = derive-final-root; resume =
bind-as-init-root. The same theorem pair, used at the seam.

**Gaps (new).**
- A `UmemRef` value type: `{ domain(s), declared_addresses, root, optional sturdyref to store }`,
  serializable, passable as an effect output / pipeline payload / fork attachment.
- An effect (or effect-output) that *emits* a umem-ref (checkpoint) and one that *consumes* one
  (resume-against-bound-init). This is the only genuinely new circuit-adjacent surface, and it
  is small: the init-binding leg already exists in the keystone; the effect wires its root to a
  public input.
- Wiring `EventualRef` resolution / pipeline payloads / `SharedFork` to carry `UmemRef`.

**First step (after the keystone) — see §6.**

---

## 5. Composable umems

**The model.** One umem references or embeds another. A service-cell that fronts N cells holds a
umem whose *values* are umem-refs (the fronted cells' boundary roots). Reading "through" the
service opens the service's umem to get a child root, then opens the child against that root —
a two-level bind, each level the same `boundary_init_root_bound` step.

**Reusable.** The structure already exists implicitly:

- `system_roots` is a per-cell sub-block of *roots* — a umem whose cells are themselves
  committed roots, with namespace separation proven (`cell/src/state.rs:191`, the kernel side
  -tables at fixed indices). That IS a composed umem (a umem of roots).
- The `index` domain (the receipt MMR, `umem.rs:99`) is a umem referenced by, but owned outside,
  the executor — `receipt_op` lets a caller compose its writes into a whole-turn witness
  (`umem.rs:474`). The composition seam (one umem's ops folded into another's trace) is already
  demonstrated.
- Cross-cell heap reads (§2) are the degenerate composition: cell A's umem holds a key whose
  value is "go read cell B's `heap_root`".

**Gaps (new).** A `UVal::UmemRef` variant (a value that IS another umem's boundary root), and a
recursive open: bind the outer root, read a child root, bind the child root. The soundness is
*compositional for free* — each level is an independent `boundary_init_root_bound` application;
tag isolation (`consistentFrom_filter`) guarantees the levels don't alias. No new theorem; the
keystone composes with itself.

**First step.** Add `UVal::UmemRef([u8;32])` and a test that a two-level open (service umem →
child cell heap) binds both roots. Pure composition over §2 + the keystone; no circuit change
beyond a second init-binding leg.

---

## 6. Soundness story (how the keystone makes each witnessed)

Every use rests on the SAME two facts, applied at different seams:

1. **One balance certifies all slices** — `universal_memory_sound` (line 197): consistency of
   the whole trace ⟹ consistency of every domain projection standalone. Per-cell heaps,
   working scratch, checkpointed states, composed levels are all disjoint domain/key slices of
   ONE trace; they cannot alias (`consistentFrom_filter`/`_strip`) and they share one cheap
   memory argument.
2. **Both boundary edges are bound** — the *final* edge already pinned to a committed root
   (`boundary_root_from_memcheck`, line 429; `memcheck_pins_final`, line 281); the *init* edge
   pinned by the keystone (`boundary_init_root_bound`, line 475). With both edges committed, a
   umem is a value whose content is named by its root, re-bindable on resume, tamper-evident
   under one CR floor.

So: **per-cell** = a committed-root slice you can open cross-cell (final edge already there);
**working** = a slice that rides the balance but publishes no boundary; **passable** = derive
final root → hand off → re-pin as init root → resume (both edges, used at the seam);
**composable** = a value that is itself a root, bound recursively (the keystone applied twice).
The keystone is the *one* missing edge that turns "the world's committed state" into "any
committed-root slice, passable and resumable".

---

## 7. Staged build path

The keystone (init-binding) lands in parallel — assume it. Then:

- **STAGE A (recommended FIRST step): per-cell heap umem (§2).** Project `CellState.heap_map`
  as a `Heap{cell, collection, key}` `UKey` collection and emit `umem_op` rows on heap writes.
  Purely additive on the existing recursion-gated witness (`umem.rs:28`); the derived root
  already equals the committed `heap_root` (`boundary_root_derived`), so it's a refactor of
  *where* the commitment is read, not *what*. **This is the first step because** it is the
  lowest-risk, exercises the keystone's cross-cell init-binding immediately (a cross-cell read
  is the first real consumer), and it is the substrate every later stage stands on (passable
  states and composition both checkpoint/embed *heap slices*).

- **STAGE B: passable umem-ref (§4).** Define `UmemRef` + a checkpoint effect-output (emit final
  root) and a resume input (bind as init root). Smallest new circuit surface; init leg already
  exists.

- **STAGE C: wire the carriers (§4).** `EventualRef` resolution → `UmemRef`; CapTP pipeline
  payload → `UmemRef`; `SharedFork` attachment → `UmemRef`. No circuit change — these consume
  Stage B's value over existing transports.

- **STAGE D: working-domain split + composition (§3, §5).** A dedicated working domain beyond
  `registers`; `UVal::UmemRef` + recursive open. Both are additive `Domain`/`UVal` values over
  the proven base.

**Recommended FIRST step:** *Stage A — project the per-cell `heap_map` as a first-class umem
collection and emit its op rows.* It is honest (the root already exists and is committed),
additive (recursion-gated witness only), and it is the keystone's first cross-cell consumer —
the foundation passable + composable umems both build on.

**Integration target (the worked example, §8):** once Stage A + B land, ride the dregg document
language (`dregg-doc/`) onto the primitive — its commitment is already specified to become the
document cell's `heap_root` (`commit.rs:30`). The document language exercises all four uses at
once and is the proof that the primitive is general (sovereign docs · portable patches ·
composable transclusion · conflicts-as-objects, all verified).

---

## 8. Worked example — the document language ("Xanadu that ships")

The **dregg document language** (`dregg-doc/`, `docs/deos/DOCUMENT-LANGUAGE.md`,
`docs/deos/DOC-CELL-COMPOSITION.md`) is the killer app: it exercises ALL FOUR umem uses at
once. It is a Pijul-shaped patch-theoretic core (`dregg-doc/src/lib.rs:1`) — documents are
graphs of alive/dead content atoms, edits are patches, merge is the categorical pushout, and a
conflict is a first-class *state* the document carries, never a merge failure. umem-as-primitive
is exactly what turns that elegant core into a *verified, sovereign, portable* one.

### A document = a cell with a umem-heap (§2, per-cell)

"Today a dreggverse document IS a cell (1:1)" (`composition.rs:3`). Its content — the atom
graph (atoms with id/content/status/provenance + order-edges + the single-valued field store,
`lib.rs:18`) — is exactly a `(collection, key) → value` map: **the cell's umem-heap.** The
document's commitment is currently the crate's 128-bit stand-in (`commit.rs:38`), but the code
already names the target: *"The real substrate commitment is sorted-Poseidon2 over the document
cell's heap (the faithful 8-felt commitment floor); this crate rides that later"*
(`commit.rs:30`). That ride-on IS Stage A: the document's `heap_root` becomes its boundary, so
the doc commitment is a derived umem boundary (`boundary_root_derived`) — a **sovereign
document**, its whole content (atoms + edges + fields + provenance) bound by one committed root.

### A patch = a passable witnessed umem (§4, passable-intermediate-state)

A patch *is* a turn: *"on the substrate a patch is a turn whose effects write these leaves,
tombstones, and fields, leaving a receipt"* (`patch.rs:18`). So an edit's intermediate
state — the patch applied but not yet merged in — is a **umem-in-progress with a derivable
boundary root.** This makes **patch-theory ↔ event-structure literal: a patch IS a passable
umem.** Concretely:

- **Collaborative editing / offline sync.** `History::branch`/`stitch` and the two-device
  offline stitch (`dregg-doc/examples/two_device_offline_stitch.rs`, `dregg-doc/src/merge.rs`)
  hand an edit-state between devices. Carry it as a `UmemRef`: device A checkpoints its
  patch-state's boundary root, device B re-pins it as init and continues
  (`boundary_init_root_bound`). A tampered patch produces a different root → the pin refuses.
  **Witnessed portable patches** — a patch you can hand off and *prove what it was*.
- **Membrane carry.** A `SharedFork` (`starbridge-v2/src/shared_fork.rs`) handing a doc into a
  chat membrane attaches the document umem-ref; the guest binds it. The patch crosses the
  membrane as a witnessed value, not a trusted blob (§4).
- The patch grammar is additive (`Add`/`Delete`(tombstone)/`Connect`/`SetField`, `patch.rs:1`)
  and invertible (RCCS, `lib.rs:24`) — so the passable umem inherits time-travel and undo for
  free; resuming an earlier checkpoint is binding an earlier boundary root.

### Transclusion = composable umems (§5, composable)

`Op::Embed` is the one new idea: *"an atom whose content is a `ChildRef` (a `dregg://` child
cell + a Pin)"* (`composition.rs:9`). A composed document is *"a graph of cells: the parent
layout graph plus, by reference, each child's graph"* — resolved recursively through the
membrane (`ChildResolver`, `content_composed`, `composition.rs:40`). This is **composable umems
literally**: the parent's umem holds, at an embed key, a value that IS another cell's boundary
root; opening "through" the embed binds the child root and opens it — the recursive open of §5.
The `dregg://` link becomes a **witnessed transclusion**:

- A `Pin::At(receipt)` embed (`composition.rs:71`) is the *snapshot* form — a child umem-ref to
  an immutable committed root. "A citation that does not break" (`composition.rs:74`) is exactly
  a content-addressed umem boundary: the cited content is bound by its root, tamper-evident
  under one CR floor. This is the Xanadu transclusion guarantee, *verified*.
- A `Pin::Live` embed tracks the child's tip — its umem-ref re-resolves each render, each
  resolution a fresh init-bind of the child's current `heap_root`.
- Confinement is free: `merge_composed` is the **product of pushouts** — *"a child edit can
  NEVER conflict with a layout edit"* (`composition.rs:49`) — which is exactly umem tag
  isolation (`consistentFrom_filter`): the parent-layout slice and each child slice are
  disjoint, so composition cannot alias.

### Conflicts-as-objects = umems over the merge-state (§3 working + §4 passable)

A conflict is *"a first-class STATE the document carries until a later patch resolves it, never
a merge failure"* (`lib.rs:7`; `ConflictRegion`/`Segment::Conflict`, each `Alternative` tagged
with provenance, `lib.rs:48`). The merge-state holding two live mutually-unordered alternatives
is a **umem over the intermediate merge** — a working-memory umem (§3) while unresolved, and a
passable one (§4) when handed to a collaborator to resolve. The soundness this needs is already
the keystone's job:

- `commit.rs` exists precisely to bind a conflict so *"a light client cannot be shown a forged
  conflict"* — it folds **both alternatives and their provenance** into the commitment, so
  *"mutating one conflict alternative's author... changes the commitment"* (`commit.rs:1,19`).
  Riding the umem-heap (Stage A) makes that the umem boundary: a conflict is a witnessed umem,
  not a silent last-writer-win overwrite. **Conflicts-as-objects, verified.**
- The desktop layer already drives this: two devices contending for focus produce *"a
  first-class conflict state... rather than silently last-writer-win"*
  (`dregg-doc/src/desktop.rs:28,247`). That contended desktop-state is a working umem whose
  resolution is a passable handoff.

### The payoff: Xanadu that ships

Put together, umem-as-primitive yields the four Xanadu/Pijul promises *as verified substrate
facts*, not aspirations:

| promise | mechanism | umem use |
|---------|-----------|----------|
| **sovereign documents** | doc = cell, content = umem-heap, commitment = derived `heap_root` | per-cell (§2) |
| **witnessed portable patches** | patch = turn, edit-state = passable umem-ref, re-pinned on resume | passable (§4) |
| **composable transclusion** | `Op::Embed` = umem value that is a child root; `dregg://` = witnessed boundary | composable (§5) |
| **conflicts-as-objects** | merge-state = working/passable umem; both alternatives bound in the root | working+passable (§3,§4) |

Each is the same two boundary theorems (§6) applied at the document seam. The document language
is therefore the recommended *integration* target once Stage A + B land: it is the app that
proves the primitive is general, and it is the app that makes "Xanadu that ships" a verified
claim — sovereign, portable, composable, conflict-honest, all under one committed-root algebra.

---

*Honest scope.* What EXISTS today: the single global umem (`turn/src/umem.rs`), its five
domains, the Blum trace + agreement check, the no-chip-table circuit row
(`descriptor_ir2.rs:363`), the final-boundary derivation + non-vacuity
(`UniversalMemory.lean`), and the per-cell `heap_root`/`heap_map`/`fields_map` embryos
(`cell/src/state.rs`). What is NEW: the init-binding keystone (landing in parallel), per-cell
heap *projection*, the `UmemRef` value + checkpoint/resume effect surface, the carrier wiring,
and the working-domain split. None of it requires a new soundness argument — every use is the
two existing boundary theorems applied at a new seam.
