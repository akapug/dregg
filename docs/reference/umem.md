# Universal memory (umem)

A *umem* is **a witnessed key→value store whose committed root is its boundary**:
a `(domain, key) → value` address space, a Blum memory-checking trace of the
accesses to it, and a sorted-Poseidon2 root over its final present cells that any
verifier can bind to. dregg's whole-world state is one umem; the same construct is
now reused for per-cell heaps, transient working memory, passable intermediate
states, and composed umem-refs. The Rust lives in `dregg-turn`
(`turn/src/umem.rs`); the soundness is Lean (`metatheory/Dregg2/Crypto/`).

The design narrative is `docs/deos/UMEM-PRIMITIVE.md`; this entry is the grounded
what-is at HEAD.

## The address space — six domains

`UDomain` (`turn/src/umem.rs:99–118`) tags the disjoint planes; `UKey`
(`turn/src/umem.rs:165` ff.) is the in-domain key; `UVal` is the value.

| domain | tag | what it holds | persistent? |
|--------|-----|---------------|-------------|
| `Registers` | 0 | per-proof VM register file | no (transient) |
| `Heap` | 1 | per-cell record state (fields, balances, roots, **heap cells**) | yes |
| `Caps` | 2 | authority state (c-lists, delegation, programs, factories) | yes |
| `Nullifiers` | 3 | insert-only sets (note/bridged nullifiers) | yes |
| `Index` | 4 | the append-only receipt MMR | yes |
| `Working` | 5 | service/interpreter transient scratch (Stage D) | no (transient) |

Domains are isolated by tag: a write in one plane can never cancel a claim in
another. The witness path is recursion-gated (`turn/src/umem.rs:28`).

## The three parts

- **Address space** — `(domain, key) → Option value`, domains disjoint by tag.
- **Access trace** — Blum `(kind, addr, val, prev_val, prev_serial)` ops; ONE
  balance certifies consistency of every domain projection
  (`UMemOpSpec`, `circuit/src/descriptor_ir2.rs:363`).
- **Boundary** — the sorted-Poseidon2 root over the domain's final present cells;
  the committed commitment a verifier binds.

## Load-bearing Lean theorems (`metatheory/Dregg2/Crypto/`)

All `#assert_axioms`-clean.

- **`universal_memory_sound`** (`UniversalMemory.lean:197`) — consistency of the
  whole trace ⟹ consistency of every domain projection standalone. Per-cell heaps,
  working scratch, checkpoints, composed levels are all disjoint slices of ONE
  trace; they cannot alias and share one cheap memory argument.
- **`memcheck_pins_final`** (`UniversalMemory.lean:281`) — the prover's claimed
  final cells ARE the genuine fold, so the derived boundary root is trustworthy,
  not prover-chosen.
- **`boundary_root_from_memcheck` / `boundary_root_derived`**
  (`UniversalMemory.lean:429,416`) — the *final* edge: the published root equals
  the derived root over the genuine post-state, by canonicity (no extra crypto).
- **The keystone — `boundary_init_root_derived` / `boundary_init_root_bound`**
  (`UniversalMemory.lean:463,475`; `#assert_axioms` 868–869; `99a8dc94`) — the
  *init* edge: a umem's init image is pinned to a committed root supplied as a
  public input, and the binding **refuses a tampered declared heap**. With both
  edges bound a umem is a value you hand off and resume; the receiver inherits the
  producer's pin. This is the edge that unlocks the per-cell / passable /
  composable uses.

## What is built on the keystone

- **Per-cell heap umem (Stage A, `7686c488`).** `Heap{cell, collection, key}`
  (`turn/src/umem.rs:165–175`) projects every `CellState.heap_map` entry as a umem
  cell; the derived root equals the committed `heap_root` (`umem.rs:396–398`, via
  `compute_heap_root`). Soundness: `metatheory/Dregg2/Crypto/PerCellUmem.lean`
  (`f0372f220`) — the `UKey::cell()` filter preserves the boundary = `heap_root`
  binding (5 theorems). A cross-cell read is a Lean theorem: circuit `MapOp::Read`
  REFINES `ObservedFieldEquals` (`crossCellRead_refines_observedField`,
  `metatheory/Dregg2/Exec/UniversalBridge.lean:1019,1028`; `bee42d4af`).
- **Working domain (Stage D, `09bf81ce`).** `UDomain::Working` + `UKey::Working{
  service, collection, key}` (`turn/src/umem.rs:118,216`): transient scratch keyed
  by owning service, never projected from persistent state (`umem.rs:294`) so its
  boundary never enters the commitment. Checkpoint on demand via
  `working_umem_root`.
- **Composable umem-refs (Stage D, `09bf81ce`).** `UVal::UmemRef([u8;32])`
  (`umem.rs:324`) is a value that IS another umem's boundary root;
  `open_through_umem_ref` (`umem.rs:691`) binds the outer umem, reads the child
  ref, binds the child against its named root, opens the key — two independent
  `boundary_init_root_bound` applications kept disjoint by tag isolation. Tested in
  `turn/tests/umem_stage_d.rs`.

## Live applications

- **Time-travel via the boundary** (`b1bd3305`). The cockpit's TIME scrubber
  restores a past image by an O(1) `reify_ledger` inverse fold over a captured umem
  boundary (*the boundary IS the state*) instead of genesis replay; held to the
  anti-substitution discipline (the reified ledger must reproduce the recorded root
  tooth, else `RootMismatch`, fail-closed). `reify_cell` is byte-identical to the
  inverse of `project_cell` (`7c01210a4`). `turn/tests/umem_time_travel.rs`.
- **Continuations as passable umems** (`087a4cd7`). A suspended turn resumes into
  the running ledger rather than re-executing from pre-state
  (`turn/src/continuation.rs`, `turn/src/continuation_resume.rs`).
- **Documents ride the heap** (`bf5e0154b`). `DocHeapCell` (`dregg-doc/src/doc_heap.rs`)
  projects a `DocGraph` into `heap_map` and reseals `heap_root` — a sovereign
  document bound by one committed umem root (`docs/deos/UMEM-PRIMITIVE.md` §8).

## Open seam

The checkpoint/resume **kernel-effect** surface (Stage B) is a *design*, not built
— `docs/deos/UMEM-STAGE-B-DESIGN.md` (`089f1cbf`). The `UVal::UmemRef` *value*
exists; a first-class effect that emits a umem-ref (checkpoint) and one that
consumes one (resume-against-bound-init), plus the carrier wiring (`EventualRef` /
CapTP pipeline payload / `SharedFork`), remain named. The init-binding leg already
exists in the keystone, so the new circuit surface is small. An agent's working-set
as a witnessed portable umem is a prototype (`3911af58c`), not yet load-bearing.
