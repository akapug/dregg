# Compute as a cell — a persistent server IS a checkpointable umem cell

*The #1 re-dregg from `MYOPIA-AUDIT.md §3` / `THE-BIGGER-DREGGNET.md §1` /
`VISION-DREGG-NATIVE-CLOUD.md §1`. Today a "server" is a fly.io Machine clone — a
serde struct in a `Mutex` map plus a `lessee` field (`control/src/server.rs`),
durably recorded as JSON lines. The dregg-native form — a checkpointable / forkable
umem cell with a committed boundary root — exists in the substrate
(`project-umem-as-primitive-epoch`, `umem_time_travel.rs`, `continuation.rs`) and was
used in **zero** cloud surfaces. This carves the server's STATE out of umem.*

The AGPL firewall is dissolved (ember owns the copyright; `FIREWALL-DISSOLUTION.md`),
so this depends on the **real substrate umem boundary-root primitive directly** — the
same `dregg-circuit` Poseidon2 heap root `storage/` already commits buckets with, and
the same `dregg-types::CellId::derive_raw` `webauth/` already anchors accounts with.
No new crypto, no stand-in.

---

## 0 · The one move

> A persistent server / running workload **is a umem cell.** Its durable state is a
> umem heap whose committed **boundary root** is its identity-over-time. The server
> lifecycle is not a fly.io machine state machine — it is **umem operations**:
>
> | server lifecycle | umem operation | what it IS |
> |---|---|---|
> | **sleep** (`stop`) | **checkpoint** | the boundary root commits the live state; the server stops consuming compute, the cell persists as a 32-byte root |
> | **wake** (`wake`) | **restore** | reconstruct the running state from the checkpoint root, fail-closed if the reified image does not reproduce it |
> | **scale / clone** (`fork`) | **fork** | a second running instance from the same checkpoint — a new cell id, an independent heap that diverges |
> | **rollback** (`time_travel`) | **restore an earlier boundary root** | roll the cell back to any past committed root in its checkpoint log |
> | **pay-only-while-awake** | meter draws iff **not checkpointed** | sleeping = checkpointed = not metered; checkpoint makes pay-per-use *real*, not a wall-clock timer |

The keystone the substrate already proved: `boundary_init_root_bound`
(`UniversalMemory.lean:475`, `#assert_axioms`-clean) — *a umem is a value you hand off
and resume; the receiver inherits the producer's pin.* **The boundary IS the state.**
A checkpoint is therefore not "ask the provider to snapshot a VM" — it is *taking the
boundary root of your own cell*, and a restore is reproducing the reified image and
checking it folds back to that exact root.

---

## 1 · The primitive — `ComputeCell` (`control/src/compute_cell.rs`)

A `ComputeCell` is the dregg-native unit of compute. It carries:

- **identity** — a `CellId` (`dregg_types::CellId::derive_raw(seed, COMPUTE_ROOT_TOKEN)`),
  content/key-derived from `(lessee, app, name)`, exactly the way `webauth`'s
  `account_id` derives an account's identity cell. A server's identity is its **cell
  id**, not a random `srv_…` row key.
- **the live heap** — a witnessed `(key → value)` store (`ComputeHeap`), the server's
  durable working state. This is the per-cell umem heap (`PerCellUmem.lean`,
  `f0372f22`): a tampered value flips the root.
- **a checkpoint log** — the captured boundary roots + their reified images, the
  time-travel record (`umem_time_travel.rs`'s inverse-fold image, made explicit).

The **boundary root** is the REAL wide-8-felt (~124-bit) sorted-Poseidon2 heap root —
`dregg_circuit::heap_root::compute_heap_root_entries` folded under
`wire_commit_8` — *byte-identical in shape to the commitment `storage/src/bucket.rs`
already publishes for a bucket cell* (`FAITHFUL-STATE-COMMITMENT.md` discipline, no
31-bit intermediate, matching the proof's ~130-bit FRI floor). Each `(key, value)`
becomes a leaf `H(key, value)` placed in the canonical sorted heap keyed by the key's
collection hash; the root folds them. A one-byte change to any value moves the root
(injective, anti-vacuous).

Operations:

- `checkpoint() -> root` — reify the live heap into a `Checkpoint { root, image }`,
  push it onto the log, return the boundary root. **Sleep.** The commitment is durable
  (it rides the `ServerRecord`); the image is held live (see §3, the Stage-B seam).
- `restore_checkpoint(cp) -> Result` — verify `boundary_root(cp.image) == cp.root`
  (**fail-closed** — `RestoreError::ImageRootMismatch` if the reified image does not
  reproduce the committed root), then set the live heap to the image. **Wake.**
- `time_travel(root) -> Result` — find the checkpoint for `root` in the log and restore
  it (`RestoreError::UnknownRoot` if it was never committed). **Rollback.**
- `fork(new_seed) -> ComputeCell` — a new cell id over `new_seed`, its live heap a
  *copy* of this cell's latest checkpoint image, its log seeded with that fork-point
  root. The two cells share a provable common ancestor (the fork-point root) and
  diverge independently — a write to one does not touch the other. **Scale / clone.**

Every one of these is real over the deployed boundary-root primitive — no kernel
effect required to compute, commit, verify, fork, or roll back a boundary root.

---

## 2 · Re-anchoring the server (`control/src/server.rs`)

`ServerRecord` gains two fields (both `#[serde(default)]`, so a record written before
this epoch still loads):

- `cell_id: String` — the server's dregg identity = hex of
  `CellId::derive_raw(blake3(lessee‖app‖name), COMPUTE_ROOT_TOKEN)`. Content-addressed,
  like the account re-anchor; the same `(lessee, app, name)` always names the same cell.
- `checkpoint_root: Option<String>` — the boundary root committed while the server is
  **asleep** (`Stopped`). `None` while `Running` (awake — the live state is mutating and
  not yet committed) or `Created`.

The `ServerFleet` holds each server's live `ComputeCell` in its in-memory map
(`LiveServer.cell`). The lifecycle methods map onto umem operations:

- `stop` (**sleep**) → `cell.checkpoint()`; the boundary root is persisted in
  `checkpoint_root`; the backend is released; **no uptime is metered while asleep**
  (the existing `meter_period` returns `NotRunning` for a non-running server, so a
  checkpointed server draws nothing — this is exactly pay-only-while-awake).
- `wake` (**restore**) → `cell.time_travel(checkpoint_root)` verifies the image
  reproduces the committed root (fail-closed; a corrupt checkpoint refuses the wake
  *before* any backend is provisioned), clears `checkpoint_root`, then brings the
  server up at its persisted uptime cursor.
- `fork` (**scale / clone**) → a new lease-gated `Created` server whose `ComputeCell`
  is `src.cell.fork(...)` — a distinct cell id, an independent heap sharing the
  source's fork-point root. The fork can be launched and diverge with no effect on the
  source.
- `restore_to` (**time-travel / rollback**) → `cell.time_travel(root)` for any earlier
  boundary root in the cell's checkpoint log.

The lease/budget gating is unchanged and stays load-bearing: `create`/`launch`/`wake`
still read the real funded reserve, pre-pay the upcoming period, enforce the
per-lessee + global quota, and lapse→reap on budget exhaustion. **Pay-while-awake =
draw-while-not-checkpointed**: the meter is reached only through a tick over a
`Running` (awake) server.

---

## 3 · Honest — what is a real umem weld vs the named Stage-B seam

**Real here (depends on the deployed substrate umem pieces, proven):**

- The **boundary root** is the genuine `dregg-circuit` wide-8-felt sorted-Poseidon2
  heap root (the deployed umem heap-root primitive, the same one `storage/` commits a
  bucket with). Checkpoint commits it; restore verifies the reified image reproduces
  it; a one-byte tamper moves it.
- The **cell identity** is the genuine `dregg_types::CellId::derive_raw` (the deployed
  substrate cell-id, the same one `webauth/` anchors an account with).
- **Checkpoint → restore preserves state**, **fork diverges** (independent cells, a
  write to one leaves the other unchanged), **time-travel restores an earlier root**,
  and **sleeping draws nothing** — all proven in `compute_cell.rs` + `server.rs` tests
  over the real boundary-root primitive.

**The named Stage-B umem checkpoint/resume kernel-effect seam (designed, not deployed —
`UMEM-STAGE-B-DESIGN.md`):** two things the deployed pieces do not yet give, both gated
behind the *first-class umem checkpoint/resume kernel-effect* (an `Effect` that emits a
umem-ref and one that consumes one):

1. **Live in-sandbox image capture.** Today the `ComputeCell` heap holds the server's
   dregg-visible **working state** (the `(key→value)` cells a workload reads/writes
   through the `exec/src/host_api.rs` seam). Capturing a *live polyana / Firecracker
   process image* (the OS memory of a running sandbox) into that heap is the kernel
   effect — until it lands, the working-state heap is the checkpointable surface, and a
   wake re-provisions a fresh backend that resumes from the restored working state
   rather than from a frozen process image.
2. **Cross-restart image durability + the light-client witness.** The boundary-root
   *commitment* rides the durable `ServerRecord` today, but the reified *image* is held
   in-process. The kernel-effect emits a umem-ref the node durably materializes, so a
   control-plane restart can restore from the root alone and a **light client** (not
   just a re-executing control plane) witnesses checkpoint/restore as an on-chain turn.
   Durable image persistence is deliberately **not** re-implemented here as a side store
   — that would be the `dreggnet-store` myopia (`MYOPIA-AUDIT §7`, the #2 re-dregg); the
   honest home is the node's committed heap via the kernel-effect.

Neither is a wall: each is a weld between the boundary-root primitive built here and the
designed Stage-B effect.

---

## 4 · What re-dregging unlocks

- **Genuine pay-per-use.** Sleep = checkpoint = a 32-byte boundary root; a sleeping
  server consumes no compute and is metered nothing. Pay-only-while-awake stops being a
  wall-clock timer and becomes a structural property of the commitment.
- **Fork-to-scale.** Scale out by *forking a checkpoint* into a second sovereign cell
  that diverges independently — the cloud equivalent of `fork()` for real, metered
  compute, with a provable common ancestor.
- **A live workload you can snapshot and pass.** A server is a cell with a committed
  boundary root: snapshot it (checkpoint), hand the root to another agent who resumes
  from the inherited pin (the umem keystone), or roll it back to any earlier root for
  time-travel debugging — none of which a `Mutex<HashMap>` of serde structs can do.

The server learns to fork.
