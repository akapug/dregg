# pg-dregg Tier-D feasibility spike — can the verified executor run IN postgres?

**The question** (the north star, `.docs-history-noclaude/PG-DREGG.md` §13.1 / the QUICKSTART roadmap
Tier-D row): can the VERIFIED executor run inside the postgres backend process —
i.e. can `libdregg_lean.a` (the `@[export]`ed Lean executor that
`dregg-lean-ffi` builds) **link and execute inside a postgres C-extension's
process model**, so that `SELECT dregg_submit_turn_inproc(envelope)` runs the
kernel inside the same transaction that `UPDATE`s your app tables — kernel state
and app state committing atomically?

**The verdict (one line): D-SIDECAR.** The executor **links and runs** in a
process on this host today, and a *cdylib already links it* (so a pgrx
extension `.so` _can_ link it) — but hosting it **in the backend process** is
unsafe because the Lean runtime (a) statically overrides the global allocator
with **mimalloc** and (b) spawns **worker threads**, both of which collide with
the postgres backend's single-threaded `palloc` / `longjmp` / signal model. The
realizable, safe shape is the executor in a **co-process** (a pgrx
`BackgroundWorker`, or the standalone node) that the backend hands intents to —
which is exactly the seam the landed drainer's PRODUCE gate
(`dregg_drain_once`) already plugs into.

This is an honest engineering reconnaissance, not a forced build. Below is the
minimal concrete evidence for the call, the specific blockers, and the path each
verdict would take.

---

## 1. What "full-D" vs "D-sidecar" mean

| | **full-D (in-backend)** | **D-sidecar (co-process)** |
|---|---|---|
| Where the executor runs | inside the postgres *backend* process (the connection's process), called from a `#[pg_extern]` | in a separate process (a pgrx `BackgroundWorker`, forked by the postmaster, or the standalone node) |
| Cross-domain atomicity | TRUE: kernel state + app `UPDATE` in ONE backend transaction | the backend enqueues an intent; the sidecar executes + the post-image is applied through the `commit_log` gate (the drainer). NOT one backend transaction with the app `UPDATE` |
| The link | `libdregg_lean.a` linked into the extension `.so` AND called on the backend's own stack | the executor links into the sidecar process; the backend never links it |
| Process-model risk | HIGH (see §4) | LOW (the executor owns its own process / allocator / threads) |

Full-D is the strictly-more-powerful north star (it is the one thing a separate
node *cannot* offer — cross-domain atomicity). D-sidecar is the safe realizable
slice that still gives "postgres is the verified store, the executor produces the
verified turns" — and it is what pg-dregg already ships the seam for.

---

## 2. Evidence the executor LINKS and RUNS (the link attempt)

The hard prerequisite for either verdict is "the verified Lean executor links and
runs in a host process at all." It does, on this host, today:

* **`libdregg_lean.a` exports the executor entry.** `nm libdregg_lean.a` shows
  `T _dregg_exec_full_forest_auth` — the `@[export]`ed credential-gated
  complete-turn executor (`FullForestAuth.execFullForestG`), plus the C string
  bridge `dregg_exec_full_forest_auth_str` (`dregg-lean-ffi/src/lean_init.c`).
  The archive is the whole transitive Lean closure (~3000 reachable members after
  the build's reachability GC: mathlib + batteries + the Dregg2 modules).

* **It links into a Rust host binary and EXECUTES a turn.** `cargo test -p
  dregg-lean-ffi --features lean-lib --test overspend_probe` links the archive +
  the Lean runtime statics into a test binary and runs the executor three times
  through `dregg_lean_ffi::shadow_exec_full_forest_auth(wire)` — the real Lean
  `execFullForestG`, which correctly does NOT commit the overspends. The link
  succeeds and the executor runs in-process (the build emits ~8 minutes of
  closure compilation the first time; thereafter it is a normal `.a` link).

* **The Lean runtime init is a once-per-process ritual** (`lean_init.c`
  `dregg_ffi_init`): `lean_initialize_runtime_module()` → the module
  initializers → `lean_io_mark_end_initialization()`; `dregg-lean-ffi` guards it
  behind a `OnceLock` (`src/lib.rs` `lean_init_once`). The executor call itself is
  a single synchronous `String -> String` C call.

* **Precedent: the executor links into a static MUSL binary that runs a real
  turn** — the seL4 `executor-pd` lane (`sel4/dregg-pd/executor-pd/`) reports the
  whole closure ELF-recompiles and `dregg-executor.elf` (static aarch64-musl, 0
  undefined) "runs ONE real turn through the VERIFIED
  `dregg_exec_full_forest_auth` → status:2 ok:1". So the executor is portable to
  constrained process models — *as its own process*.

**Conclusion of §2:** the executor is real, links, and runs. The question is not
*whether it links* but *whether it is safe inside a postgres backend*.

---

## 3. Evidence a cdylib (the extension `.so` shape) CAN link it

A pgrx extension is a **cdylib** that postgres `dlopen`s into the backend.
`pg-dregg/target/debug/libpg_dregg.dylib` is a `Mach-O 64-bit dynamically linked
shared library arm64` — postgres loads it into the backend process. So the
in-backend link question reduces to: *can a cdylib link `libdregg_lean.a`?*

It can — there is a **shipping precedent in this very repo**:

* **`sdk-py` is a pyo3 cdylib that links the verified Lean executor.** Its
  `.cargo/config.toml` sets `DREGG_LEAN_LINK = "shared"`, and `dregg-lean-ffi`'s
  `build.rs` (`shared_link_mode`) links the executor against the toolchain's
  `libleanshared.dylib` (155 MB, present at
  `$LEAN_SYSROOT/lib/lean/libleanshared.dylib`) instead of the static runtime
  archives. `sdk-py`'s `crate-type = ["cdylib", "rlib"]` is the SAME cdylib shape
  a pgrx extension is.

* **Why the SHARED runtime link is the cdylib path (not static).** `build.rs`
  documents it precisely: `libleanrt.a`'s mimalloc members use **local-exec TLS**
  (`R_X86_64_TPOFF32`) which the linker **rejects under `-shared`** on ELF
  (Convergence round 7). So a cdylib must link the runtime *shared*
  (`libleanshared`), while the spliced `libdregg_lean.a` (Lean MODULE objects
  only, all `-fPIC`) is linked statically in both modes.

**Conclusion of §3:** the executor archive links into a cdylib (proven by
sdk-py). A pgrx extension `.so` could link it the same way (`DREGG_LEAN_LINK=shared`
+ the rpath to `libleanshared`). The link is **not** the blocker.

---

## 4. The actual blocker: the Lean runtime vs the postgres backend process model

The blocker is not the *link*; it is **what the Lean runtime does to the process
it links into**, versus what a postgres backend requires. Two hard conflicts,
both grounded in the toolchain on this host:

### 4.1 mimalloc overrides the global allocator (the decisive one)

The Lean runtime statically bundles **mimalloc** and overrides `malloc`/`free`
process-wide: `ar t libleanrt.a` lists `alloc.cpp.o`, `allocprof.cpp.o`,
`static.c.o` (the mimalloc static-override TU). Loading the Lean runtime into a
postgres **backend** replaces the C allocator *under postgres* in that process.

Why that is unsafe in a backend specifically:
* postgres manages memory through its own **`MemoryContext` / `palloc`**
  discipline and assumes a well-behaved `malloc` underneath; it does NOT expect
  its allocator to be swapped for mimalloc inside a live backend.
* postgres error handling is `longjmp`-based (`PG_TRY`/`elog(ERROR)` unwinds via
  `siglongjmp`); an allocator with its own thread-local heaps and deferred-free
  machinery interacts badly with a backend that `longjmp`s out of arbitrary
  call frames.
* under `EXEC_BACKEND` / on the fork path the postmaster's expectations about the
  process allocator are violated.

This is the same class of hazard the build already fights on the cdylib link
(`-shared` rejects mimalloc's local-exec TLS); in-backend it resurfaces as a
*runtime* hazard rather than a *link* hazard.

### 4.2 the Lean runtime spawns worker threads

`lean/lean.h` exposes a **task manager with worker threads**
(`lean_init_task_manager` / `lean_init_task_manager_using(num_workers)`, the
`spawn_worker` lock around task dequeue). The Lean runtime is multi-threaded.

A postgres **backend is strictly single-threaded** and signal-driven: `palloc`,
`elog`, the relcache/catcache, and the `longjmp` error path are all NOT
thread-safe and assume one thread of control. Introducing Lean's worker threads
into the backend process is a direct violation of that invariant (a Lean worker
thread calling back into anything that touches a postgres global would corrupt
backend state).

### 4.3 init point + fork

The init ritual (`dregg_ffi_init`) must run **once per process that calls the
executor**. In the backend model that means running it in `_PG_init` or lazily on
first call — but a backend is itself `fork()`ed from the postmaster, and the Lean
runtime's threads + mimalloc heaps do not survive `fork()` cleanly (threads are
not duplicated across fork; mimalloc's per-thread state is left dangling). So
even the init point is process-model-hostile in the backend.

**Conclusion of §4:** full-D would put a multi-threaded, allocator-overriding
runtime inside a single-threaded, `palloc`/`longjmp`/fork-based backend. That is
the specific, concrete blocker. It is not a *link* failure — it is a *process
model* incompatibility, which is worse (it would link and then misbehave under
load / error paths / fork).

---

## 5. The verdict and the recommended shape

**D-SIDECAR.** Host the verified executor in a **co-process** the backend hands
intents to:

* the executor runs in its OWN process — its own mimalloc-overridden address
  space, its own worker threads, its own once-per-process init — none of which
  touch a postgres backend;
* a pgrx **`BackgroundWorker`** (pgrx 0.17 ships the API, `src/bgworkers.rs`) is
  the in-cluster form: the postmaster forks it, it links `libdregg_lean.a`, and
  it drains `dregg.submit_queue` exactly like the standalone `drainerd` daemon —
  applying each produced post-image through the `commit_log` gate. The standalone
  node is the out-of-cluster form.

This is **already the seam pg-dregg ships**: the landed drainer
(`src/drainer.rs`, `dregg_drain_once`) runs the four-gate spine SUBMIT → PRODUCE
→ CHAIN → MIRROR, where **PRODUCE is a `Producer` trait** — the executor seam. A
real deployment supplies the verified Lean executor at that seam (the sidecar);
pg-dregg's postgres-free core ships a deterministic conserving stand-in
(`FoldProducer`) so every OTHER gate is proven without the executor in the build.
The sidecar verdict is therefore not a compromise bolted on — it is the shape the
write path was already built around.

### What D-sidecar gives up vs full-D

The one thing the sidecar gives up is **single-backend-transaction cross-domain
atomicity**: with the sidecar, the backend enqueues the intent and the sidecar
executes it; the app's `UPDATE` in the *same* backend transaction does not commit
together with the kernel turn. You get *eventual* consistency between the queue
and the mirror (the drainer applies the verified post-image through the
`commit_log` gate, fail-closed), not *immediate* two-phase atomicity. For most
deployments that is the right trade; the strict-atomicity payoff is what would
justify the (substantial) work to make full-D safe.

---

## 6. What full-D would require (if the atomicity payoff is wanted later)

Full-D is not impossible — it is *expensive and risky*, and would need ALL of:

1. **Defuse the allocator override.** Build the Lean runtime to NOT replace the
   global `malloc` (a `LEAN_*` allocator-shim build, or route Lean allocation
   through postgres `palloc` via a custom allocator) so the backend keeps its own
   allocator. This is a Lean-toolchain build change, not a pg-dregg change.
2. **Single-thread the runtime.** Run the executor with the task manager pinned to
   the calling thread (`lean_init_task_manager_using(0)`/no workers), and verify
   `execFullForestG`'s execution never spawns a task — i.e. the executor path is
   provably worker-free. (Plausible: a turn is a deterministic fold; the seL4
   single-image run is evidence it can execute without the scheduler.)
3. **Own the init point.** Run `dregg_ffi_init` once per backend, AFTER fork
   (lazily on first call, never in the postmaster), with the no-worker runtime so
   there is nothing thread-shaped to survive fork.
4. **Bound the in-backend execution** so a long turn cannot stall the backend's
   signal handling / statement timeout.

Each is a real piece of work; (1) and (2) are the load-bearing ones and both live
in the Lean toolchain / runtime configuration, not in pg-dregg. Until they land,
in-backend is the wrong process model and **D-sidecar is the verdict**.

---

## 7. Evidence index (so the call is checkable)

| Claim | Evidence |
|---|---|
| executor exports the entry | `nm dregg-lean-ffi/libdregg_lean.a` → `T _dregg_exec_full_forest_auth` |
| executor links + runs in-process | `cargo test -p dregg-lean-ffi --features lean-lib --test overspend_probe` (3 turns through `execFullForestG`) |
| executor runs as its own static process | `sel4/dregg-pd/executor-pd/` — `dregg-executor.elf` runs one real turn (status:2 ok:1) |
| a cdylib links the executor | `sdk-py` (`crate-type=["cdylib","rlib"]`, `.cargo/config.toml` `DREGG_LEAN_LINK="shared"`) |
| the extension is a dlopen'd cdylib | `file target/debug/libpg_dregg.dylib` → Mach-O dynamically linked shared library |
| `-shared` rejects the static runtime (mimalloc TLS) | `dregg-lean-ffi/build.rs` `shared_link_mode` doc + sdk-py `.cargo/config.toml` comment (Convergence round 7) |
| Lean runtime bundles mimalloc statically | `ar t $LEAN_SYSROOT/lib/lean/libleanrt.a` → `alloc.cpp.o`, `static.c.o` |
| Lean runtime spawns worker threads | `$LEAN_SYSROOT/include/lean/lean.h` → `lean_init_task_manager[_using]`, `spawn_worker` |
| pgrx has a BackgroundWorker (the sidecar form) | pgrx 0.17 `src/bgworkers.rs` (`BackgroundWorker`) |
| the sidecar seam already exists | `src/drainer.rs` `Producer` trait; `dregg_drain_once` PRODUCE gate |

*(The `tier-d` cargo feature in `Cargo.toml` stays declared-but-unbuilt: it
implies `tier-c` and is the place the executor link would be wired IF full-D is
pursued. Per this spike it is gated on the §6 toolchain work; the default build
links nothing executor-shaped and the drainer's PRODUCE seam is the stand-in.)*
