# The embeddable Lean runtime — pg-Tier-D + the seL4 executor PD

*Status (2026-06-14): the **pg-Tier-D-embeddable half is GREEN and verified** —
the same `libdregg_lean.a` + static Lean runtime the host links today runs the
verified executor (`execFullForestG`) **single-threaded, with no global allocator
override and no IO event-loop thread**, in a normal host process, with all three
properties MEASURED (not assumed). The **seL4 `executor` PD is already booting** —
the verified turn runs INSIDE a real seL4 protection domain under
`qemu-system-aarch64` (re-verified by a live boot here). This doc records what the
toolchain actually offers (by inspection), the spike result, and the precise
remaining work per frontier.*

The two stuck frontiers this targets:

- **pg-dregg full Tier-D** — the executor IN the postgres backend, so kernel state
  and app `UPDATE`s commit in one transaction (`pg-dregg/docs/PG-DREGG-TIER-D-SPIKE.md`).
  Was D-SIDECAR, blocked on the belief that the Lean runtime overrides the global
  allocator (mimalloc) and spawns worker threads — both fatal in a single-threaded
  `palloc`/`longjmp`/`fork` backend.
- **the seL4 `executor` PD** — `libdregg_lean.a` linked on seL4/musl
  (`docs/SEL4-EMBEDDING.md` §2), blocked on an IO-free/libuv-free `leanrt`+GMP ELF
  build.

Both reduce to the SAME need: a Lean runtime that **does not override `malloc`, does
not spawn threads, and does no IO** — and that is what this doc establishes.

---

## 1. What the toolchain ACTUALLY offers (verified by inspection)

Probed against the live toolchain on this host: **Lean v4.30.0** (`leanprover/lean4:v4.30.0`,
commit `d024af099`), sysroot `~/.elan/toolchains/leanprover--lean4---v4.30.0`. All
claims below are `nm`/`ar`/source-grep, not assumption.

### 1.1 mimalloc is a PRIVATE heap — there is NO global allocator override

This is the load-bearing correction. The pg-Tier-D spike §4.1 called mimalloc "the
decisive" blocker: "the Lean runtime statically bundles mimalloc and overrides
`malloc`/`free` process-wide." **That is not what the toolchain does.**

- Lean's `config.h` sets `#define LEAN_MIMALLOC` (mimalloc *enabled*) but **NOT**
  `MI_MALLOC_OVERRIDE` — the mimalloc malloc-override TU (`alloc-override.c`) is
  **not compiled in**. Evidence: `nm static.c.o` (the mimalloc amalgamation member
  of `libleanrt.a`) defines `_mi_malloc` / `_mi_free` (mimalloc's *own* API) but
  **zero** override hooks (`malloc_zone`, `malloc_default_zone`, `mi_cmalloc` — all
  absent).
- Lean's core (`object.cpp`) calls `mi_malloc` / `mi_malloc_small` **explicitly**
  from `lean_alloc_*`. mimalloc is the allocator Lean's *own objects* use — it never
  interposes the process-wide `malloc`.
- **Proven at the linked binary**: in a host binary that links the executor,
  `nm` shows `U _malloc` (imported from libSystem, *not defined locally*) and
  `T _mi_malloc` (mimalloc present as a *private* symbol). `dladdr(malloc)` resolves
  to `/usr/lib/system/libsystem_malloc.dylib` — the host C library, untouched.

**Consequence for pg:** a postgres backend's `palloc` rides the libc `malloc` it
expects; the Lean runtime, sharing the address space, allocates from its own private
mimalloc heap via `mi_malloc`. They do not collide. Blocker 4.1 does not hold.

*Cross-platform note:* `MI_MALLOC_OVERRIDE`-off is a property of Lean's mimalloc
*build config*, the same source on Linux. The real ELF-specific hazard is a *link*
hazard, not a runtime override: `libleanrt.a`'s mimalloc uses local-exec TLS
(`R_X86_64_TPOFF32`), which an ELF `-shared` link rejects — which is exactly why a
**cdylib** (a pgrx extension `.so`) must link the runtime *shared*
(`DREGG_LEAN_LINK=shared` → `libleanshared`), as `dregg-lean-ffi/build.rs`
(`shared_link_mode`) and `sdk-py` already do. So on Linux the in-backend path links
the runtime shared; the allocator is still private (no override), and the cdylib-link
mechanism is the established one. See §5 for the Linux caveat in full.

### 1.2 worker threads are LAZY and UNSTARTED — `Task.spawn` runs inline

The pg spike §4.2 called worker threads the second blocker. The task manager is
**lazy**:

- `object.cpp`: `static task_manager * g_task_manager = nullptr;` — created *only*
  by an explicit `lean_init_task_manager[_using]()` call, which the executor
  embedding **never makes** (`dregg_ffi_init` does not call it; the verified closure
  references the symbol but never invokes it).
- The decisive line — `lean_task_spawn_core`:
  ```cpp
  if (!g_task_manager) {
      return lean_task_pure(apply_1(c, box(0)));   // runs the closure INLINE, synchronously
  } else { ... enqueue to a worker ... }
  ```
  With `g_task_manager == nullptr`, **every `Task.spawn` runs inline on the calling
  thread**. No worker thread is ever created.

So the Lean runtime is *single-threaded by default* in our embedding — the task
manager simply never starts.

### 1.3 the ONE thread the default init DOES spawn: the libuv event loop

There is exactly one thread the *default* init creates, and it is not the task
manager. `init_module.cpp`'s `lean_initialize_runtime_module()` calls
`initialize_libuv()`, whose body (`libuv.cpp`) ends with:
```cpp
lthread([]() { event_loop_run_loop(&global_ev); });   // spawns the libuv event-loop thread
```
(`lthread`, in the `LEAN_MULTI_THREAD` build, is a real `pthread`.) **Measured: the
default `dregg_ffi_init` takes the process from 2 → 3 OS threads** (mach
`task_threads`), and that thread persists. It is the libuv IO event loop — pulled at
init even though the pure executor turn does no socket/file/timer IO.

This is the host analogue of the seL4 lane's libuv excision, and the one thing the
embeddable path must remove. The eight other initializers
(`alloc, debug, object, io, thread, mutex, process, stack_overflow`) are
libuv-free and thread-free (`initialize_thread` is only thread-local-reset-fns;
`initialize_io` is the IO-monad *core* — heartbeats, the mono clock,
`lean_io_mark_end_initialization` — which the executor needs, with no libuv).

### 1.4 GMP

`libgmp.a` ships in the sysroot (`lib/libgmp.a`, 829 KB) and the static runtime link
already pulls it. On the **host/pg** path GMP is a non-issue — it links the
toolchain's real GMP. It is only a *bare seL4* concern (the toolchain bundles GMP but
exposes no ELF `libgmp.a` for that target), and that is already solved in the seL4
lane (§4).

---

## 2. THE SPIKE (Part 1) — the pg-Tier-D-embeddable half, GREEN

The fix is the smallest real path: **do not call `lean_initialize_runtime_module()`;
call the eight libuv-free initializers directly, omitting `initialize_libuv()`.**
Because nothing then references `lean_initialize_runtime_module`, the linker never
pulls `init_module.cpp.o` → never pulls `libuv.cpp.o` → the event-loop thread is
never even linked in. This is a tiny, **additive** change — the default
`dregg_ffi_init` path is untouched (swarm-safe for node / dregg-turn).

**Files (this lane):**
- `dregg-lean-ffi/src/lean_init_st.cpp` — the new single-threaded init
  (`dregg_ffi_init_st`): calls `lean::initialize_alloc/debug/object/io/thread/mutex/
  process/stack_overflow` then the module initializers, then
  `lean_io_mark_end_initialization`. No `initialize_libuv`.
- `dregg-lean-ffi/build.rs` — compiles `lean_init_st.cpp` into the same shim archive
  (additive; default path unchanged).
- `dregg-lean-ffi/src/lib.rs` — `init_single_threaded()` +
  `shadow_exec_full_forest_auth_single_threaded()` (separate `OnceLock`; a process
  picks ONE init flavor).
- `dregg-lean-ffi/tests/embeddable_runtime_probe.rs` — the measured proof.

### 2.1 The link line (the static Lean runtime, authoritative from build.rs)

```
cargo:rustc-link-lib=static:+whole-archive=dregg_ffi_shim   ← now holds lean_init.c + lean_init_st.cpp
cargo:rustc-link-lib=static=dregg_lean                       ← the verified closure (libdregg_lean.a)
cargo:rustc-link-lib=static=Init  static=Std  static=Lean  static=leancpp  static=leanrt  static=Lake
cargo:rustc-link-lib=static=gmp   static=uv
cargo:rustc-link-lib=dylib=c++
cargo:rustc-link-search=native=.../v4.30.0/lib   +   .../v4.30.0/lib/lean
```
(`static=uv` is on the line, but the ST path references none of its event-loop
symbols, so the linker dead-strips them — see §2.3.)

### 2.2 The run (measured, single-threaded, committing turn)

`cargo test -p dregg-lean-ffi --features lean-lib --test embeddable_runtime_probe -- --nocapture`:

```
========== EMBEDDABLE-LEAN-RUNTIME SPIKE (host process) ==========
[PROP-1] malloc resolves to: /usr/lib/system/libsystem_malloc.dylib
[PROP-1] ✓ global allocator is the host libc; mimalloc is Lean-private (no interposition)
[PROP-2] threads BEFORE init:                2
[PROP-2] threads AFTER  init_single_threaded: 2
[PROP-2] threads AFTER  one real turn:        2
[PROP-2] ✓ no worker threads spawned by init or by the turn
[PROP-3] demo-turn receipt: {... "bal":[[0,0,70],[1,0,35]] ... "status":2,"ok":1}
[PROP-3] ✓ verified executor ran a real committing turn (nonce 7→8; 100→70, 5→35)
[PROP-3] ✓ overspend rejected (fail-closed; the executor genuinely decides)
========== ALL THREE GREEN: the runtime is embeddable on this host ==========
test result: ok. 1 passed; 0 failed
```

The contrast that proves the excision is load-bearing: the **default** init path
(`dregg_ffi_init`, same test machinery) measures **2 → 3 → 3** (the libuv thread);
the **single-threaded** path measures **2 → 2 → 2**.

### 2.3 Symbol-level proof at the linked binary

```
nm <test-bin>:  T _dregg_ffi_init_st          (the ST init is present)
                U _malloc                       (imported from libSystem — NOT a local override)
                T _mi_malloc                    (mimalloc present, but PRIVATE to Lean)
                (no _initialize_libuv, no _event_loop_run_loop — dead-stripped, never linked)
otool -L <test-bin>:  /usr/lib/libc++.1.dylib  +  /usr/lib/libSystem.B.dylib   (only — libuv/GMP are static)
```

**Verdict (Part 1): the executor IS embeddable into a single-threaded host on this
platform.** Same `libdregg_lean.a`, same static runtime, the ST init — `execFullForestG`
runs with no `malloc` override, no threads, no IO. That is precisely the
pg-Tier-D-in-backend precondition.

---

## 3. Remaining work for pg full Tier-D (precise)

The two §4.1/§4.2 process-model blockers in `PG-DREGG-TIER-D-SPIKE.md` are
**removed** (the runtime overrides no allocator and spawns no thread under the ST
init). The spike was on macOS; pg deploys on Linux, so:

1. **Wire the ST init into the pgrx extension build.** A pgrx extension is a cdylib;
   on Linux that must link the runtime **shared** (`DREGG_LEAN_LINK=shared`, per
   §1.1 / `build.rs` / `sdk-py`) and call `dregg_ffi_init_st` (not `dregg_ffi_init`)
   from `_PG_init`-deferred / first-call, **after** `fork()` (never in the postmaster).
   With no worker thread and no libuv thread, there is nothing thread-shaped to
   survive fork — which also removes spike §4.3.
2. **Re-run the §2 measurement on Linux** to confirm `malloc` resolves to glibc (not
   interposed) under the *shared* runtime link, and the thread count is flat across
   `dregg_ffi_init_st` + a turn. The source config (`MI_MALLOC_OVERRIDE` off, lazy
   task manager) is identical, so this is expected — but it must be MEASURED on the
   deploy platform, not inferred. *(This host has no Linux Lean toolchain; this is
   the one un-run check, and it is a measurement, not new engineering.)*
3. **`longjmp` safety.** With Lean on a private heap and no threads, the remaining
   question is whether a postgres `siglongjmp` (statement timeout / `elog(ERROR)`)
   can fire *through* a Lean call frame. The executor turn is a single synchronous
   `String→String` C call with bounded work; the safe discipline is to run it to
   completion without a postgres-interruptible point inside it (bound the turn,
   spike §6.4). This is a backend-integration discipline, not a runtime change.

Effort: **the load-bearing toolchain blockers are gone.** What remains is pgrx
wiring + the Linux re-measurement + the longjmp discipline — *days*, not the
quarters the original "defuse the allocator override / single-thread the runtime"
framing implied. (Those two were believed to require a Lean-toolchain rebuild;
§1–§2 show they require neither.)

---

## 4. The seL4 `executor` PD (Part 2) — already BOOTING (re-verified)

The seL4 frontier is substantially further than `SEL4-EMBEDDING.md` §2's "weeks-to-a-
quarter fog." Two prior lanes —
`sel4/dregg-pd/executor-pd/` (the closure + ELF runtime) and
`sel4/dregg-pd/executor-rootserver/` (the seL4 PD host) — have carried it to a real
boot. **Re-verified here, not trusted from markdown:**

- **Step 1 (closure ELF-recompile) reproduces today.** Fresh run of the toolchain
  clang on the executor FFI facet:
  `$LEAN_SYSROOT/bin/clang --target=aarch64-unknown-none -ffreestanding -O1 …
  Dregg2/Exec/FFI.c` → an **ELF 64-bit aarch64** object with
  `T dregg_exec_full_forest_auth` (the executor entry survives). The whole closure
  (757 Dregg2 facets) recompiles the same way (`scripts/cross-compile-closure.sh`).
- **The PD BOOTS — live-verified.** Booting the existing image fresh in QEMU here:
  ```
  qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 3072M \
    -nographic -serial mon:stdio -kernel out/dregg-executor-rootserver.img
  ```
  → the seL4 kernel boots, drops to user space, the root task installs its
  `sel4-musl` syscall handler, the Lean runtime initializes, and
  `dregg_exec_full_forest_auth` produces **`status:2, ok:1`** (transfer 100→70,
  5→35) INSIDE the protection domain. This is a genuine boot, not a transcribed log.

How the seL4 lane handles the same three concerns (a *different* mechanism than the
host ST init — build-time excision rather than init-path avoidance, because seL4
needs a from-source ELF runtime anyway):
- **libuv**: excised at *build* time — `scripts/build-leanrt-elf.sh` drops
  `libuv.cpp` + the 8 `uv/*.cpp` and patches `init_module.cpp` to skip
  `initialize_libuv()`; a small panic-if-reached stub resolves the few `uv_*`
  symbols `io.cpp` imports. (The host ST init reaches the same end — no event-loop
  thread — without rebuilding the runtime.)
- **mimalloc**: a 5-symbol shim over musl `malloc` (no global override — same private
  -heap shape as §1.1).
- **GMP**: real GMP 6.3.0 cross-built for aarch64-musl (`build-gmp-elf.sh`).
- **the runtime**: rebuilt from `lean4@d024af099` sources for aarch64-linux-musl
  (`build-leanrt-elf.sh` / `build-leanlib-elf.sh` / `build-leancpp-elf.sh`), then
  linked under `sel4-root-task-with-std` + `sel4-musl`.

### What remains for the seL4 executor PD (honest)

The PD boots and runs a turn; it is **not** yet a production executor PD:

1. **The crypto floor is stubbed.** `link-probe.sh`'s `crypto-stub.c` panics-if-
   reached on the 8 `dregg_*` crypto symbols (poseidon2/blake3/ed25519/stark/…). A
   non-crypto turn links + runs; a turn that hashes/verifies would abort. Production
   supplies these from the **Rust PD** (the firmament's `verifier-stark` PD already
   runs a real STARK on seL4 — `docs/SEL4-EMBEDDING.md` §8 M-STARK). Wiring the Rust
   crypto floor into the executor PD is the next real step.
2. **The elaborator is cut at init.** `init-stubs.c` no-ops
   `initialize_Lean`/`initialize_aesop_Aesop`/`initialize_Dregg2_Dregg2_Tactics` —
   the executor's compute path calls ZERO elaborator/kernel primitives (verified),
   but `Dregg2.Tactics` (a proof module imported pervasively) drags the elaborator
   into the init chain. The cut is sound for the turn but is a stub the production
   build should make principled (trim the tactic import from the executor's module
   closure so the elaborator is never pulled, rather than no-op'd).
3. **One re-emission fidelity gap** (`l_String_instDecidableLtRaw___aux__1`),
   characterized and recovered exactly in `executor-pd/WALL.md` (`aux-defs.c`,
   `lean_nat_dec_lt(p1,p2)`).
4. **It is a root-task-with-std, not the decomposed 5-PD Microkit assembly.**
   `sel4/dregg.system` is the steady-state 5-PD shape (verifier · executor · persist
   · ingress · gossip); the booting executor is a single root task. Folding it into
   the Microkit assembly with the cap-partition trust boundary is the integration
   step.

Effort: the *runtime port* (the §2 "one true blocker") is **done and boots**.
Remaining is productionization — crypto-floor wiring, the principled elaborator trim,
and the Microkit assembly — *weeks*, and none of it is the open-ended runtime fog the
roadmap feared.

---

## 5. The one honest caveat: Linux measurement

The §2 spike is **macOS** (`dladdr`/mach `task_threads`). The pg deploy target is
Linux. The two facts the spike turns on — (a) mimalloc override OFF
(`MI_MALLOC_OVERRIDE` unset in Lean's config), and (b) the lazy task manager — are
**source/config properties identical on Linux**, and the libuv-thread excision is
the same init-path change. So the ST runtime is expected to be embeddable on Linux
too. But per green-or-bust, the Linux equivalent of the §2.2/§2.3 measurement
(malloc → glibc, threads flat, under the *shared* runtime link a cdylib needs) is
**not yet run on this host** (no Linux Lean toolchain present). It is the single
remaining check for the pg frontier — a measurement to confirm, not new work to
build. The seL4 frontier already runs on Linux/musl semantics (sel4-musl) and boots.

---

## 6. Bottom line

| Frontier | Was | Now | Remaining |
|---|---|---|---|
| **pg full Tier-D** (executor in-backend) | D-SIDECAR (blocked on "mimalloc override + worker threads") | **the two blockers are refuted/removed** — ST init runs the executor with no override, no threads, no IO (measured, macOS) | pgrx wiring (shared link + `dregg_ffi_init_st` post-fork) · the Linux re-measurement · the longjmp discipline — *days* |
| **seL4 executor PD** | blocked on "IO-free/libuv-free leanrt+GMP" (weeks-to-a-quarter fog) | **BOOTS** — the verified turn runs inside a real seL4 PD (live-verified); step-1 ELF recompile reproduces | crypto-floor from the Rust PD · principled elaborator trim · the 5-PD Microkit assembly — *weeks* |

The headline: the thing both frontiers were stuck on — "Lean's runtime overrides the
allocator and spawns threads, so it can't live in a constrained single-threaded host"
— **is not what the toolchain does.** mimalloc is a private heap (override off), the
task manager is lazy (never started), and the only thread is the libuv event loop,
which the pure executor neither needs nor (under the ST init / the seL4 excision)
links. The embeddable Lean runtime is real, and it runs the verified executor.
