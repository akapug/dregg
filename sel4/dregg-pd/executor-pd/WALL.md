# The executor-PD wall — exact remaining blocker + the precise next step

*The firmament's one true blocker (docs/FIRMAMENT.md §6, §7), characterized to
the symbol. Probed directly against the live toolchain (leanrt v4.30.0, Lean
v4.30.0 `d024af099`, the in-tree `metatheory/` closure) on 2026-06-13.*

## The four-step excision plan and where each stands

The destination: an seL4 PD that embeds the VERIFIED executor (`execFullForestG`
via `dregg_exec_full_forest_auth`) and runs one real turn, printing the receipt
over serial. The plan (docs/SEL4-EMBEDDING.md §2):

| Step | What | Status |
|------|------|--------|
| (1) | ELF-recompile the Lean closure under leanc | **✅ GREEN — done** |
| (2) | ELF leanrt + stub `initialize_libuv`/`initialize_io` | **⛔ THE WALL** |
| (3) | GMP for ELF, or a fixnum-only shim | ◐ shim plausible (evidence below) |
| (4) | host on `sel4-musl` + `root-task-with-std` | ◐ gated on (2)+(3) |

## Step (1) — GREEN (the part the roadmap called "weeks-to-a-quarter fog")

`scripts/cross-compile-closure.sh` ELF-recompiles the whole application closure:

- **All 757 Dregg2 `:c` facets** emitted by `lake build` (`metatheory/.lake/
  build/ir/Dregg2/**/*.c`) compile to **ELF aarch64** with the in-toolchain
  clang, **ZERO source changes**. `OK=757 FAIL=0`.
- The verified executor's production entry **`dregg_exec_full_forest_auth`**
  (emitted by `@[export]` in `Dregg2/Exec/FFI.lean:3313`, lands in
  `Dregg2/Exec/FFI.c:37508`) survives into the ELF closure as a **global text
  symbol (`T`)**, verified with `nm` on the archived `out/libdregg_lean_elf.a`
  (757-member, 58.9 MB, ELF aarch64).

The two knobs that made it work (vs. the naive attempt that fails on
`stddef.h not found`):

1. The Lean toolchain's clang ships its **freestanding headers** (`stddef.h`,
   `stdint.h`, `stdarg.h`) under `$LEAN_SYSROOT/include/clang`, **not** the
   usual `-print-resource-dir`/include. Pass `-isystem $LEAN_SYSROOT/include/clang`.
2. The archive must be built with the toolchain's **`llvm-ar`**, not the host
   BSD `ar` — the latter mangles cross-arch (ELF-on-Mach-O-host) archives
   (collapses members, runs a Mach-O-only ranlib).

So the object-format wall (Mach-O→ELF) is **passable on the native macOS host
with the in-toolchain clang**. This was the highest-risk line item in the
roadmap; it is now retired for the application closure.

## Step (2) — THE WALL: there is no ELF Lean runtime to link against

The ELF application closure (`libdregg_lean_elf.a`) is the *application* half of
the link. Its objects call leanrt entry points — `lean_nat_add`,
`lean_alloc_ctor`, `lean_initialize_runtime_module`, the GC, `mi_malloc`, … —
which live in the **Lean runtime archives** (`libleanrt.a`, `libleancpp.a`,
`libInit.a`, `libStd.a`, `libLean.a`). On this toolchain those archives are
**Mach-O arm64 only** (the host build), e.g. `libleanrt.a`'s 34 objects are all
`Mach-O 64-bit object arm64`. They cannot link into an ELF image.

**The exact wall: the toolchain ships NO C++ runtime sources to recompile them
for ELF.** `$LEAN_SYSROOT/src/lean/` contains the Lean *library* sources
(`Init/`, `Std/`, `Lean/` — `.lean` files) and an empty `runtime/uv/` tree, but
**none of the runtime `.cpp`** (`init_module.cpp`, `object.cpp`, `alloc.cpp`,
`mpz.cpp`, …). `find $LEAN_SYSROOT/src -name '*.cpp'` returns nothing. Unlike
step (1) — where the `.c` facets are on disk and recompile trivially — the
runtime must be **rebuilt from the upstream lean4 repo** at the toolchain commit.

### The precise next step (step 2)

Fetch `github.com/leanprover/lean4` at commit **`d024af099ca4bf2c86f649261ebf59565dc8c622`**
(the v4.30.0 toolchain commit, from `lean --version`), then build the runtime
bottom-half for the ELF target. With the runtime sources present, the libuv
excision is *weld, not build* — it is concentrated and separable:

- **The libuv coupling is exactly 10 of leanrt's 34 objects** (`dns,
  event_loop, io, libuv, net_addr, signal, system, tcp, timer, udp`), named by
  IO concern. The pure executor path (`dregg_exec_full_forest_auth`, no
  socket/file/timer) calls **none** of them.
- **The pull is at init only**: `lean_initialize_runtime_module` (in
  `init_module.cpp.o`) has undefined refs to **`initialize_libuv`** and
  **`lean::initialize_io`** (`nm init_module.cpp.o` confirms exactly these two).
  Stub both as no-op-success and provide the handful of `uv_*` symbols the
  linker demands but execution never reaches; drop the 10 libuv objects. The
  other six initializers (`alloc, debug, mutex, object, thread, process,
  stack_overflow`) are libuv-free and stay.

## Step (3) — GMP: the fixnum-only shim is plausible (measured)

GMP is referenced by exactly **2 leanrt objects** (`mpz.cpp.o`,
`sharecommon.cpp.o`; `mpz.cpp.o` carries 43 `__gmpz_*` refs). The question
(decision §8.2): does any kernel turn ever exceed a 63-bit fixnum, forcing the
`mpz` bignum path? **Evidence it does not:**

- **Zero** Dregg2 `:c` facets reference `lean_alloc_mpz` / `lean_mpz` / any
  bignum-allocation entry (`grep -lrE 'lean_alloc_mpz|...' Dregg2/*.c` → 0).
- All executor arithmetic is via `lean_nat_add` (630×), `lean_int_add` (349×),
  `lean_nat_sub`/`mul`/`mod`/`div`/`pow`, etc. — the small-arg fast paths.
  These fall back to GMP only when a runtime value exceeds 63 bits. The kernel
  state (cell ids, balances, nonces, heights) operates on small values, so the
  GMP path is **reachable but cold**.

⇒ A **fixnum-only shim** that stubs `__gmpz_*` (panic-if-reached) is plausible
and deletes a whole C dependency. The conservative alternative — recompile GMP
(portable C, malloc+libc only) for ELF — is also available; it is the safer of
the two and the right default unless the shim is proven exhaustively safe.

## Step (4) — the host substrate (gated on 2+3)

The executor-PD is a **root-task-with-std** style PD, not a bare Microkit PD: it
needs malloc/pthread/TLS/C++-exceptions. The substrate exists experimentally in
rust-sel4: `crates/experimental/sel4-musl` (a musl syscall-emulation shim) +
`crates/private/support/sel4-root-task-with-std`. Build musl for the ELF target,
wire `sel4-musl`'s syscall handler, link the ELF closure + the ELF leanrt (from
step 2) + the fixnum/GMP layer (step 3) under the shim. Decision §8.3: root-task
(simpler, weaker isolation) vs. a Microkit-PD musl substrate (the steady-state
`dregg.system` shape).

## Summary — the one symbol that is the wall

The whole blocker reduces to: **there is no ELF build of `lean_initialize_runtime_module`
+ the six libuv-free runtime initializers** (the toolchain ships them Mach-O-only
and carries no sources). Everything downstream of an ELF leanrt — the libuv
excision, the GMP shim, the musl host — is characterized and low-risk. The next
concrete action is to build an ELF leanrt from `lean4@d024af099` with the 10
libuv objects excised and the two init stubs in place.
