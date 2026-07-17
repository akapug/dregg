# executor-pd — the firmament's HEART (the leanrt excision)

This is the attempt at "the firmament's one true blocker": building the VERIFIED
dregg executor (`execFullForestG` via `dregg_exec_full_forest_auth`, proved in
`metatheory/`) for the bare-metal `aarch64-sel4-microkit` target, so a protection
domain can run one real turn and print the receipt over serial — the firmament's
first heartbeat (.docs-history-noclaude/FIRMAMENT.md §6).

## What this lane BANKED

**Steps (1)-(3) are GREEN and the VERIFIED EXECUTOR RUNS one real turn.** The
object-format wall (step 1) recompiles the Mach-O Lean closure to ELF with zero
source changes:

```
$ ./scripts/cross-compile-closure.sh
[xcompile] executor import-closure (rooted at Dregg2.Exec.FFI): 76 facets
[xcompile]   (runtime-dead trim, elaborator-severing: Dregg2.Tactics — EXCLUDED)
[xcompile] closure facets: OK=76  FAIL=0
[xcompile] ✓ trim invariant: Dregg2_Tactics.o absent (elaborator init-chain severed)
[xcompile] ✅ executor entry dregg_exec_full_forest_auth present in ELF closure (global text symbol)
```

…and the deeper wall (step 2, the ELF Lean *runtime*) is now built, so the closure
links and EXECUTES (see below).

The closure is the **PRINCIPLED** one (the production form, `docs/EMBEDDABLE-LEAN-
RUNTIME.md` §4 #2): the transitive IMPORT closure rooted at `Dregg2.Exec.FFI` —
the module that `@[export]`s the executor entry — is 77 local modules, NOT the
~820 facets `lake build` emits for the whole proof/circuit/distributed tree. This
script compiles exactly those, MINUS the one runtime-dead leaf `Dregg2.Tactics`
(pure metaprogramming: its facet `LEAN_EXPORT`s zero `l_*` runtime functions, only
the module initializer that drags the Lean elaborator into the init-chain). So the
elaborator is severed at the SHAPE of the archive — `Tactics.c`, the only facet in
the closure that calls `initialize_Lean`, is simply absent — and the verified
production entry `dregg_exec_full_forest_auth` survives as a global text symbol in
the resulting 76-member `out/libdregg_lean_elf.a` (verified: 0 undefined `l_*`
runtime symbols after the trim; the static ELF links with 0 undefined symbols).
See `WALL.md` for the exact knobs (`-isystem .../include/clang`, `llvm-ar`).

**The wall is PASSED — the verified executor runs.** `scripts/link-probe.sh`
links the verified closure against a freshly-built **ELF Lean runtime** (leanrt +
the Init/Std/Lean/mathlib/deps library bottom-half + the Lean kernel C++ + real
GMP) into a static `aarch64-linux-musl` executable (`out/dregg-executor.elf`,
**0 undefined symbols**) and drives ONE real turn:

```
$ ./scripts/link-probe.sh "$(cat out/demo-wire.txt)"
[exec] lean_initialize_runtime_module()
[exec] >>> dregg_exec_full_forest_auth(wire)
[exec] <<< receipt (313 bytes):   ...  "status":2,"ok":1
```

`dregg_exec_full_forest_auth` (= `execFullForestG` + admission) decoded the wire,
ran the gated forest turn, executed real state transitions (nonce 7→8, a 30-unit
transfer, a nullifier + commitment), and emitted **`status:2, ok:1` (bodyCommitted
— accepted)**. Evidence: `out/dregg-executor-run.log`. This is the host-musl
validation of what the seL4 executor-PD will run (sel4-musl emulates the musl
syscall surface), banking the turn before the PD link. See `WALL.md`.

## The remaining step (step 4): the seL4-PD host

The Lean runtime is now an ordinary musl aarch64 image. The remaining work is to
host it on seL4 as a **root-task-with-std** PD (it needs malloc/pthread/TLS/C++-
exceptions, not a bare Microkit PD): wire `sel4-musl`'s syscall handler
(`~/sel4-sdk/rust-sel4/crates/experimental/sel4-musl`), link the executor object
set into a `sel4-root-task-with-std` PD, and boot under `qemu-system-aarch64`.

## Files

- `scripts/cross-compile-closure.sh` — ELF-recompile the verified closure: the
  principled import closure rooted at `Dregg2.Exec.FFI` (77 modules), minus the
  runtime-dead tactic leaf `Dregg2.Tactics` (the elaborator-severing trim).
- `scripts/build-leanrt-elf.sh` — ELF leanrt (runtime + mimalloc/libuv stubs).
- `scripts/build-leanlib-elf.sh <Init|Std|Lean>` — re-emit + ELF-compile a Lean
  library from `lean4@d024af099` sources.
- `scripts/build-leancpp-elf.sh` — ELF Lean kernel C++ (Expr/Level/typechecker).
- `scripts/build-gmp-elf.sh` — real GMP 6.3.0 cross-built for aarch64-musl.
- `scripts/compile-facets-elf.sh` — ELF-compile a tree of pre-emitted `.c` facets
  (mathlib + the dependency libs).
- `scripts/link-probe.sh` — link the static executor + run one turn.
- `scripts/driver.c` — the embedded-Lean init + one-turn harness (the PD `main` seed).
- `scripts/{init,kernel,dead}-stub*.{c,txt}`, `scripts/aux-defs.c` — the small
  stub TUs (crypto floor = Rust-PD-supplied; the cut elaborator; the one recovered
  re-emission auxiliary). All justified in `WALL.md`.
- `src/main.rs` — the (current) bare-Microkit status-heart PD; the root-task-with-std
  PD that embeds `dregg-executor.elf` is step 4.
- `Cargo.toml` / `.cargo/config.toml` / `rust-toolchain.toml` — standalone build.
- `WALL.md` — the full pipeline + the precise remaining step.
- `out/` (gitignored) — all ELF build artifacts + `dregg-executor.elf` + the run log.

## Build + boot

```sh
# 1) the closure ELF-recompile (banks step 1):
cd metatheory && lake build            # populates .lake/build/ir
cd ../sel4/dregg-pd/executor-pd && ./scripts/cross-compile-closure.sh

# 2) the PD (boots as the status heart):
cd /path/to/sel4/dregg-pd/executor-pd
SEL4_INCLUDE_DIRS=$HOME/sel4-sdk/microkit-sdk-2.2.0/board/qemu_virt_aarch64/debug/include \
  CARGO_TARGET_DIR=$PWD/target-pd cargo build --release
# then link + boot with the Makefile's LINK_AND_RUN pattern (see make target
# `run-exec` proposed to the main loop).
```

## Relationship to the `executor-stub` lane

A sibling lane created `executor-stub/` — a placeholder PD that holds the
executor's SEAT in the 5-PD `dregg.system` assembly (maps the `turn_in`/`commit_out`
shared regions). That lane keeps the assembly booting with the heart seat wired;
THIS lane is the deeper port attempt that banks the ELF-recompile breakthrough and
characterizes the runtime wall. They are complementary: when step 2 lands, this
crate's real executor PD replaces the stub in the assembly.
