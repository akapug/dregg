# executor-pd — the firmament's HEART (the leanrt excision)

This is the attempt at "the firmament's one true blocker": building the VERIFIED
dregg executor (`execFullForestG` via `dregg_exec_full_forest_auth`, proved in
`metatheory/`) for the bare-metal `aarch64-sel4-microkit` target, so a protection
domain can run one real turn and print the receipt over serial — the firmament's
first heartbeat (docs/FIRMAMENT.md §6).

## What this lane BANKED

**Step (1) of the excision plan is GREEN.** The object-format wall — recompiling
the Mach-O Lean closure to ELF, the part the roadmap called "weeks-to-a-quarter
fog" — is **passable on the native macOS host with zero source changes**:

```
$ ./scripts/cross-compile-closure.sh
[xcompile] Dregg2 facets: OK=757  FAIL=0
[xcompile] ✅ executor entry dregg_exec_full_forest_auth present in ELF closure (global text symbol)
```

All 757 Dregg2 `:c` facets (the whole verified-executor closure) ELF-recompile
for aarch64, and the production entry `dregg_exec_full_forest_auth` survives as a
global text symbol in the resulting `out/libdregg_lean_elf.a` (757-member ELF
archive). See `WALL.md` for the exact knobs (`-isystem .../include/clang`,
`llvm-ar`).

**The PD boots.** `dregg-executor-pd.elf` cross-builds for `aarch64-sel4-microkit`
and boots on the seL4 microkernel in QEMU, printing the heart's bring-up state +
the cross-compile proof over serial (captured: `/tmp/sel4-executor-pd-boot.log`,
ends `[exec] heart slot OCCUPIED + self-reporting`). It is a STATUS heart today —
it occupies the firmament's heart slot and self-reports rather than leaving it
empty — because the Lean runtime cannot yet link (step 2, below).

## The remaining wall (step 2)

The ELF *application* closure has no ELF *runtime* to link against: the toolchain
ships `leanrt`/`leancpp`/`Init`/`Std`/`Lean` as **Mach-O archives only** and
carries **no C++ runtime sources** to recompile them. The next concrete action is
to build an ELF `leanrt` from `lean4@d024af099` with the 10 libuv objects excised
(`initialize_libuv` + `lean::initialize_io` stubbed no-op) and a fixnum/GMP layer.
`WALL.md` characterizes this to the symbol, with the GMP-shim feasibility measured.

## Files

- `scripts/cross-compile-closure.sh` — the real ELF-recompile of the closure
  (runnable today; needs `metatheory/.lake/build/ir` populated by `lake build`).
- `src/main.rs` — the executor-PD (boots, reports bring-up state over serial).
- `Cargo.toml` / `.cargo/config.toml` / `rust-toolchain.toml` — standalone build
  (own workspace + own target dir; NOT a member of the dregg-pd workspace, to
  stay swarm-safe alongside the `executor-stub` assembly-seat lane).
- `WALL.md` — the exact remaining blocker + the precise next step.
- `out/` (gitignored) — the ELF closure build artifacts (`libdregg_lean_elf.a`).

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
