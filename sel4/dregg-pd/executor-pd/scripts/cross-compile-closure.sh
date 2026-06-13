#!/usr/bin/env bash
#
# cross-compile-closure.sh — ELF-recompile the verified-executor Lean closure
# for the bare-metal seL4 aarch64 target.
#
# THE HEART, step (1) of the executor-PD excision plan (docs/SEL4-EMBEDDING.md §2,
# docs/FIRMAMENT.md §6): the compiled Lean closure (`libdregg_lean.a`) is Mach-O
# arm64 (the macOS host build); the seL4 target is ELF aarch64. The whole closure
# must be RECOMPILED with the Lean toolchain's clang targeting an ELF triple — a
# recompile, not a relink.
#
# PROVEN (2026-06-13): this works. All 757 Dregg2 `:c` facets emitted by
# `lake build` compile cleanly to ELF aarch64 with ZERO source changes, and the
# executor FFI entry `dregg_exec_full_forest_auth` survives into the ELF closure.
# The object-format wall — the part the roadmap called "weeks-to-a-quarter fog" —
# is PASSABLE on the native macOS host with the in-toolchain clang.
#
# What this script does NOT yet do (the precise remaining wall, see WALL.md):
#   * It compiles the Dregg2 IR facets (pure Lean → C → ELF). It does NOT
#     recompile the Lean RUNTIME (leanrt/leancpp/Init/Std/Lean), because the
#     toolchain ships those only as Mach-O `.a` — the C++ runtime SOURCES
#     (`init_module.cpp`, `object.cpp`, …) are NOT in $LEAN_SYSROOT/src. Getting
#     an ELF leanrt requires the upstream lean4 repo at the toolchain commit.
#   * It therefore produces `libdregg_lean_elf.a` (the application closure), the
#     INPUT to the final link — not the linked PD. The link needs the ELF runtime.
#
# Usage:
#   ./cross-compile-closure.sh [OUT_DIR]
# Env:
#   LEAN_SYSROOT   (default: `lean --print-prefix`)
#   METATHEORY     (default: repo-root/metatheory) — must have `.lake/build/ir`
#   TARGET         (default: aarch64-unknown-none) — the ELF triple
set -euo pipefail

LEAN_SYSROOT="${LEAN_SYSROOT:-$(lean --print-prefix)}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
METATHEORY="${METATHEORY:-$(cd "$HERE/../../../../metatheory" && pwd)}"
TARGET="${TARGET:-aarch64-unknown-none}"
OUT_DIR="${1:-$HERE/../out}"

CLANG="$LEAN_SYSROOT/bin/clang"
# Use the toolchain's llvm-ar: the host BSD `ar` mangles cross-arch (ELF on a
# Mach-O host) archives, collapsing members and running a Mach-O-only ranlib.
AR="$LEAN_SYSROOT/bin/llvm-ar"
# The Lean toolchain's clang ships its freestanding headers (stddef.h, stdint.h,
# stdarg.h) under include/clang, NOT the usual resource-dir/include. The Lean C
# runtime header lives under include/lean.
FREESTANDING_INC="$LEAN_SYSROOT/include/clang"
LEAN_INC="$LEAN_SYSROOT/include"

IR_DIR="$METATHEORY/.lake/build/ir"
if [ ! -d "$IR_DIR" ]; then
    echo "ERROR: $IR_DIR not found. Run 'lake build' in $METATHEORY first" >&2
    echo "(the C facets are emitted by the lake :c facet; see dregg-lean-ffi/build.rs)" >&2
    exit 1
fi

mkdir -p "$OUT_DIR/obj"
echo "[xcompile] LEAN_SYSROOT=$LEAN_SYSROOT"
echo "[xcompile] TARGET=$TARGET   IR_DIR=$IR_DIR"

ok=0; fail=0; failed=""
# Compile every Dregg2 IR facet. -ffreestanding: no hosted libc assumptions.
# The facet C is pure (decode→step→encode over Lean objects); it calls leanrt
# entry points (lean_nat_add, lean_alloc_ctor, …) that the final link resolves.
while IFS= read -r c; do
    rel="${c#"$IR_DIR"/}"
    name="${rel%.c}"; name="${name//\//_}"
    if "$CLANG" --target="$TARGET" -ffreestanding -O1 -fno-exceptions \
            -isystem "$FREESTANDING_INC" -I "$LEAN_INC" \
            -c "$c" -o "$OUT_DIR/obj/$name.o" 2>"$OUT_DIR/obj/$name.err"; then
        ok=$((ok+1)); rm -f "$OUT_DIR/obj/$name.err"
    else
        fail=$((fail+1)); failed="$failed $name"
    fi
done < <(find "$IR_DIR/Dregg2" "$IR_DIR/Metatheory" -name '*.c' 2>/dev/null)

echo "[xcompile] Dregg2 facets: OK=$ok  FAIL=$fail"
if [ "$fail" -ne 0 ]; then
    echo "[xcompile] FAILED:$failed" >&2
    f="$(echo "$failed" | awk '{print $1}')"
    echo "[xcompile] first error ($f):" >&2
    head -12 "$OUT_DIR/obj/$f.err" >&2
    exit 1
fi

# Archive the ELF closure. This is `libdregg_lean_elf.a` — the application half
# of the link. (The runtime half — an ELF leanrt — is the remaining wall.)
rm -f "$OUT_DIR/libdregg_lean_elf.a"
"$AR" rcs "$OUT_DIR/libdregg_lean_elf.a" "$OUT_DIR"/obj/*.o
echo "[xcompile] wrote $OUT_DIR/libdregg_lean_elf.a"
file "$OUT_DIR/libdregg_lean_elf.a"
echo "[xcompile] members: $("$AR" t "$OUT_DIR/libdregg_lean_elf.a" | wc -l | tr -d ' ')"

# Prove the executor entry survived into the ELF closure. (Use the host `nm`,
# which reads these host-emitted ELF objects correctly; the toolchain's
# `llvm-nm` mis-parses them on this macOS host.)
if nm "$OUT_DIR/libdregg_lean_elf.a" 2>/dev/null | grep -q ' T dregg_exec_full_forest_auth'; then
    echo "[xcompile] ✅ executor entry dregg_exec_full_forest_auth present in ELF closure (global text symbol)"
else
    echo "[xcompile] ⚠ executor entry NOT found — check Dregg2/Exec/FFI.c emitted" >&2
    exit 1
fi
