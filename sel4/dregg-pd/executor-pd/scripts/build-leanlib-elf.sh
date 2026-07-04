#!/usr/bin/env bash
#
# build-leanlib-elf.sh — ELF-recompile a Lean LIBRARY closure (Init / Std / Lean)
# for the seL4 substrate, by re-emitting its C facets from the lean4 sources at the
# toolchain commit and compiling them aarch64-ELF (same recipe as the Dregg2
# closure in cross-compile-closure.sh).
#
# Why this exists (WALL.md, step 2 follow-on): the verified executor closure was
# compiled against the full Lean stdlib + mathlib, so its module-init chain pulls
# `initialize_Init` (+ Lean-core + mathlib inits) and ~94 bare-core `l_Nat_*/
# l_List_*/l_Array_*/...` runtime functions. Those live ONLY in the toolchain's
# Mach-O `libInit.a`/`libLean.a` (no C facets shipped). BUT the toolchain `lean -c`
# re-emits the C from the cloned `Init/**.lean` sources, and that C ELF-compiles
# cleanly (probed: l_Nat_blt, initialize_Init_Data_Nat_Basic, ... as global T).
# This recovers the missing library bottom-half for ELF.
#
# Usage: build-leanlib-elf.sh <LIB>   where LIB in {Init, Std, Lean}
# Output: out/leanlib-elf/lib<LIB>_elf.a
set -euo pipefail

LEAN_SYSROOT="${LEAN_SYSROOT:-$(lean --print-prefix)}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN4_SRC="${LEAN4_SRC:-/tmp/lean4-rt}"
LIB="${1:?usage: build-leanlib-elf.sh <Init|Std|Lean>}"
TARGET="${TARGET:-aarch64-unknown-none}"
OUT_DIR="${OUT_DIR:-$HERE/../out/leanlib-elf}"
JOBS="${JOBS:-8}"

CLANG="$LEAN_SYSROOT/bin/clang"
AR="$LEAN_SYSROOT/bin/llvm-ar"
SRCROOT="$LEAN4_SRC/src"
LIBROOT="$SRCROOT/$LIB"

[ -d "$LIBROOT" ] || { echo "ERROR: $LIBROOT not found (clone lean4@d024af099)" >&2; exit 1; }

mkdir -p "$OUT_DIR/c/$LIB" "$OUT_DIR/obj"
echo "[leanlib-elf] LIB=$LIB  modules=$(find "$LIBROOT" -name '*.lean' | wc -l | tr -d ' ')"

# Step A: emit C for each module via the toolchain lean (-c), reading the prebuilt
# .olean from the toolchain (LEAN_PATH) and the .lean source from the clone.
# Re-emit is idempotent; skip if the .c already exists and is newer than source.
emit_one() {
  local lean="$1"
  local rel="${lean#"$SRCROOT"/}"          # e.g. Init/Data/Nat/Basic.lean
  local cout="$OUT_DIR/c/${rel%.lean}.c"
  mkdir -p "$(dirname "$cout")"
  if [ -f "$cout" ] && [ "$cout" -nt "$lean" ]; then return 0; fi
  ( cd "$SRCROOT" && LEAN_PATH="$LEAN_SYSROOT/lib/lean" \
      "$LEAN_SYSROOT/bin/lean" --root=. -c "$cout" "$rel" ) 2>"$cout.err" \
    && rm -f "$cout.err" || { echo "EMIT-FAIL $rel" >&2; return 1; }
}
export -f emit_one
export SRCROOT OUT_DIR LEAN_SYSROOT

echo "[leanlib-elf] emitting C facets ($JOBS-way)…"
emit_ok=0; emit_fail=0
# The umbrella module `$LIB.lean` (sibling of `$LIB/`) defines the top-level
# `initialize_<LIB>` that the closure calls — emit it too, not just the subtree.
[ -f "$SRCROOT/$LIB.lean" ] && emit_one "$SRCROOT/$LIB.lean" || true
# xargs -P for parallelism; collect failures.
if find "$LIBROOT" -name '*.lean' -print0 \
     | xargs -0 -P "$JOBS" -I{} bash -c 'emit_one "$@"' _ {} 2>"$OUT_DIR/emit.$LIB.errlog"; then
  :
fi
emit_fail=$(grep -c '^EMIT-FAIL' "$OUT_DIR/emit.$LIB.errlog" 2>/dev/null || echo 0)
emit_ok=$(find "$OUT_DIR/c/$LIB" -name '*.c' | wc -l | tr -d ' ')
echo "[leanlib-elf] C emitted: $emit_ok  (emit-fail=$emit_fail)"
if [ "$emit_fail" -ne 0 ]; then
  echo "[leanlib-elf] first emit failures:" >&2
  grep '^EMIT-FAIL' "$OUT_DIR/emit.$LIB.errlog" | head -5 >&2
fi

# Step B: ELF-compile each emitted .c (the cross-compile-closure recipe).
echo "[leanlib-elf] ELF-compiling facets…"
comp_ok=0; comp_fail=0; failed=""
while IFS= read -r c; do
  rel="${c#"$OUT_DIR"/c/}"; name="${rel%.c}"; name="${name//\//_}"
  if "$CLANG" --target="$TARGET" -ffreestanding -O1 -fno-exceptions \
        -isystem "$LEAN_SYSROOT/include/clang" -I "$LEAN_SYSROOT/include" \
        -c "$c" -o "$OUT_DIR/obj/$name.o" 2>"$OUT_DIR/obj/$name.err"; then
    comp_ok=$((comp_ok+1)); rm -f "$OUT_DIR/obj/$name.err"
  else
    comp_fail=$((comp_fail+1)); failed="$failed $name"
  fi
done < <(find "$OUT_DIR/c/$LIB" -name '*.c'; [ -f "$OUT_DIR/c/$LIB.c" ] && echo "$OUT_DIR/c/$LIB.c")
echo "[leanlib-elf] ELF objects: OK=$comp_ok FAIL=$comp_fail"
if [ "$comp_fail" -ne 0 ]; then
  f="$(echo "$failed" | awk '{print $1}')"
  echo "[leanlib-elf] first compile error ($f):" >&2
  head -12 "$OUT_DIR/obj/$f.err" >&2
fi

# Step C: archive this library's objects (the subtree ${LIB}_*.o AND the umbrella ${LIB}.o).
rm -f "$OUT_DIR/lib${LIB}_elf.a"
find "$OUT_DIR/obj" \( -name "${LIB}_*.o" -o -name "${LIB}.o" \) -print0 \
  | xargs -0 "$AR" rcs "$OUT_DIR/lib${LIB}_elf.a"
echo "[leanlib-elf] wrote $OUT_DIR/lib${LIB}_elf.a"
file "$OUT_DIR/lib${LIB}_elf.a"
echo "[leanlib-elf] members: $("$AR" t "$OUT_DIR/lib${LIB}_elf.a" 2>/dev/null | wc -l | tr -d ' ')"
