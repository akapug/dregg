#!/usr/bin/env bash
# compile-facets-elf.sh — ELF-compile a tree of pre-emitted Lean .c facets.
# Usage: compile-facets-elf.sh <IR_DIR> <PREFIX> <OUT_ARCHIVE>
set -euo pipefail
LEAN_SYSROOT="${LEAN_SYSROOT:-$(lean --print-prefix)}"
IR_DIR="$1"; PREFIX="$2"; OUT_AR="$3"
TARGET="${TARGET:-aarch64-unknown-none}"
JOBS="${JOBS:-8}"
OBJ_DIR="$(dirname "$OUT_AR")/obj-$PREFIX"
mkdir -p "$OBJ_DIR"
CLANG="$LEAN_SYSROOT/bin/clang"; AR="$LEAN_SYSROOT/bin/llvm-ar"
compile_one() {
  local c="$1"
  local name; name="$(echo "$c" | sed -E 's|.*/ir/||; s|/|_|g; s|\.c$||')"
  "$CLANG" --target="$TARGET" -ffreestanding -O1 -fno-exceptions \
    -isystem "$LEAN_SYSROOT/include/clang" -I "$LEAN_SYSROOT/include" \
    -c "$c" -o "$2/$name.o" 2>"$2/$name.err" && rm -f "$2/$name.err" || echo "CFAIL $c"
}
export -f compile_one; export CLANG AR LEAN_SYSROOT TARGET
find "$IR_DIR" -name '*.c' -print0 | xargs -0 -P "$JOBS" -I{} bash -c 'compile_one "$@"' _ {} "$OBJ_DIR" 2>"$OBJ_DIR.cfail" || true
nfail=$(grep -c '^CFAIL' "$OBJ_DIR.cfail" 2>/dev/null || echo 0)
nok=$(find "$OBJ_DIR" -name '*.o' | wc -l | tr -d ' ')
echo "[compile-facets] $PREFIX: OK=$nok FAIL=$nfail"
[ "$nfail" -gt 0 ] && head -3 "$OBJ_DIR.cfail" >&2
rm -f "$OUT_AR"
find "$OBJ_DIR" -name '*.o' -print0 | xargs -0 "$AR" rcs "$OUT_AR"
echo "[compile-facets] wrote $OUT_AR ($("$AR" t "$OUT_AR" 2>/dev/null | wc -l | tr -d ' ') members)"
