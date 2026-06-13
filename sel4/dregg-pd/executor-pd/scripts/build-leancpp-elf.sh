#!/usr/bin/env bash
#
# build-leancpp-elf.sh — ELF-compile the Lean KERNEL C++ (src/kernel + src/util)
# for the seL4 substrate. This is the part of `leancpp` the executor's module-init
# path genuinely needs: lean_expr_*/lean_level_*/lean_kernel_* (Expr/Level smart
# constructors, instantiate, the typechecker). Some live module initializers build
# Expr/Level literals at init time, so these are NOT dead (the kernel-stub abort on
# lean_level_mk_data surfaced this — an honest result of the run probe).
#
# The kernel is self-contained (17 files) and does NOT need the elaborator/parser/
# frontend, so we compile kernel/ + util/ only (not the whole leancpp). Same hosted
# aarch64-linux-musl recipe as build-leanrt-elf.sh.
#
# Output: out/leancpp-elf/libleancpp_kernel_elf.a
set -euo pipefail

LEAN_SYSROOT="${LEAN_SYSROOT:-$(lean --print-prefix)}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LEAN4_SRC="${LEAN4_SRC:-/tmp/lean4-rt}"
MUSL_PREFIX="${MUSL_PREFIX:-/opt/homebrew/opt/aarch64-unknown-linux-musl}"
GXX="$MUSL_PREFIX/bin/aarch64-linux-musl-g++"
AR="$MUSL_PREFIX/bin/aarch64-linux-musl-ar"
OUT_DIR="${1:-$HERE/../out/leancpp-elf}"
LEANRT_ELF="${LEANRT_ELF:-$HERE/../out/leanrt-elf}"  # for the generated githash.h

SRC="$LEAN4_SRC/src"
[ -f "$SRC/kernel/expr.cpp" ] || { echo "ERROR: kernel sources not at $SRC/kernel" >&2; exit 1; }

mkdir -p "$OUT_DIR/obj"
INC=(-I "$SRC" -I "$LEANRT_ELF" -I "$LEAN_SYSROOT/include" -I "$SRC/include")
FLAGS=(-std=c++20 -O2 -DNDEBUG -DLEAN_EXPORTING -DLEAN_MULTI_THREAD -DLEAN_USE_GMP)

echo "[leancpp-elf] GXX=$GXX  ($($GXX -dumpmachine))"
ok=0; fail=0; failed=""
for f in "$SRC"/kernel/*.cpp "$SRC"/util/*.cpp; do
  name="kc_$(basename "$f" .cpp)"
  if "$GXX" "${FLAGS[@]}" "${INC[@]}" -c "$f" -o "$OUT_DIR/obj/$name.o" 2>"$OUT_DIR/obj/$name.err"; then
    ok=$((ok+1)); rm -f "$OUT_DIR/obj/$name.err"
  else
    fail=$((fail+1)); failed="$failed $(basename "$f")"
  fi
done
echo "[leancpp-elf] kernel+util: OK=$ok FAIL=$fail"
if [ "$fail" -ne 0 ]; then
  echo "[leancpp-elf] FAILED:$failed" >&2
  f="$(echo "$failed" | awk '{print $1}' | sed 's/\.cpp//')"
  echo "[leancpp-elf] first error (kc_$f):" >&2
  head -20 "$OUT_DIR/obj/kc_$f.err" >&2
  exit 1
fi

# The kernel's NATIVE-REDUCTION path (type_checker.cpp) references three library/
# symbols — mk_bool_true/false and ir::run_boxed_kernel — that live in src/library
# (the elaborator side we deliberately don't pull). They are reached ONLY when the
# kernel evaluates native code during whnf/is_def_eq, which the executor never does
# (lean_kernel_* are not on the turn path). Provide abort-if-reached definitions with
# the exact mangled signatures so the kernel links without dragging src/library.
cat > "$OUT_DIR/library-stub.cpp" <<'EOF'
#include "kernel/expr.h"
#include "kernel/environment.h"
#include "library/util.h"          /* declares mk_bool_true/false */
#include "library/ir_interpreter.h" /* declares ir::run_boxed_kernel */
#include <cstdlib>
#include <cstdio>
namespace lean {
[[noreturn]] static void lib_unreached(const char* w){
  std::fprintf(stderr,"[exec] library native-reduction symbol reached: %s (executor turn must not native-reduce)\n", w);
  std::abort();
}
expr mk_bool_true()  { lib_unreached("mk_bool_true"); }
expr mk_bool_false() { lib_unreached("mk_bool_false"); }
namespace ir {
object * run_boxed_kernel(environment const &, options const &, name const &, unsigned, object **){ lib_unreached("ir::run_boxed_kernel"); }
}
}
EOF
if "$GXX" "${FLAGS[@]}" "${INC[@]}" -c "$OUT_DIR/library-stub.cpp" -o "$OUT_DIR/obj/library-stub.o" 2>"$OUT_DIR/library-stub.err"; then
  echo "[leancpp-elf] library native-reduction stub compiled (3 symbols, abort-if-reached)"
else
  echo "[leancpp-elf] library-stub failed:" >&2; head -20 "$OUT_DIR/library-stub.err" >&2; exit 1
fi

rm -f "$OUT_DIR/libleancpp_kernel_elf.a"
"$AR" rcs "$OUT_DIR/libleancpp_kernel_elf.a" "$OUT_DIR"/obj/*.o
echo "[leancpp-elf] wrote $OUT_DIR/libleancpp_kernel_elf.a ($("$AR" t "$OUT_DIR/libleancpp_kernel_elf.a"|wc -l|tr -d ' ') members)"
file "$OUT_DIR/libleancpp_kernel_elf.a"
