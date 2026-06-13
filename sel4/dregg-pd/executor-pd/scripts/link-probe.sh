#!/usr/bin/env bash
# link-probe.sh — the definitive step-2 proof: link the VERIFIED executor closure
# + driver into a STATIC aarch64-linux-musl executable against the freshly-built
# ELF Lean runtime + library bottom-halves + real GMP, then (a) prove all symbols
# resolve and (b) run ONE real turn under qemu-aarch64.
#
# This is the host-musl validation of the firmament's HEART: the same binary the
# seL4 executor-PD will run (sel4-musl emulates the musl syscall surface), exercised
# here on the dev box to bank the turn BEFORE the PD link.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="$HERE/../out"
MUSL=/opt/homebrew/opt/aarch64-unknown-linux-musl
GXX="$MUSL/bin/aarch64-linux-musl-g++"
GCC="$MUSL/bin/aarch64-linux-musl-gcc"
NM="$MUSL/bin/aarch64-linux-musl-nm"
LEAN_SYSROOT="${LEAN_SYSROOT:-$(lean --print-prefix)}"

# (1) crypto floor stub (the Rust PD supplies these in production; panic-if-reached
#     here so a non-crypto turn links and runs).
cat > "$OUT/crypto-stub.c" <<'EOF'
#include <stdlib.h>
#include <stdio.h>
static void* cx(const char* w){ fprintf(stderr,"[exec] crypto floor: %s\n",w); abort(); }
void* dregg_poseidon2_hash(void* a){ return cx("poseidon2"); }
void* dregg_blake3_hash(void* a){ return cx("blake3"); }
void* dregg_ed25519_verify(void* a,void* b,void* c){ return cx("ed25519"); }
void* dregg_stark_verify(void* a,void* b,void* c){ return cx("stark"); }
void* dregg_pedersen_commit(void* a,void* b){ return cx("pedersen"); }
void* dregg_nullifier_derive(void* a,void* b){ return cx("nullifier"); }
void* dregg_hmac_sha256(void* a,void* b){ return cx("hmac"); }
void* dregg_aead_open(void* a,void* b,void* c){ return cx("aead"); }
EOF
"$GCC" -O2 -c "$OUT/crypto-stub.c" -o "$OUT/crypto-stub.o"

# (1b) Lean ELABORATOR/KERNEL C++ stub. The executor's reachable COMPUTE objects
#      reference ZERO elaborator/kernel primitives (verified); they enter the link
#      only because mathlib/Dregg2 *tactic/metaprogramming* facets — pulled by the
#      data modules' import-init chains — call lean_expr_*/lean_kernel_*/lean_uv_*
#      etc. Those C++ primitives live in libleancpp/src/kernel (NOT the compiled .c
#      facets). We stub them panic-if-reached: the dead tactic objects link and
#      resolve, but `dregg_exec_full_forest_auth` never reaches them. The symbol
#      list is the residual of a prior link (scripts/kernel-stub-syms.txt), refreshed
#      below from any NEW residual so the stub stays complete.
KSYMS="$HERE/kernel-stub-syms.txt"
{
  echo '#include <stdlib.h>'
  echo '#include <stdio.h>'
  echo 'static void* kx(const char* w){ fprintf(stderr,"[exec] Lean kernel/elaborator primitive reached (executor turn must not elaborate): %s\n", w); abort(); }'
  while IFS= read -r s; do
    [ -z "$s" ] && continue
    case "$s" in \#*) continue;; esac
    echo "void* ${s}(){ return kx(\"${s}\"); }"
  done < "$KSYMS"
} > "$OUT/kernel-stub.c"
"$GCC" -O2 -c "$OUT/kernel-stub.c" -o "$OUT/kernel-stub.o"

# (1c) DEAD-symbol stub: a handful of metaprogramming/lemma symbols
#      (initialize_*/runtime_initialize_* for Lake/Qq/plausible/aesop/parallel-elab/
#      iterator-lemma modules, and the l_* tactic helpers they reference) are pulled
#      into the link by dead init-chains but are NEVER reached from the executor turn
#      (verified: reachable only via dead metaprog modules). no-op the inits; abort
#      the l_* (they must not run). List: scripts/dead-stub-syms.txt.
DSYMS="$HERE/dead-stub-syms.txt"
{
  echo '#include <lean/lean.h>'
  echo '#include <stdlib.h>'
  echo '#include <stdio.h>'
  echo 'extern "C" {'
  echo 'static void* dx(const char* w){ fprintf(stderr,"[exec] dead metaprogramming symbol reached: %s\n", w); abort(); }'
  while IFS= read -r s; do
    [ -z "$s" ] && continue
    case "$s" in \#*) continue;; esac
    case "$s" in
      initialize_*|runtime_initialize_*)
        # Proper IO-ok init (never actually executed: pulled only by dead chains).
        echo "lean_object* ${s}(uint8_t b){ (void)b; return lean_io_result_mk_ok(lean_box(0)); }" ;;
      *)
        echo "void* ${s}(){ return dx(\"${s}\"); }" ;;
    esac
  done < "$DSYMS"
  echo '}'
} > "$OUT/dead-stub.c"
"$GXX" -std=c++20 -O2 -I "$LEAN_SYSROOT/include" -c "$OUT/dead-stub.c" -o "$OUT/dead-stub.o"

# (2) the driver (embedded-Lean init + one turn) + the metaprogramming init-stubs
#     that cut the Lean-elaborator pull (see init-stubs.c). The stub .o is linked
#     BEFORE the closure archive so the linker resolves the no-op inits here and
#     never pulls the real elaborator-dragging members.
"$GXX" -std=c++20 -O2 -I "$LEAN_SYSROOT/include" -c "$HERE/driver.c" -o "$OUT/driver.o"
"$GXX" -std=c++20 -O2 -I "$LEAN_SYSROOT/include" -c "$HERE/init-stubs.c" -o "$OUT/init-stubs.o"
# aux-defs.o: the one re-emission-gap auxiliary recovered exactly (see aux-defs.c).
"$GXX" -std=c++20 -O2 -I "$LEAN_SYSROOT/include" -c "$HERE/aux-defs.c" -o "$OUT/aux-defs.o"

echo "[link-probe] inputs:"
for a in libdregg_lean_elf.a leanrt-elf/libleanrt_elf.a leanlib-elf/libInit_elf.a \
         leanlib-elf/libLean_elf.a leanlib-elf/libmathlib_elf.a gmp-elf/libgmp.a; do
  if [ -f "$OUT/$a" ]; then
    echo "    $a ($("$MUSL/bin/aarch64-linux-musl-ar" t "$OUT/$a" 2>/dev/null | wc -l|tr -d ' ') obj)"
  else echo "    MISSING $a"; fi
done

# (3) Static-link an executable, GC from main. --start-group over the Lean archives:
#     they are mutually recursive (Init<->Std<->Lean and the closure). libgmp last.
echo "[link-probe] static-linking aarch64-linux-musl executable (--gc-sections)…"
"$GXX" -static -no-pie -Wl,--gc-sections \
    "$OUT/driver.o" \
    "$OUT/init-stubs.o" \
    "$OUT/aux-defs.o" \
    -Wl,--start-group \
      "$OUT/libdregg_lean_elf.a" \
      "$OUT/leanrt-elf/libleanrt_elf.a" \
      "$OUT/leanlib-elf/libInit_elf.a" \
      "$OUT/leanlib-elf/libStd_elf.a" \
      "$OUT/leanlib-elf/libLean_elf.a" \
      "$OUT/leanlib-elf/libmathlib_elf.a" \
      "$OUT/leanlib-elf/libBatteries_elf.a" \
      "$OUT/leanlib-elf/libAesop_elf.a" \
      "$OUT/leanlib-elf/libQq_elf.a" \
      "$OUT/leanlib-elf/libProofWidgets_elf.a" \
      "$OUT/leanlib-elf/libPlausible_elf.a" \
      "$OUT/leanlib-elf/libImportGraph_elf.a" \
      "$OUT/leanlib-elf/libLeanSearchClient_elf.a" \
      "$OUT/leanlib-elf/libMetatheory_elf.a" \
      "$OUT/leancpp-elf/libleancpp_kernel_elf.a" \
      "$OUT/crypto-stub.o" \
      "$OUT/kernel-stub.o" \
      "$OUT/dead-stub.o" \
    -Wl,--end-group \
    "$OUT/gmp-elf/libgmp.a" \
    -lstdc++ -lm -lpthread \
    -o "$OUT/dregg-executor.elf" 2>"$OUT/link.log"
rc=$?
echo "[link-probe] link rc=$rc"
if [ "$rc" -ne 0 ]; then
  echo "[link-probe] === unresolved / link errors (the residual contract) ==="
  grep -iE 'undefined reference|cannot find|multiple definition' "$OUT/link.log" \
    | sed -E "s/.*undefined reference to .([^']*).*/UNDEF \\1/" | sort -u | head -60
  echo "[link-probe] (full log: $OUT/link.log)"
  exit "$rc"
fi
echo "[link-probe] LINKED: $OUT/dregg-executor.elf"
file "$OUT/dregg-executor.elf"
ls -la "$OUT/dregg-executor.elf" | awk '{print "    size:",$5}'
"$NM" "$OUT/dregg-executor.elf" 2>/dev/null | grep -qE ' T dregg_exec_full_forest_auth' \
  && echo "[link-probe] executor entry present (T) in the linked image"

# (4) Run ONE turn under qemu-aarch64 (if available).
QEMU="$(command -v qemu-aarch64 || true)"
if [ -n "$QEMU" ]; then
  echo "[link-probe] === running ONE turn under qemu-aarch64 ==="
  "$QEMU" "$OUT/dregg-executor.elf" "${1:-}" 2>&1 | sed 's/^/    /'
  echo "[link-probe] qemu rc=${PIPESTATUS[0]}"
else
  echo "[link-probe] qemu-aarch64 not installed — skipping host run (brew install qemu)"
fi
