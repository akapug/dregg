#!/usr/bin/env bash
#
# build-leanrt-elf.sh — build an ELF aarch64 Lean RUNTIME (the leanrt bottom-half)
# for the seL4 substrate, from the upstream lean4 sources at the toolchain commit.
#
# This is step (2) of the executor-PD excision plan (WALL.md): the toolchain ships
# leanrt/leancpp as Mach-O archives only, with NO C++ runtime sources, so the ELF
# application closure (libdregg_lean_elf.a, step 1) has no runtime to link against.
# We rebuild the runtime bottom-half from lean4@d024af099 for a HOSTED
# aarch64-linux-musl target (the substrate rust-sel4's sel4-musl emulates).
#
# Key decisions (see WALL.md):
#   * Target = aarch64-linux-musl (GCC cross), NOT bare freestanding: the Lean
#     runtime is hosted C++ (<vector>/<string>/<atomic>/exceptions) + needs malloc
#     + GMP. The musl cross toolchain supplies all three; sel4-musl emulates the
#     musl syscall surface in-PD. (`-ffreestanding` fails: no libstdc++.)
#   * libuv EXCISION (weld, not build): drop io.cpp + libuv.cpp + the 8 uv/*.cpp,
#     and patch init_module.cpp to not call initialize_io()/initialize_libuv().
#     The pure executor path (dregg_exec_full_forest_auth) touches no socket/file/
#     timer, so this is sound. (init_module's only undefined refs were exactly
#     `initialize_io` + `initialize_libuv` — `nm` confirmed.)
#   * mimalloc: the toolchain config.h forces LEAN_MIMALLOC and the closure
#     references mi_malloc_small (757x). Rather than rebuild the 757-obj closure,
#     we supply a 4-symbol mimalloc shim over musl malloc (mimalloc-shim.c).
#   * GMP: kept real (musl toolchain bundles it). 0 closure facets hit the bignum
#     path, but mpz.cpp provides the *_big_* fallback symbols the closure imports.
#
# Output: out/leanrt-elf/libleanrt_elf.a  (the ELF runtime bottom-half).
set -euo pipefail

LEAN_SYSROOT="${LEAN_SYSROOT:-$(lean --print-prefix)}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# Upstream lean4 runtime sources at the toolchain commit (fetched by the caller).
LEAN4_SRC="${LEAN4_SRC:-/tmp/lean4-rt}"
# The aarch64-linux-musl GCC cross toolchain (brew: aarch64-unknown-linux-musl).
MUSL_PREFIX="${MUSL_PREFIX:-/opt/homebrew/opt/aarch64-unknown-linux-musl}"
GXX="$MUSL_PREFIX/bin/aarch64-linux-musl-g++"
AR="$MUSL_PREFIX/bin/aarch64-linux-musl-ar"
GCC="$MUSL_PREFIX/bin/aarch64-linux-musl-gcc"
OUT_DIR="${1:-$HERE/../out/leanrt-elf}"

RT="$LEAN4_SRC/src/runtime"
if [ ! -f "$RT/object.cpp" ]; then
  echo "ERROR: lean4 runtime sources not at $RT" >&2
  echo "Fetch: git -C $LEAN4_SRC fetch --depth 1 origin d024af099ca4bf2c86f649261ebf59565dc8c622 && git checkout FETCH_HEAD" >&2
  exit 1
fi
if [ ! -x "$GXX" ]; then
  echo "ERROR: musl cross g++ not at $GXX (brew install aarch64-unknown-linux-musl)" >&2
  exit 1
fi

mkdir -p "$OUT_DIR/obj"
# githash.h is configure_file'd by cmake from githash.h.in; platform.cpp #includes
# it for LEAN_GITHASH. Generate it with the toolchain commit (this IS v4.30.0).
LEAN_COMMIT="d024af099ca4bf2c86f649261ebf59565dc8c622"
printf '// generated for the ELF leanrt build\n#define LEAN_GITHASH "%s"\n' "$LEAN_COMMIT" \
  > "$OUT_DIR/githash.h"
# Include order: repo src (for "runtime/*.h"), OUT_DIR (githash.h), toolchain
# include (the REAL generated lean/config.h + version.h + mimalloc.h matching the
# closure build), repo include.
INC=(-I "$LEAN4_SRC/src" -I "$OUT_DIR" -I "$LEAN_SYSROOT/include" -I "$LEAN4_SRC/src/include")
FLAGS=(-std=c++20 -O2 -DNDEBUG -DLEAN_EXPORTING -DLEAN_MULTI_THREAD -DLEAN_USE_GMP -fno-omit-frame-pointer)

echo "[leanrt-elf] GXX=$GXX"
echo "[leanrt-elf] target=$($GXX -dumpmachine)"

# EXCISE only the libuv socket/file/timer code: libuv.cpp + the 8 uv/*.cpp.
# We KEEP io.cpp: it is the IO-monad CORE (lean_st_ref_get, lean_io_result_show_error,
# lean_io_mark_end_initialization, g_initializing) — pure runtime, no libuv. It only
# REFERENCES 9 uv_fs_*/uv_os_* filesystem symbols, which the libuv-stub below resolves
# (panic-if-reached; the pure executor turn touches no filesystem). init_module keeps
# initialize_io() (needed) and drops only initialize_libuv().
EXCISE="libuv"   # plus uv/* handled by globbing only the top-level *.cpp below

ok=0; fail=0; failed=""
for f in "$RT"/*.cpp; do
  name="$(basename "$f" .cpp)"
  skip=0
  for e in $EXCISE; do [ "$name" = "$e" ] && skip=1; done
  [ "$skip" = 1 ] && { echo "[leanrt-elf] EXCISE $name.cpp"; continue; }

  # init_module.cpp: weld out ONLY the libuv initializer call (keep initialize_io).
  src="$f"
  if [ "$name" = "init_module" ]; then
    src="$OUT_DIR/init_module.patched.cpp"
    sed -e 's/^\( *\)initialize_libuv();/\1\/* EXCISED initialize_libuv(); *\//' \
        "$f" > "$src"
  fi

  if "$GXX" "${FLAGS[@]}" "${INC[@]}" -c "$src" -o "$OUT_DIR/obj/$name.o" 2>"$OUT_DIR/obj/$name.err"; then
    ok=$((ok+1)); rm -f "$OUT_DIR/obj/$name.err"
  else
    fail=$((fail+1)); failed="$failed $name"
  fi
done
echo "[leanrt-elf] runtime objects: OK=$ok FAIL=$fail"
if [ "$fail" -ne 0 ]; then
  echo "[leanrt-elf] FAILED:$failed" >&2
  f="$(echo "$failed" | awk '{print $1}')"
  echo "[leanrt-elf] first error ($f):" >&2
  head -20 "$OUT_DIR/obj/$f.err" >&2
  exit 1
fi

# mimalloc shim: the 4 symbols leanrt + the closure reference, over musl malloc.
cat > "$OUT_DIR/mimalloc-shim.c" <<'EOF'
/* mimalloc-shim.c — the 4 mi_* entry points the Lean runtime + the verified
 * closure import, redirected to musl malloc/free. The closure was compiled with
 * LEAN_MIMALLOC (toolchain default) and imports mi_malloc_small; leanrt's object
 * path imports mi_malloc/mi_free/mi_free_size. None of mimalloc's heap policy is
 * load-bearing for a single-turn executor — musl malloc suffices. */
#include <stddef.h>
extern void *malloc(size_t);
extern void free(void *);
void *mi_malloc(size_t n)              { return malloc(n); }
void *mi_malloc_small(size_t n)        { return malloc(n); }
void *mi_new_n(size_t c, size_t s)     { return malloc(c * s); }  /* C++ new[] path (sharecommon.cpp) */
void  mi_free(void *p)                 { free(p); }
void  mi_free_size(void *p, size_t sz) { (void)sz; free(p); }
EOF
"$GCC" -O2 -c "$OUT_DIR/mimalloc-shim.c" -o "$OUT_DIR/obj/mimalloc-shim.o"
echo "[leanrt-elf] mimalloc shim compiled (4 symbols over musl malloc)"

# libuv stub: the symbols io.cpp imports from the excised libuv objects. The pure
# executor turn touches no filesystem/socket/timer, so these are panic-if-reached.
# C linkage matches io.cpp's `uv_*` call sites (libuv is a C library); `initialize_libuv`
# and `lean_libuv_version` are in namespace lean (C++ mangling) — provided in C++.
cat > "$OUT_DIR/libuv-stub.cpp" <<'EOF'
/* libuv-stub.cpp — resolve the handful of libuv symbols the Lean IO-monad core
 * (io.cpp) imports, WITHOUT pulling libuv. None is reachable on the pure executor
 * turn (no fs/socket/timer); each aborts if ever called. This is the WALL.md
 * "libuv excision": keep the IO monad, drop the event loop. */
#include <cstdlib>
#include <cstdio>
extern "C" {
/* libuv C ABI — opaque args; never invoked on the executor path. */
__attribute__((noreturn)) static void uv_unreached(const char *w) {
    std::fprintf(stderr, "[leanrt-elf] libuv stub reached: %s (executor turn must not do IO)\n", w);
    std::abort();
}
int  uv_fs_stat(void*, void*, const char*, void*)            { uv_unreached("uv_fs_stat"); }
int  uv_fs_lstat(void*, void*, const char*, void*)           { uv_unreached("uv_fs_lstat"); }
int  uv_fs_link(void*, void*, const char*, const char*, void*){ uv_unreached("uv_fs_link"); }
int  uv_fs_unlink(void*, void*, const char*, void*)          { uv_unreached("uv_fs_unlink"); }
int  uv_fs_mkdtemp(void*, void*, const char*, void*)         { uv_unreached("uv_fs_mkdtemp"); }
int  uv_fs_mkstemp(void*, void*, const char*, void*)         { uv_unreached("uv_fs_mkstemp"); }
void uv_fs_req_cleanup(void*)                                { uv_unreached("uv_fs_req_cleanup"); }
int  uv_os_tmpdir(char*, size_t*)                            { uv_unreached("uv_os_tmpdir"); }
const char* uv_strerror(int)                                 { return "libuv-excised"; }
/* lean_setup_args lives in the excised libuv.cpp; io.cpp DEFINES lean_decode_uv_error
 * itself, so we must NOT redefine it here. */
char** lean_setup_args(int, char** argv)                     { return argv; }
}
namespace lean {
/* initialize_libuv is dropped from init_module; provide a no-op in case any other
 * TU references it. lean_libuv_version likewise. */
extern "C" void initialize_libuv() { /* no event loop on seL4 executor-PD */ }
extern "C" void* lean_libuv_version(void*)                   { uv_unreached("lean_libuv_version"); }
}
EOF
"$GXX" -std=c++20 -O2 -I "$LEAN4_SRC/src" -I "$OUT_DIR" -I "$LEAN_SYSROOT/include" -I "$LEAN4_SRC/src/include" \
  -fno-exceptions -c "$OUT_DIR/libuv-stub.cpp" -o "$OUT_DIR/obj/libuv-stub.o" 2>"$OUT_DIR/libuv-stub.err" \
  || { echo "[leanrt-elf] libuv-stub compile failed:" >&2; head -15 "$OUT_DIR/libuv-stub.err" >&2; exit 1; }
echo "[leanrt-elf] libuv stub compiled (fs/socket symbols, panic-if-reached)"

# GMP: mpz.cpp imports 39 __gmpz_* (the >63-bit bignum fallback). The musl GCC
# toolchain bundles GMP for its own use but exposes NO libgmp.a to link, so we
# cross-compile real GMP 6.3.0 for aarch64-musl separately (scripts/build-gmp-elf.sh)
# and link its libgmp.a at FINAL link time. We deliberately DO NOT ship a fixnum
# panic-shim here: an init-time Nat literal >63 bits (e.g. a hash constant) could
# call __gmpz_init_set_str during module init, and a silent-abort shim would mask
# that. Real GMP is the right default (WALL.md §8.2 "the safer of the two").

rm -f "$OUT_DIR/libleanrt_elf.a"
"$AR" rcs "$OUT_DIR/libleanrt_elf.a" "$OUT_DIR"/obj/*.o
echo "[leanrt-elf] wrote $OUT_DIR/libleanrt_elf.a"
file "$OUT_DIR/libleanrt_elf.a"
echo "[leanrt-elf] members: $("$AR" t "$OUT_DIR/libleanrt_elf.a" | wc -l | tr -d ' ')"
