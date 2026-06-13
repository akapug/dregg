#!/usr/bin/env bash
# build-gmp-elf.sh — cross-compile GMP 6.3.0 static for aarch64-linux-musl, the
# bignum dependency of leanrt's mpz.cpp. The musl GCC cross-toolchain bundles GMP
# internally but exposes no libgmp.a to user links, so we build our own.
# Output: out/gmp-elf/libgmp.a
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OUT="${1:-$HERE/../out/gmp-elf}"
MUSL=/opt/homebrew/opt/aarch64-unknown-linux-musl
WORK=/tmp/gmp-build
mkdir -p "$WORK" "$OUT"
cd "$WORK"
if [ ! -f gmp.tar.xz ]; then
  curl -sSL -o gmp.tar.xz https://gmplib.org/download/gmp/gmp-6.3.0.tar.xz \
    || curl -sSL -o gmp.tar.xz https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz
fi
[ -d gmp-6.3.0 ] || tar xf gmp.tar.xz
cd gmp-6.3.0
make distclean >/dev/null 2>&1 || true
# -std=gnu17: GMP 6.3.0 predates C23; GCC 15 defaults to C23 and rejects GMP's
# implicit-declaration configure probes. --build set to the darwin host so configure
# knows it is cross-compiling (won't try to RUN aarch64 test binaries).
env -i PATH="$MUSL/bin:/usr/bin:/bin" \
  CC=aarch64-linux-musl-gcc AR=aarch64-linux-musl-ar RANLIB=aarch64-linux-musl-ranlib \
  CFLAGS="-O2 -std=gnu17" \
  ./configure --host=aarch64-linux-musl --build="$(./config.guess)" \
    --disable-shared --enable-static --disable-cxx --prefix="$WORK/install"
env -i PATH="$MUSL/bin:/usr/bin:/bin" make -j8
env -i PATH="$MUSL/bin:/usr/bin:/bin" make install
cp "$WORK/install/lib/libgmp.a" "$OUT/libgmp.a"
cp "$WORK/install/include/gmp.h" "$OUT/gmp.h"
echo "[gmp-elf] wrote $OUT/libgmp.a"; file "$OUT/libgmp.a"
