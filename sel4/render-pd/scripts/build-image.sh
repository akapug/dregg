#!/usr/bin/env bash
# build-image.sh — assemble the bootable render-PD seL4 image: the lavapipe
# software-Vulkan ICD (Mesa+lavapipe+llvmpipe + static LLVM 20.1.8 JIT) + the
# gpui-offscreen render path running INSIDE a seL4 root-task PD.
#
#   ./scripts/build-image.sh
#   qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 3072M \
#     -nographic -serial mon:stdio -kernel out/dregg-render-pd.img
#
# Prereqs (all reused from the executor-rootserver lane, which this clones):
#   * the gate artifacts: out/mesa-elf/libvulkan_lvp.so + the gate build trees
#     (/tmp/mesa-cross-musl, /tmp/llvm-cross-musl) holding the component .a's the
#     PD statically links — run scripts/build-llvm-elf.sh + build-mesa-lavapipe-elf.sh first;
#   * the provisioned seL4 substrate (out/musl-sel4, out/dummy-libunwind, sel4-prefix) —
#     symlinked from ../dregg-pd/executor-rootserver (already provisioned there), or
#     run that lane's scripts/provision-sel4.sh;
#   * the prebuilt loader + add-payload from ../dregg-pd/executor-rootserver/out.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$HERE/.."
OUT="$ROOT/out"
ER="$ROOT/../dregg-pd/executor-rootserver"          # the PD-class precedent we clone

# Reuse executor-rootserver's provisioned substrate if this lane lacks it.
mkdir -p "$OUT"
for d in musl-sel4 dummy-libunwind; do
  [ -e "$OUT/$d" ] || ln -s "$(cd "$ER/out/$d" && pwd)" "$OUT/$d"
done
[ -e "$ROOT/sel4-prefix" ] || ln -s "$(cd "$ER/sel4-prefix" && pwd)" "$ROOT/sel4-prefix"
PFX="$ROOT/sel4-prefix"

echo "== [1/3] cargo build the render-PD root task (links lavapipe + the W->X JIT handler) =="
( cd "$ROOT"
  export SEL4_PREFIX="$PFX" SEL4_INCLUDE_DIRS="$PFX/libsel4/include"
  export SEL4_CONFIG="$PFX/libsel4/include/kernel/gen_config.json"
  export SEL4_PLATFORM_INFO="$PFX/support/platform_gen.yaml"
  export LIBCLANG_PATH=/opt/homebrew/opt/llvm/lib
  export CARGO_TARGET_DIR="$ROOT/target-roottask"
  export MESA_SRC="${MESA_SRC:-/tmp/mesa-src}"
  export MESA_CROSS_BUILD="${MESA_CROSS_BUILD:-/tmp/mesa-cross-musl}"
  export LLVM_CROSS_BUILD="${LLVM_CROSS_BUILD:-/tmp/llvm-cross-musl}"
  cargo build --release
)
APP="$ROOT/target-roottask/aarch64-sel4-roottask-musl/release/dregg-render-pd.elf"

echo "== [2/3] reuse the seL4 kernel-loader + add-payload (executor-rootserver lane) =="
LOADER="$ER/out/sel4-kernel-loader.elf"
ADDPAYLOAD="$ER/out/loader-target/release/sel4-kernel-loader-add-payload"
[ -f "$LOADER" ] || { echo "ERROR: loader not built — run ../dregg-pd/executor-rootserver/scripts/build-loader.sh" >&2; exit 1; }

echo "== [3/3] assemble the bootable image =="
"$ADDPAYLOAD" --loader "$LOADER" --sel4-prefix "$PFX" --app "$APP" \
  --out-file "$OUT/dregg-render-pd.img"
echo "== DONE -> $OUT/dregg-render-pd.img =="
ls -la "$OUT/dregg-render-pd.img" | awk '{print "   size:", $5}'
echo "   boot: qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 \\"
echo "           -m 3072M -nographic -serial mon:stdio -kernel $OUT/dregg-render-pd.img"
