# render-pd — the cockpit RE-FLOW PD (lavapipe-in-a-PD on seL4).
#
#   make gate        # the LLVM + Mesa-lavapipe cross-build gate (BANKED; both green)
#   make build       # cargo build the render-PD root task (links lavapipe + W->X handler)
#   make image       # assemble the bootable seL4 image
#   make run         # boot it headless in QEMU (serial to stdout)
#
# The render-PD links the lavapipe software-Vulkan ICD (Mesa+lavapipe+llvmpipe +
# static LLVM 20.1.8 JIT) + the gpui-offscreen render driver into a
# std-on-sel4-musl root task, with the JIT's W->X executable mapping serviced by
# the sel4-musl syscall handler (src/main.rs). See WIRING.md + README.md.

ROOT := $(shell pwd)
ER   := $(ROOT)/../dregg-pd/executor-rootserver
IMG  := $(ROOT)/out/dregg-render-pd.img

export SEL4_PREFIX        := $(ROOT)/sel4-prefix
export SEL4_INCLUDE_DIRS  := $(ROOT)/sel4-prefix/libsel4/include
export SEL4_CONFIG        := $(ROOT)/sel4-prefix/libsel4/include/kernel/gen_config.json
export SEL4_PLATFORM_INFO := $(ROOT)/sel4-prefix/support/platform_gen.yaml
export LIBCLANG_PATH      := /opt/homebrew/opt/llvm/lib
export CARGO_TARGET_DIR   := $(ROOT)/target-roottask
export MESA_SRC           ?= /tmp/mesa-src
export MESA_CROSS_BUILD   ?= /tmp/mesa-cross-musl
export LLVM_CROSS_BUILD   ?= /tmp/llvm-cross-musl

.PHONY: gate build image run clean

gate:
	bash scripts/build-gate.sh

build:
	cargo build --release

image: build
	bash scripts/build-image.sh

run: image
	qemu-system-aarch64 -machine virt,virtualization=on -cpu cortex-a53 -m 3072M \
	  -nographic -serial mon:stdio -kernel $(IMG)

clean:
	rm -rf target-roottask out/driver-render.o out/musl-compat.o $(IMG)
