# BN254 Poseidon2 on AMD Vulkan: compiler-wall escape hatch

Status: **optimized and hardware-green on hbox, 2026-07-14**. The working path
compiles, runs, matches the gnark gold KAT and 65,536 pinned-Plonky3 reference
permutations bit-for-bit, and reaches **13.688 Mperm/s on stock RADV** and
**24.738 Mperm/s on AMDVLK** on the RX 6750 XT. These are 6.23x and 4.66x the
respective pre-optimization baselines.

The portable WGSL remains the WebGPU source of truth, but it is not a viable
native-Linux pipeline on this GPU: three unrelated AMD compiler stacks
SIGSEGV while lowering its emulated-64-bit Montgomery arithmetic. The native
Vulkan escape hatch is compact direct SPIR-V using the device's `shaderInt64`
feature. It retains wgpu for adapter, buffer, bind-group, command, and queue
management.

## Artifacts

- `bn254_poseidon2_hiperf.wgsl`: portable WebGPU kernel and parity contract;
  still the browser/Metal design, and the deliberate AMD crash repro.
- `bn254_poseidon2_int64.comp`: exact generated GLSL kernel that passed on
  hbox. Its 80 round constants are supplied in Montgomery form through binding
  2. SHA-256:
  `2c6c441806f8d9d7c7ed7ec459885b6bfbeb63378b0d7ba8eccf7f9a7bf5bba4`.
- `bn254-poseidon2-wgpu/src/direct_spirv.rs`: authoritative generator and
  compiler path. It derives Montgomery constants from the pinned canonical
  p3 constants, runs `glslangValidator`, `spirv-opt -O`, and `spirv-val`, and
  supplies the resulting SPIR-V to wgpu without Naga translation.
- `bn254-poseidon2-wgpu/src/main.rs`: CPU/KAT/parity/performance harness. On
  Linux it defaults to direct SPIR-V. Set `DREGG_BN254_FORCE_WGSL=1` only to
  reproduce the compiler crash.

No change was made to `circuit-prove/src/gpu_backend.rs`.

## hbox ground truth

Hardware and OS:

```text
Ubuntu 24.10 (oracular), kernel 6.11.0-8-generic
AMD Radeon RX 6750 XT, Navi 22, PCI 1002:73df, XFX subsystem 1eae:6710
amdgpu kernel driver
```

The stock userspace was Mesa/RADV 24.2.8 with LLVM 19.1.1. The first field-KAT
pipeline died before dispatch:

```text
CPU oracle: pinned p3 Poseidon2Bn254<3> == gnark gold KAT OK
adapter: AMD Radeon RX 6750 XT (RADV NAVI22) (Vulkan)
Segmentation fault; exit 139 at create_compute_pipeline
```

Captured hbox log: `/tmp/bn254-radv-baseline-20260714.log`.

## Pre-optimization driver matrix

| Driver/compiler | Installation | Portable WGSL | Direct SPIR-V int64 | Best rate |
| --- | --- | --- | --- | ---: |
| Mesa/RADV 24.2.8 (stock) | Ubuntu package | SIGSEGV, exit 139 | KAT + parity green | 2.198 Mperm/s |
| AMDVLK 2025.Q2.1 / LLPC | official AMD `.deb` | SIGSEGV, exit 139 | KAT + parity green | **5.314 Mperm/s** |
| Mesa/RADV 26.1.4 / ACO | local source build, LLVM disabled | SIGSEGV, exit 139 | KAT + parity green | 2.326 Mperm/s |

The pre-existing investigation also reproduced the WGSL crash on stock RADV's
LLVM backend; de-unrolling the WGSL did not change it. This run independently
reproduced stock ACO, the newest stable ACO, and AMD's LLPC failure.

## Optimization result

The comparison uses the task's established best baselines and the best of two
clean final runs. Each final run independently executed the complete parity
gate before timing. The repeated best-result ranges were 13.683--13.688
Mperm/s on RADV and 24.644--24.738 Mperm/s on AMDVLK.

| Driver | Before | After | Improvement | Final best WG |
| --- | ---: | ---: | ---: | ---: |
| stock Mesa/RADV 24.2.8 | 2.198 Mperm/s | **13.688 Mperm/s** | **+522.7% (6.23x)** | 128 |
| AMDVLK 2025.Q2.1 / LLPC | 5.314 Mperm/s | **24.738 Mperm/s** | **+365.5% (4.66x)** | 32 |

The profiling-driven ablation makes the two independent bottlenecks visible
(representative best rates in Mperm/s):

| Variant | RADV | AMDVLK |
| --- | ---: | ---: |
| reproduced 17-limb SOS baseline | 2.192 | 5.299 |
| round constants in SSBO, SOS unchanged | 5.377 | 5.312 |
| 10-limb CIOS, limb loops retained | 6.405 | 6.107 |
| CIOS inner loop unrolled | 11.951 | 20.801 |
| CIOS outer + inner loops unrolled (final) | **13.688** | **24.738** |

Workgroup size is not a sensitive parameter after the instruction-level fix.
The 32/64/128/256 sweep was effectively flat on both drivers (about 13.7
Mperm/s on RADV and 24.6 Mperm/s on AMDVLK), so the saved kernel uses 128 as a
robust cross-driver default rather than baking in the noisy single-run winner.

### Micro changes

1. Replaced the 17-limb schoolbook-product-plus-SOS reducer with a 10-limb
   coarsely integrated operand-scanning (CIOS) Montgomery multiplier. Each
   product row is immediately followed by its reduction row, shortening live
   ranges and eliminating the variable carry-propagation loop.
2. Fully unrolled both eight-limb CIOS loops. This exposes the native 64-bit
   multiply/high-half and carry schedule to ACO and LLPC. The x^5 S-box remains
   the minimum three Montgomery products (`x^2`, `x^4`, `x^5`).
3. Unrolled the four initial and four terminal external rounds while retaining
   the 56-round partial-round loop. The external and sparse internal matrices
   remain add-only: one shared state sum, with the internal third diagonal
   realized by one extra doubling.
4. Removed the impossible carry-out branch from canonical field addition:
   because `P < 2^254`, two reduced inputs cannot overflow 256 bits. The
   canonical `>= P` subtraction remains.
5. Kept the entire permutation in Montgomery form. Only the three input lanes
   and three output lanes cross representations; round constants are already
   Montgomery encoded.

A branchless final reduction and embedding the dynamically indexed constants
back into the shader were also measured. Both caused compiler/code-size or
register-pressure regressions and were rejected.

### Macro changes

1. Moved the 640 round-constant words from a dynamically indexed GLSL constant
   array to a 2.5 KiB read-only storage buffer. It is uploaded once per
   pipeline/batch and reused across the warmup and repeated timed dispatches.
2. Added explicit binding 2 and retained contiguous 96-byte states, one
   permutation per invocation, and one input/output transaction per state.
   Performance timing keeps buffers device-resident and does not read back
   between warmup and measured dispatches.
3. Swept 32, 64, 128, and 256 threads per workgroup on both drivers. The flat
   curve shows neither workgroup scheduling nor memory coalescing is the
   limiter; 128 is the portable saved setting.
4. Added a profile-only long-submit mode (`DREGG_BN254_PROFILE_ONLY=1`, with
   `DREGG_BN254_PROFILE_WG`, `_N`, and `_REPEATS`) so external counters can
   sample a stable compute workload without KAT/compile noise.

The standalone artifact is a permutation primitive rather than the MMCS tree
orchestrator. A production tree should batch a level per dispatch and retain
intermediate levels on-device; that integration belongs in the GPU backend,
which was deliberately not edited during this optimization pass.

### Bottleneck evidence

The original RADV shader statistics showed **256 VGPRs and 1,920 bytes of
scratch per invocation** at WG=256. Dynamic access to the embedded constant
array had been materialized as thread-private scratch. Binding 2 reduced the
permutation shader to **80 VGPRs, zero scratch, and 12 resident subgroups per
SIMD**.

For a six-second long-submit sample, `radeontop` reported 100% GPU and 100%
SPI/shader-processor utilization while the memory clock stayed at its 96 MHz
idle state (8.54% of maximum); texture/address activity was only about 12.5%.
The kernel is therefore ALU/issue-bound, not bandwidth- or launch-bound. The
final ACO ISA dump contains 17,552 each of `v_mul_hi_u32` and `v_mul_lo_u32`,
40,812 carry adds, and no scratch loads/stores. ACO still emits separate high
and low multiplies, whereas LLPC's stronger scheduling/lowering explains much
of AMDVLK's remaining lead.

Radeon Developer Tool Suite/RGP 2.7, `radeontop`, and the Mesa SQTT path were
installed on hbox. Mesa's SQTT per-submit layer does not intercept the legacy
`vkQueueSubmit` used by this wgpu version, and RDP classified the mixed Intel +
AMD DRM host as unsupported for capture; shader resource statistics, ISA, and
the live hardware counters above provided the actionable profile.

### AMDVLK installation

The installed package is AMD's last upstream release (the project is now
discontinued, but Navi 22 and Ubuntu 24.04 are in its published support set):

```text
release: v-2025.Q2.1
asset:   amdvlk_2025.Q2.1_amd64.deb
sha256:  4845bb0a3bada8cc1b850e6e004be17b0f55250e87b686eda3b8e2da60a039fb
package: amdvlk:amd64 2025.Q2.1
ICD:     /etc/vulkan/icd.d/amd_icd64.json
driver:  AMD open-source driver 2025.Q2.1 (LLPC), Vulkan 1.4.313
```

Install/reproduce:

```sh
curl -fLO https://github.com/GPUOpen-Drivers/AMDVLK/releases/download/v-2025.Q2.1/amdvlk_2025.Q2.1_amd64.deb
sha256sum amdvlk_2025.Q2.1_amd64.deb
sudo dpkg -i amdvlk_2025.Q2.1_amd64.deb
sudo apt-get -f install
```

RADV remains installed. Select deterministically rather than relying on ICD
enumeration:

```sh
export VK_ICD_FILENAMES=/etc/vulkan/icd.d/amd_icd64.json
export DISABLE_LAYER_AMD_SWITCHABLE_GRAPHICS_1=1
```

### Mesa 26.1.4 build

This was installed under the user's driver lab; it did not replace system
Mesa:

```text
tarball: https://archive.mesa3d.org/mesa-26.1.4.tar.xz
sha256:  072705caa9adf4740f1489194b13e278ad959166863b5271fe423a86353c9ab6
prefix:  ~/dregg-build/driver-lab/mesa-26.1.4-install
ICD:     ~/dregg-build/driver-lab/mesa-26.1.4-install/share/vulkan/icd.d/radeon_icd.x86_64.json
```

Build configuration:

```sh
meson setup mesa-26.1.4/build-radv mesa-26.1.4 \
  --prefix="$HOME/dregg-build/driver-lab/mesa-26.1.4-install" \
  --buildtype=release \
  -Dgallium-drivers=[] -Dvulkan-drivers=amd \
  -Dllvm=disabled -Dshared-llvm=disabled \
  -Dglx=disabled -Degl=disabled -Dgbm=disabled \
  -Dopengl=false -Dgles1=disabled -Dgles2=disabled \
  -Dvideo-codecs=[] -Dvalgrind=disabled \
  -Dlibunwind=disabled -Dlmsensors=disabled
ninja -C mesa-26.1.4/build-radv -j"$(nproc)"
ninja -C mesa-26.1.4/build-radv install
```

Installed build/runtime utilities included `glslang-tools`, `spirv-tools`,
`vulkan-tools`, Meson/Ninja, the libdrm/udev/ELF headers, and X11/Wayland WSI
headers. Mesa 26.1.4 used its wayland-protocols 1.41 subproject because Ubuntu
24.10 supplies 1.36.

## The fix

WGSL has no `u64`. Its `mul64` expands a single 32x32 product to four 16-bit
products plus explicit carries. A Poseidon2 permutation performs 240 BN254
Montgomery products, and the AMD pipeline compilers expand/lower enough of the
resulting IR to crash. Looped versus host-unrolled rounds did not remove that
lowering volume.

The Vulkan path requests:

```text
wgpu::Features::SHADER_INT64 | wgpu::Features::SPIRV_SHADER_PASSTHROUGH
```

Its Montgomery multiplier keeps 10 **u32 limbs** and uses `uint64_t` only for
the exact multiply-accumulate temporary:

```text
uv = limb + uint64(a_i) * uint64(b_j) + carry
```

The maximum is exactly `2^64-1`, so no wider temporary is needed. The shader
uses a fully unrolled CIOS product/reduction; the optimized permutation module
is 344,708 bytes after `spirv-opt -O`. The larger static module buys a much
shorter dynamic schedule and zero scratch. `spirv-val --target-env vulkan1.2`
passes before wgpu sees it.

Important integration trap: raw SPIR-V bypasses Naga reflection. Therefore
`ComputePipelineDescriptor { layout: None }` creates an empty layout and can
crash RADV in `load_buffer_descriptor`. The harness explicitly declares set 0:

| Binding | Vulkan/wgpu type | Purpose |
| --- | --- | --- |
| 0 | read-only storage buffer | canonical input states |
| 1 | read-write storage buffer | canonical output states |
| 2 | read-only storage buffer | Montgomery round constants |

Inputs and outputs are three canonical BN254 values, eight little-endian u32
limbs each. The shader converts inputs with `R^2`, keeps the state and binding-2
constants in Montgomery form for all 64 rounds, then converts outputs with
canonical one.

## Hardware gate and evidence

Run the winning configuration:

```sh
ssh hboxip
cd ~/dregg-build/codex-bn254-harness
export VK_ICD_FILENAMES=/etc/vulkan/icd.d/amd_icd64.json
export DISABLE_LAYER_AMD_SWITCHABLE_GRAPHICS_1=1
cargo run --release
```

For stock RADV, use the same command with:

```sh
export VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/radeon_icd.x86_64.json
unset DISABLE_LAYER_AMD_SWITCHABLE_GRAPHICS_1
cargo run --release
```

Final AMDVLK result using the exact documented command (full logs:
`/tmp/bn254-opt-final-amdvlk-run{1,2}-20260714.log`):

```text
shader path: direct SPIR-V + Vulkan shaderInt64
adapter: AMD Radeon RX 6750 XT (Vulkan)
field KAT: 1024 mul+add pairs bit-exact vs num-bigint OK
GPU gold KAT: permute([0,1,2]) == bn254KATOutHex OK
perm parity: 65536 permutations bit-exact vs pinned p3 Poseidon2Bn254<3> OK
GPU best: 24.738 Mperm/s (wg=32, batch 1048576)
process exit: 0
```

The best AMDVLK dispatch processed 1,048,576 permutations in 42.4 ms. Relative
to the measured 0.17-0.19 Mperm/s twelve-core outer-MMCS CPU stack, this is
about 137x; relative to the conservative 0.13 Mperm/s figure, 190x. With BN254
hashing at roughly 60% of the 95-second shrink, the measured Amdahl projection
is 2.47x end-to-end (2.5x hash-free ceiling).

Final cross-driver green logs:

```text
/tmp/bn254-opt-final-radv-run1-20260714.log    13.683 Mperm/s, exit 0
/tmp/bn254-opt-final-radv-run2-20260714.log    13.688 Mperm/s, exit 0
/tmp/bn254-opt-final-amdvlk-run1-20260714.log  24.644 Mperm/s, exit 0
/tmp/bn254-opt-final-amdvlk-run2-20260714.log  24.738 Mperm/s, exit 0
```

The saved `bn254_poseidon2_int64.comp` was also compiled independently with
`glslangValidator`, optimized, and validated. Its workgroup-128 binary SHA-256
is `53c6884f5e826da0bb3f17766a7db20a29183e98e14d64b55dd617867b167093`,
byte-for-byte identical to the generator's workgroup-128 output.

## Wiring notes

1. For native Linux/Vulkan, use the direct-SPIR-V pipeline in
   `bn254-poseidon2-wgpu`; do not send the emulated-u64 WGSL to RADV/LLPC.
2. Precompile the generated `.comp` at build/package time for production.
   Runtime `glslangValidator` is retained in the probe so every run regenerates
   the Montgomery constants and validates the exact module.
3. Preserve the explicit pipeline layout when moving this into an MMCS
   backend. Raw-SPIR-V auto-layout is not valid.
4. Batch independent width-three states exactly as the harness does. Leaf
   packing and tree-level orchestration stay separate; use this permutation
   primitive for the `MultiField32PaddingFreeSponge` leaves and
   `TruncatedPermutation` compression levels.
5. Keep the portable WGSL path for browser WebGPU and Metal. Browsers cannot
   accept raw SPIR-V or request native `shaderInt64`; that target still needs a
   split-dispatch/reduced-IR WGSL multiplier. This does not block the real AMD
   shrink prover, which is the gate closed here.

## Prior-art result

The successful approach matches the actual trick used by mature GPU crypto
libraries rather than their surface language:

- sppark's CUDA field code uses `mad.lo.cc.u32`/`madc.hi` chains, and its HIP
  code uses `v_mad_u64_u32`; it gives the compiler a native wide
  multiply-accumulate rather than thousands of 16-bit split operations.
- Mina's historical GPU prover uses CUDA `mul_hi` primitives. It does not
  solve a portable shader compiler's emulated-wide-integer IR problem.
- zkSecurity's Stwo WebGPU work targets the 31-bit M31/QM31 field. It is useful
  for dispatch/memory design, but it does not implement a 254-bit WGSL
  Montgomery multiplier.

The hbox solution applies the same native-wide-operation principle through a
standard Vulkan capability while keeping the rest of the wgpu backend.
