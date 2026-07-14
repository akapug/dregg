# BN254 Poseidon2 on AMD Vulkan: compiler-wall escape hatch

Status: **hardware-green on hbox, 2026-07-14**. The working path compiles,
runs, matches the gnark gold KAT and 65,536 pinned-Plonky3 reference
permutations bit-for-bit, and reaches **5.314 Mperm/s** on the RX 6750 XT.

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
  hbox. Its 80 round constants are already in Montgomery form. SHA-256:
  `66e53ad4be12089312ec3ec5c79d5daf1023e680741c8c9ab8a4e8419a84d23b`.
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

## Driver matrix tried

| Driver/compiler | Installation | Portable WGSL | Direct SPIR-V int64 | Best rate |
| --- | --- | --- | --- | ---: |
| Mesa/RADV 24.2.8 (stock) | Ubuntu package | SIGSEGV, exit 139 | KAT + parity green | 2.198 Mperm/s |
| AMDVLK 2025.Q2.1 / LLPC | official AMD `.deb` | SIGSEGV, exit 139 | KAT + parity green | **5.314 Mperm/s** |
| Mesa/RADV 26.1.4 / ACO | local source build, LLVM disabled | SIGSEGV, exit 139 | KAT + parity green | 2.326 Mperm/s |

The pre-existing investigation also reproduced the WGSL crash on stock RADV's
LLVM backend; de-unrolling the WGSL did not change it. This run independently
reproduced stock ACO, the newest stable ACO, and AMD's LLPC failure.

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

Its Montgomery multiplier keeps 17 **u32 limbs** and uses `uint64_t` only for
the exact multiply-accumulate temporary:

```text
uv = limb + uint64(a_i) * uint64(b_j) + carry
```

The maximum is exactly `2^64-1`, so no wider temporary is needed. The shader
uses a looped schoolbook product plus SOS Montgomery reduction; the full
optimized permutation module is 153,520 bytes. `spirv-val --target-env
vulkan1.2` passes before wgpu sees it.

Important integration trap: raw SPIR-V bypasses Naga reflection. Therefore
`ComputePipelineDescriptor { layout: None }` creates an empty layout and can
crash RADV in `load_buffer_descriptor`. The harness explicitly declares set 0:

| Binding | Vulkan/wgpu type | Purpose |
| --- | --- | --- |
| 0 | read-only storage buffer | canonical input states |
| 1 | read-write storage buffer | canonical output states |

Inputs and outputs are three canonical BN254 values, eight little-endian u32
limbs each. The shader converts inputs with `R^2`, keeps the state and RCs in
Montgomery form for all 64 rounds, then converts outputs with canonical one.

## Hardware gate and evidence

Run the winning configuration:

```sh
ssh hboxip
cd ~/dregg-build/codex-bn254-harness
export VK_ICD_FILENAMES=/etc/vulkan/icd.d/amd_icd64.json
export DISABLE_LAYER_AMD_SWITCHABLE_GRAPHICS_1=1
cargo run --release
```

Final AMDVLK result using the exact documented command (full log:
`/tmp/bn254-final-bare-amdvlk-20260714.log`):

```text
shader path: direct SPIR-V + Vulkan shaderInt64
adapter: AMD Radeon RX 6750 XT (Vulkan)
field KAT: 1024 mul+add pairs bit-exact vs num-bigint OK
GPU gold KAT: permute([0,1,2]) == bn254KATOutHex OK
perm parity: 65536 permutations bit-exact vs pinned p3 Poseidon2Bn254<3> OK
wg=64 best: 5.314 Mperm/s
process exit: 0
```

The best dispatch processed 1,048,576 permutations in 197.3 ms. Relative to
the measured 0.17-0.19 Mperm/s twelve-core outer-MMCS CPU stack, this is
29.5x; relative to the conservative 0.13 Mperm/s figure, 40.9x. With BN254
hashing at roughly 60% of the 95-second shrink, the measured Amdahl projection
is 2.38x end-to-end (2.5x hash-free ceiling).

Cross-driver green logs:

```text
/tmp/bn254-direct-full-mesa-24.2.8.log       2.198 Mperm/s, exit 0
/tmp/bn254-direct-full-mesa-26.1.4-attempt1.log 2.326 Mperm/s, exit 0
/tmp/bn254-direct-full-amdvlk-2025Q2.1.log   5.304 Mperm/s, exit 0
/tmp/bn254-final-bare-amdvlk-20260714.log     5.314 Mperm/s, exit 0
```

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
