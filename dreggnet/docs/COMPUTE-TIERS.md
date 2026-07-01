# DreggNet Compute Tiers

DreggNet runs a (dregg-authorized) workload through [polyana](../polyana)'s real
polyglot execution engine. `dreggnet-exec` (`exec/src/lib.rs`) is the seam that
maps a lease's **capability grade** to a **sandbox tier** to a concrete polyana
`ExecutionProvider`, and refuses to run a workload whose cap-tier demands more
isolation than the selected provider can guarantee — never a silent downgrade.

This document is the what-is: which tier for which trust level, what is real
versus hardware-gated, and the resource each tier needs.

## The cap-grade → tier → provider map

`CapTier` is ordered weakest → strongest isolation. Each grade routes to exactly
one provider family; `dreggnet_exec::run_workload_with_input` does the routing.

| `CapTier`      | trust level / use                                  | lang(s)                   | provider                          | enforcement (Linux / macOS)        | feature        |
|----------------|----------------------------------------------------|---------------------------|-----------------------------------|------------------------------------|----------------|
| `Sandboxed`    | trusted/bounded compute, cheapest real sandbox     | `wasm` / `wat` (core)     | `polyana-wasmi-provider`          | `WasmSandbox` (both)               | `polyana`      |
| `JitSandboxed` | untrusted wasm needing a runaway bound             | `wasm` / `wat` (component)| `polyana-wasmtime`                | `WasmFullSandbox` (both)           | `polyana`      |
| `Caged`        | semi-trusted native code / polyglot agents         | `native`/`bin`, `python`/`py`, `node`/`js` | `polyana-native-process-provider`, `polyana-python-provider`, `polyana-node-provider` | `OsSandbox` / `None` | `caged`, `python`, `node` |
| `MicroVm`      | **untrusted** workloads, homelab's big boxes       | any (VM runs the runtime) | `polyana-firecracker-provider`    | `Container` (direct) / `FullVm` (jailed) / refuses | `firecracker`  |
| `Gpu`          | **heavy compute** — ML / inference / CUDA          | any (VM runs the runtime) | GPU-passthrough VM seam (VFIO / MIG) | `FullVm` / refuses              | `polyana`      |

`enforcement` is the isolation grade the workload *actually* ran under, as
reported by the provider, and is surfaced in `Output::enforcement` — a downgrade
is made LOUD, not silent. On macOS the OS cage (seccomp + Landlock) does not
exist, so the native tiers report `None` (process isolation only); the wasm
tiers are identical on every platform.

### Why a stronger provider can't be silently substituted

`check_floor` refuses to run a tier on a provider whose enforcement is below the
tier's floor. The wasm interpreter (`WasmSandbox`) does not clear the
`JitSandboxed` floor (`WasmFullSandbox`), so the JIT tier never downgrades to the
interpreter. The native tiers are kept distinct by provider *identity* + lang
routing (a wasm provider is never constructed for a `native`/`python`/`node`
workload, and vice-versa).

## The tiers in detail

### `Sandboxed` / `JitSandboxed` — wasm (REAL)

Two in-process wasm backends. `wasmi` is a pure interpreter (numeric args only,
no fuel meter — for trusted/bounded compute). `wasmtime` is Cranelift JIT + a
fuel meter + WASI Preview 2 (numeric + string args; a runaway component traps
"out of fuel" instead of hanging). Both run on every platform and carry the
unconditional default-green coverage.

### `Caged` — native + seccomp (REAL)

A real host process run as a child under a seccomp-bpf syscall allowlist + a
Landlock filesystem allowlist (Linux), speaking polyana's newline-JSON wire
(`{"fn":"run","args":[...]}` → `{"ok":[...]}` / `{"err":"..."}`). Three providers
serve this grade:

- **`native`/`bin`** — `polyana-native-process-provider`: an arbitrary host
  binary (ELF / shebang script). Off by default (`caged` feature) because the
  cage only *engages* on Linux. As of this pass it threads the lease's cap
  bundle + tenant into the cage via `instantiate_with_caps` (network syscalls
  are denied without a Network cap; filesystem caps become Landlock paths;
  `POLYANA_TENANT` / `POLYANA_CAPS_JSON` reach the guest).
- **`python`/`py`** — `polyana-python-provider`: a genuine `python3`
  subprocess (NOT a wasm CPython port). Default-on (`python`).
- **`node`/`js`** — `polyana-node-provider`: a genuine `node` subprocess (NOT
  the in-process V8 isolate pool, which SIGSEGVs on the second isolate).
  Default-on (`node`). Real JSON args reach the handler; a runaway guest is
  killed at the wall-clock deadline (`ExecError::Timeout`); a syntax error fails
  cleanly. Cap bundle + tenant are threaded exactly like the Python tier.

All three report `OsSandbox` on Linux and `None` on macOS, where the live
end-to-end run is proven (the cage is exercised by the providers' own
Linux-gated tests + the differential against the Lean spec).

### `MicroVm` — Firecracker (REAL; live boot proven, direct + jailed)

The strong-isolation tier for **untrusted** workloads and the homelab's
KVM-capable boxes: a per-workload Firecracker microVM with its own guest kernel
behind the KVM boundary (the fly.io / AWS-Lambda model). Routed for every lang —
the VM runs the language runtime inside, reached over a **vsock + newline-JSON
wire**: `run_on_microvm` ships a `{"lang","source","fn","args"}` request line to
a tiny in-guest agent, which runs the real runtime and replies `{"ok":[...]}` /
`{"err":"..."}`. Wired behind the default-on `firecracker` feature.

The live VM boot needs three host facilities:

1. the `firecracker` binary on `PATH`,
2. `/dev/kvm` — Linux + hardware virtualization (the homelab / node-a boxes
   have it; an edge `t3` without nested virt does NOT — check before relying on
   it), and
3. a guest kernel + rootfs image (built by the provider's `image/build-image.sh`).

`run_on_microvm` checks (1) and (2) up front and **refuses cleanly** when either
is missing, naming what's absent — it never downgrades to a weaker tier. Where
the hardware is present it constructs the provider, loads the workload, boots the
VM, runs the guest, and tears it down.

**Direct vs jailed (`Container` vs `FullVm`).** By default firecracker is spawned
directly (the dev / CI posture) and the run reports `EnforcementLevel::Container`.
Setting `DREGGNET_FC_JAILER` routes every VM through the firecracker **jailer**
(a cgroup, fresh namespaces, a `chroot` into a private jail root, and a privilege
drop to an unprivileged uid/gid before exec'ing firecracker — the production
posture); the run then reports the stronger `EnforcementLevel::FullVm`. The jailer
requires the launching process to start as root (its precondition for building
the cgroup/namespaces/chroot) and drops privilege after. `--cgroup-version 2` is
passed so it works on modern cgroup-v2-only hosts.

**Proven live (node-a, Firecracker v1.10.1, cgroup v2).** A real CPython
workload boots inside a **jailed** microVM, returns `42` over vsock at `FullVm`,
and is torn down — `~0.8–1.1 s` end to end, repeatably (the provider clears any
stale jail before launch and removes the jail tree on drop, so consecutive runs
don't collide). Tests: `polyana-firecracker-provider`'s `jailed_microvm_boot`
integration test (provider level) and `dreggnet-exec`'s
`tests/microvm_kvm.rs::microvm_runs_real_cpython{,_jailed}` (full stack). Both are
`#[ignore]`d and self-skip off a KVM host, so the default suite stays green
everywhere; the live proof runs on node-a.

The remaining production work is capability gating inside the VM (the
`Capability` → tap/MMDS/drive/vsock-port translation) and per-call trace records.

### `Gpu` — GPU passthrough VM (DESIGN + SEAM; live boot hardware-gated)

The heavy-compute tier — ML / inference / CUDA — the one axis the Liftoff matrix
flagged Akash ahead on. A hardware-isolated VM with a **passed-through GPU**:
either a whole device via **VFIO**, or an **NVIDIA MIG** slice (an A100/H100
partitioned into isolated GPU instances). The VM boundary is mandatory (GPU
passthrough is unsafe without it), so the floor is `FullVm`.

**Not Firecracker.** Firecracker is deliberately CPU-only — no PCI passthrough —
so the Gpu tier routes to a separate passthrough-VM provider seam: a
passthrough-capable VMM (Cloud-Hypervisor / QEMU) that binds the GPU into the
guest. `run_on_gpu` gates and refuses cleanly, naming what's missing: no GPU
device on the host → names the missing hardware; a GPU but no `DREGGNET_GPU_VMM`
configured → names the missing provider seam. Never a silent downgrade to
CPU-only.

**The cap-grade → GPU + metering** (the `dreggnet_exec::gpu` module):

- `GpuClass` — `Mig { compute_sevenths, memory_gib }` (MIG granularity is 1/7th of
  the physical GPU; the profiles are 1g.5gb / 2g.10gb / 3g.20gb / 7g.40gb) or
  `Whole { memory_gib }`. Fixes the guest VRAM ceiling + the metering rate.
- `GpuBounds` — `GpuClass` + a hard `max_gpu_seconds` budget (refuse a spent
  lease; tear down an overrun — the GPU analogue of the CPU wall-clock timeout).
- `GpuMeter` — accrues **GPU-seconds** scaled by the compute fraction (a 1g MIG
  slice bills 1/7th the GPU-seconds of a whole GPU for the same wall-clock),
  settling through the same conserving exactly-once `$DREGG` rail.

**Wired now:** the `CapTier::Gpu` variant, the routing + clean refusal, the host
GPU probe, the `FullVm` floor, and the `GpuClass` / `GpuBounds` / `GpuMeter` types
+ tests. **Hardware-gated remaining (reviewed-go fleet rung):** a discrete GPU
bound to `vfio-pci` (or a MIG-partitioned card) on a fleet GPU node, the
passthrough-VM provider implementation, and the bridge-rung settlement of
GPU-seconds. node-a carries only an integrated APU (no passthrough device), so
the live GPU boot is queued for real GPU hardware.

## Resource needs at a glance

| tier         | needs                                                            |
|--------------|-----------------------------------------------------------------|
| `Sandboxed`  | nothing host-side (pure interpreter)                            |
| `JitSandboxed` | nothing host-side (Cranelift builds + runs everywhere)       |
| `Caged`      | the interpreter binary (`python3` / `node`) on PATH; Linux for the seccomp + Landlock cage |
| `MicroVm`    | `firecracker` binary + `/dev/kvm` + a guest kernel/rootfs image (Linux + hardware virtualization); the jailed (`FullVm`) posture also needs root + the `jailer` binary |
| `Gpu`        | a GPU bound to `vfio-pci` (or a MIG-partitioned card) + a passthrough-VM VMM (`DREGGNET_GPU_VMM`) on a fleet GPU node |

## Building

The default build wires the wasm, Python, Node, and Firecracker tiers:

```
cargo test -p dreggnet-exec          # default = ["polyana","python","node","firecracker"]
cargo test -p dreggnet-exec --features caged   # add the native-binary Caged tier
```

The native-interpreter tiers (`python` / `node`) and the `firecracker` tier
compile on every platform; their default-on tests skip cleanly when the
interpreter (`python3` / `node`) is absent or when `/dev/kvm` + `firecracker`
are unavailable. Turning the `polyana` feature off
(`--no-default-features`) drops the whole engine and `run_workload` compiles to
an honest "not wired" bail.
