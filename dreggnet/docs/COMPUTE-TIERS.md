# DreggNet Compute Tiers

DreggNet runs a (dregg-authorized) workload through an **owned, in-crate**
execution engine. `dreggnet-exec` (`exec/src/lib.rs`) is the seam that maps a
lease's **capability grade** to a **sandbox tier** to a concrete execution
engine, and refuses to run a workload whose cap-tier demands more isolation than
the selected engine can guarantee — never a silent downgrade.

Today exactly one tier has an owned engine linked: `Sandboxed` runs on a
pure-Rust `wasmi` interpreter that is vendored into the crate (zero unsafe, no
external submodule). Every stronger tier is an **honest, fail-closed seam** —
it refuses cleanly (`ExecError::NotWired` / `TierNotServed`) rather than pretend
to run or quietly downgrade. Wiring an owned engine for each stronger tier is
future work.

This document is the what-is: which tier for which trust level, what is real
versus a fail-closed seam, and the resource each tier needs.

## The cap-grade → tier → engine map

`CapTier` is ordered weakest → strongest isolation. Each grade routes to exactly
one engine; `dreggnet_exec::run_workload_with_input` does the routing.

| `CapTier`      | trust level / use                                  | lang(s)                   | engine                            | status |
|----------------|----------------------------------------------------|---------------------------|-----------------------------------|--------|
| `Sandboxed`    | trusted/bounded compute, cheapest real sandbox     | `wasm` / `wat` (core)     | owned `wasmi` interpreter (`WasmSandbox`) | **REAL** — genuinely executes |
| `JitSandboxed` | untrusted wasm needing a runaway bound             | `wasm` / `wat` (component)| (future) owned JIT engine         | fail-closed seam |
| `Caged`        | semi-trusted native code / polyglot agents         | `native`/`bin`, `python`/`py`, `node`/`js` | (future) owned native/python/node engines | fail-closed seam |
| `MicroVm`      | **untrusted** workloads, homelab's big boxes       | any (VM runs the runtime) | (future) owned microVM engine     | fail-closed seam |
| `Gpu`          | **heavy compute** — ML / inference / CUDA          | any (VM runs the runtime) | (future) owned GPU-passthrough VM engine | fail-closed seam |

The bridge maps grades to provider labels for records: `Sandboxed` →
`dreggnet-wasmi`, `Caged` → `dreggnet-native (seam)`, `MicroVm` →
`dreggnet-microvm (seam)`.

`enforcement` is the isolation grade the workload *actually* ran under, surfaced
in `Output::enforcement` — a downgrade is made LOUD, not silent. The owned
`wasmi` tier is identical on every platform.

### Why a stronger tier can't be silently substituted

`check_floor` refuses to run a tier on an engine whose enforcement is below the
tier's floor. The owned `wasmi` interpreter (`WasmSandbox`) does not clear the
`JitSandboxed` floor (`WasmFullSandbox`), so the JIT tier never downgrades to the
interpreter. The stronger tiers have no owned engine linked yet, so they refuse
cleanly (`ExecError::NotWired` / `TierNotServed`) — the seam is honest, never a
fake run.

## The tiers in detail

### `Sandboxed` — wasm (REAL, owned)

The owned, in-crate `wasmi` engine: a pure-Rust wasm interpreter (numeric args,
no fuel meter — for trusted/bounded compute), zero unsafe, no external submodule.
It runs on every platform, genuinely executes (the `add(40,2)=42` dogfood runs
here), and carries the unconditional default-green coverage. Enforcement is
reported as `WasmSandbox`.

### `JitSandboxed` — JIT wasm (SEAM)

The untrusted-wasm tier that needs a runaway bound (a fuel meter / component
model). No owned JIT engine is linked yet, so this tier is a fail-closed seam:
`run_workload` refuses cleanly rather than downgrade to the interpreter. Wiring
an owned JIT engine (with a fuel meter so a runaway component traps "out of fuel"
instead of hanging) is future work.

### `Caged` — native + OS cage (SEAM)

A host-process tier for semi-trusted native code and polyglot agents — a child
process under an OS syscall/filesystem cage (seccomp-bpf + Landlock on Linux).
Three langs would route here — `native`/`bin`, `python`/`py`, `node`/`js` — but
no owned engine is linked for any of them today, so each is a fail-closed seam
(`ExecError::NotWired`). The bridge records the `dreggnet-native (seam)` label.
Wiring owned native/python/node engines (threading the lease's cap bundle +
tenant into the cage) is future work.

### `MicroVm` — microVM (SEAM)

The strong-isolation tier for **untrusted** workloads and the homelab's
KVM-capable boxes: a per-workload microVM with its own guest kernel behind the
KVM boundary (the fly.io / AWS-Lambda model). No owned microVM engine is linked
yet, so this tier is a fail-closed seam: `run_workload` refuses cleanly and names
what is absent, never downgrading to a weaker tier. The bridge records the
`dreggnet-microvm (seam)` label.

A future owned microVM engine will need three host facilities:

1. a microVM launcher binary on `PATH`,
2. `/dev/kvm` — Linux + hardware virtualization, and
3. a guest kernel + rootfs image.

Wiring the owned engine (VM boot, in-guest agent over a vsock + newline-JSON
wire, direct vs jailed enforcement, capability gating inside the VM, and
per-call trace records) is future work.

### `Gpu` — GPU passthrough VM (SEAM)

The heavy-compute tier — ML / inference / CUDA. A hardware-isolated VM with a
**passed-through GPU** (a whole device via VFIO, or an NVIDIA MIG slice). The VM
boundary is mandatory (GPU passthrough is unsafe without it), so the floor is
`FullVm`. No owned engine is linked yet, so this tier is a fail-closed seam:
`run_workload` refuses cleanly, naming what is missing (no GPU device / no VMM
configured), never a silent downgrade to CPU-only.

The metering design is retained in `dreggnet_exec::gpu`:

- `GpuClass` — `Mig { compute_sevenths, memory_gib }` (MIG granularity is 1/7th of
  the physical GPU; profiles 1g.5gb / 2g.10gb / 3g.20gb / 7g.40gb) or
  `Whole { memory_gib }`. Fixes the guest VRAM ceiling + the metering rate.
- `GpuBounds` — `GpuClass` + a hard `max_gpu_seconds` budget.
- `GpuMeter` — accrues **GPU-seconds** scaled by the compute fraction, settling
  through the same conserving exactly-once `$DREGG` rail.

Wiring the owned passthrough-VM engine (a passthrough-capable VMM binding the GPU
into the guest) is future work.

## Resource needs at a glance

| tier         | needs                                                            |
|--------------|-----------------------------------------------------------------|
| `Sandboxed`  | nothing host-side (owned pure-Rust interpreter)                |
| `JitSandboxed` | an owned JIT engine (future work)                             |
| `Caged`      | an owned native/python/node engine + (Linux) the seccomp + Landlock cage (future work) |
| `MicroVm`    | an owned microVM engine + a launcher binary + `/dev/kvm` + a guest kernel/rootfs image (future work) |
| `Gpu`        | an owned passthrough-VM engine + a GPU bound to `vfio-pci` (or a MIG-partitioned card) on a fleet GPU node (future work) |

## Building

The default build wires the owned `wasmi` sandbox tier:

```
cargo test -p dreggnet-exec          # owned wasmi Sandboxed tier, default-green
```

The `Sandboxed` tier compiles and runs on every platform. Every stronger tier is
a fail-closed seam today: `run_workload` compiles to an honest "not wired" bail
(`ExecError::NotWired` / `TierNotServed`) rather than a fake run or a silent
downgrade. Wiring an owned engine for each stronger tier is future work.
