# DreggNet ↔ polyana: the supported configuration

`dreggnet-exec` (`exec/src/lib.rs`) is the seam where a dregg-authorized workload
is handed to polyana's polyglot execution engine. polyana
(`polyana`, Apache-2.0, pinned at `../polyana`) is co-developed; this
document records which of its surfaces DreggNet *relies on* (solid, tested),
which it *steers around* (fragile), and the input/error/resource conventions
the wrapper enforces.

## What we drive

`run_workload(lang, source, cap_tier)` and
`run_workload_with_input(lang, source, cap_tier, &[Input])` route to a
`polyana_core::ExecutionProvider` by `lang` + `cap_tier`:

| `lang`           | `cap_tier`       | provider                          | enforcement (Linux / macOS)        | runs                          |
|------------------|------------------|-----------------------------------|------------------------------------|-------------------------------|
| `wasm` / `wat`   | `Sandboxed`      | `polyana-wasmi-provider`          | `WasmSandbox`                      | core wasm module (interpreter)|
| `wasm` / `wat`   | `JitSandboxed`   | `polyana-wasmtime`                | `WasmFullSandbox`                  | wasm component (Cranelift JIT)|
| `python` / `py`  | (any)            | `polyana-python-provider`         | `OsSandbox` / `None`               | **real CPython subprocess**   |
| `native` / `bin` | `Caged`          | `polyana-native-process-provider` | `OsSandbox` / *(refuses off-Linux)*| host binary / shebang script  |

`Output.enforcement` always reports the level the run *actually* achieved, so a
downgrade is loud, never silent.

## The supported-vs-fragile finding (per polyana's own tests/markers)

polyana's own design intent (python-provider docstring) is to **stop being "a
wasm-tax demo for non-wasm guest languages"** — native interpreters are the
real polyglot path, not wasm costumes. Status of the tiers we touch:

- **Native CPython (`polyana-python-provider`) — SOLID.** Spawns a real
  `python3` child, threads args as JSON over a newline-delimited stdin/stdout
  wire, and **overrides `instantiate_with_caps`** so tenant + caps (network /
  Landlock paths) reach the cage. seccomp-bpf + Landlock engage on Linux
  (`OsSandbox`); macOS runs process-isolated only (`None`, honestly reported).
  Default-on tests in `dreggnet-exec` drive it end-to-end.
  - Known gap (flagged for an operator): **runtime cap-mutation is unimplemented** —
    `respawn.rs` refuses a cap-change rather than lying about it. We do not rely
    on mid-run cap changes (a workload gets its caps at instantiate time).

- **wasmtime (`JitSandboxed`) — SOLID, and the resource-safe wasm tier.** Real
  Cranelift JIT, component model, **a fuel meter that bounds runaway code**
  (default 50M units even with an empty cap slice → "out of fuel" trap). Accepts
  numeric + string entrypoint args.

- **wasmi (`Sandboxed`) — SOLID but UNMETERED.** Pure-Rust interpreter, lowest
  cold start, numeric-only args, **no fuel meter** → a runaway core module loops
  in-process and a wall-clock timeout cannot interrupt it. Use it for trusted /
  bounded compute; route untrusted workloads to `JitSandboxed` or a native tier.

- **native-process (`Caged`) — SOLID on Linux, refuses elsewhere.** Real host
  binary under seccomp + Landlock. Linux-only sandbox; off-Linux `instantiate`
  errors cleanly (never an unsandboxed run).
  - Known gap (flagged for an operator): it does **not** override
    `instantiate_with_caps`, so tenant/caps env do not reach the host-binary
    guest the way they do for the Python provider. (We hardened the leak side —
    see below — but the cap-threading override is still owed.)

- **v8 / Node (`polyana-v8-provider`) — STEER AROUND for now.** Every test is
  `#[ignore]`d because v8-130 SIGSEGVs when a second `OwnedIsolate` is created in
  the same process, which breaks instance pooling. DreggNet does **not** wire the
  v8 tier yet; real Node should ride the native-process tier (a `node` binary
  speaking the wire) or wait for the isolate-reuse fix. Tracked for an operator.

- **graalvm-polyglot — NOT WIRED.** Mock-only in polyana (Slice 1, jar not
  built). Not used.

- **firecracker / MicroVm — NOT WIRED.** Declared, heavier native tree; refused
  cleanly rather than downgraded.

## Input convention (the real one — not templated-WAT)

Workloads receive **real argument values** via `Input` (`I32/I64/F32/F64/Text/
Json`), passed to the `run` entrypoint:

- wasmi: numeric args only (rejected-with-a-typed-error otherwise).
- wasmtime: numeric + string args.
- native CPython: every variant, delivered as the JSON `args` array of a
  `{"fn":"run","args":[...]}` request — so a workload gets real strings / JSON
  bodies, not integer-only query params.

The legacy webapp `/add` handler still uses integer-validated template
substitution into WAT; that path is safe (integers only) but is the *narrow*
convention. New code should pass `Input` values through `run_workload_with_input`
(the durable `WorkloadSpec` does not yet carry args — threading them through the
durable layer is the next rung, owned alongside `durable/`).

## Error + resource conventions the wrapper enforces

- **Typed errors.** `run_workload_with_input` returns `Result<Output, ExecError>`
  — every polyana failure is a clean category (`Assembly`, `ProviderInit`,
  `Load`, `Instantiate`, `Call`, `FloorUnmet`, `UnsupportedArg`,
  `TierNotServed`, `UnsupportedLang`, `Timeout`, `NotWired`, `Runtime`), never a
  panic or a bare string. `run_workload` keeps its `anyhow::Result` signature for
  the existing callers (durable layer, webapp router).
- **No silent downgrade.** The wasm tiers refuse if the provider's enforcement
  is below the tier floor (`FloorUnmet`). The native tiers run at the provider's
  real level and report it in `Output.enforcement`.
- **No hang on the interruptible tiers.** Native subprocess calls are bounded by
  `DREGGNET_EXEC_TIMEOUT_SECS` (default 30s); a runaway guest is killed at the
  deadline → `ExecError::Timeout`. The kill is real: see the polyana branch
  hardening below.

## polyana branch hardening (flagged for an operator)

Branch `harden/native-tier-kill-on-drop` on the polyana submodule:

- `python-provider` + `native-process-provider`: set `.kill_on_drop(true)` on
  the interpreter/binary spawn. Without it, dropping a `LiveProcess` (e.g. a
  caller timing out a runaway guest) leaks the kernel-side process and the
  spinning loop. With it, a timed-out call's dropped instance reaps the child.
  This makes the wrapper's timeout a genuine kill, not just a give-up.

Still owed in polyana (not yet patched, flagged):

- `native-process-provider::instantiate_with_caps` override (cap/tenant env →
  host-binary guest), mirroring the Python provider.
- `v8-provider` second-isolate SIGSEGV (blocks pooled Node).
- `python-provider` runtime cap-mutation (`respawn.rs`).
