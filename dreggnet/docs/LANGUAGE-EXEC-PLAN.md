# DreggNet — Language & Execution Maturation Plan

The goal in one sentence: **a DreggNet workload should be a cap-bounded,
metered, receipted *transacting agent* — not just a sandboxed function.** Fly
Machines and Cloudflare Workers can run your code in a strong sandbox; what they
structurally cannot give you is a guest that *calls a verified service, moves
value, and reads/writes committed state from inside the sandbox, leaving a
receipt for each move.* That inner affordance (§3) is the thing worth building,
and everything else here (more languages, tier robustness, streaming, metrics)
is the substrate that makes it real and trustworthy.

This document is the buildable plan. Each step states **what to build**, a
**rough effort** (S ≈ hours, M ≈ a day, L ≈ multi-day), its **dependency
order**, and whether it is **safe-autonomous** (additive, feature-gated,
default-green preserved, no shared-manifest edit-war).

## 0. Where we are (the grounded what-is)

`dreggnet-exec` (`exec/src/lib.rs`) is the seam. `run_workload_with_input(lang,
source, cap_tier, &[Input])` routes a `(lang, CapTier)` pair to a concrete
`polyana_core::ExecutionProvider`, refusing any run whose tier demands more
isolation than the chosen provider guarantees (never a silent downgrade).

Wired today:

| `CapTier`      | lang(s)                       | provider                          | enforcement          |
|----------------|-------------------------------|-----------------------------------|----------------------|
| `Sandboxed`    | `wasm`/`wat` (core)           | `polyana-wasmi-provider`          | `WasmSandbox`        |
| `JitSandboxed` | `wasm`/`wat` (component)      | `polyana-wasmtime`                | `WasmFullSandbox`    |
| `Caged`        | `native`/`bin`, `python`, `node` | native-process / python / node provider | `OsSandbox` / `None` |
| `MicroVm`      | any (VM runs the runtime)     | `polyana-firecracker-provider`    | `Container` (gated)  |

Three facts shape the whole plan:

1. **polyana already has the providers.** `polyana/src/` carries a deep
   interpreter family (`python`, `node`, `php-fpm`, `ruby`, `luajit`, plus
   `*-runtime-embedded`: `lua`, `perl`, `bash`, `awk`, `sed`, `grep`, `sort`,
   `haskell`, `ocaml`, `zig`, `rust`) and a compiled-language family (`swift`,
   `nim`, `koka`, `moonbit`, `roc`, `crystal`, `dart`, `dotnet-aot`, `jvm`,
   `graal`, `lean`, `llvm-bitcode`, `cosmocc`). **Adding a language to DreggNet
   is mostly wiring an existing provider into the router**, not writing a
   runtime. The four shipped interpreter providers (python/ruby/luajit/php-fpm)
   share one pattern (§1).

2. **One wire everywhere.** Every native tier speaks polyana's newline-delimited
   JSON wire: host writes `{"fn":"run","args":[...]}`, guest replies
   `{"ok":[...]}` / `{"err":"..."}`. The firecracker tier carries that same wire
   into the VM over **vsock**. This single wire is the carrier for the inner
   host-API (§3) and for streaming (§4) — we extend it, we don't replace it.

3. **The cap/tenant lane is still stubbed at the exec rung.** Every
   `instantiate_with_caps` call passes `&[]` (deny-all) plus a single static
   `TENANT = "dreggnet-exec"` (`exec/src/lib.rs`). The bridge
   (`bridge/src/lib.rs::map_cap_grade`) maps a lease's `CapGrade` → tier but
   hardcodes `lang = "wat"` and does not yet derive the tenant from the lessee.
   Firecracker's `enforce_capabilities` is a documented no-op (the
   `Capability` → tap/MMDS/drive/vsock-port translation is "slice-3"). These
   stubs are the real per-tenant + resource work (§2).

---

## 1. More languages

### 1.1 The pattern to add one (the newline-JSON wire)

A new interpreter language is four mechanical pieces, all behind a per-language
cargo feature:

1. **A `run_on_<lang>` fn** in `exec/src/lib.rs`, copy-shaped from
   `run_on_python` / `run_on_node`: build the runtime, construct the provider,
   `store(NativeBinary, source)`, `load_component`, `instantiate_with_caps`,
   `call(ENTRYPOINT, args)` under `workload_timeout()`, surface
   `Output { values, enforcement }`.
2. **A match arm** in `run_workload_with_input` routing `"<lang>"` (and aliases)
   to it, with the `#[cfg(not(feature))]` honest-`NotWired` twin.
3. **A feature** in `exec/Cargo.toml` pulling the polyana provider crate.
4. **Dogfood tests** mirroring the python/node set: real-args add, text-arg
   roundtrip, runaway-times-out, syntax-error-fails-cleanly, skip-if-absent.

Because the providers already exist and share the wire, each language is **S–M**
once the first non-python/node one lands. The *first* one (PHP) also pins the
generic shape; budget it **M**.

> **Swarm hazard:** the match arm + Cargo feature are edits to *shared* files
> (`exec/src/lib.rs`, `exec/Cargo.toml`). Agents draft the disjoint
> `run_on_<lang>` body + tests; the **main loop serializes** the router-arm and
> manifest edits to avoid the clobber. Treat the arm-wiring as a quiet-window
> batch, not parallel.

### 1.2 Which languages next (prioritized by cloud value × low effort)

The providers already in polyana make these near-free; ordered by demand:

1. **PHP** (`polyana-php-fpm-provider`) — **M** (first one; sets the shape).
   High cloud demand (WordPress-class). Provider is shipped + cage-aware.
   *Safe-autonomous.*
2. **Ruby** (`polyana-ruby-provider`) — **S**. Rails/scripts. Shipped provider.
   *Safe-autonomous.*
3. **Lua / LuaJIT** (`polyana-luajit-provider`) — **S**. Embedded/edge logic,
   tiny cold-start. Shipped provider. *Safe-autonomous.*
4. **Bash / POSIX shell** (`bash-runtime-embedded`) — **S**. Glue/ops workloads;
   the most-requested "just run my script." *Safe-autonomous.*
5. **Go / Rust / compiled native** via the `Caged` `native`/`bin` path — **M**.
   The `native-process-provider` already runs an arbitrary host binary; the work
   is accepting `&[u8]` ELF (today `run_on_native_process` takes text/shebang)
   and a small upload convention. *Safe-autonomous (additive arg path).*
6. **Compiled-on-ingest languages** (`swift`, `nim`, `roc`, `moonbit`, `zig`,
   `crystal`, `dotnet-aot`) — **M each**. These providers compile source → a
   native artifact then run it; they want a *build cache* (§1.3) to amortize the
   compile. Lower priority than the interpreters. *Safe-autonomous per language.*

Recommended overnight batch: **PHP → Ruby → Lua → Bash** (four arms, one
quiet-window manifest pass), then the `native`/ELF widening. That quadruples the
language surface with shipped providers and zero new runtimes.

### 1.3 Cross-cutting language work (do once, benefits all)

- **`Input::Json` for wasmtime** — **S**. Today the component-model tier lowers
  `Value::Json` to an empty string; the native tiers already carry full JSON.
  Either teach the wasmtime lowering a JSON string param or document the tier as
  numeric+string-only (it is). *Safe-autonomous.*
- **A build/compile cache** for the compiled-language providers — **M**. Key on
  `hash(source, lang, flags)` → cached native artifact in a content-addressed
  store (the same shape as the storage cell). Turns a multi-second compile into
  a warm-start. Prereq for making §1.2-item-6 economical. *Safe-autonomous.*
- **A capability/`describe` table** — **S**. One generated table (lang → tier →
  provider → enforcement → accepted arg types) emitted from the router so docs,
  the webapp, and the bridge agree on one source of truth. *Safe-autonomous.*

---

## 2. Tier robustness

### 2.1 Firecracker completion (the `MicroVm` tier → live boot)

The provider's VM lifecycle is real (spawn the `firecracker` API process,
per-handle keying, vsock UDS, teardown on drop). The named remaining work, in
build order:

1. **Image build → a committed boot asset.** Run the provider's
   `image/build-image.sh` on a KVM host (the node-a / homelab checkout —
   fast-forward it first), producing `vmlinux.bin` + `rootfs.ext4` + the
   in-guest agent. Publish their paths via the existing
   `DREGGNET_FC_KERNEL` / `DREGGNET_FC_ROOTFS` env knobs. **M.** *Not
   default-green-safe to run in CI (needs `/dev/kvm`); safe to script + stage on
   the homelab. Autonomous on a KVM box, gated elsewhere.*
2. **Guest-plane end-to-end.** Confirm the host→guest vsock + newline-JSON wire
   drives `call` round-trip inside a booted VM (the same wire the native tiers
   speak). The provider's `call` already reaches the agent over vsock; the gap
   is an exercised live boot. **M**, depends on (1). *Autonomous on a KVM host.*
3. **Jailer-as-standard.** `FirecrackerProvider::with_jailer` exists (cgroup +
   namespaces + chroot + privilege-drop). Make jailer the **default** launch
   path for production hosts via a `microvm_config` knob
   (`DREGGNET_FC_JAILER=1` → `with_jailer`), defaulting on where the jailer
   binary + root-then-drop are available. **S**, depends on (1). *Safe-autonomous
   (config + plumbing).*
4. **`EnforcementLevel::FullVm`.** Today the provider reports `Container` because
   the core enum lacks a VM rung, so `MicroVm`'s floor is `Container` — weaker
   than the hardware boundary actually delivered. Add `FullVm` to
   `polyana_core::EnforcementLevel` (strongest), make the firecracker provider
   report it, and raise `cap_tier_enforcement(MicroVm)` to `FullVm`. **M** (it is
   a shared-enum edit in polyana core → ripples to the ordering tests; do it in a
   quiet window). *Polyana-core edit — coordinate; not a casual parallel edit.*

### 2.2 Real per-tenant isolation (replace the single static `TENANT`)

The red-team flag: `TENANT = "dreggnet-exec"` is one static string, so caps +
filesystem + cage all key to a single tenant — no per-tenant partition.

- **Thread the lessee through as the tenant.** The bridge already holds the
  lease's `lessee`; derive `tenant_id` from it (`CapabilityScope::actor(tenant,
  actor)` is the polyana-side shape) and pass it down through `run_workload_*`
  instead of the constant. **M.** Touches the `run_workload` signatures (shared
  file) → main-loop-serialized; the per-provider plumbing is already there
  (`instantiate_with_caps(component, caps, tenant_id)`). *Coordinated, not
  casual-parallel.*
- **Per-tenant filesystem partition.** Each tenant's Landlock/preopen roots and
  any working dir derive from `tenant_id`, so tenant A's cell paths are
  unreachable from tenant B. **M**, depends on the tenant thread. *Safe-autonomous
  once the thread lands.*
- **A cross-tenant isolation test** — two tenants, A writes, B is denied A's
  paths + cells; an explicit red-team regression. **S.** *Safe-autonomous.*

### 2.3 Resource limits per workload (CPU / mem / time / fs quotas)

Today only a wall-clock timeout (`DREGGNET_EXEC_TIMEOUT_SECS`, native tiers) and
wasmtime fuel bound a run. Add a per-workload `ResourceLimits { cpu_ms, mem_bytes,
wall_secs, fs_bytes, fd_count }` carried from the lease and enforced per tier:

- **wasmtime:** fuel (already) + a memory-pages cap + epoch-based wall bound. **S.**
- **native tiers (python/node/php/…):** `setrlimit` (RLIMIT_AS, RLIMIT_CPU,
  RLIMIT_NOFILE, RLIMIT_FSIZE) in the provider's `pre_exec`, plus the existing
  kill-on-timeout. The providers already do `pre_exec` for seccomp/Landlock — add
  rlimits in the same hook. **M** (a polyana-provider edit, mirrored across the
  interpreter family). *Polyana edit; coordinate.*
- **firecracker:** VM `machine-config` (vcpu_count, mem_size_mib) from the limits,
  plus jailer cgroup caps. **S**, depends on §2.1. *Safe-autonomous.*

A `ResourceLimits` type lives in `exec` (additive); per-tier enforcement is the
work. **Dependency:** the limits *type* first (S, safe-autonomous), then each
tier's enforcement.

### 2.4 The cap → sandbox-resource translation (`enforce_capabilities` is a no-op)

This is the load-bearing one. `firecracker-provider::enforce_capabilities`
accepts any cap set and does nothing; the mapping is named in its own docstring:

```
Capability::Network    → tap device + MMDS routing  (allowlisted egress)
Capability::Filesystem → drive bind (read_only flag honored)
Capability::Clock      → host-clock pass-through
+ a vsock-port allowlist for the host-API (§3)
```

Build it as `instantiate_with_caps` (cage-locked: firecracker binds tap/drive at
boot, cannot mutate after) rather than post-hoc `enforce_capabilities`:

- **No `Network` cap → no tap device** (the VM has no NIC; egress impossible). A
  `Network` cap with an allowlist → a tap + MMDS route scoped to it. **M.**
- **`Filesystem` caps → drive binds** with the `read_only` flag from the cap
  (default RO). **M.**
- **A vsock-port allowlist** gating which host-API methods (§3) the guest may
  invoke. **S**, but co-designed with §3.

**Dependency:** §2.4 sits under §3 (the host-API is a vsock service the cap set
gates) and under §2.1 (needs a live boot to test). **M–L total.** *Polyana
firecracker-provider edit; coordinate, but high-value — do it early.*

---

## 3. The inner host-API — the distinctive affordance

**The thesis:** the guest already has a duplex JSON channel to the host (the
provider's stdin/stdout, or vsock for firecracker). Today it carries one
direction: host→guest `run`. **Make it bidirectional.** The guest emits
*host-call* requests on the same wire; a host-side broker services each one
**cap-bounded, metered, and receipted**, and replies. That turns the workload
from a function into a transacting agent.

### 3.1 The wire (an additive multiplexing over the existing protocol)

Keep `{"fn":"run","args":[...]}` → `{"ok":[...]}`. Add, on the *same* line
protocol, a host-call frame the guest may emit mid-run:

```
guest → host:  {"host":"<method>","id":<n>,"args":[...]}
host  → guest: {"reply":<n>,"ok":<value>}   |   {"reply":<n>,"err":"<reason>"}
```

`id` multiplexes concurrent calls; `host` names the method. The broker reads
guest lines, dispatches `host` frames to the host-API, forwards `ok`/`err`/`run`
frames as today. For firecracker the identical frames ride vsock — the
`call_stream`/vsock plumbing already exists.

### 3.2 The methods (the dregg affordance, in priority order)

1. **`invoke` — call a service (the ToolGateway).** `{"host":"invoke",
   "service":"<name>","args":[...]}` → the host runs the named DreggNet service
   (storage put/get, KV, nameservice, another workload) **through the same
   cap-gated turn path the SERVICES catalog defines**, returns the result. This
   is the agent's "call a tool." **M.** *The keystone — build first.*
2. **`cell_read` / `cell_write` — the workload's own committed state.** Read/write
   the workload's cell (its umem heap) by key; the write is a cap-gated turn that
   moves the cell to a new committed root and leaves a receipt. This is what makes
   a workload *stateful* across invocations (§4.3). **M.**
3. **`transfer` — move value.** `{"host":"transfer","to":"<cell>","asset":"<id>",
   "amount":<n>}` → a dregg `Effect::Transfer`/shielded-transfer sub-turn,
   cap-gated against the lease's value authority, Σδ=0 conserved, receipted. The
   thing no other cloud guest can do. **M.**
4. **`subturn` — a metered nested turn.** A general "do a dregg turn over my
   state under an attenuated cap"; the others (2,3) are special cases. Pairs with
   `spawn_nested_context` (Espresso recursive, ADR-0134) for in-substrate
   recursion. **L** (general case); ship 1–3 first.

### 3.3 Cap-threading

The lease's `CapBundle` is the guest's **ambient authority**, delivered at spawn
via the existing `POLYANA_CAPS_JSON` / `instantiate_with_caps` path. Every
host-call **attenuates from it**: the broker runs the requested effect set
through `gate_effect_set(held = lease bundle, requested)` (the dregg-bridge
surface already re-exports `gate_effect_set` / `gate_auth` / `CapBundle`). A
call outside the bundle returns `{"err":"not-an-attenuation"}` — fail-closed, the
guest never escalates. No new trust: the guest's authority is exactly the lease's,
sub-divided per call.

### 3.4 Metering

Each host-call is a **metered sub-turn** against the *same* execution-lease
budget the bridge already ticks. The broker charges the call's cost (per-invoke +
per-byte, the `Payable` rail) *before* committing the effect; an over-budget call
returns `{"err":"over-budget"}` and the workload may handle or abort — the spend
is refused before the commit, never after. Because meter ticks are durable
history (the bridge's exactly-once property), a crash mid-workload resumes within
the same budget.

### 3.5 Receipting

Each committed host-call emits a `TurnShadowReceipt` (the dregg-bridge
`turn_shadow_receipt` / `witness_receipt` surface), **chained into the workload's
receipt chain** (`previous_receipt_hash`). The result: a workload's whole run is a
verifiable chain of *who-called-what-service / moved-what-value / wrote-which-cell*
— a re-witnessable audit of the agent's transactions, not just a function return.

> **License gate:** the receipting/gate surface lives behind the
> `dregg-verify` feature in `polyana-dregg-bridge` (AGPL-isolated). DreggNet is
> already AGPL, so this is fine on the DreggNet side — but the broker that calls
> it must keep the feature gate explicit so a default polyana build stays
> Apache-pure.

**Build order for §3:** the wire (§3.1, **M**, safe-autonomous, additive frame on
the native tiers) → `invoke` (§3.2.1) + cap-threading (§3.3) + metering (§3.4) +
receipting (§3.5) as one keystone slice (**L** together) → `cell_read/write`
(§3.2.2) → `transfer` (§3.2.3) → `subturn` (§3.2.4). Start on the **native
tiers** (python/node, simplest wire) where it is safe-autonomous; carry it to
firecracker after §2.1's live boot.

---

## 4. Streaming, long-running, stateful

### 4.1 Streaming output

The trait already carries `call_stream(instance, name, args, stream_id) ->
ProviderDelta` chunks (ADR-0013), with `supports_streaming()` and a
`DeltaKind::Final`/`Error` terminator. Build:

- **`run_workload_stream`** in `exec` returning a `Stream<ProviderDelta>` for
  providers where `supports_streaming()`, falling back to a one-shot wrapped as a
  single `Final` delta where not. **M.**
- **Provider `call_stream` impls** for the native tiers: the guest emits
  `{"stream":<n>,"chunk":...}` frames on the wire (a natural extension of §3.1),
  terminated by `{"stream":<n>,"final":...}`. **M** per tier; firecracker rides
  the same frames over vsock (its `call_stream` slot is noted slice-3). *Polyana
  edits; coordinate.*
- **SSE/webapp surface:** the webapp router streams deltas to the client; pairs
  with the pub/sub service (SERVICES #3). **M**, depends on the above.

### 4.2 Long-running workloads (the durable layer)

`polyana-long-lived-guest` (ADR-0099) is the persistent-guest primitive:
spawn / health / quiesce / teardown / respawn, with a `CapBundleEnv` carried at
spawn and a `cap_hash` proving the bundle survives respawn. Pair it with
`dreggnet-durable`:

- **A long workload = a durable workflow** whose steps each drive a long-lived
  guest; the meter ticks per period; an over-budget tick **lapses → reaps** the
  guest (no work runs unfunded). Crash mid-run **resumes within the same budget**
  (the durable exactly-once property the bridge already proves). **L**, depends
  on the long-lived-guest provider being wired into `exec` (today only the
  one-shot providers are). *Coordinated (new exec surface).*
- **Health-gated respawn:** a crashed guest respawns with the *same* cap bundle
  (`cap_hash` checked), so a long workload survives a restart without
  re-authorizing. **M**, depends on the above.

### 4.3 Stateful workloads (the umem)

A stateful workload is a **cell + a handler**: its state is the committed content
of its own cell (the umem heap, whose root anchors the trustless read). Each
invocation `cell_read`s prior state (§3.2.2), computes, `cell_write`s new state
(a cap-gated turn to a new committed root), and leaves a receipt. This is the
dregg-native "durable object" / actor:

- **The state surface is §3.2.2's `cell_read`/`cell_write`** — so §4.3 is *built
  by* §3, not separately. The additional work is the convention that a workload
  *names* its state cell and the lease authorizes a `StorageCap`-style token over
  it. **M**, depends on §3.2.2.
- **Trustless read of workload state:** a client re-witnesses the workload's
  state cell against its committed root (the same `verify_opening` shape as the
  storage service), so the agent's state is verifiable, not trust-me. **S**,
  reuses the storage pattern. *Safe-autonomous.*

The synthesis: **streaming + long-running + stateful are the same workload viewed
three ways** — it streams deltas (§4.1), persists as a long-lived guest (§4.2),
and holds committed cell state across invocations (§4.3). The host-API (§3) is
the spine of all three.

---

## 5. Measurement / benchmarking

Tie every tier to the existing o11y (the node_exporter ×3 + Host/Cloud/Protocol
dashboards already shipped). Benches already stubbed: `exec/benches/`,
`durable/benches/`, `webapp/benches/` (untracked — land them).

- **Per-tier cold-start** — time-to-first-result, one criterion bench per
  provider: wasmi (≈instant), wasmtime (JIT compile), python/node/php (interpreter
  spawn), native ELF (exec), firecracker (VM boot). Emit a `cold_start_seconds`
  histogram labeled by tier. **M.** *Safe-autonomous (additive benches).*
- **Throughput** — sustained calls/sec per tier with a warm/pooled instance (the
  long-lived-guest path makes the native tiers poolable). Emit `calls_total` +
  `call_latency_seconds`. **M**, the native-tier throughput depends on §4.2's
  pooling. *Safe-autonomous.*
- **Isolation overhead** — the latency delta for the *same* workload across tiers
  (wasmi → wasmtime → caged → microvm), so the cap-grade→tier cost is legible to
  the bridge's pricing. **S**, depends on the cold-start + throughput benches.
  *Safe-autonomous.*
- **Host-API cost** — per `invoke`/`transfer`/`cell_write` latency + meter-tick
  count, so §3's affordance has a measured price feeding the `Payable` rail.
  **S**, depends on §3. *Safe-autonomous.*
- **Wire it to o11y** — a Prometheus exporter on the exec metrics consumed by the
  existing dashboards; a per-tier panel + a host-API panel. **M.** *Safe-autonomous.*

---

## 6. Prioritized roadmap & the overnight ordering

### Dependency DAG (what blocks what)

```
§1.1 add-a-language pattern ─┬─ §1.2 PHP/Ruby/Lua/Bash (parallel drafts)
                             └─ §1.3 Input::Json, build-cache, describe-table
§2.2 tenant thread ─── §2.2 fs partition ─── §2.2 cross-tenant test
§2.3 ResourceLimits type ─── per-tier enforcement
§2.1 fc image build → fc guest-plane → §2.1 jailer-default → §2.1 FullVm
                              └──────── §2.4 cap→sandbox translation
§3.1 host-call wire ─── §3.2.1 invoke + §3.3 caps + §3.4 meter + §3.5 receipt (keystone)
                              ├─ §3.2.2 cell_read/write ─── §4.3 stateful
                              └─ §3.2.3 transfer ──── §3.2.4 subturn
§4.1 call_stream wiring (independent)
§4.2 long-lived-guest → exec ─── durable long workload ─── pooled throughput (§5)
§5 benches (mostly independent; host-API/throughput panels depend on §3/§4.2)
```

### The safe-autonomous overnight batch (do these unsupervised)

These are additive, feature-gated, default-green-preserving, and touch shared
files only in serialized quiet-window passes:

1. **Languages:** wire PHP → Ruby → Lua → Bash (disjoint `run_on_<lang>` drafts +
   tests in parallel; one quiet-window pass to add the four router arms +
   features). Then `Input::Json` clarification + the `describe` table. *(§1)*
2. **Resource limits type + wasmtime enforcement** (`ResourceLimits` is additive;
   wasmtime fuel/mem/epoch is local). *(§2.3, the wasmtime slice)*
3. **The host-call wire on the native tiers** (§3.1) + the **`invoke` keystone**
   over python/node with cap-threading + metering + receipting (§3.2.1, 3.3, 3.4,
   3.5), then **`cell_read`/`cell_write`** (§3.2.2) and **stateful trustless read**
   (§4.3). This is the headline — the transacting-agent affordance — and it is
   safe on the native tiers without any KVM hardware.
4. **`call_stream` wiring** (§4.1) on the native tiers.
5. **The benchmarks** (§5) — cold-start + isolation-overhead + host-API-cost
   benches, emitted to the dashboards.

### The coordinate-with-a-human (or KVM-host) batch

- **Firecracker live boot, jailer-default, `FullVm`** (§2.1) — needs `/dev/kvm`
  (the node-a/homelab checkout, fast-forwarded). Autonomous *on* a KVM box;
  the `FullVm` core-enum edit is a shared-polyana-enum change → quiet window.
- **The tenant thread + fs partition** (§2.2) — changes `run_workload_*`
  signatures (shared file) and the bridge; main-loop-serialized.
- **The cap→sandbox-resource translation** (§2.4) and **rlimits in the
  interpreter providers** (§2.3) — polyana-provider edits mirrored across the
  family; high value, do early, but coordinate the shared edits.
- **`transfer` / `subturn`** (§3.2.3–4) and **the long-running durable layer**
  (§4.2) — value-movement + new exec surfaces; land after the keystone proves out.

### The one-line through-line

Wire the languages polyana already ships, make the strong tier (firecracker)
boot for real with real per-tenant + per-resource cap translation, and — the
distinctive part — give the guest a cap-bounded, metered, receipted host-API so a
DreggNet workload *transacts* instead of merely *computes*. Streaming, long-running,
and stateful all fall out of that one host-API spine; the benchmarks price it.
