# DreggNet architecture & build ladder

## Layering (bottom → top)

```
  Hetzner fleet (bare metal / cloud)            ← the host
  └─ wireguard (boringtun) / tailscale mesh     ← secure plane between control + fleet (control::wg + TailscaleMesh)
     └─ dreggnet-exec (owned, in-crate)          ← the execution engine (owned wasmi sandbox; stronger tiers are fail-closed seams)
        └─ dreggnet-bridge (build)               ← fulfills a dregg execution-lease ⟷ a live sandbox workload
           └─ dreggnet-control (build)           ← scheduling, provisioning, lifecycle, billing-ticks
              └─ dreggnet-gateway (dreggnet-http) ← the public API (fly.io-compatible surface), per-workload ingress
                 └─ agents                        ← rent durable execution, reach their workload
```

dregg (`~/dev/breadstuffs`, AGPL) provides the **rail**: the `execution-lease` cell,
`Payable` (conserving Transfer), the intent ring (match a *promise* of execution),
`StandingObligation` (per-period metering), the ToolGateway (pay-per-tool). DreggNet
consumes that rail and provides the **reality**.

## The owned execution engine

The compute is **owned and in-crate** — there is no external submodule and no
external compute dependency.
- **`dreggnet-exec`** is the execution seam. The `Sandboxed` cap-tier runs on a
  vendored pure-Rust `wasmi` interpreter (zero unsafe), which genuinely executes
  (the `add(40,2)=42` dogfood runs here).
- Every stronger tier (`JitSandboxed`/JIT, `Caged`/native, `MicroVm`/microVM,
  `Gpu`, and the native python/node langs) is an honest, fail-closed seam today
  (`ExecError::NotWired`/`TierNotServed`) — never a fake run, never a silent
  downgrade. Wiring an owned engine per tier is future work.
- `dreggnet-exec` maps the dregg lease's cap-grade → a sandbox tier → the owned
  engine, running a workload at the cap-grade the dregg lease authorizes. See
  `docs/COMPUTE-TIERS.md`.

## Build status — the serving layer is owned, AGPL-clean

The Elide-copyright `net/*` stack has been **ejected** — see
`docs/ELIDE-NET-EJECTION.md` for the full audit + eject + history-clean recommendation.
DreggNet now links **zero Elide code**. The serving/transport layer is DreggNet's own:

| piece | what | note |
|---|---|---|
| `http/` (`dreggnet-http`) | the gateway's HTTP/1.1 value vocabulary | clean-room, pure-`std`; replaced the Elide `httpe` engine |
| `control/src/wg.rs` | userspace WireGuard config parser + engine | over `boringtun` (BSD-3-Clause); replaced the Elide `wireguard`/`tailscale` engine |
| `net/conformance-kit` | the conformance/perf kit | DreggNet-authored; the only crate left under `net/` |

The old Elide net closure (`httpe transport tailscale wireguard iocoreo pki base core
sys dns nodeapi rpc bindings builder macros native-dispatch foreign-gai jvm-stubs`) was
deleted from the tree, along with the orphaned `protocol/elide/v1/*` schemas and the
net-only `[patch.crates-io]` forks (ntex, compio, jni). The one real product edge that
linked Elide code — `control → wireguard` (Linux-only) — was replaced by `control::wg`.

### Target + cross-build

`boringtun` is cross-platform userspace, so the mesh engine now builds on every host
(the old Elide net stack was Linux-only). The deploy target is still Linux (the Hetzner
fleet); from a macOS dev box `cargo-zigbuild` cross-compiles:

```
cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-control   # the mesh
cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-gateway   # the gateway
```

## The bridge (the keystone — where the two halves meet)

A funded dregg `execution-lease` (the verified record: who, what cap-grade, what budget,
metered per-period) is the *authorization*; the bridge turns it into a running sandbox
workload:
1. Watch dregg for funded/active leases (via the dregg node / light client).
2. Map the lease's cap-grade → a sandbox tier (the owned `wasmi` `Sandboxed` tier;
   stronger tiers — JIT / native+seccomp / microVM — are fail-closed seams today)
   and language routing.
3. Launch the workload on the fleet; checkpoint its durable image (replay).
4. Tick the lease meter (`StandingObligation`) each period; settle via `Payable`.
5. On lapse / revocation, reap the workload. On stitch/branch (dregg's reversibility),
   fork the durable image.

The honest invariant: **the bridge never lets DreggNet claim more than the dregg lease
proves was paid for, and never lets a workload run beyond what the lease authorizes.**

## The secure mesh (control ↔ fleet)

The control plane provisions a machine, but to *reach* it — dispatch a workload onto
it, health-check it, serve a workload's ingress through it — it needs a secure link
that does not depend on the machine exposing a public bridge port. That link is a
WireGuard overlay (the `100.64.0.0/10` carrier-grade-NAT range, the same Tailscale
uses): every fleet node and the control plane share one encrypted private network, and
the control plane addresses a node by its *overlay* address, not its public IP.

`dreggnet-control`'s `mesh` module (`control/src/mesh.rs`) is this plane:

- **`MeshKeypair` / `MeshConfig`** — the control plane's WireGuard identity (an x25519
  keypair, private half zeroized) and overlay parameters. `MeshConfig::wireguard_ini`
  renders the standard WireGuard `[Interface]`+`[Peer]` config — exactly what the owned
  `control::wg::WireGuardConfig::from_ini` parses, so it round-trips into a real engine.
- **`MeshNode`** — a fleet node to reach (its WireGuard pubkey + public endpoint +
  overlay address), as its worker registers on boot.
- **`Mesh::connect(node) -> MeshLink`** then `MeshLink::health_check()` / `target(port)`.
  `WireguardMesh` backs `connect` with a real `control::wg::WireGuardEngine` (boringtun,
  cross-platform); `default_mesh` uses it on Linux (the deploy target) and the
  cross-platform `StubMesh` elsewhere; `TailscaleMesh` rides the host's tailnet overlay.
- **`dispatch_lease_over_mesh`** — the control-uses-mesh path, wired into
  `Ec2Provider::run_lease`: with a mesh attached (`with_mesh`) and the machine's worker
  registered (`register_mesh_node`), it establishes the link, health-checks the node,
  and dispatches the workload to its bridge agent over the overlay.

Real today: the keypair/config/INI, the link setup, and the control plane *using* a
`MeshLink` to reach a provisioned machine (compiles for Linux via
`cargo zigbuild --target x86_64-unknown-linux-gnu -p dreggnet-control`; unit-tested on
macOS via the stub). The named deploy step (rung 6) is the **live two-node handshake**:
bringing the TUN device up and streaming the durable workflow to the *second* live
node's bridge agent over the tunnel — that needs two machines, not a unit test.

## Build ladder (in order)

Rungs 1–5 are **done and build today**; rung 6 (live metal) is the build ahead.

1. ✅ **Workspace + green build** — a coherent Cargo workspace that builds on the owned `dreggnet-http` serving vocabulary (the Elide `net/*` stack has since been ejected — `docs/ELIDE-NET-EJECTION.md`).
2. ✅ **Owned engine wired** — a `dreggnet-exec` crate that runs a trivial workload through the owned `wasmi` sandbox (the `add(40,2)=42` dogfood, driven by us); stronger tiers are fail-closed seams.
3. ✅ **The bridge** — `dreggnet-bridge`: read a (mock, then `dregg-verify`-decoded) dregg `execution-lease` → launch a durable metered workflow at the mapped tier → tick the meter. The lease⟷workload⟷meter weld is proven end to end.
4. ✅ **The control plane** — `dreggnet-control`: scheduling, provider provisioning (Hetzner + EC2), fleet lifecycle, the settlement ledger, the mesh.
5. ✅ **The gateway** — `dreggnet-gateway`: the runnable fly-compatible machines API server binary; per-workload ingress over the mesh.
6. **Hetzner deploy** — real metal, the live mesh, a first paying workload. (The build ahead.)

## Productization (the two vision rungs above the ladder)

### Agent-served web apps (`dreggnet-webapp`)

The headline vision: **fully agentic web-facing apps** — an agent autonomously
assembles a web API and DreggNet runs + serves it. An agent declares a `WebApp`
(routes → sandbox handlers, plain `serde` data); the router matches an inbound
request, **runs the matched handler on the owned sandbox** (`dreggnet_exec::run_workload`),
and renders the response. A `LeasedRouter` meters each served request against a
funded dregg execution-lease (validated through the bridge's real gate) and
refuses an over-budget request with `402` before the handler runs.

- Portable serving: the `dreggnet-serve` binary serves an assembled app over
  std sockets on any host — `curl localhost:8787/add?a=40&b=2` → `{"result":42}`
  computed in the wasm sandbox.
- Gateway serving: the `dreggnet-gateway` (on the owned `dreggnet-http`) adopts the
  same `Router` via `gateway::WebAppHandler` (the data plane, beside the fly-machines
  control plane). See `docs/AGENT-WEB-APPS.md`.

### The self-hostable provider (`dreggnet-provider`)

DreggNet is **not a monolith**: anyone runs their own provider against their own
dregg cells, their own machines, their own gateway. `dreggnet-provider` (a binary
in `dreggnet-control`) loads a `ProviderConfig` (TOML + `DREGGNET_*` env) — the
cells source (mock / a dregg node), the machine backend (`local` / `ec2`), the
region, the gateway bind — and stands up the `VmProvider` it describes. With a
local backend + mock cells it runs a demo lease end-to-end to prove the wiring.
Federated providers, one open lease/meter/pay protocol between them: the moat is
the network, not the code. See `docs/SELF-HOST.md`.

## Revenue (why this exists)

DreggNet bills for **real execution** — durable container/agent runtime — settled over
dregg's open Payable rail. The substrate is free and verifiable; the operated infra is
the product. First resource: durable execution for agents. Next: the semi-chained
provider set (storage, relay, model endpoints) over the same lease/meter/pay pattern.
