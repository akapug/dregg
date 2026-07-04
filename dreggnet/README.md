# DreggNet — the operated service layer

**AGPL-3.0, open-core.** The public, formally-verified dregg substrate lives at
`github.com/emberian/dregg` (AGPL-3.0); **DreggNet** is the operated layer, also
AGPL-3.0, that runs real workloads on real metal and earns the revenue. The moat is
not secret code — it is the live network, the multi-operator federation, and the
verifiable proofs (verify, don't trust). (This working repo is kept private for its
history, live-infra config, and retained third-party Elide sources; the product ships
as a clean public AGPL snapshot.)

## The split (open core)

| | what it is | license | where |
|---|---|---|---|
| **dregg** | the verified ocap substrate — kernel, value layer, intent ring, Payable, the execution-*lease* (the on-substrate, light-client-witnessed *record* of a workload + its metering + payment) | AGPL-3.0, public | `~/dev/breadstuffs` |
| **DreggNet** | the thing that actually *runs* the workload, serves it, and hosts it — and bills for it | AGPL-3.0, open | here |

dregg says *what was promised, paid, and owed*, verifiably. DreggNet *delivers it*.
The substrate is the open, trustless rail; the moat is the operated network + federation + proofs, not closed code.

## What composes here

- **the owned execution engine** (`exec/`, `dreggnet-exec`) — an owned, in-crate
  compute sandbox. The `Sandboxed` tier runs on a vendored pure-Rust `wasmi`
  interpreter (zero unsafe, no external submodule) that genuinely executes (the
  `add(40,2)=42` dogfood runs here). Every stronger sandbox tier
  (`JitSandboxed`/JIT, `Caged`/native, `MicroVm`/microVM, `Gpu`, and the
  native python/node langs) is an honest, fail-closed seam today
  (`ExecError::NotWired`/`TierNotServed`) — never a fake run, never a silent
  downgrade; wiring an owned engine for each is future work. Capability gates at
  every boundary. See `docs/COMPUTE-TIERS.md`.
- **the serving + transport layer** — DreggNet-owned, AGPL-clean. An earlier build
  vendored ember's Elide (research-director) net/* stack, which was
  Elide-proprietary and **not relicensable** — the one thing blocking a public
  release. It has been **ejected** (see `docs/ELIDE-NET-EJECTION.md`):
  - `http/` (`dreggnet-http`) — the clean-room, pure-`std` HTTP/1.1 value vocabulary
    (Method/StatusCode/Request/ResponseWriter/Handler) the gateway serves on. Replaces
    the Elide `httpe` engine.
  - `control/src/wg.rs` — the owned userspace WireGuard config parser + engine over
    `boringtun` (Cloudflare, BSD-3-Clause). Replaces the Elide `wireguard`/`tailscale`
    mesh engine; `TailscaleMesh` rides the host's existing tailnet/headscale overlay.
  - `net/conformance-kit` — the DreggNet-authored conformance/perf kit (the only
    surviving crate under `net/`; self-contained, no Elide code).
- **the bridge** (`bridge/`) — fulfills a dregg `execution-lease` by running the
  workload on the owned sandbox through the durable layer, metered + charged against the
  lease budget; the lease cell on dregg ⟷ the live workload on DreggNet. Real
  library: the funded-lease → tier → durable-workflow → meter weld, plus the
  `dregg-verify` lease-watcher that decodes funded execution-lease grants off a
  dregg node's receipt log (the live light-client RPC fetch is the named next
  step). Driven by control/gateway; not a standalone daemon.
- **the control plane** (`control/`) — the orchestrator / provider / trust-rail:
  Hetzner + EC2 provisioning, the scheduler + fleet lifecycle, the provision
  server, the settlement ledger, and the wireguard/tailscale mesh + node API.
  A substantial real crate (~10K LOC) that builds; some provider backends still
  reach live infra behind their own config/credentials.
- **the gateway** (`gateway/`) — the live product host: `dreggnet-gateway` is a
  runnable fly-compatible machines-API server binary (~5K LOC) that binds a TCP
  listener and serves the real route table + lease gate over HTTP. Builds and
  runs (on Linux — the deploy target).

## The flow (an agent rents durable execution)

1. Agent posts an intent / opens an `execution-lease` on **dregg** (verified, paid via Payable; the intent ring can even match a *promise* of execution).
2. **DreggNet** sees the funded lease, schedules a workload on the owned sandbox on the **Hetzner** fleet (the right sandbox tier per the cap-grade), networked via **wireguard/tailscale**.
3. The workload runs durably (checkpoint/replay); the agent's state is a passable, witnessed image.
4. Metering ticks the lease on dregg (`StandingObligation` per-period); payment settles through Payable (a real conserving `Transfer`). Non-payment lapses the lease → the container is reaped.
5. The agent reaches its workload through the **`dreggnet-gateway`** (fly.io-compatible if we choose) over the mesh.

The honest line: **dregg's half is verifiable; DreggNet's half is the operated, paid reality.** Neither claim outruns the other.

## Status

The serving layer is live: the `dreggnet-gateway` runs on the owned `dreggnet-http`
vocabulary and cross-builds from macOS with `cargo-zigbuild`. The Elide net/* stack has
been ejected — DreggNet now links zero Elide code (`docs/ELIDE-NET-EJECTION.md`).
The execution engine is owned and in-crate (the owned `wasmi` sandbox; stronger
tiers are fail-closed seams — see `docs/COMPUTE-TIERS.md`). The bridge (lease→durable
workflow→meter), the control plane (provisioning, scheduler, fleet, settlement, mesh),
and the `dreggnet-gateway` fly-compatible machines-API server all exist and build today.
The build ahead is the live deploy: wiring the provider backends to real Hetzner infra
and the bridge's lease-watcher to a live dregg light-client RPC. See `ARCHITECTURE.md`
for the build ladder and the exact vendoring/pinning.
