# node-a — the primary DreggNet compute/hosting backend

This is the concrete deployment of `deploy/ARCHITECTURE-COMPUTE-BACKEND.md` onto
**node-a**, ember's home Linux box. The architecture doc is the shape; this is
the *what is actually installed and running on node-a*, the systemd units, how
it survives a reboot, the overlay wiring, and the cost.

node-a is a native Linux x86_64 box (Ubuntu, a modern kernel, multiple cores,
ample RAM and disk, Docker). Because it is native x86_64, it **builds and runs
the whole DreggNet stack natively — no cross-compile, no zigbuild.**

## The split — what lives where

| component | edge (AWS, `<EDGE_HOST>`) | node-a (home) |
| --- | --- | --- |
| Caddy (public TLS + basic-auth) | ✅ the one public door | |
| gateway (fly-compatible machines API) | ✅ | |
| control (lease orchestration / dispatch) | ✅ | |
| postgres (durable / billing) | ✅ | |
| headscale (mesh control + embedded DERP) | ✅ | |
| **bridge agent (`:8021` `/fulfill`)** | | ✅ the heavy workloads |
| owned-sandbox exec runtime (owned wasmi tier; stronger tiers are seams) | | ✅ |
| prover (STARK turn proving) | | ✅ memory/CPU hungry → home |
| dregg node (Lean `libdregg_lean.a`) | (federation size 1) | optional co-locate |

The economic point: cloud spend is bounded to one small always-on t3-class edge
box (stable IP + TLS + mesh control + relay). Everything that scales with load —
lease execution and STARK proving — runs on hardware ember already owns, at ~free
marginal cost (home power). The edge is a thin door; node-a is the engine room.

## What is installed on node-a

- **Rust toolchain:** `nightly-2026-03-24` (the DreggNet pin in
  `rust-toolchain.toml`) via rustup. `cargo build` from `~/dev/DreggNet`
  auto-selects it.
- **Lean toolchain:** `elan` + `lake` (Lean 4.30.0), for the optional dregg node
  (`libdregg_lean.a` is only needed for the `dregg-verify` / federation-node lane;
  the default backend build does **not** link Lean).
- **Source:** `~/dev/DreggNet` and
  `~/dev/breadstuffs` as siblings — the path-deps (`demo/stripe-receiver`,
  `dregg-verify`) resolve against the sibling layout.
- **The bridge agent:** `deploy/node-agent/` — a new workspace member, built
  natively to `target/release/node-agent`.

## The bridge agent — `:8021/fulfill`

`deploy/node-agent/` is the runnable far end of the mesh dispatch path. The
edge control plane (`control/src/mesh.rs::dispatch_lease_over_mesh`) connects to a
fleet node over the overlay and `POST`s a funded lease to
`http://<overlay-addr>:8021/fulfill`. The agent is what answers that POST on
node-a: it runs the lease as a **real durable metered workflow** via
`dreggnet_bridge::fulfill` (the lease⟷tier⟷meter weld — add(40,2)→×2 genuinely
runs in the wasmi sandbox) and returns the metered result.

Routes:

- `GET  /health`  — liveness for the mesh health-check leg (`200 ok`).
- `POST /fulfill` — JSON lease descriptor in, metered result out.

Local smoke test (the dogfood lease):

```sh
curl -s -X POST http://127.0.0.1:8021/fulfill -d '{}'
# -> {"ok":true,"lessee":"agent-mesh","instance":"mesh-wl-0",
#     "step1":"42","step2":"84","outputs":["42","84"],"meter_units":2}
```

A funded lease descriptor:

```sh
curl -s -X POST http://127.0.0.1:8021/fulfill -H 'content-type: application/json' \
  -d '{"lessee":"agent-A","cap_grade":"sandboxed","asset":"USD","budget_units":100,"per_period_units":1,"instance":"wl-1"}'
```

An unfunded / over-budget lease returns `402` with `{"ok":false,"error":...}` and
**no claimed work** — the bridge never runs beyond what the lease authorizes.

## Build (native, on node-a)

```sh
cd ~/dev/DreggNet
cargo build --release -p dreggnet-bridge          # the lease->durable->owned-sandbox core
cargo build --release -p dreggnet-node-agent  # the :8021 agent
# the edge services (built on the edge, not node-a): gateway / control / cli
```

## systemd — the agent as a service (survives reboot)

The unit lives at `deploy/node-agent/node-agent.service`. Install it as a
system service:

```sh
sudo cp ~/dev/DreggNet/deploy/node-agent/node-agent.service \
        /etc/systemd/system/node-agent.service
sudo systemctl daemon-reload
sudo systemctl enable --now node-agent.service   # enable = start on every boot
systemctl status node-agent.service
journalctl -u node-agent.service -f
```

`Restart=on-failure` + `WantedBy=multi-user.target` means the agent comes back on
its own after a crash and on every reboot. It binds `0.0.0.0:8021`, so once
node-a is on the overlay it is reachable at `node-a.dregg.mesh:8021` /
`<overlay-ip>:8021` from the edge, and on `127.0.0.1:8021` locally.

## The overlay (headscale mesh) — join command + current status

node-a joins the edge's self-hosted headscale control plane to get a stable
private overlay address the edge can dispatch to (without node-a exposing any
public port). The join command (the authkey is `tag:compute`, reusable, 30d):

```sh
# install tailscale if absent: curl -fsSL https://tailscale.com/install.sh | sh
sudo tailscale up \
  --login-server=https://headscale.dreggnet.example.com \
  --authkey=<tag:compute preauth key> \
  --hostname=node-a \
  --accept-routes=false
```

**Status (2026-06-28): JOINED.** node-a is on the headscale mesh as `node-a`
→ overlay **`100.64.0.2`** (`tag:compute`); the edge is `100.64.0.1`.
`https://headscale.dreggnet.example.com/health` returns `{"status":"pass"}`
with a real Let's Encrypt cert. The two boxes reach each other over the overlay
(edge↔node-a `tailscale ping` succeeds — a direct NAT-traversed path, DERP relay
as fallback). The switch required `--force-reauth` (changing `--login-server`).

> ⚠️ **public-tailnet displacement (flag for ember):** tailscaled supports ONE
> control server at a time, so joining headscale **replaced** node-a's
> membership on the *public* Tailscale tailnet (its old `<NODE_TAILNET_IP>`, where a
> collaborator device was visible). This is *required* — the edge
> and node-a must share ONE mesh for dispatch — but it means node-a is **no
> longer on the public tailnet**. Anything that relied on reaching node-a there
> must now use the headscale overlay (`100.64.0.2`). (A second `tailscaled`
> instance could carry both meshes if dual membership is ever wanted; not set up
> here.) headscale also pushed the `dregg.mesh` search domain; node-a's general
> DNS resolution still works (verified), so that part is cosmetic.

## End-to-end dispatch — proven vs the remaining seam

- **PROVEN — edge→overlay→node-a, end to end.** From the AWS edge box
  (`ssh -i dreggnet-staging.pem ubuntu@<EDGE_HOST>`), over the headscale overlay:
  `POST http://100.64.0.2:8021/fulfill` runs the real durable metered workload on
  node-a's cores and returns the metered result — verified for both the dogfood
  (`{}` → `step1=42, step2=84, meter_units=2`) and a funded `edge-dispatch` lease.
  `GET /health` answers `ok` over the overlay; `tailscale ping 100.64.0.2` from the
  edge gets a direct pong. This is the first genuine edge→home-compute round trip:
  a request originating on the cloud edge, crossing the private overlay, executing
  on home hardware, metered back.
- **Control-plane wiring — CLOSED + proven (2026-06-28).**
  `control/src/mesh.rs::dispatch_lease_over_mesh` now *issues* the real
  `POST <overlay-addr>:8021/fulfill` and decodes the durable metered result — it no
  longer returns an `Unimplemented` plan. The `TailscaleMesh` backend resolves the
  node's tailnet IP and rides the host's existing headscale overlay (the live edge
  backend); `WireguardMesh` (Linux) is the self-managed-tunnel alternative;
  `StubMesh` backs tests / the macOS dev host. Proven live **through the control
  plane** (not raw curl): from the edge, a funded lease dispatched via
  `dreggnet-control` over the overlay ran on node-a and returned
  `step1=42, step2=84, meter_units=2`; an under-budget lease came back as a
  `WorkloadLapsed` (`HTTP 402`), no work claimed. Driven with the
  `dispatch_over_tailscale` example (`control/examples/`) cross-built for
  `x86_64-unknown-linux-gnu` and run on the edge against `100.64.0.2:8021`. The
  user-facing shape of this is `deploy/COMPUTE-OFFERING.md`.

## Cost

- **node-a:** ~free at the margin — home power, hardware already owned. Hosts
  all the compute that scales with load (lease execution + proving).
- **edge:** one small always-on t3-class box for the stable public IP, TLS,
  headscale control + DERP relay, and the orchestration front. This is the only
  recurring cloud spend, and it does not grow with workload.

## What node-a can now host to cut cloud spend

- All lease execution (the owned wasmi sandbox tier; stronger tiers are seams) — moved off any
  cloud worker onto the multi-core box.
- STARK turn proving — the memory/CPU-hungry job the t3 edge can't afford
  (`DREGG_PROVE_TURNS=0` on the edge precisely because a t3 chokes). node-a makes
  audit-grade proving affordable.
- Optionally the dregg federation node (Lean is installed), co-located instead of
  on the edge.
- Bursty/parallel batch workloads — many cores absorb concurrency the edge can't.
