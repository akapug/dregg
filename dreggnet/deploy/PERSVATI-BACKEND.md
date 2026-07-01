# persvati — the primary DreggNet compute/hosting backend

This is the concrete deployment of `deploy/ARCHITECTURE-COMPUTE-BACKEND.md` onto
**persvati**, ember's home Linux box. The architecture doc is the shape; this is
the *what is actually installed and running on persvati*, the systemd units, how
it survives a reboot, the overlay wiring, and the cost.

persvati is native Linux x86_64 (Ubuntu, kernel 6.17, 24 cores, 83 GiB RAM,
~289 GiB free, Docker 29.1.3). Because it is native x86_64, it **builds and runs
the whole DreggNet stack natively — no cross-compile, no zigbuild.**

## The split — what lives where

| component | edge (AWS, `34.224.208.52`) | persvati (home) |
| --- | --- | --- |
| Caddy (public TLS + basic-auth) | ✅ the one public door | |
| gateway (fly-compatible machines API) | ✅ | |
| control (lease orchestration / dispatch) | ✅ | |
| postgres (durable / billing) | ✅ | |
| headscale (mesh control + embedded DERP) | ✅ | |
| **bridge agent (`:8021` `/fulfill`)** | | ✅ the heavy workloads |
| owned-sandbox exec runtime (wasmi tier) | | ✅ |
| prover (STARK turn proving) | | ✅ memory/CPU hungry → home |
| dregg node (Lean `libdregg_lean.a`) | (federation size 1) | optional co-locate |

The economic point: cloud spend is bounded to one small always-on t3-class edge
box (stable IP + TLS + mesh control + relay). Everything that scales with load —
lease execution and STARK proving — runs on hardware ember already owns, at ~free
marginal cost (home power). The edge is a thin door; persvati is the engine room.

## What is installed on persvati

- **Rust toolchain:** `nightly-2026-03-24` (the DreggNet pin in
  `rust-toolchain.toml`) via rustup. `cargo build` from `~/dev/DreggNet`
  auto-selects it.
- **Lean toolchain:** `elan` + `lake` (Lean 4.30.0), for the optional dregg node
  (`libdregg_lean.a` is only needed for the `dregg-verify` / federation-node lane;
  the default backend build does **not** link Lean).
- **Source:** `~/dev/DreggNet` and
  `~/dev/breadstuffs` as siblings — the path-deps (`demo/stripe-receiver`,
  `dregg-verify`) resolve against the sibling layout.
- **The bridge agent:** `deploy/persvati-agent/` — a new workspace member, built
  natively to `target/release/persvati-agent`.

## The bridge agent — `:8021/fulfill`

`deploy/persvati-agent/` is the runnable far end of the mesh dispatch path. The
edge control plane (`control/src/mesh.rs::dispatch_lease_over_mesh`) connects to a
fleet node over the overlay and `POST`s a funded lease to
`http://<overlay-addr>:8021/fulfill`. The agent is what answers that POST on
persvati: it runs the lease as a **real durable metered workload** via
`dreggnet_bridge::fulfill` (the lease⟷tier⟷meter weld — add(40,2)=42 genuinely
runs in the owned wasmi sandbox) and returns the metered result.

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

## Build (native, on persvati)

```sh
cd ~/dev/DreggNet
cargo build --release -p dreggnet-bridge          # the lease->durable->exec core
cargo build --release -p dreggnet-persvati-agent  # the :8021 agent
# the edge services (built on the edge, not persvati): gateway / control / cli
```

## systemd — the agent as a service (survives reboot)

The unit lives at `deploy/persvati-agent/persvati-agent.service`. Install it as a
system service:

```sh
sudo cp ~/dev/DreggNet/deploy/persvati-agent/persvati-agent.service \
        /etc/systemd/system/persvati-agent.service
sudo systemctl daemon-reload
sudo systemctl enable --now persvati-agent.service   # enable = start on every boot
systemctl status persvati-agent.service
journalctl -u persvati-agent.service -f
```

`Restart=on-failure` + `WantedBy=multi-user.target` means the agent comes back on
its own after a crash and on every reboot. It binds `0.0.0.0:8021`, so once
persvati is on the overlay it is reachable at `persvati.dregg.mesh:8021` /
`<overlay-ip>:8021` from the edge, and on `127.0.0.1:8021` locally.

## The overlay (headscale mesh) — join command + current status

persvati joins the edge's self-hosted headscale control plane to get a stable
private overlay address the edge can dispatch to (without persvati exposing any
public port). The join command (the authkey is `tag:compute`, reusable, 30d):

```sh
# install tailscale if absent: curl -fsSL https://tailscale.com/install.sh | sh
sudo tailscale up \
  --login-server=https://headscale.dreggnet.fg-goose.online \
  --authkey=<tag:compute preauth key> \
  --hostname=persvati \
  --accept-routes=false
```

**Status (2026-06-28): JOINED.** persvati is on the headscale mesh as `persvati`
→ overlay **`100.64.0.2`** (`tag:compute`); the edge is `100.64.0.1`.
`https://headscale.dreggnet.fg-goose.online/health` returns `{"status":"pass"}`
with a real Let's Encrypt cert. The two boxes reach each other over the overlay
(edge↔persvati `tailscale ping` succeeds — a direct NAT-traversed path, DERP relay
as fallback). The switch required `--force-reauth` (changing `--login-server`).

> ⚠️ **public-tailnet displacement (flag for ember):** tailscaled supports ONE
> control server at a time, so joining headscale **replaced** persvati's
> membership on the *public* Tailscale tailnet (its old `100.74.40.124`, where a
> collaborator device `pug-thinkpad` was visible). This is *required* — the edge
> and persvati must share ONE mesh for dispatch — but it means persvati is **no
> longer on the public tailnet**. Anything that relied on reaching persvati there
> must now use the headscale overlay (`100.64.0.2`). (A second `tailscaled`
> instance could carry both meshes if dual membership is ever wanted; not set up
> here.) headscale also pushed the `dregg.mesh` search domain; persvati's general
> DNS resolution still works (verified), so that part is cosmetic.

## End-to-end dispatch — proven vs the remaining seam

- **PROVEN — edge→overlay→persvati, end to end.** From the AWS edge box
  (`ssh -i dreggnet-staging.pem ubuntu@34.224.208.52`), over the headscale overlay:
  `POST http://100.64.0.2:8021/fulfill` runs the real durable metered workload on
  persvati's cores and returns the metered result — verified for both the dogfood
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
  `dreggnet-control` over the overlay ran on persvati and returned
  `step1=42, step2=84, meter_units=2`; an under-budget lease came back as a
  `WorkloadLapsed` (`HTTP 402`), no work claimed. Driven with the
  `dispatch_over_tailscale` example (`control/examples/`) cross-built for
  `x86_64-unknown-linux-gnu` and run on the edge against `100.64.0.2:8021`. The
  user-facing shape of this is `deploy/COMPUTE-OFFERING.md`.

## Cost

- **persvati:** ~free at the margin — home power, hardware already owned. Hosts
  all the compute that scales with load (lease execution + proving).
- **edge:** one small always-on t3-class box for the stable public IP, TLS,
  headscale control + DERP relay, and the orchestration front. This is the only
  recurring cloud spend, and it does not grow with workload.

## What persvati can now host to cut cloud spend

- All lease execution (the owned wasmi sandbox tier) — moved off any
  cloud worker onto the 24-core box.
- STARK turn proving — the memory/CPU-hungry job the t3 edge can't afford
  (`DREGG_PROVE_TURNS=0` on the edge precisely because a t3 chokes). persvati makes
  audit-grade proving affordable.
- Optionally the dregg federation node (Lean is installed), co-located instead of
  on the edge.
- Bursty/parallel batch workloads — 24 cores absorb concurrency the edge can't.
