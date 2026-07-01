# DreggNet compute backend — persvati (compute) · AWS (edge) · headscale (mesh)

This is the deploy topology that minimizes cloud spend: the heavy compute runs on
a home box, the cloud is only the edge, and a self-hosted Tailscale control server
(headscale) is the private mesh that ties them together.

```
                    public internet
                          │
                 (DNS A: 34.224.208.52)
                          │
        ┌─────────────────▼──────────────────┐
        │   AWS edge box  i-03365e2bcf4ea08b2 │   t3-class, 24/7, cheap
        │   EIP 34.224.208.52  (stable IP)    │
        │                                     │
        │   Caddy :443  ── TLS + basic-auth   │   the only public door
        │     ├─ dreggnet.fg-goose.online → gateway:8080
        │     └─ headscale.dreggnet.fg-goose.online → headscale:8080
        │                                     │
        │   gateway   (httpe machines API)    │   EDGE services
        │   control   (lease orchestration)   │
        │   postgres  (durable / billing)     │
        │   dregg-node (federation size 1)    │
        │                                     │
        │   headscale (mesh control + DERP)   │   MESH control plane
        │     overlay 100.64.0.0/10           │
        └───────────────┬─────────────────────┘
                        │  headscale tailnet (WireGuard overlay)
                        │  direct path, or DERP-relayed through the edge
        ┌───────────────▼─────────────────────┐
        │   persvati  (home box, 24 cores)     │   PRIMARY COMPUTE BACKEND
        │   tailnet IP 100.64.0.x              │
        │  owned-sandbox exec runtime :8021    │   the heavy lease workloads
        │     prover (STARK turn proving)      │   memory/CPU hungry → home
        └─────────────────────────────────────┘
                        ▲
        ┌───────────────┴─────────────────────┐
        │   ember's devices (laptop / phone)   │   operator plane
        │   tailnet IP 100.64.0.x              │   ssh / inspect / drive
        └──────────────────────────────────────┘
```

## The split — why this shape

- **Compute = persvati.** The home box has 24 cores and is free at the margin.
  The expensive workloads — owned-sandbox lease execution and STARK turn proving — run
  there. Proving in particular is memory-hungry (the staging compose keeps
  `DREGG_PROVE_TURNS=0` precisely because a t3.small chokes on it); persvati makes
  audit-grade proving affordable.
- **Edge = the AWS box.** It contributes the one thing a home box can't: a stable
  public IP and always-on reachability. It runs the public surface (Caddy TLS +
  basic-auth, the gateway/machines API), the orchestration control plane, the
  durable/billing postgres, and a federation-size-1 dregg node. It does **not** do
  the heavy compute — it dispatches it across the mesh.
- **Mesh = headscale.** A self-hosted Tailscale control server. It gives every box
  a stable address on a private WireGuard overlay (`100.64.0.0/10`) and handles key
  distribution + NAT traversal + a relay (DERP) fallback — so the edge can reach
  persvati at home behind NAT without persvati exposing any public port.

The economic point: cloud spend is bounded to one small always-on box; all the
compute that scales with load lands on hardware ember already owns.

## How a lease's workload dispatches over the mesh

A lease opened at the edge gateway is fulfilled on persvati:

1. The gateway records the lease (durable / metered in postgres on the edge).
2. The control plane (`control/`) resolves persvati's mesh address — its tailnet
   IP `100.64.0.x`, or the MagicDNS name `persvati.dregg.mesh`.
3. It establishes a mesh link and **health-checks** persvati over it.
4. It dispatches the durable workload to persvati's bridge agent:
   `POST http://<persvati-tailnet-ip>:8021/fulfill`.
5. persvati's owned-sandbox exec runtime runs the workload (and, for audit-grade leases,
   the prover proves the resulting turn); the result streams back over the overlay.

The overlay carries this traffic; nothing but Caddy is exposed to the internet.

## Mapping onto the existing mesh module (`control/src/mesh.rs`)

The control plane already speaks a WireGuard overlay. headscale slots under it
cleanly — it replaces the manual legs, preserves the addressing and the dispatch.

| `control/src/mesh.rs` today (raw WireGuard) | under headscale |
| --- | --- |
| `OVERLAY_CIDR = "100.64.0.0/10"` | **identical** — headscale's `prefixes.v4` is exactly this CGNAT range. The headscale tailnet *is* this overlay. |
| `MeshConfig` generates the control plane's own x25519 keypair; `wireguard_ini()` renders an `[Interface]`+`[Peer]` INI; `WireguardMesh` brings up a `net/wireguard` engine in-process | the host's `tailscaled` is the WireGuard data plane. No per-node INI to render, no in-process engine to bring up — the tunnel is already up on the box. |
| `MeshNode { public_key, endpoint, overlay_addr, agent_port }`, self-registered by each worker on boot (`register_mesh_node`) | headscale owns `public_key` (key distribution) and `endpoint` (NAT traversal / DERP). `overlay_addr` is **the tailnet IP headscale allocates**; `agent_port` (8021, `DEFAULT_AGENT_PORT`) is unchanged. The `MeshNodeRegistry` is populated from `headscale nodes list` / MagicDNS instead of worker self-registration. |
| `dispatch_lease_over_mesh()`: `connect` → `health_check` → `POST …:agent_port/fulfill` | **unchanged at the application layer.** A future `TailscaleMesh` backend implements `Mesh::connect` by resolving the node's tailnet IP (the OS tunnel is already established) instead of building a raw-WG engine — the same seam `StubMesh`/`WireguardMesh` already abstract. |

Net: headscale takes over **key exchange, NAT traversal, and relay** (the parts
`mesh.rs` left as "the live two-node deploy step"); the **overlay addressing
(`100.64.0.0/10`) and the dispatch path (`overlay_addr:8021 → /fulfill`) carry over
unchanged.** The raw-WireGuard `mesh.rs` path remains valid for a control-plane
that wants to manage its own keys; headscale is the operationally simpler mesh that
gives NAT traversal + DERP for free, which is what a home compute box behind a
residential NAT needs.

## What runs where

| component | edge (AWS) | persvati (home) |
| --- | --- | --- |
| Caddy (public TLS + basic-auth) | ✅ | |
| gateway (httpe machines API) | ✅ | |
| control (lease orchestration / dispatch) | ✅ | |
| postgres (durable / billing) | ✅ | |
| dregg node (federation size 1) | ✅ | (could co-locate later) |
| headscale (mesh control + embedded DERP) | ✅ | |
| owned-sandbox exec runtime (`:8021`) | | ✅ the heavy workloads |
| prover (STARK turn proving) | | ✅ memory/CPU hungry |

## DNS

One record, added at the fg-goose.online registrar:

| field | value |
| --- | --- |
| type | `A` |
| host / name | `headscale.dreggnet` (FQDN `headscale.dreggnet.fg-goose.online`) |
| value | `34.224.208.52` (the edge box EIP) |
| TTL | `300` |

Caddy auto-issues a Let's Encrypt cert for the name once this propagates; at that
moment the public HTTPS control + DERP endpoint goes live and remote nodes
(persvati, ember's devices) can join. The edge box itself is already enrolled via
the host loopback and does not wait on DNS.

## The mesh — control, users, ACLs

- **Control server:** headscale v0.29.1, container `dreggnet-headscale-1` in
  `deploy/staging/docker-compose.yml`, config `deploy/staging/headscale/config.yaml`.
- **Public endpoint:** `https://headscale.dreggnet.fg-goose.online` (Caddy → `headscale:8080`).
- **Embedded DERP relay:** region 999 "DreggNet Edge (AWS us-east-1)"; STUN on
  `3478/udp` (the edge security group allows it). `derp.urls: []` — a fully
  self-hosted private mesh, no dependence on Tailscale's public DERP.
- **User:** `ember` (id 1).
- **Tags / roles** (assigned by the pre-auth key at join time;
  `deploy/staging/headscale/acls.hujson`):
  - `tag:edge` — the AWS edge box.
  - `tag:compute` — persvati.
  - `tag:device` — ember's personal devices.
  - ACLs: ember/devices reach everything; `tag:edge` reaches
    `tag:compute:22,8021,8420,9420` (the dispatch path); `tag:compute` reaches back
    to `tag:edge:22,5432,8080,8420` (postgres + control surface).
- **MagicDNS:** base domain `dregg.mesh` → nodes are addressable as
  `persvati.dregg.mesh`, `edge.dregg.mesh`.

## Join commands

Pre-auth keys are reusable, 30-day expiry, tagged. **These keys are live
credentials — treat them as secrets; rotate with `headscale preauthkeys expire`
after the nodes are enrolled if you want single-use hygiene.** Regenerate any time
with `docker compose exec headscale headscale preauthkeys create --user 1
--reusable --expiration 720h --tags tag:<role>`.

### persvati — after the hardware surgery (the primary compute node)

Uses the public HTTPS endpoint (remote box), so this waits on the DNS record above.
Install tailscale (`curl -fsSL https://tailscale.com/install.sh | sh`), then:

```sh
sudo tailscale up \
  --login-server=https://headscale.dreggnet.fg-goose.online \
  --authkey=<HEADSCALE_AUTHKEY — ask ember / generate fresh: docker compose exec headscale headscale preauthkeys create --user 1 --reusable --expiration 720h --tags tag:compute> \
  --hostname=persvati \
  --accept-routes=false
```

Then bring up the owned-sandbox exec runtime bound to `0.0.0.0:8021` so the edge can
reach it at `persvati.dregg.mesh:8021` over the overlay.

### ember's devices (laptop / phone)

```sh
sudo tailscale up \
  --login-server=https://headscale.dreggnet.fg-goose.online \
  --authkey=<HEADSCALE_AUTHKEY — ask ember / generate fresh on the edge>
```

On macOS, the Tailscale.app reads a custom control server from
`https://headscale.dreggnet.fg-goose.online/...`; or use the CLI
`tailscale login --login-server=https://headscale.dreggnet.fg-goose.online
--authkey=…`.

### edge box — already enrolled

The edge box (`tag:edge`, tailnet `100.64.0.1`) is joined and online. It was
enrolled against the host loopback control endpoint because it is co-located with
headscale and does not need the public HTTPS path:

```sh
# already run on the edge box:
sudo tailscale up --login-server=http://127.0.0.1:8080 \
  --authkey=<HEADSCALE_AUTHKEY — ask ember / generate fresh on the edge> \
  --hostname=edge --accept-routes=false
```

## Operating the mesh

```sh
# on the edge box, from /opt/dreggnet:
sudo docker compose exec headscale headscale nodes list      # who's on the mesh
sudo docker compose exec headscale headscale users list
sudo docker compose exec headscale headscale preauthkeys list --user 1
sudo docker compose logs -f headscale
sudo tailscale status                                        # the edge's view
```

## What is live now vs. what waits on persvati's surgery

**Live (verified):**
- headscale running on the edge (`dreggnet-headscale-1`), `headscale nodes list`
  works, health endpoint passes.
- The edge box enrolled in the tailnet, **online**, at `100.64.0.1`, `tag:edge`.
- User `ember` + three tagged pre-auth keys created.
- Caddy serves `headscale.dreggnet.fg-goose.online` and routes to headscale (cert
  is the internal/fallback CA until the public DNS A record lands → Let's Encrypt).
- STUN `3478/udp` open on the edge security group for DERP NAT traversal.

**Waits on persvati's hardware surgery (it is down now):**
- persvati cannot enroll until it is back up. The join command above is the
  deliverable; persvati actually runs it after surgery.
- Bringing up the owned-sandbox exec runtime + prover on persvati bound to `:8021`.
- The first end-to-end lease dispatch edge → overlay → persvati `:8021/fulfill`.
- A `TailscaleMesh` backend for `control/src/mesh.rs` (resolve tailnet IP instead
  of raw-WG bringup) — optional; the addressing + dispatch path already match.

**Waits on the DNS A record (ember adds it):**
- Remote nodes (persvati, ember's devices) joining over the public HTTPS endpoint.
- Let's Encrypt issuance for `headscale.dreggnet.fg-goose.online`.
- DERP relay between remote nodes (the region HostName resolves once DNS is live).
