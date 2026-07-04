# MESH — headscale on the edge (the private overlay)

The fabric rides a **self-hosted Tailscale control server (headscale)** on the
edge box: a private WireGuard overlay (`100.64.0.0/10`) with key distribution,
NAT traversal, and an embedded DERP relay — so the edge can reach home/homelab
boxes behind NAT without anyone exposing a public port. This runbook is minting
keys, reading the overlay, and the operational gotchas.

Deeper: `deploy/ARCHITECTURE-COMPUTE-BACKEND.md` §"The mesh", the live config in
`deploy/staging/headscale/{config.yaml,acls.hujson}`.

## The overlay map

| node | overlay addr | tag | role |
|---|---|---|---|
| **edge** | `100.64.0.1` | `tag:edge` | AWS box; co-located with headscale (enrolled via host loopback) |
| **node-a** | `100.64.0.2` | `tag:compute` | home box; the compute backend |
| homelab ×N | `100.64.0.x` | `tag:compute` | additional backends/nodes |
| ember's devices | `100.64.0.x` | `tag:device` | operator plane (ssh / inspect) |

- **Control server:** headscale v0.29.1, container `dreggnet-headscale-1` in the
  edge compose, public endpoint `https://headscale.dreggnet.example.com`
  (Caddy → `headscale:8080`, no basic-auth — tailscale clients authenticate with
  the headscale Noise protocol + pre-auth keys; a basic-auth gate would break them).
- **Embedded DERP relay:** region 999 "DreggNet Edge (AWS us-east-1)", STUN on
  `3478/udp` (open in the edge security group). `derp.urls: []` — a fully
  self-hosted private mesh, no dependence on Tailscale's public DERP.
- **User:** `ember` (numeric id **1**).
- **MagicDNS:** base domain `dregg.mesh` → nodes addressable as
  `node-a.dregg.mesh`, `edge.dregg.mesh`.
- **ACLs** (`acls.hujson`): ember/devices reach everything; `tag:edge` reaches
  `tag:compute:22,8021,8420,9420` (the dispatch path); `tag:compute` reaches back
  to `tag:edge:22,5432,8080,8420` (postgres + control surface).

## Mint a pre-auth key

Keys are minted on the edge. The live keys are **never committed** — regenerate,
don't paste from history (the keys that were once in docs have been rotated).

```sh
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>
cd /opt/dreggnet

# reusable, 30-day (720h) key for user id 1 (ember):
sudo docker compose exec headscale \
  headscale preauthkeys create --user 1 --reusable --expiration 720h

# tag it to a role at mint time (assigns the node's ACL tag on join):
sudo docker compose exec headscale \
  headscale preauthkeys create --user 1 --reusable --expiration 720h --tags tag:compute
```

> `--user` wants the **numeric id**, not the name — `headscale users list` shows
> `ember = 1`.

Hand the key to the joining operator out of band; they run the `tailscale up`
join (OPERATOR-ONBOARDING.md §1). After nodes are enrolled, you can expire a key
for single-use hygiene: `headscale preauthkeys expire <key>`.

## Read + operate the mesh

All from `/opt/dreggnet` on the edge:

```sh
sudo docker compose exec headscale headscale nodes list           # who's on the mesh
sudo docker compose exec headscale headscale users list           # users (ember = 1)
sudo docker compose exec headscale headscale preauthkeys list --user 1
sudo docker compose logs -f headscale
sudo tailscale status                                             # the edge's own view
curl -s https://headscale.dreggnet.example.com/health         # {"status":"pass"}
```

Reachability check between two boxes (a direct NAT-traversed path, DERP fallback):

```sh
sudo tailscale ping 100.64.0.2        # from the edge → node-a
```

## Gotchas (the ones we actually hit)

- **The `.env` is root-owned** → compose needs `sudo`. The edge stack's `.env`
  (and the headscale data dir) are owned by root, so every `docker compose …` on
  the edge is `sudo docker compose …`. See SECRETS.md for editing it safely.
- **One control server per box.** `tailscaled` carries exactly one control
  server, so joining headscale **displaces** the public Tailscale tailnet on that
  box. This is required (edge + the joining box must share ONE mesh) but it broke
  reaching node-a on its old public-tailnet address — anything that relied on
  the public tailnet must move to the overlay. (A second `tailscaled` instance
  could carry both meshes if dual membership is ever needed; not set up.)
- **Switching `--login-server` needs `--force-reauth`.** Re-pointing an
  already-enrolled box at headscale required `tailscale up … --force-reauth`.
- **Remote joins wait on DNS.** Remote boxes join over the **public HTTPS**
  endpoint, which needs the `headscale.dreggnet.example.com` A-record live +
  the Let's Encrypt cert issued (DEPLOY.md). The edge itself was enrolled against
  the host loopback (`http://127.0.0.1:8080`) and did not wait on DNS.
- **DERP between remote nodes** needs the region HostName to resolve — i.e. the
  same DNS gate. Until then traffic relays/traverses through the edge.

## See also

- OPERATOR-ONBOARDING.md — the `tailscale up` join + role pick.
- DEPLOY.md — the DNS records + Caddy that front headscale.
- SECRETS.md — the root-owned `.env`, the authkey-leak lesson.
</content>
