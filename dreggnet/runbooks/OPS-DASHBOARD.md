# OPS-DASHBOARD — the operator's single pane of glass

`dreggnet-ops` is the admin-only dashboard that aggregates the live read surfaces
into one view. It is **not** the public portal — it's the operator's pane, gated
by its **own distinct admin password**.

Source: `ops/` (the `dreggnet-ops` crate). Served by `ops/src/main.rs` (a
pure-std thread-per-connection HTTP/1.1 server), rendered by `ops/src/render.rs`,
aggregated by `ops/src/aggregate.rs`.

## Where it is

| | |
|---|---|
| **URL** | `https://ops.dreggnet.example.com` |
| **Pre-DNS** | `curl -k --resolve ops.dreggnet.example.com:443:<EDGE_HOST> -u admin:<pw> https://ops.dreggnet.example.com/healthz` |
| **Login** | basic-auth user **`admin`** (a separate credential — NOT the public `operator` operator account) |
| **Service** | the `ops` container, `:8090` internal, behind Caddy (DEPLOY.md) |

## What it shows

The dashboard polls the aggregated `CloudSnapshot` on an interval and renders four
panels:

- **Whole-cloud health** — an overall rollup (healthy / warn / down) across the
  node, gateway, bot, and postgres.
- **All-activity** — recent network activity pulled from the read surfaces.
- **Status tables** — the per-service status (node `dag_height`/`peer_count`,
  gateway machine count, bot/cells, postgres reachability).
- **Logs** — a service's tailed container logs on demand (via the Docker Engine
  API over the mounted socket).

The HTTP surface:

| method + path | serves |
|---|---|
| `GET /` | the self-contained HTML dashboard |
| `GET /api/snapshot` | the full aggregated `CloudSnapshot` JSON |
| `GET /api/health` | the whole-cloud health rollup JSON |
| `GET /api/containers` | running containers (Docker Engine API) |
| `GET /api/logs?container=<name>&tail=<n>` | a service's tailed logs (text) |
| `GET /healthz` | ops liveness — **always open** (for compose/Caddy probes) |

What it aggregates (compose defaults, overridable off-stack via env):

```
OPS_NODE_URL     (default http://dregg-node:8420)
OPS_GATEWAY_URL  (default http://gateway:8080)
OPS_BOT_URL      (default http://dreggnet-discord-bot:8080)
DATABASE_URL     (the durable/billing postgres)
OPS_DOCKER_SOCKET (mount /var/run/docker.sock for the logs/containers panels)
```

If no Docker socket is mounted, the logs panel returns a clear "logs unavailable"
rather than failing — and `/api/containers` returns `[]`.

## The separate-admin-password design (defence in depth)

The ops pane is deliberately gated by a **second, distinct** credential, separate
from the public operator surface:

1. **Caddy (the primary gate).** The `ops.dreggnet.example.com` block in the
   Caddyfile is the **only** route to `ops:8090`, behind basic-auth user
   `admin` (its own bcrypt hash, independent of the `operator` realm). So the
   public operator password does **not** open the admin pane.
2. **App-layer token (optional, underneath).** `OPS_ADMIN_TOKEN` adds an optional
   Bearer/`?token=` check *under* Caddy. Left **unset by default** so the normal
   browser-behind-Caddy flow works; set it for belt-and-suspenders. The check is
   constant-time (`ct_eq`). `/healthz` stays open regardless (probes).

Rotate the `admin` password — it is **not** an env var, it's bcrypt-hashed
in the Caddyfile (SECRETS.md):

```sh
sudo docker compose exec caddy caddy hash-password --plaintext '<new>'
# paste the hash into the ops block in Caddyfile, then:
sudo docker compose restart caddy
```

> **DNS/cert note:** the ops block uses `tls internal` (self-signed CA) so it's
> reachable by raw IP **before** the `ops.dreggnet.example.com` A-record
> propagates. Once the A-record lands, drop `tls internal` from that block to
> switch it to Let's Encrypt, then `sudo docker compose restart caddy`.

## See also

- DEPLOY.md — the Caddy faces, the DNS records, the cert gotcha.
- SECRETS.md — rotating the `admin` password + the basic-auth design.
</content>
