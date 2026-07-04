# DEPLOY — the edge box, the compose stack, Caddy + DNS

The edge is the **thin public door**: a small always-on AWS box that the box just
RUNS — it pulls images and `docker compose up`, never builds Rust (a small box
OOMs on the Lean/net closure). This runbook is the edge facts, the stack, the
Caddy proxy (with the cert gotcha), and the DNS records.

Deeper: `deploy/staging/README.md` (deploy mechanics + provisioning from scratch),
`deploy/staging/USING-STAGING.md` (operate / stop-start / cost),
`deploy/staging/Caddyfile` (the live committed config).

## The edge box

| | |
|---|---|
| **Instance** | `<INSTANCE_ID>` (t3.medium, us-east-1c, Ubuntu 24.04 amd64) |
| **Stable IP (EIP)** | `<EDGE_HOST>` (`<EIP_ALLOCATION_ID>`) — survives stop/start |
| **SSH** | `ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>` |
| **Stack dir** | `/opt/dreggnet` |
| **Security group** | `<EDGE_SECURITY_GROUP_ID>` — ingress 22, 80, 443, 8420, 9420, 3478/udp |

Manage the instance (stop when idle — the EIP keeps the address stable so DNS
doesn't break):

```sh
REGION=us-east-1; IID=<INSTANCE_ID>
aws ec2 stop-instances  --region $REGION --instance-ids $IID    # ~$30/mo → ~$1.60/mo (EBS only)
aws ec2 start-instances --region $REGION --instance-ids $IID
aws ec2 describe-instances --region $REGION --instance-ids $IID \
  --query 'Reservations[0].Instances[0].{state:State.Name,ip:PublicIpAddress}' --output table
```

> **Keep the EIP associated.** It's free while associated, ~$3.6/mo if
> allocated-but-unassociated — never release it.

## The compose stack

On `/opt/dreggnet` (everything is `sudo docker compose …` — the `.env` is
root-owned, see SECRETS.md):

| service | what it is | reached at |
|---|---|---|
| `caddy` | TLS + basic-auth reverse proxy — the **only** public HTTP surface | `:80`/`:443` |
| `gateway` | `dreggnet-gateway` — the fly-compatible machines API | internal `:8080`, behind Caddy |
| `dreggnet-discord-bot` | the community front door + the `/admin` portal + the portal read API | internal `:8080`, behind Caddy |
| `ops` | `dreggnet-ops` — the single-pane dashboard | internal `:8090`, behind Caddy (OPS-DASHBOARD.md) |
| `postgres` | durable / billing substrate | internal `:5432` |
| `headscale` | mesh control + embedded DERP | via Caddy; STUN `:3478/udp` (MESH.md) |
| `dregg-node` | the verified node (the chain the bot/leases talk to) | `:8420` api, `:9420/udp` gossip (NODE-OPS.md) |

```sh
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>
cd /opt/dreggnet
sudo docker compose ps                              # what's running
sudo docker compose up -d <service>                 # (re)start one service
sudo docker compose logs -f --tail=100 gateway      # follow
sudo docker compose restart caddy                   # after a DNS/cert change (clears ACME backoff)
```

`restart: unless-stopped` + dockerd-on-boot → every service comes back after a
box reboot.

### How images get to the box

The box never builds Rust. Each piece ships pre-built:

| piece | how it gets there |
|---|---|
| `gateway`, `dreggnet` (cli), `ops` | cross-build with `cargo zigbuild --target x86_64-unknown-linux-gnu`, rsync the binaries, wrap in `debian-slim` (`Dockerfile.runtime`) — pure cross-compilable Rust |
| `postgres` | `postgres:16-bookworm` (pulled) |
| `dregg-node` | pre-built linux/amd64 image, `docker save`→ship→`docker load` — links a host-native Lean archive, **cannot** be cross-compiled (NODE-OPS.md) |
| `dreggnet-discord-bot` | built native on node-a (`--features dregg-sdk/no-lean-link`), `docker save`→ship→`docker load` (MINI-DEVNET path; SECRETS.md for go-live) |

From a dev Mac, the cross-build half:

```sh
cp deploy/staging/.env.example deploy/staging/.env   # fill DREGG_NODE_IMAGE + secrets
BOX_HOST=<EDGE_HOST> SSH_KEY=~/.ssh/dreggnet-staging.pem \
  deploy/staging/deploy.sh         # build (zigbuild) + ship (rsync) + up
# sub-commands: deploy.sh {build|ship|up|down|logs|build-node}
```

## Caddy — the two faces + the cert gotcha

Caddy (`deploy/staging/Caddyfile`) terminates TLS and routes by host. **Four
host blocks:**

- **`portal.example.com`** — **public, NO basic-auth**: the static portal +
  the wasm light client, with `/api/*` + `/observability/*` proxied to the edge
  bot's read surface (read-only).
- **`dreggnet.example.com`** — the **gated operator surface** (basic-auth):
  `/admin*` → the bot's admin portal, everything else → the gateway machines API.
- **`ops.dreggnet.example.com`** — the ops dashboard, a **separate** basic-auth
  credential (`admin`) → `ops:8090` (OPS-DASHBOARD.md).
- **`headscale.dreggnet.example.com`** — headscale control + DERP, **no
  basic-auth** (it would break the tailscale Noise handshake).

### The basic-auth credential

The committed Caddyfile carries a **single shared operator account** `operator`
(bcrypt-hashed; plaintext handed out of band) on the `dreggnet.example.com`
and raw-IP blocks. (Doc drift: `deploy/staging/USING-STAGING.md` still lists
`ember`/`operator` accounts — the Caddyfile is the source of truth; reconcile.) Rotate:

```sh
sudo docker compose exec caddy caddy hash-password --plaintext '<new-password>'
# paste the $2a$... hash into the matching block in Caddyfile, then:
sudo docker compose up -d caddy
```

### The raw-IP / pre-DNS fallback (the cert gotcha)

Clients hitting the **raw IP** (`https://<EDGE_HOST>/`) send no TLS SNI, so the
Caddyfile sets `default_sni localhost` and a `<EDGE_HOST>, localhost` block with
`tls internal` (Caddy's self-signed CA) so the stack **handshakes before the real
domain certs land** (`curl -k`). Automatic Let's Encrypt (HTTP-01 over `:80`)
issues each real cert once its A-record propagates.

> **RUNBOOK (the gotcha we hit): after the A-record lands,
> `sudo docker compose restart caddy`** to clear any ACME backoff so the real
> cert issues promptly. Without the restart Caddy can sit in a back-off window and
> the real cert lags.

## DNS records

Add plain **A records** at the `example.com` / `example.com` registrar —
each pointing at the **EIP** (so they stay correct across box stop/start):

| host | type | value | TTL |
|---|---|---|---|
| `dreggnet.example.com` | A | `<EDGE_HOST>` | 300 |
| `portal.example.com` | A | `<EDGE_HOST>` | 300 |
| `ops.dreggnet.example.com` | A | `<EDGE_HOST>` | 300 |
| `headscale.dreggnet.example.com` | A | `<EDGE_HOST>` | 300 |

`example.com` is intentionally left **pristine for production** — the live records
hang off `example.com` / `example.com`. After each record propagates,
restart caddy (above) to clear ACME backoff.

## See also

- NODE-OPS.md — the node service + the image build/ship pipeline.
- MESH.md — headscale (the fourth Caddy face) + the overlay.
- SECRETS.md — the root-owned `.env`, supplying secrets, the bot go-live.
- OPS-DASHBOARD.md — the ops surface behind Caddy.
- `deploy/staging/README.md` — provisioning a box from scratch + the cost table.
</content>
