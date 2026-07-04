# Using DreggNet STAGING

A small, always-on (when you leave the box running) staging environment that
ember + an operator can hit together. Semiprivate, best-effort: the HTTP API is behind
TLS + HTTP basic-auth; the chain node ports are open (nbd if a node leaks
blocks).

## Where it lives

| | |
|---|---|
| **URL** | `https://dreggnet.example.com/` (once the A-record below is added) |
| **Pre-DNS URL** | `https://<EDGE_HOST>/` (self-signed cert until the real cert lands — `curl -k` / click through the browser warning) |
| **Box** | EC2 `<INSTANCE_ID>` (t3.medium, us-east-1c) |
| **Stable IP (EIP)** | `<EDGE_HOST>` (`<EIP_ALLOCATION_ID>`) — survives stop/start |
| **SSH** | `ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>` |
| **Stack dir on box** | `/opt/dreggnet` |

## Logins (HTTP basic-auth)

Two accounts. The browser will prompt; or `curl -u <user>:<pass>`.

| user | password |
|---|---|
| `ember` | `<BASIC_AUTH_PASSWORD>` |
| `operator` | `<BASIC_AUTH_PASSWORD>` |

Rotate: regenerate a bcrypt hash and edit `deploy/staging/Caddyfile`, then
`docker compose up -d caddy` on the box:

```sh
docker run --rm caddy:2 caddy hash-password --plaintext '<new-password>'
# paste the $2a$... hash into Caddyfile under the user, then:
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST> \
  'cd /opt/dreggnet && docker compose up -d caddy'
```

## DNS — add one A-record (do this once)

Add a single **A record** at the `example.com` registrar:

| host | type | value | TTL |
|---|---|---|---|
| `dreggnet` | A | `<EDGE_HOST>` | 300 |

The value is the **Elastic IP**, so this record stays correct across box
stop/start. Once it propagates (usually minutes), Caddy auto-issues a real
Let's Encrypt cert for `https://dreggnet.example.com/` (HTTP-01 over :80)
and the self-signed fallback is no longer needed.

`example.com` is intentionally left untouched (kept pristine for production);
`example.com` is the infra catch-all.

> Note: an earlier Route53 hosted zone for `staging.example.com` was created
> then deleted in favor of this simpler plain-A-record path — there is no
> Route53 hosted-zone charge.

## What ember + an operator can do right now

Behind the proxy you reach the **DreggNet gateway** — the fly.io-compatible
machines API:

```sh
# list machines for an app (200 with creds, 401 without)
curl -u ember:<BASIC_AUTH_PASSWORD> https://dreggnet.example.com/v1/apps/demo/machines
# (pre-delegation: curl -k -u ember:... https://<EDGE_HOST>/v1/apps/demo/machines)
```

Drive the operator CLI + the end-to-end lease/run demo on the box:

```sh
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>
cd /opt/dreggnet
docker compose exec dreggnet dreggnet-demo          # open a funded lease, run a metered workload, print status
docker compose exec dreggnet dreggnet lease open --cap-tier sandboxed --budget 100
docker compose exec dreggnet dreggnet status
docker compose ps                                   # what's running
docker compose logs -f --tail=100 gateway           # follow the gateway
```

The **dregg node** (the substrate the leases talk to) runs as a single-node
federation; its health/API is on the box at `:8420`:

```sh
curl -s http://<EDGE_HOST>:8420/health
```

## Stop / start (save money when idle)

```sh
REGION=us-east-1; IID=<INSTANCE_ID>
aws ec2 stop-instances  --region $REGION --instance-ids $IID    # stop billing (keep disks)
aws ec2 start-instances --region $REGION --instance-ids $IID    # resume
```

The **Elastic IP keeps the address stable across stop/start**, so DNS does not
break when you restart the box. (Without the EIP a stopped instance would get a
new public IP.) The compose stack has `restart: unless-stopped`, so it comes
back up on its own after a start.

**Cost:** ~$0.0416/hr (~$30/mo) while running; ~$1.60/mo (EBS only) when
stopped. The EIP is **free while associated**; it would cost ~$3.6/mo only if
left allocated but unassociated (so don't release it — keep it on the box).

## What's deployed

- `caddy` — TLS + basic-auth reverse proxy (the only public HTTP surface)
- `gateway` — `dreggnet-gateway` (machines API), internal-only behind Caddy
- `dreggnet` — operator CLI (idle daemon you `exec` into)
- `postgres` — durable/billing substrate
- `dregg-node` — the verified dregg node image (`dregg-node:staging`), baked on a
  Lean-capable builder and loaded onto the box (it links a host-native Lean
  archive and cannot be cross-compiled)

## Security note

- The gateway port (8080) is **not** exposed on the host — only Caddy's 80/443.
- SSH (22) and the node ports (8420/9420) are open to `0.0.0.0/0`. The node
  ports are intentionally open (best-effort semiprivate). Tighten 22 to your IP
  if this box lives long:
  `aws ec2 authorize-security-group-ingress --group-id <EDGE_SECURITY_GROUP_ID> --protocol tcp --port 22 --cidr <your-ip>/32` then revoke the `0.0.0.0/0` rule.
