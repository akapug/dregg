# ⚠ SUPERSEDED — NONE OF THIS IS DEPLOYED. NONE OF IT EVER RAN ON THE EDGE.

**Do not follow anything in this directory.** It describes a systemd + Caddy +
Graviton deployment that **does not exist**. Verified 2026-07-15 by direct
inspection of `dreggnet-staging` (`i-03365e2bcf4ea08b2`).

**What is real:** [`../README.md`](../README.md) — a **docker compose stack** at
`/opt/dreggnet`, on a **t3.medium (x86, 2 vCPU)**, reached via **EC2 Instance
Connect**, whose real job is being the **tailnet's public exit**.

These files are kept because some of the *reasoning* inside them is genuine and
worth salvaging (see below). They are quarantined here so nobody reads them as
instructions again — which is precisely what happened this session, and cost us a
whole deploy plan. See `../../PRACTICES.md` §4.

## The falsifications, one line each

| File | Claim | Reality |
|---|---|---|
| `dregg-gateway.service` | the node runs under this unit | `systemctl status dregg-gateway` → **`not-found`**. The node is the container `dreggnet-dregg-node-1` (`dregg-node:n5`). |
| `dregg-discord-bot.service` | the bot runs under systemd, `Requires=dregg-gateway.service` | the bot is the container `dreggnet-dreggnet-discord-bot-1` (`dregg-discord-bot:staging`). |
| `dregg-node@.service`, `dregg-gateway-federation.conf`, `federation-keygen.sh`, `N3-RUNBOOK.md`, `node-{2,3}.env.example` | an n=3 systemd federation on the box | no such units. **One** node container runs. |
| `caddy/Caddyfile` | Caddy terminates TLS for `devnet.dregg.fg-goose.online` | **no caddy container**; `devnet.dregg.fg-goose.online/status` → **HTTP 000**. |
| `setup.sh` | `rustup` + `cargo build` **on the box**; "AWS Graviton"; `t4g.small` | it is **x86 t3.medium, 2 vCPU**, and it is the **tailnet exit** — a build here can take the exit down. **Never compile on the edge** (`PRACTICES.md` §3). |
| `update.sh`, `update-gated.sh`, `update-discord-bot.sh` | `git pull` + `cargo build` + `systemctl restart` on the box | no checkout at `/opt/dregg`, no units, no toolchain. Updates = **build elsewhere, ship the image** (`../README.md`). |
| `unlock-gateway.sh` | `ExecStartPost` of `dregg-gateway.service` | the unit does not exist. |
| `deploy-site.sh` | rsync `site/dist` to `/opt/dregg` | no such path; no site is served from the edge. |
| `node.env.example`, `discord-bot.env.example` | env files at `/etc/dregg/*` | config comes from the compose stack + `/opt/dreggnet/.env` on the box. |

Memory-unit sizing throughout ("the 8 GB t4g.large", "MemoryHigh=5G") is also
wrong: a t3.medium has **4 GB**. A `dregg-gateway.service` with `MemoryMax=6G` on a
4 GB box would never have bounded anything.

## What is worth salvaging

Real thinking, wrong container. If any of it is revived, it belongs in the
**compose** stack (TODO-4 in `../../README.md`), not in these units:

- **`caddy/Caddyfile`** — the `strip_upstream_cors` snippet and the reasoning about
  duplicate `Access-Control-Allow-Origin` (Caddy's + the node's own origin-aware
  headers) is a real bug analysis. The TODO-4 ancestor compose has a `caddy:2`
  service; this is the config it would want.
- **`N3-RUNBOOK.md` + `dregg-node@.service`** — the **finality-critical cadence**
  finding: at n=3 the default 120 s idle-heartbeat starves wave closure so
  `latest_height` pins at 0 forever even on a converged DAG; `--block-cadence-ms 1000
  --idle-heartbeat-ms 2000` paces rounds so `is_super_ratified` can assemble the
  all-three cohort. That is a protocol fact, not a systemd fact, and it survives the
  move to compose. The partition drill is likewise reusable.
- **`DREGG_TRUSTED_PROXIES=127.0.0.1,::1`** (in `dregg-gateway.service`) — the reason
  is sound: behind a loopback proxy, per-client rate limiters collapse into one
  shared `127.0.0.1` bucket unless XFF is trusted. ⚠ **It is also a live footgun**:
  the deployed node binds `0.0.0.0:8420` with **no proxy in front of it**. Setting
  this on the real stack today would let any direct client **spoof `X-Forwarded-For`
  and forge its own rate-limit identity**. It is correct *only* once a real proxy
  terminates in front of the node. Do not copy it forward blindly.
- The **restart-storm brake** (`StartLimitIntervalSec=600` / `StartLimitBurst=20`) —
  the compose equivalent is a bounded `restart:` policy; worth carrying over.
