# The AWS edge (`dreggnet-staging`)

Verified live 2026-07-15 by direct inspection. This file describes the box as it
**is**. The deployment this directory used to describe — systemd units, Caddy,
Graviton, `setup.sh` building on the box — **does not exist and never ran here**;
it is quarantined in [`SUPERSEDED/`](SUPERSEDED/).

> ## ⚠ DO NOT STOP THIS INSTANCE
>
> It is the **tailnet's public exit**: `tailscaled` + `dregg-harden-firewall.service`
> + `ip_forward=1`. Stopping it **cuts the exit for every peer on the 100.64.0.x
> tailnet**, not just this box's own services.
>
> We stopped it once this session. It recovered only because the public IP is an
> **EIP** (elastic — survives stop/start). The services still blipped and the exit
> still dropped. A non-elastic IP would also have dangled DNS.
>
> The name says `staging`. **The name is not the role.** To restart something, restart
> the *container*, not the instance.

## Facts

| | |
|---|---|
| Name | `dreggnet-staging` |
| Instance | `i-03365e2bcf4ea08b2` |
| Type | **t3.medium** (2 vCPU — x86, *not* Graviton) |
| AZ | `us-east-1c` |
| EIP | `34.224.208.52` |
| OS user | `ubuntu` |
| Tailnet | `100.64.0.x` — this box is **`100.64.0.1`**, the exit |

Peers on that tailnet: `edge` `100.64.0.1`, `persvati` `100.64.0.2`,
`lassie-dregg` `100.64.0.4`.

**⚠ hbox is NOT on this tailnet.** hbox lives on `skunk-emperor.ts.net`
(`hbox-dregg` = `100.95.240.73`). This box cannot reach it over tailscale. Any
"the gateway proxies hbox over the tailnet" plan is false at the network layer —
see `deploy/README.md`.

## Access — EC2 Instance Connect

There is no long-lived SSH key. Push an ephemeral one (**it expires in ~60s**, so
push-then-connect immediately):

```bash
ssh-keygen -t ed25519 -f /tmp/eic -N ''
aws ec2-instance-connect send-ssh-public-key \
  --instance-id i-03365e2bcf4ea08b2 \
  --instance-os-user ubuntu \
  --availability-zone us-east-1c \
  --ssh-public-key file:///tmp/eic.pub
ssh -i /tmp/eic ubuntu@34.224.208.52
```

If the key expires before you connect, re-run `send-ssh-public-key` — it is
idempotent and free. Do not "fix" this by installing a persistent key.

## What runs: a docker compose stack

`/opt/dreggnet/docker-compose.yml` + `/opt/dreggnet/docker-compose.observability.yml`.

```bash
cd /opt/dreggnet
docker compose ps
docker compose -f docker-compose.yml -f docker-compose.observability.yml ps
docker logs -f dreggnet-dregg-node-1
```

| Container | Image | Binds |
|---|---|---|
| `dreggnet-dregg-node-1` | `dregg-node:n5` | `0.0.0.0:8420`, `9420/udp` |
| `dreggnet-dreggnet-discord-bot-1` | `dregg-discord-bot:staging` | — |
| grafana | | `127.0.0.1:3000` |
| prometheus | | `127.0.0.1:9090` |
| alertmanager | | `127.0.0.1:9093` |
| node-exporter, blackbox, alert-sink | | loopback |

Grafana/prometheus/alertmanager are loopback-only. Reach them with a tunnel:
`ssh -i /tmp/eic -L 3000:127.0.0.1:3000 ubuntu@34.224.208.52`.

**Host services** (these are the exit, and are real systemd): `tailscaled`,
`dregg-harden-firewall.service` (enabled).

### Autostart is the docker restart policy

Not systemd. There is **no** `dregg-gateway.service`; `systemctl status dregg-gateway`
returns `not-found`. Containers come back after a reboot because of their `restart:`
policy — nothing else brings them up.

### Images are ~2 weeks old

`dregg-node:n5` / `dregg-discord-bot:staging` were built roughly two weeks before
2026-07-15. There is no automated image refresh.

## Updating: build elsewhere, ship the image

**⚠ Never compile on this box.** It is 2 vCPU *and* it is the exit — a build that
wedges it takes the tailnet's exit down with it (`deploy/PRACTICES.md` §3).

Build on **persvati** or **hbox**, then ship the image:

```bash
# on persvati/hbox — build and tag
docker build -t dregg-node:<tag> .

# ship (no registry today — save/load over the wire)
docker save dregg-node:<tag> | gzip | \
  ssh -i /tmp/eic ubuntu@34.224.208.52 'gunzip | docker load'

# on the edge — point the compose file at <tag>, then recreate JUST that service
ssh -i /tmp/eic ubuntu@34.224.208.52
cd /opt/dreggnet && docker compose up -d --no-deps dregg-node
```

`--no-deps` + a named service keeps the blast radius to one container. Do not
`docker compose down` — it stops everything including nothing-to-do-with-your-change.

## Known-wrong / cruft on the box

- **`/home/ubuntu/DreggNet/docker-compose.yml`** — a checkout of the **abandoned**
  DreggNet repo. **Not what runs.** `/opt/dreggnet/` is. Delete it before someone
  `docker compose up`s the wrong file (TODO-6).
- **`devnet.dregg.fg-goose.online/status` → HTTP 000.** Nothing routes the node
  publicly; there is no Caddy container. The "gateway serves devnet" story in
  `SUPERSEDED/` is stale in this respect too (TODO-5).

## ⚠ The compose files are not in this repo — but an ancestor is in git history

`/opt/dreggnet/docker-compose.yml` exists **only on the box**. Nothing reachable from
`main` defines it. **The box is authoritative; this file is only a description of it.**

The **closest known ancestor** is recoverable from history — it matches the deployed
`dregg-node` (`8420` + `9420/udp`) and `dreggnet-discord-bot` services exactly,
including the `/opt/dreggnet/` layout:

```bash
git show 0310c9e31^:dreggnet/deploy/staging/docker-compose.yml
# added   ab6328a3e  "stage the scrubbed DreggNet public tree as dreggnet/"
# deleted 0310c9e31  "execute the DELETE-NOW pass — strip-mined slop, abandoned" (2026-07-03)
```

⚠ **Neither commit is an ancestor of `main`** — that tree only ever existed on
`remotes/hbox/fable/*` and `remotes/persvati/*`. So the running production stack was
defined by a file that was *deleted as abandoned slop* on branches that never merged.
That is how it ended up undocumented.

⚠ **The ancestor is NOT identical to what is deployed.** It defines `postgres`,
`gateway`, `provider`, `ops`, `webauth`, `caddy` (80/443), `dreggnet`, and `headscale`
— **none of which are among the running containers**. The deployed stack is a *subset*.
Diff it against the box before trusting any line of it (TODO-4).

Two things it explains:

- **Why `devnet.dregg.fg-goose.online` returns 000** (TODO-5): the ancestor has a
  `caddy:2` service on 80/443 that would have routed the node publicly. It is not
  running. The public route did not break — it was never brought up here.
- **A lead on the two-tailnet split** (unverified): the ancestor defines a
  **`headscale`** service, and headscale hands out `100.64.0.x` — the edge tailnet's
  exact range. That would make `100.64.0.x` a **self-hosted headscale** net (control
  plane plausibly on this box) and `skunk-emperor` the real Tailscale one, which is
  why they are separate. **Not confirmed**: `100.64.0.0/10` is CGNAT and Tailscale uses
  it too, and headscale was not observed running. Check with
  `docker ps | grep headscale` and `tailscale status --json | jq .CurrentTailnet`
  before relying on this. If it *is* headscale on this box, the DO-NOT-STOP warning
  above is even more load-bearing: stopping the box would take down the tailnet's
  **control plane**, not just its exit.

The nearest thing in this tree is `deploy/observability/docker-compose.observability.yml`,
which is close to the deployed observability stack but has **drifted** — the box also
runs a **blackbox exporter** that file does not define. Do not assume they are the same.
