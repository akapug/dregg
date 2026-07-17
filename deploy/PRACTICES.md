# deploy practices

Five rules. Each one is here because it broke something on 2026-07-15. The
incident is attached so you can tell whether your situation is the same one.

---

## 1. The demo does not share a box with the prover

**Rule:** a box that serves users and a box that runs unbounded builds/proofs are
different boxes. If they must be the same box, the *prover* is the one that gets
capped (`systemd-run --scope -p MemoryMax= -p CPUQuota=`, or `nice`/`cgroup`) —
never the demo, because a capped demo just fails politely instead of loudly.

**Incident:** hbox runs both the public games demo and the build/prove workload. A
heavy build starved the demo — users got `PR_END_OF_FILE`, sshd started dropping
connections — and then the load **hard-killed the box**: no ARP, no SSH, no ping.
It needed a manual power-cycle. The demo did not degrade; it and the whole host
vanished. The prover had no cap, so there was no point at which anything yielded.

---

## 2. No hand-run production processes. Ever.

**Rule:** every service is a unit or a container:
- systemd **user** unit → **must** have `loginctl enable-linger <user>`, `%h` paths,
  `WantedBy=default.target`;
- docker → **must** have a `restart:` policy;
- and **every** one of them has a **persistent, named `--data-dir`**. Never
  `mktemp -d`. If the data dir is not a path you would back up, it is not a data dir.

`nohup ./thing &` is not a deploy. It is a countdown.

**Incident:** hbox's `dregg-node` was hand-run with an ephemeral `--data-dir`. When
the box died (§1) the process went with it and **the devnet ledger — the operator
cell, every anchored Descent run — was permanently lost.** Nothing to restart,
nothing to restore.

What *did* survive the same reboot, untouched: the `dregg-web-games-funnel` user
unit (it had linger), the `tailscale funnel` config, and the edge's compose stack
(it had a restart policy). The rule is not theoretical — the survivors and the
casualty were on the same box, and the only difference was this rule.

---

## 3. Build where it's fast; ship images, not source

**Rule:** build on **persvati** (CPU) or **hbox** (GPU). Ship **images/binaries**
to the edge. Never compile on the edge.

**Incident (latent, not yet cashed):** `deploy/aws/setup.sh` installs `rustup` and
runs a full `cargo build` **on the AWS box** — which is a **2-vCPU t3.medium**. Per
§1, running a build on a box that is also serving is how you kill a box; here the
box is also the **tailnet's public exit**, so killing it takes the exit with it.
That script is now quarantined in `aws/SUPERSEDED/`.

---

## 4. The docs must match the box, or they are worse than nothing

**Rule:** before planning against a config file in this repo, **confirm it exists on
the box**. A repo file is a *claim*. `systemctl status <unit>`, `docker compose ps`,
`ls` the path. When the box and the tree disagree, **the box wins** — fix the tree
in the same breath.

**Incident:** we wrote an entire deploy plan against `deploy/aws/*.service`. Those
units **do not exist on the edge** — `dregg-gateway.service` reports `not-found`.
The box has run a docker compose stack the whole time. The plan was additionally
impossible because it routed the edge's Caddy to hbox over "the tailnet", and
**the edge and hbox are on different tailnets** (`deploy/README.md`). Two
independent falsehoods, both of which one `ssh` would have caught. Cost: the whole
plan, plus the ops actions in §5 taken on a mistaken model of the box.

Corollary: if you keep a stale file for the thinking in it, **move it somewhere it
cannot be mistaken for instructions** (that is what `aws/SUPERSEDED/` is). A lie at
the live path is a trap for whoever reads it next, and that person is usually you.

---

## 5. Confirm a box's role before touching it; prefer reversible

**Rule:** before stop/restart/terminate, ask *what else does this box do?* Check for
`tailscaled` + `ip_forward=1` + a firewall unit — that shape means **other boxes
route through it**. Prefer the reversible action (restart one container, not the
instance). Public IPs must be **elastic**, or a stop dangles every DNS record
pointing at it.

**Incident:** we `stop`ped the edge to inspect it. The edge is the **tailnet's
public exit** — the stop cut the exit for every peer. It recovered only because
the IP is an **EIP** and survived the stop/start. With a non-elastic IP that stop
would have silently re-IPed the box and dangled DNS on top of the outage. Nothing
about the box's name (`dreggnet-staging`) suggested it was production-load-bearing.
**The name is not the role.**

---

## The five-second checklist

Before you touch a box:

1. What else runs here? (`docker ps`, `systemctl list-units --state=running`, `ip_forward`)
2. Does the file I am about to trust exist **on the box**?
3. Is my action reversible? Is the IP elastic?
4. If I am starting something long: is it a **unit/container**, with **linger/restart**, and a **persistent data dir**?
5. If I am building: am I on persvati or hbox? (If the answer is "the edge": stop.)
