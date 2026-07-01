# Join the dreggnet fabric

The message below was posted to the builders.dev `general` chat (the spec pug
asked for). It is kept here so it is durable and re-shareable. The reusable
pre-auth key it references is real and live (headscale, owner `ember`, reusable,
expires 2026-07-28).

---

**Join the dreggnet fabric — homelab nodes welcome (◕‿◕)**

David — here's exactly what we need to fold your homelab into the dreggnet fabric.
It's early and ARPA-style: if it falls over, we learn. The more *independent*
operators run nodes, the realer the consensus gets — that's the whole point of
asking you. Repo: https://github.com/emberian/dregg

**1. Get on the overlay (one command per machine)**

We run our own headscale control plane (the mesh is a private WireGuard overlay;
nodes never expose a public port). On each homelab machine:

```sh
# install tailscale if absent: curl -fsSL https://tailscale.com/install.sh | sh
sudo tailscale up \
  --login-server=https://headscale.dreggnet.fg-goose.online \
  --authkey=<HEADSCALE_AUTHKEY — ask ember / generate fresh: docker compose exec headscale headscale preauthkeys create --user 1 --reusable --expiration 720h> \
  --hostname=<node-name>
```

That key is reusable (good for all your nodes) and expires in 30 days. Once
`tailscale up` returns you're on the fabric — the edge can now reach you over the
overlay, no inbound firewall holes.

`https://headscale.dreggnet.fg-goose.online/health` returns `{"status":"pass"}`
right now, so the control plane is up and the join works today.

**2. Pick a role (run either or both)**

- **Consensus node** — a dregg federation node (the `dregg-node` image / a native
  build). We want **≥5 independent nodes** so the consensus resists an attacker
  who controls a few. Your 5-node simbi mesh is exactly the shape of quorum we're
  after. A node is *modest* on resources (a couple cores, a few GB RAM, a little
  disk for state) — it gossips and votes, it doesn't do the heavy lifting.

- **Compute backend** — the owned-sandbox exec+prover agent (the `persvati-agent`
  pattern). It serves `:8021/fulfill` on the overlay and runs durable, metered
  workloads (owned wasmi sandbox tier) + STARK turn proving. This one *scales*
  with load — cores and RAM in proportion to the workloads you want to take.
  Dispatch reaches it as: edge gateway → overlay → `POST :8021/fulfill`.

**3. How to operate**

- Consensus node: run `dregg-node` (the staging image is what the edge runs today;
  a native build off the repo works too). It joins the federation and participates
  in consensus — minimal babysitting.
- Compute backend: run the agent as a systemd service (the `persvati-agent.service`
  pattern in the repo — `Restart=on-failure`, `WantedBy=multi-user.target`, so it
  survives reboots) bound to `0.0.0.0:8021`. Smoke test once up:
  `curl -s -X POST http://127.0.0.1:8021/fulfill -d '{}'` → a metered result.

**4. What we're scaling (and subsidizing early)**

Consensus nodes (≥5 quorum — more independent operators = stronger), compute
backends (the owned-sandbox exec/prover :8021 agent), and subsidized early-era
compute/hosting for agents. If you point a few homelab boxes at the overlay and
tell us which roles you want them in, we'll wire dispatch to them and go from there.

Honest current state: the fabric is the AWS **edge** (stable public IP, TLS,
headscale control, DERP relay) + **persvati** (ember's 24-core home box, the
primary compute) coming online. We need ≥5 nodes for consensus that means
something — your homelab is how we get there. ٩( ᐛ )و

---

## Operator reference (links into this repo)

- Compute backend architecture: `deploy/ARCHITECTURE-COMPUTE-BACKEND.md`
- The persvati deployment (the concrete operate pattern): `deploy/PERSVATI-BACKEND.md`
- The agent itself + systemd unit: `deploy/persvati-agent/` (`persvati-agent.service`)

## Fabric facts (as of 2026-06-28)

- **headscale control:** `https://headscale.dreggnet.fg-goose.online` (LIVE, real
  Let's Encrypt cert; `/health` → `{"status":"pass"}`).
- **edge:** AWS `34.224.208.52` — Caddy (public TLS) + gateway + control + postgres
  + headscale (embedded DERP relay) + a staging `dregg-node`.
- **reusable pre-auth key (owner `ember`, reusable, 720h):**
  `<HEADSCALE_AUTHKEY — ask ember / generate fresh on the edge>` (never commit the
  live value; the keys that were once here have been rotated/expired).
  Regenerate on the edge with:
  `ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@34.224.208.52` →
  `cd /opt/dreggnet && docker compose exec headscale headscale preauthkeys create --user 1 --reusable --expiration 720h`
  (the `--user` flag wants the numeric id; `headscale users list` shows `ember` = id 1).
