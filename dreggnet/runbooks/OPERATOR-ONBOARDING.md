# OPERATOR-ONBOARDING — fold a new box into the fabric

For a **new operator** (the homelab pattern). The goal: a stranger's box runs a
real, independently-operated node and/or compute backend without ember in the
loop for the mechanics. Three things — get on the mesh, pick a role, exchange
keys — then the committee step (FEDERATION.md).

The original re-shareable invite is `deploy/FABRIC-JOIN.md` (the message posted to
builders.dev). This runbook is the durable, command-first version.

## 0. What you need

- A Linux box (a couple cores + a few GB for a consensus node; more CPU/RAM in
  proportion to load for a compute backend).
- The repo: `https://github.com/emberian/dregg` (and the DreggNet repo if you
  build node images yourself).
- A reusable headscale pre-auth key (mint a fresh one — see MESH.md; never paste
  a key from chat/history).

## 1. Join the headscale mesh

The fabric is a **private WireGuard overlay** with a self-hosted headscale
control plane — nodes never expose a public port. One command per machine:

```sh
# install tailscale if absent:
curl -fsSL https://tailscale.com/install.sh | sh

sudo tailscale up \
  --login-server=https://headscale.dreggnet.fg-goose.online \
  --authkey=<fresh reusable preauth key — see MESH.md> \
  --hostname=<node-name> \
  --accept-routes=false
```

Confirm the control plane is up:

```sh
curl -s https://headscale.dreggnet.fg-goose.online/health   # {"status":"pass"}
```

Once `tailscale up` returns you're on the overlay — the edge can reach you, no
inbound firewall holes. Note your allocated overlay address (`tailscale ip -4`,
e.g. `100.64.0.x`).

> ⚠ **One control server at a time.** `tailscaled` supports a single control
> server, so joining headscale **replaces** any membership in the public Tailscale
> tailnet on that box (this bit persvati — its old public-tailnet address went
> away). That's required (edge + your box must share ONE mesh), but anything that
> reached your box on the public tailnet must now use the headscale overlay.

## 2. Generate validator keys + share the PUBLIC key

A node identity is an Ed25519 keypair. Either let the node generate one
(`node.key` in its data dir on first run) and read the public key back:

```sh
curl -s http://localhost:8420/api/node/identity   # → { "public_key": "<hex>", ... }
```

or generate the whole committee centrally (FEDERATION.md, the `genesis ... --validators 5`
path). **Share only the PUBLIC key** with the committee — the private `node.key`
never leaves your box. The committee assembles all five public keys into the
shared `genesis.json` (that is what fixes the `federation_id`).

## 3. Pick a role (run either or both)

Two distinct resource profiles — pick by what the box is for.

### Consensus node (lean-shadowed build)

Modest resources; it gossips + votes, it doesn't do the heavy lifting. **Build
WITH Lean** so it runs the verified finality shadow (`DREGG_FINALITY_GATE` active
rather than failing open — see FEDERATION.md). The reference image
`dregg-node:staging` links the Lean archive; you can also build natively on a
Lean-capable box (elan/lake + warm mathlib). Point it at a live bootstrap peer:

```sh
dregg-node run --data-dir /data --bind 0.0.0.0 --port 8420 --gossip-port 9420 \
  --key-file node.key --federation-mode full \
  --federation-peers 100.64.0.1:9420       # the edge as bootstrap
```

Full deploy mechanics (the compose unit, the `9420/udp` gotcha): NODE-OPS.md.

### Compute backend (fast, no-Lean build)

This **scales with load** — cores + RAM in proportion to the workloads you take.
It does **not** need the Lean kernel (it runs metered owned-sandbox workloads + STARK
proving, not the verified node). Run the `persvati-agent` pattern as a systemd
service bound to `0.0.0.0:8021`:

```sh
# (build natively: cargo build --release -p dreggnet-persvati-agent)
sudo cp deploy/persvati-agent/persvati-agent.service /etc/systemd/system/
sudo systemctl daemon-reload && sudo systemctl enable --now persvati-agent.service
journalctl -u persvati-agent.service -f

# smoke test the /fulfill contract:
curl -s -X POST http://127.0.0.1:8021/fulfill -d '{}'
#   → {"ok":true,...,"step1":"42","step2":"84","meter_units":2}
```

Dispatch reaches it as: **edge gateway → overlay → `POST <overlay-ip>:8021/fulfill`**.
Full backend detail: `deploy/PERSVATI-BACKEND.md`, `deploy/COMPUTE-OFFERING.md`.

## 4. The reciprocal ssh-key exchange

So the edge operator can help operate your box (and vice-versa) over the overlay
without opening public ssh: exchange **public** keys.

```sh
# on your box — generate a key if you don't have one, then send the PUBLIC half:
ssh-keygen -t ed25519 -C "<you>@homelab"            # if needed
cat ~/.ssh/id_ed25519.pub                            # share THIS (over the mesh / a side channel)

# append a trusted operator's public key to authorize them over the overlay:
cat >> ~/.ssh/authorized_keys < their-key.pub
```

The edge's own key is `~/.ssh/dreggnet-staging.pem` (the operator reaches the edge
as `ubuntu@<EDGE_IP>`); reaching your box happens over the overlay address,
not a public IP. Keep this to keys you trust — these boxes are independently
operated on purpose (that independence is the security property, FEDERATION.md).

## 5. Join the committee

Once your node is catching up (lace-merge is automatic) and your public key is
shared, the committee does the **static re-roll** (FEDERATION.md §"How to add an
operator"): the same new `genesis.json` lands on every node, everyone restarts
`--federation-mode full`, and quorum becomes 4-of-5. Until your validators are in
the committee you are a catch-up/compute participant, not a voting member.

## See also

- FEDERATION.md — the committee model + the re-roll + cross-node verify.
- NODE-OPS.md — the concrete deploy/restart/recover.
- MESH.md — minting the preauth key, the overlay map.
- SECRETS.md — `FEDERATION_ID` matching, never-commit-keys.
</content>
