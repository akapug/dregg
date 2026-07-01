# DreggNet operational runbooks

This is the **operator's home** — the durable, grounded record of how the live
DreggNet fabric is actually run: the exact commands, the topology, the secrets
handling, and the incidents we hit (with the fixes). It exists because a lot of
this knowledge was trapped in agent-lane reports and one-off conversations; here
it is organized for whoever operates the network next — ember, a homelab operator, or
a future Claude session.

Everything here is grounded to what we **actually did** as of 2026-06-29. Where a
step is staged, single-token-gated, or known-divergent across docs, it says so —
no aspiration. Verify any specific value against HEAD before relying on it; live
secrets are never committed (they are regenerated on the edge).

## The fabric in one breath

A **2-node federation** (target 5) over a self-hosted headscale WireGuard mesh:

```
   community ── Discord ──► dreggnet-discord-bot ──► dregg-node (edge) ──► chain
                                 │                        ▲
   portal.example.com ──► edge bot read API ──┘         │
   ops.dreggnet.example.com ──► dreggnet-ops (single pane) ──┘
                          headscale overlay 100.64.0.0/10
   AWS edge (100.64.0.1)  ◄────── mesh ──────►  node-a (100.64.0.2)
   thin door: Caddy/gateway/bot/pg/headscale    engine room: compute :8021 + STARK proving
```

| node | host | overlay | role |
|---|---|---|---|
| **edge** (node-0) | AWS `<EDGE_HOST>` (t3.medium, EIP, `<INSTANCE_ID>`) | `100.64.0.1` | the public door: Caddy, gateway, control, postgres, headscale+DERP, a `dregg-node`, the Discord bot, the ops dashboard |
| **node-a** (node-1) | the home Linux box (node-a) | `100.64.0.2` | the engine room: compute backend (`:8021/fulfill`), STARK proving, a `dregg-node`, the reference build box |
| homelab ×3 | an operator (target) | `100.64.0.x` | additional **independently-operated** consensus nodes + compute → the 5-quorum |

The economic shape: cloud spend is pinned to **one small always-on edge box**;
everything that scales with load (lease execution + STARK proving) runs on owned
hardware at ~free marginal cost.

## The runbooks

**When the page fires, start at [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md).**

### The fabric model + operating

| # | runbook | what it covers |
|---|---|---|
| 1 | [FEDERATION.md](FEDERATION.md) | the consensus model: lace-merge (CRDT union of disjoint cells), committee-union via epoch transitions, the intentional rust/lean finality mix, how to add an operator |
| 2 | [OPERATOR-ONBOARDING.md](OPERATOR-ONBOARDING.md) | the new-operator (homelab) path: join the mesh, generate keys, stand up a node and/or compute backend, pick a role, the ssh-key exchange |
| 3 | [NODE-OPS.md](NODE-OPS.md) | deploy/restart/shutdown a node, the STORE-INTEGRITY recovery runbook, the bounded build, the warm-worktree + `docker save`→ship→`docker load` pipeline |
| 4 | [MESH.md](MESH.md) | headscale on the edge: minting preauth keys, the overlay map, `headscale nodes/users list`, the root-owned `.env` (sudo) gotcha |
| 5 | [HARDWARE-NODE.md](HARDWARE-NODE.md) | node-a: fan control, the CPU/pstate config, earlyoom, the thermal logger — and that these reset on reboot |
| 6 | [DEPLOY.md](DEPLOY.md) | the edge box facts, the compose stack, Caddy (the basic-auth + LE-cert-after-DNS gotcha), DNS records |
| 7 | [SECRETS.md](SECRETS.md) | the root-owned `.env`, supplying secrets without printing them, the discord secrets + `FEDERATION_ID` matching, key rotation, the leak lesson |
| 8 | [OPS-DASHBOARD.md](OPS-DASHBOARD.md) | `ops.dreggnet.example.com`: what it shows, the separate-admin-password design |

### The Stripe USD-credit rail (earn → mint → spend)

| # | runbook | what it covers |
|---|---|---|
| S1 | [STRIPE-SETUP.md](STRIPE-SETUP.md) | stand the rail up on a Stripe **sandbox**: test keys, the `whsec_…` webhook secret, `stripe listen --forward-to`, configure + run the receiver, the `metadata.dregg_recipient`+amount convention, fire a test (`stripe trigger` / `demo/stripe-trigger.sh`), confirm the conserving mint |
| S2 | [STRIPE-OPS.md](STRIPE-OPS.md) | operate it: monitor the conservation invariant (`live_supply == total_verified_payments`) via the ops Bridge panel / admin History, the payment/refund/dispute workflows, the incident trees (sig-fail / duplicate-mint / conservation breach / receiver-down), and the **sandbox→live** go-live checklist |

### When something goes wrong / changes (the incident + lifecycle runbooks)

| # | runbook | what it covers |
|---|---|---|
| 9 | [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md) | **first-responder diagnostic trees**: won't-finalize (below-quorum), peer-won't-mesh (`peer_count:0`), rust↔lean divergence, STORE-INTEGRITY on restart, bridge conservation breach — symptom → diagnose → cause → fix → escalate |
| 10 | [COMMITTEE-CHANGE.md](COMMITTEE-CHANGE.md) | add/remove a validator: the **static genesis re-roll** we actually run (the n=4 `{edge,node-a,node-a-rust,node-b}` dance) + the future live epoch-transition |
| 11 | [DISASTER-RECOVERY.md](DISASTER-RECOVERY.md) | lost `node.key`, store corruption, restore from backup, genesis re-seed, a **divergent-ledger node** (wipe + re-sync from the committee — what we did with node-a) |
| 12 | [UPGRADE.md](UPGRADE.md) | safe rolling redeploy of node/bot/gateway/compute: build off-box → ship → swap → verify; the order; the bounded build; coordinating a multi-node upgrade |
| 13 | [KEY-MANAGEMENT.md](KEY-MANAGEMENT.md) | the credential lifecycles: validator `node.key` (gen/backup/rotate-costs-a-re-roll), the node/bot submit token, the headscale authkeys (rotation, the leak lesson) |
| 14 | [NETWORK-TROUBLESHOOTING.md](NETWORK-TROUBLESHOOTING.md) | the mesh/gossip diagnostics: the overlay, the overlay-IP bind (MESH-2 scoping), `--federation-peers` + the self-mesh fix, `9420/9421` udp, the ACL (the `:8022` lesson) |

> The two pre-existing prose operator docs **[`docs/OPERATING.md`](../docs/OPERATING.md)**
> (run + restart + topology + cost) and **[`docs/MONITORING.md`](../docs/MONITORING.md)**
> (the alert thresholds + what each signal means) are the companions to these — the
> incident-response trees here *act on* the signals MONITORING.md defines.

## Relationship to the rest of the repo

These runbooks are the **curated operator layer**. They consolidate the real
commands and the gotchas; the deeper per-component detail still lives where it was
authored, and the runbooks cross-link into it:

- `docs/OPERATING.md` — the prose operator overview (topology, cost, reboot story).
- `docs/USING-DREGGNET.md` — the user-facing "I just joined, now what".
- `deploy/FEDERATION.md`, `deploy/FABRIC-JOIN.md` — the original consensus + overlay specs (FEDERATION.md and OPERATOR-ONBOARDING.md here consolidate and extend these).
- `deploy/COMPUTE-BACKEND.md`, `deploy/ARCHITECTURE-COMPUTE-BACKEND.md`, `deploy/COMPUTE-OFFERING.md` — the compute backend.
- `deploy/staging/README.md`, `deploy/staging/USING-STAGING.md`, `deploy/staging/MINI-DEVNET.md` — the staging deploy + the discord-bot go-live.
- `deploy/staging/Caddyfile` — the live committed proxy config (the source of truth for the two-faces + ops gate).
- `docs/SELF-HOST.md` — run your **own** provider (separate from joining this fabric).

For *what dregg is underneath* (the verifiable substrate), the keystone is
`~/dev/breadstuffs/docs/ONBOARDING.md`.

## Open TODOs captured across these runbooks

These are the honest, named follow-ups (not parked — burn them down):

- **node-a hardware config does not persist a reboot** (fan level, pstate caps,
  thermal logger). Persist via `modprobe.d` + a systemd oneshot. See HARDWARE-NODE.md.
- **The genesis-baseline recovery fix** (`breadstuffs` commit `1a61dc16d`) lands
  the sound recovery order; until every deployed node image carries it, the
  wipe-`dregg.redb`-and-resync recovery is the operational fallback. See NODE-OPS.md.
- **Rust↔Lean finality parity is a differential, not yet a hard gate everywhere**:
  `DREGG_FINALITY_GATE` defaults ON but **fails open** (rust-only) when a node lacks
  the Lean archive; a divergence is logged, not fatal. Goal: every consensus member
  runs lean-shadowed. See FEDERATION.md.
- **Live-node epoch-transition wiring**: the static committee re-roll is the
  recommended 5-quorum path today; the dynamic `MembershipAction::Join` + epoch
  rotation exists but is not yet exercised end-to-end on the live nodes. See
  FEDERATION.md, COMMITTEE-CHANGE.md (the wanted improvement that retires the re-roll).
- **Missing CLI affordances** (use the metrics/`/status` instead, honestly noted in
  the runbooks): no `dregg-node peers` command — read `peer_count` from `/status`
  and `dregg_federation_peers_connected` from `:8420/metrics` (the one populated
  native gauge); no standalone `gen-validator-key` — keys come from a node's first
  run or `genesis --validators N` (KEY-MANAGEMENT.md, NETWORK-TROUBLESHOOTING.md).
- **Name the node submit-token env var here** once confirmed on the box —
  KEY-MANAGEMENT.md documents the bearer-token turn-submit auth but defers the exact
  var name to the deployed config.
- **Doc drift to reconcile**: the operator basic-auth username (the committed
  Caddyfile carries `operator`; `deploy/staging/USING-STAGING.md` still lists `ember`/`operator`);
  and the node-a spec (compute-backend docs cite the box's core/RAM specs, the build/thermal facts
  here are the compute node's). Reconcile when next on the box.
</content>
</invoke>
