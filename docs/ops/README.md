# docs/ops — operator runbooks for the native deploy

The first-responder + lifecycle runbooks for running dregg nodes on the
`deploy/aws` topology (an always-on gateway node behind Caddy, optional
in-box federation members `dregg-node@N`, the Discord bot, QUIC gossip fenced
by security groups). Ported from the operated layer's runbook set (the prior operated layer) and **re-grounded on this repo at HEAD** — every command
here is the native one; nothing references the dead operated fabric.

## The set

| Runbook | Covers |
|---|---|
| [MONITORING.md](MONITORING.md) | what each signal/alert means + running the `deploy/observability/` stack |
| [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md) | symptom → diagnostic commands → cause → fix (the triage trees) |
| [DISASTER-RECOVERY.md](DISASTER-RECOVERY.md) | lost keys, store corruption, lost box, re-sync |
| [KEY-MANAGEMENT.md](KEY-MANAGEMENT.md) | credential lifecycles + what each rotation costs |
| [UPGRADE.md](UPGRADE.md) | safe redeploy: `deploy/aws/update-gated.sh` (health gate + rollback) |
| [PAYMENTS-GO-LIVE.md](PAYMENTS-GO-LIVE.md) | the native `$DREGG`/USDC payment rail — devnet→mainnet go-live, custody contract, treasury refuel, the deferred signer-gated edges |
| [DISCORD-BOT.md](DISCORD-BOT.md) | running the bot frontend (env, hbox deploy, the paid-run flow, monitor, keys) |
| [PRIVATE-NODE.md](PRIVATE-NODE.md) | the private-deployment foundation — a single verified `dregg-node` on hbox, bound localhost/LAN (never public), executing real turns; `scripts/private-node.sh` start/stop/check |

Companions elsewhere in the tree:

- `docs/OPERATOR-ONBOARDING.md` — fold a new node/validator into a federation
  (the `gen-validator-key` / `join` / `add-validator` dance) — this IS the
  committee-change runbook's core.
- `deploy/aws/N3-RUNBOOK.md` — bringing the 3-member devnet up from scratch.
- `deploy/observability/README.md` — the Prometheus/Grafana/Alertmanager stack.

## What was deliberately NOT ported (dead-by-design)

The operated layer's runbooks for its own fabric have no native referent and
were dropped, not lost: `MESH.md` + headscale/WireGuard overlay operations
(native peers over public QUIC + security groups; overlay joins are a
per-federation deployment concern — `docs/OPERATOR-ONBOARDING.md`),
`HARDWARE-PERSVATI.md` + thermal tuning (no operated compute box),
`STRIPE-SETUP/OPS.md` (superseded — the native rail is the `$DREGG`/USDC
`dregg-pay` rail; see PAYMENTS-GO-LIVE.md, not Stripe), `OPS-DASHBOARD.md` (the
the prior operated layer ops aggregator; the native pane is Grafana — MONITORING.md), and
`SECRETS.md`'s edge-box `.env` conventions (native secrets live in
`/etc/dregg/*.env` + the `secrets/` crate's local store; see KEY-MANAGEMENT).
The originals remain readable at `the private operated-layer tree` (reference only).
