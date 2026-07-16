# KEY-MANAGEMENT — credential lifecycles

Every long-lived secret in the native deploy, its lifecycle (generate → store
→ back up → rotate), and what rotating it *costs* (some rotations are free;
one forces a committee change). Ported from the operated layer's lifecycle
runbook, re-grounded on native commands.

**Rule zero: live secrets are never committed.** Docs and examples carry the
*regenerate command*, never the value (`deploy/games/.env.example` is the
pattern; real values live only on the box — container environment via the
compose stack, or 0600 files in the per-node data dirs). A secret that
reaches a commit or any shared surface is
compromised — scrub the text AND rotate the secret, in the same breath. The
repo's pre-commit/pre-push hooks run `scripts/git-hooks/secret-scan.sh` as
the backstop (`.gitleaks.toml` is that scan's config). No CI workflow runs a
secret scan — the local hooks are the only automated gate; a push from a box
without the hooks installed is unscanned.

## 1. Validator key (`node.key`) — the consensus identity

An Ed25519 keypair. The private half signs blocks + finalization votes; the
**public** half sits in `genesis.json`, defining the validator's committee
slot and contributing to `federation_id`
(`federation/src/identity.rs::derive_federation_id_with_epoch`).

- **Generate** (idempotent — re-running prints the existing pubkey):
  ```sh
  dregg-node gen-validator-key --data-dir /opt/dregg-data
  ```
  Writes `node.key` (raw 32-byte seed, `0600`) if absent and prints the
  PUBLIC key — that is what you hand the federation operator
  (`docs/OPERATOR-ONBOARDING.md`).
- **Lives** in the node's data dir (whatever `--data-dir` the deployment
  passes — on the edge, the mount the compose file gives the container),
  beside `genesis.json` (committee) and the redb store (ledger). Identity /
  committee / ledger — only the ledger is disposable
  ([DISASTER-RECOVERY.md](DISASTER-RECOVERY.md)).
- **Back up — the one that matters.** A backed-up `node.key` turns a lost box
  into a non-event; without it, loss forces a committee change. Copy
  `node.key` (+ `genesis.json` for convenience) to encrypted offline storage,
  out of band. Never to the repo, never to a shared surface.
- **Rotate — costs a committee change.** A new key = a new public key = a new
  committee. Two paths (`docs/OPERATOR-ONBOARDING.md`):
  - live: `dregg-node propose-epoch-transition --rotate <old-pub> <new-pub>`
    (quorum-voted on-chain epoch transition, no genesis re-roll);
  - offline: `add-validator` re-roll → new `genesis.json` + new
    `federation_id`, distribute, coordinated restart.

## 2. Committee descriptor (`genesis.json`)

Not a secret (it holds *public* keys + threshold), but integrity-critical: a
member with the wrong genesis speaks into the void (its votes reject as
`unknown_sender`/`bad_signature`). Verify with `sha256sum genesis.json`
across members after any committee change. Re-obtainable from any member —
never worth backing up secretly, always worth backing up *conveniently*.

## 3. Discord bot token (`DISCORD_TOKEN`)

- Generate/rotate in the Discord developer portal; free rotation.
- Install: the bot runs as the container `dreggnet-dreggnet-discord-bot-1` on
  the edge; the token reaches it as `DISCORD_TOKEN` in the box's compose stack
  (`/opt/dreggnet/`, box-only — `deploy/README.md` TODO-4). Rotate = update the
  env, `docker compose up -d --no-deps dreggnet-discord-bot`. ⚠ One token = one
  bot: stop the running container before starting the bot anywhere else.
  Full env table: [DISCORD-BOT.md](DISCORD-BOT.md).

## 4. TLS

No TLS terminates on the edge: nothing routes the node publicly
(`deploy/README.md` TODO-5), so there are no ACME certs to manage there. The
one live public TLS surface is the hbox games funnel
(`https://hbox-dregg.skunk-emperor.ts.net`), whose certs Tailscale provisions
and rotates automatically — nothing to manage. The Caddy-ACME story is
quarantined in `deploy/aws/SUPERSEDED/caddy/Caddyfile`; it describes a
deployment that never ran.

## 5. Grafana admin (`GRAFANA_ADMIN_PASSWORD`)

Supplied as an env var at `docker compose up` time
(`deploy/observability/docker-compose.observability.yml` refuses to boot
without it). Free rotation: `docker compose up -d` with the new value after
resetting the admin user (`grafana cli admin reset-admin-password` inside the
container). Grafana binds loopback; the tunnel is the access path.

> The operated layer's Grafana credential once leaked into git history — the
> reason the compose *requires* the env var and this repo's hooks run
> secret-scan. Keep it that way.

## 6. Node signing/unlock (cipherclerk)

No live deployment exercises a post-start cipherclerk unlock today. (The
systemd-gateway flow that did — `dregg-gateway.service` → `unlock-gateway.sh`,
with federation members deliberately staying locked because consensus signing
needs no unlock — is quarantined in `deploy/aws/SUPERSEDED/` and never ran.)
The handling rule stands wherever unlock material exists: data-dir file, 0600,
backed up offline, never committed — treat it exactly like `node.key`.

## What rotation costs — the table

| credential | rotation cost |
|---|---|
| `node.key` | committee change (live epoch path or re-roll) |
| `genesis.json` | n/a (public); changes only via committee change |
| bot token | free (portal + container recreate) |
| TLS | automatic (Tailscale funnel certs on hbox); no public TLS route on the edge |
| Grafana admin | free (env + restart) |
