# DISCORD-BOT — running the bot as a DreggNet Cloud frontend

The bot (`dregg-discord-bot`, a standalone cargo workspace under `discord-bot/`)
is a primary front door to the platform: `/dungeon` (a shared AI-narrated crawl
on the real `dungeon-on-dregg` executor), the deos affordance surfaces (`/deos`,
`/card`), payments (`/buy-credits`, `/balance`), and the offering/channel
orchestration layer. **It runs as the docker container
`dreggnet-dreggnet-discord-bot-1`** (image `dregg-discord-bot:staging`) in the
AWS edge box's compose stack — see [`deploy/aws/README.md`](../../deploy/aws/README.md).
Build/test on hbox via `scripts/hbuild`, never on the laptop and never on the
edge. Named seam (`deploy/README.md` TODO-2): the bot is planned to move off the
edge to persvati — the edge exists to be a network exit, not an app host.

## Environment (`discord-bot/src/config.rs` + `pay.rs`)
Supplied to the container as environment variables by the box's compose stack
(`/opt/dreggnet/docker-compose.yml`, which lives only on the box —
`deploy/README.md` TODO-4). Wherever they live, treat the values as 0600
material:

| Var | Meaning |
|---|---|
| `DISCORD_TOKEN` | the bot token (Discord Developer Portal) |
| `DISCORD_APP_ID` | the application id (slash-command registration) |
| `BOT_SECRET` | seed for deriving each user's dregg identity (`UserCipherclerk`) — **rotating it re-derives every user's identity; treat as a key** |
| `ADMIN_DISCORD_ID` | the admin user id — gates channel/role orchestration + the HTTP webportal |
| `DREGG_DEVNET_DOMAIN` | the node the bot talks to for on-chain reads/turns |
| `DREGG_NARRATOR_MODEL` / `_USD_PER_RUN` / `_MAX_TOKENS` / `_RUN_DIR` | real-Bedrock narration: model id, the **per-run USD cap**, token bound, per-run ledger dir |
| `AWS_PROFILE` | AWS creds for Bedrock (paid runs) — the operator's profile |
| `DREGG_PAY_*` | the payment rail — see [PAYMENTS-GO-LIVE.md](PAYMENTS-GO-LIVE.md) |
| `OLLAMA_URL` | the free-tier narrator fallback (local gemma) |

**Gateway intents** the platform layer needs (in `main.rs`): the base set plus
`GUILDS` + `GUILD_MEMBERS` for channel/role orchestration. **OAuth bot perms:**
`MANAGE_CHANNELS` (already needed by `/channel`), `MANAGE_ROLES` for the
orchestration layer.

## Deploy / redeploy
**Never compile on the edge** (2 vCPU, and it is the tailnet's exit). Build the
image elsewhere, ship it:

1. Build on hbox or persvati: `scripts/hbuild bot 'cd discord-bot && cargo build
   --release'` (rsyncs WIP → hbox, builds in an isolated lane dir), then wrap the
   binary with `discord-bot/Dockerfile` → `dregg-discord-bot:<tag>`.
2. Ship the image to the edge (no registry — `docker save | ssh | docker load`),
   point the box's compose file at `<tag>`, then recreate **just this service**:
   `cd /opt/dreggnet && docker compose up -d --no-deps dreggnet-discord-bot`.
   Exact recipe + edge access: [`deploy/aws/README.md`](../../deploy/aws/README.md).
   ⚠ One token = one bot — stop the running container before starting the bot
   anywhere else, or every command double-fires.
3. Health: the bot logs a ready line + registers its slash commands on connect;
   `/status` and `/dregg` should respond in a test channel.

Update/rollback discipline: [`deploy/aws/README.md`](../../deploy/aws/README.md)
("build elsewhere, ship the image") + [`deploy/PRACTICES.md`](../../deploy/PRACTICES.md).

## The paid-run flow (what a player experiences)
`/buy-credits` shows the user's deterministic deposit address + price → the
watcher credits them → `/dungeon` (paid) debits **one credit** and narrates via
**real Bedrock under the per-run cap**; an empty balance falls back to the
**free tier** (ollama/scripted), never free-riding the paid backend; a failed
paid call **never burns a credit**. Named seam: the wired watcher is a
`MockWatcher` (`pay.rs` constructs it on both paths; the real `SolanaWatcher`
in `dregg-pay/src/watcher.rs` is never constructed by the bot), so a real
on-chain `$DREGG`/USDC payment credits no one today. The paid run's honesty
signal is the narrator-kind string (`bedrock:<model>` vs `gemma`/`scripted`);
the MPC-TLS narration attestation ("you paid for real Claude") lives in
`attested-dm` behind the `tlsn-live` feature (an in-tree fixture otherwise),
and the bot's dependency does not enable it — paid runs hand back no
attestation.

## Monitor + incident
- **Free-riding / drain:** the per-run USD cap is per-user (not the old global
  $20). Watch `DREGG_NARRATOR_RUN_DIR` ledger growth + the AWS Bedrock spend.
- **Bot down:** `docker logs dreggnet-dreggnet-discord-bot-1` on the edge; the
  sqlite db (`credits`, `dungeon` sessions) persists across a container restart.
  Whether it survives a *recreate* depends on the box-only compose file's mounts
  (`deploy/README.md` TODO-4) — verify before recreating with credits at stake.
- **Bedrock refused / limit:** paid runs fall back to the free tier + surface the
  narrator kind honestly (`bedrock:<model>` vs `gemma`/`scripted`) — a paid run
  reporting a non-Bedrock kind means the fallback fired; check AWS creds/quota.
- Triage trees: [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md).

## Keys this service touches
`BOT_SECRET` (per-user identity derivation), the AWS profile (Bedrock spend), and
— via the payment rail — the payment seed itself: the bot **holds custody
material**. `DREGG_PAY_SEED` loads into the bot's process (`pay.rs` →
`PayConfig::from_env`), and ed25519 SLIP-0010 has no public child derivation,
so deriving a deposit address requires the secret seed (`dregg-pay/src/hd.rs`).
Named seam: the watch-only-bot / sweeper-holds-the-seed split is the
[PAYMENTS-GO-LIVE.md](PAYMENTS-GO-LIVE.md) target shape, not the current one.
See [KEY-MANAGEMENT.md](KEY-MANAGEMENT.md).
