# DISCORD-BOT — running the bot as a DreggNet Cloud frontend

The bot (`dregg-discord-bot`, a standalone cargo workspace under `discord-bot/`)
is a primary front door to the platform: `/dungeon` (a shared AI-narrated crawl
on the real `dungeon-on-dregg` executor), the deos affordance surfaces (`/deos`,
`/card`), payments (`/buy-credits`, `/balance`), and the offering/channel
orchestration layer. **It runs on hbox** (also the build host); build/test it
there via `scripts/hbuild`, never on the laptop.

## Environment (`discord-bot/src/config.rs` + `pay.rs`)
`/etc/dregg/bot.env`, mode 0600:

| Var | Meaning |
|---|---|
| `DISCORD_TOKEN` | the bot token (Discord Developer Portal) |
| `DISCORD_APP_ID` | the application id (slash-command registration) |
| `BOT_SECRET` | seed for deriving each user's dregg identity (`UserCipherclerk`) — **rotating it re-derives every user's identity; treat as a key** |
| `admin_discord_id` | the admin user id — gates channel/role orchestration + the HTTP webportal |
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
1. From the laptop: `scripts/hbuild bot 'cd discord-bot && cargo build --release'`
   (rsyncs WIP → hbox, builds there in an isolated lane dir).
2. On hbox: install/replace the `dregg-discord-bot` binary, `systemctl restart
   dregg-discord-bot` (a `dregg-discord-bot.service` under `/etc/dregg/`).
3. Health: the bot logs a ready line + registers its slash commands on connect;
   `/status` and `/dregg` should respond in a test channel.
Follow [UPGRADE.md](UPGRADE.md)'s health-gate + rollback discipline.

## The paid-run flow (what a player experiences)
`/buy-credits` shows the user's deterministic deposit address + price →
they pay `$DREGG`/USDC → the watcher credits them → `/dungeon` (paid) debits **one
credit** and narrates via **real Bedrock under the per-run cap**; an empty balance
falls back to the **free tier** (ollama/scripted), never free-riding the paid
backend; a failed paid call **never burns a credit**. Each paid run can hand back
the **MPC-TLS attestation** ("you paid for real Claude").

## Monitor + incident
- **Free-riding / drain:** the per-run USD cap is per-user (not the old global
  $20). Watch `DREGG_NARRATOR_RUN_DIR` ledger growth + the AWS Bedrock spend.
- **Bot down:** `journalctl -u dregg-discord-bot`; the sqlite db (`credits`,
  `dungeon` sessions) persists across restart, so credits survive a bounce.
- **Bedrock refused / limit:** paid runs fall back to the free tier + surface the
  narrator kind honestly (`bedrock:<model>` vs `gemma`/`scripted`) — a paid run
  reporting a non-Bedrock kind means the fallback fired; check AWS creds/quota.
- Triage trees: [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md).

## Keys this service touches
`BOT_SECRET` (per-user identity derivation), the AWS profile (Bedrock spend), and
— via the payment rail — the deposit-address derivation. The bot is **watch-only
on the payment seed** (the sweeper holds it separately). See
[KEY-MANAGEMENT.md](KEY-MANAGEMENT.md) + [PAYMENTS-GO-LIVE.md](PAYMENTS-GO-LIVE.md).
