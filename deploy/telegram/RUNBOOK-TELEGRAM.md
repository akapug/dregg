# RUNBOOK — dreggnet-telegram-bot (the Telegram runtime shell)

**Status: BUILT + TESTED, NOT DEPLOYED.** The whole shell (long-poll loop, durable
per-`(offering, chat)` sessions, command surface) is driven green over `MockTransport` in
`dreggnet-telegram/tests/`. The one thing no test can supply is the **BotFather token** — the
real run is ops-gated on ember minting one. Nothing else is missing.

## What runs

`target/release/dreggnet-telegram-bot` (crate `dreggnet-telegram`, bin
`src/bin/dreggnet-telegram-bot.rs`):

- **long-polls** `https://api.telegram.org` `getUpdates` (outbound 443 only — no listening
  socket, no funnel, nothing public to expose);
- routes inline-button callbacks + text commands (`/offerings`, `/open <key>`, `/verify`,
  `/act <turn> <arg>`, `/help`) through the ONE `TelegramHost` router — every move is a real
  substrate turn, every `/verify` a real replay re-verification;
- persists every session as a **move-log** (`FileResumeStore`) under `TELEGRAM_SESSION_DIR`
  and **resumes by replay on boot** — a restart drops no game, and a stale button pressed
  after a restart auto-rebinds its chat and still lands;
- persists the consumed `getUpdates` offset beside the sessions (no double-routing across
  restarts).

## Deploy (ops steps, in order)

1. **Mint the token** (ember): talk to `@BotFather`, `/newbot`, copy the token.
2. **Env file** on the target box (`chmod 600`), `~/.config/dregg/telegram-bot.env`:

   ```
   TELEGRAM_BOT_TOKEN=<the BotFather token>
   # Optional but RECOMMENDED for any long-lived deploy: pin the identity master secret so a
   # later token rotation does not remap every user's derived dregg identity.
   # TELEGRAM_BOT_SECRET=<64 hex chars, e.g. `openssl rand -hex 32`>
   # Optional: comma-separated Telegram user ids seated as the council electorate.
   # TELEGRAM_COUNCIL_UIDS=1001,1002
   ```

3. **Build**: `cargo build --release -p dreggnet-telegram` (on hbox: wrap in `swarm-build`).
4. **Unit**: copy `deploy/telegram/dregg-telegram-bot.service` to
   `~/.config/systemd/user/`, then
   `systemctl --user daemon-reload && systemctl --user enable --now dregg-telegram-bot`,
   and `loginctl enable-linger` if not already on.
5. **Verify live**: journal shows `authenticated as @<botname>`, then DM the bot `/offerings`
   and press a button; `/verify` must answer `… re-verified by replay`.

## Failure modes (all fail-fast / fail-closed)

- **No/bad token** → exit 2 with a clear message (getMe is checked before anything spins).
  Ten fast exits trip the unit's restart-storm brake by design.
- **Tampered session log** → that session REFUSES to resume (executor re-checks every logged
  move on replay); the file is kept on disk as evidence, everything else resumes.
- **Unwritable session dir** → loud warning, sessions degrade to in-memory (bot still runs).
- **Network flap** → the loop backs off 5s and re-polls; sessions are unaffected.

## Identity note

Every Telegram user's dregg identity derives from the bot master secret. Default = derived
from the token; **rotating the token therefore remaps identities** unless
`TELEGRAM_BOT_SECRET` is pinned in the env file. Pin it before inviting real users.
