# Games deploy runbook — the dregg games stack on hbox, public at demo.dregg.net

The ordered go-live for the **standalone games public demo** (docs/DEPLOY-PLAN.md
Phase 0 + Phase 1): the `dreggnet-web-server` (all 5 games + the no-cheat-by-REPLAY
Descent leaderboard, node-free) fronted by Caddy TLS, plus the `dregg-discord-bot`
Descent daily. This makes the go-live a **small, safe flip** — build → install →
reload → health — not a new build.

**Honest scope.** AUTOMATED by `deploy-hbox.sh`: build the two binaries, snapshot a
rollback point, install the user systemd units + the Caddyfile, reload, health-check
`/health`, and auto-revert on a failed gate. **EMBER-GATED** (this runbook's manual
steps, never touched by the script): DNS, the token env, stop-the-old-bot, opening
hbox's firewall/ports, and the go-live decision itself. The demo verifies by REPLAY;
the portable STARK proof is the labeled Phase-3 upgrade (docs/DEPLOY-PLAN.md), not a
go-live blocker.

---

## Topology

Two supported models — the script defaults to **A**, `SKIP_CADDY=1` selects **B**.

**A. Caddy ON hbox (default, simplest one-command).**
```
  demo.dregg.net (DNS -> hbox public IP)
        │  :443 TLS (Let's Encrypt, auto)
   ┌────▼─────────────── hbox ───────────────────┐
   │  Caddy (system unit, /etc/caddy/Caddyfile)   │
   │        │ reverse_proxy 127.0.0.1:8790        │
   │  dregg-web-games (user unit)  127.0.0.1:8790 │  ← games, board, /health
   │  dregg-games-bot (user unit)  -> Discord     │  ← Descent daily
   └──────────────────────────────────────────────┘
```
Needs hbox reachable on :80/:443 (DNS + port-forward + ufw). hbox `ufw` is currently
**INACTIVE** (OPS-RUNBOOK) — see step (g).

**B. Caddy on the AWS gateway (the OPS-RUNBOOK topology).** The gateway terminates
TLS and reverse-proxies over a WireGuard tunnel to `hbox-wg-ip:8790`; hbox opens NO
public port. Run `deploy-hbox.sh` with `SKIP_CADDY=1` on hbox, and install
`caddy/Caddyfile.games` (retargeted to the wg peer) on the gateway. Stronger security
posture; more moving parts. Choose per ember's audit bar.

---

## Ordered go-live

### (a) DNS — point demo.dregg.net -> hbox  ⟨EMBER⟩
Add an A/AAAA record `demo.dregg.net` -> hbox's public IP (model A) or the gateway's
(model B). Let's Encrypt (model A) needs this resolving + :80/:443 reachable BEFORE
Caddy can issue a cert.

### (b) Place the env / tokens  ⟨EMBER⟩
Copy `deploy/games/.env.example` to hbox and fill the real values:
```bash
# on hbox:
mkdir -p ~/.config/dregg ~/.local/state/dregg-games
cp ~/dev/breadstuffs/deploy/games/.env.example ~/.config/dregg/games.env
$EDITOR ~/.config/dregg/games.env      # DISCORD_TOKEN / DISCORD_APP_ID / BOT_SECRET,
                                        # DESCENT_ANNOUNCE_CHANNEL_ID, DATABASE_URL, bind
chmod 600 ~/.config/dregg/games.env
```
No prod token is ever committed or placed by an agent — this is ember's hand-placement
(same discipline as deploy/hbox/RUNBOOK.md).

### (c) ⚠ STOP THE OLD BOT FIRST  ⟨EMBER⟩
Two bots on one Discord token fire **every command twice**. Stop the previously-running
bot before the hbox games bot starts:
```bash
# graviton (the deploy/aws unit), if it was running the token:
ssh <graviton> 'sudo systemctl stop dregg-discord-bot'      # or disable --now
# or a prior hbox bot (deploy/hbox/RUNBOOK.md's unit):
ssh hbox 'systemctl --user stop dregg-discord-bot'
```
Skip only if you are certain no other process holds this token.

### (d) Run the deploy  ⟨AUTOMATED⟩
```bash
ssh hbox
cd ~/dev/breadstuffs/deploy/games
./deploy-hbox.sh --dry-run     # rehearse — prints every step, no side effects
./deploy-hbox.sh               # build -> snapshot -> install -> reload -> health (+auto-revert)
```
Knobs: `SKIP_CADDY=1` (model B), `SKIP_BOT=1` (web demo only), `AUTO_REVERT=0`,
`HEALTH_TIMEOUT=180`. The script installs the two **user** units (with
`loginctl enable-linger` so they survive logout) and, in model A, the Caddyfile into
`/etc/caddy` + `systemctl reload caddy`.

### (e) Health-check + smoke test  ⟨AUTOMATED gate, then MANUAL smoke⟩
The script's health gate polls `http://127.0.0.1:8790/health` (200 `{"status":"ok"}`).
Then, by hand:
```bash
curl -fsS https://demo.dregg.net/health                 # 200 through Caddy/TLS
```
- Open `https://demo.dregg.net/` — the landing + `/offerings` catalog load.
- Play a game; open `/descent/leaderboard` — the no-cheat board renders.
- Submit a run (`POST /descent/submit`) — it ranks and survives a restart (durable
  sqlite, re-verified by replay).
- In Discord: `/descent play` rolls the daily; confirm the announce channel posts.

### (f) Rollback  ⟨AUTOMATED⟩
A failed health gate **auto-reverts** to the pre-deploy snapshot. Manual:
```bash
./deploy-hbox.sh releases            # list snapshots
./deploy-hbox.sh rollback            # revert binaries to the newest snapshot + restart
./deploy-hbox.sh rollback <stamp>    # to a specific one
```
Take it fully offline instantly:
```bash
systemctl --user stop dregg-web-games dregg-games-bot
# model A: also `sudo systemctl stop caddy` (or remove the demo.dregg.net route)
# model B: ember disables the gateway reverse-proxy route -> public surface gone
```

### (g) Firewall / ports  ⟨EMBER⟩
hbox `ufw` is **INACTIVE** and hbox already listens on `0.0.0.0` for unrelated
services (OPS-RUNBOOK). Before going public:
- **Model A** (Caddy on hbox): allow inbound **:80** and **:443** (Caddy/Let's Encrypt)
  from the public internet; keep **:8790 bound to 127.0.0.1 only** (it is — the unit
  sets `DREGGNET_WEB_BIND=127.0.0.1:8790`); never expose it.
- **Model B** (gateway): open **no** public port on hbox; allow only the WireGuard
  peer / ssh. The gateway holds :443.
- The node's QUIC **:9420** is only relevant if you also run a testnet node here
  (Phase 2) — the games demo is node-free and does not open it.
```bash
sudo ufw default deny incoming
sudo ufw default allow outgoing
sudo ufw allow 22/tcp
sudo ufw allow 80,443/tcp          # model A only
sudo ufw enable
sudo ss -tlnp | grep 8790          # verify: LISTEN 127.0.0.1:8790, NOT 0.0.0.0
```

### (go-live) The flip  ⟨EMBER⟩
With (a)–(g) green and the health gate passed, the demo is live. The go-live decision
— the honest-grade + stranger-usable bar — is ember's, per OPS-RUNBOOK's go-live
checklist.

---

## What is automated vs ember-gated (the honest cut)

| Step | Who |
|---|---|
| build the web + bot binaries | **script** |
| snapshot a rollback point | **script** |
| install user systemd units + enable-linger | **script** |
| validate + install the Caddyfile + reload caddy (model A) | **script** (sudo) |
| health-check `/health` + auto-revert on failure | **script** |
| DNS `demo.dregg.net` -> hbox | ember |
| place `~/.config/dregg/games.env` (tokens) + chmod 600 | ember |
| stop the old bot first (double-fire) | ember |
| open hbox :80/:443 / ufw | ember |
| the go-live decision | ember |

## Caveats (named, once)
- **Two cargo workspaces.** `dreggnet-web` is a root-workspace member (builds into
  `target/`); `dregg-discord-bot` is a **separate, excluded workspace** (sqlx links-
  conflict; `discord-bot/Cargo.toml`) that builds into `discord-bot/target/`. The
  script + the bot unit account for this (the bot's `ExecStart` points at
  `discord-bot/target/release/...`). A plain `cargo build -p dregg-discord-bot` from
  the repo root FAILS — build it from within `discord-bot/`.
- **Rate limiting** is NOT in Caddy core — it needs the `caddy-ratelimit` plugin baked
  into a custom `xcaddy` build (named in `caddy/Caddyfile.games`). Until then, per-IP
  rate limiting is an ember-gated go-live item; the body-size cap (2 MB) is active.
- **Live game sessions are ephemeral** — a restart drops in-progress sessions; the
  Descent leaderboard is durable (sqlite, re-verified by replay on boot).
- The **Descent daily needs egress** to `https://api.drand.sh` (BLS-verified round);
  hbox has egress (OPS-RUNBOOK dry-run).
- One combined `games.env` puts the Discord token in the web server's environment too
  (same box, same user). To isolate, split into two `EnvironmentFile`s and point each
  unit at its own.
