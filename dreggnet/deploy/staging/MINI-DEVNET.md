# DreggNet mini-devnet + the Discord bot — runbook

The community-facing slice of staging: a live dregg node, the public Caddy door,
and the **DreggNet Discord bot** — the front door the community uses to open a
per-user channel, drive a Hermes, and see their cells land on the real chain.

This file is the operator runbook: what is live, how the bot is built and
shipped, the single token-drop that takes it live, and the mini-devnet shape.

---

## 1. What is live right now

On the AWS edge box (`i-03365e2bcf4ea08b2`, EIP `34.224.208.52`):

| Piece | State | Reached at |
|---|---|---|
| `dregg-node` (federation size 1, solo) | **healthy** | `:8420` API, `:9420` gossip; `/health` returns `healthy:true` |
| `gateway` (httpe machines API) | up | Caddy `/` (basic-auth) |
| `caddy` (TLS + basic-auth) | up | `:443` (real domain + raw-IP fallback) |
| `headscale` (mesh control + DERP) | up | `headscale.dreggnet.fg-goose.online`, STUN `:3478/udp` |
| `postgres` (durable / billing) | healthy | internal |
| `dreggnet-discord-bot` | **wired, token-gated** | Caddy `/admin*`; live the moment a real `DISCORD_TOKEN` is set |

Node health probe (from the box or over the mesh):

```sh
curl -s http://localhost:8420/health
# {"healthy":true,"federation_mode":"solo","public_key":"70f396…","consensus_live":true,…}
```

The bot is the only piece not yet *connected*, and only because it needs a real
Discord token (the one blocker). Everything else around it is proven (§6).

---

## 2. Build the bot (native linux/amd64 — no cross-compile)

The bot is a member of a **standalone cargo workspace** whose path-deps reach back
into the (huge) breadstuffs root workspace. It is built **natively** on a Linux
box with the full breadstuffs checkout — not cross-compiled. It does **not** need
the Lean kernel archive: the bot signs+submits turns to the node over HTTP and
lets the *node* prove, so we build with `--features dregg-sdk/no-lean-link`
(`dregg-lean-ffi`'s build script then skips the archive link entirely).

On a capable native-Linux box (the reference builder is **persvati**, 24 cores):

```sh
cd ~/dev/breadstuffs/discord-bot
cargo build --release --features dregg-sdk/no-lean-link
# → target/release/dregg-discord-bot   (a self-contained glibc binary:
#   rustls TLS, statically-bundled SQLite, no Lean, no openssl)
```

> The binary is a glibc (gnu) binary. The runtime image base must have glibc
> **>=** the build box's glibc. persvati is glibc 2.42, so `discord-bot/Dockerfile`
> bases on `ubuntu:25.10` (glibc 2.42). Build the binary and the image on the
> same box and there is nothing to worry about.

---

## 3. Containerize + ship to the edge

The bot image is built where the binary was built (the COPY-into-base is trivial,
no Rust), then `docker save`d + loaded onto the edge box — the same shape the
dregg-node image uses.

```sh
# on the build box (persvati), in the breadstuffs checkout:
cd ~/dev/breadstuffs/discord-bot
docker build -t dregg-discord-bot:staging .

# ship to the edge (save → scp → load):
docker save dregg-discord-bot:staging | gzip > /tmp/dregg-bot.tgz
scp -i ~/.ssh/dreggnet-staging.pem /tmp/dregg-bot.tgz ubuntu@34.224.208.52:/tmp/
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@34.224.208.52 \
  'gunzip -c /tmp/dregg-bot.tgz | docker load'
```

Then point the compose service at the loaded ref in `/opt/dreggnet/.env`:

```
DREGG_BOT_IMAGE=dregg-discord-bot:staging
```

(`docker compose config` validates the service; the compose file already carries
the `dreggnet-discord-bot` service + `bot-data` volume.)

---

## 4. Go-live — the single token-drop

The bot **requires** `DISCORD_TOKEN`, `DISCORD_APP_ID`, and `BOT_SECRET`; it exits
1 with a friendly message without them, so until they are set it simply will not
stay up. The non-secret wiring (node endpoint, DB, admin token, Caddy route) is
already in place.

1. Create the Discord application + bot at <https://discord.com/developers/applications>
   → **New Application**. Copy the **Application ID** (General Information) and,
   under **Bot**, **Reset Token** and copy the token. Enable the **Message
   Content Intent** (Bot → Privileged Gateway Intents) — the bot uses it to drive
   Hermes from channel messages.

2. On the edge box, fill the secrets in `/opt/dreggnet/.env` (NOT committed):

   ```sh
   ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@34.224.208.52
   sudo -e /opt/dreggnet/.env     # or append with the values:
   #   DISCORD_TOKEN=<the bot token>
   #   DISCORD_APP_ID=<the numeric application id>
   #   ADMIN_DISCORD_ID=<your numeric Discord user id>
   ```

   `BOT_SECRET`, `ADMIN_TOKEN`, and `DREGG_BOT_IMAGE` are already populated
   (BOT_SECRET + ADMIN_TOKEN were generated with `openssl rand`; keep BOT_SECRET
   stable — it is the seed for every user's deterministic cipherclerk).

3. Bring the bot up:

   ```sh
   cd /opt/dreggnet
   docker compose up -d dreggnet-discord-bot
   docker compose logs -f dreggnet-discord-bot
   ```

   You will see: database connected → node preflight (`node OK: mode=solo …`) →
   bot dregg cell materialized → **HTTP read surface on 0.0.0.0:8080** →
   **`Bot connected as <name>`** → slash commands registered. At that point the
   community can use it.

4. **FEDERATION_ID** (so transfers verify on the solo node). Already set in
   `.env` to the current node's value
   `5ceebd3a8ea48d4f47ace367a1e05ec1aea7d3d97e7ac146002153cf69db4283`
   (= `blake3(node_public_key)`; pubkey
   `70f3967847f789aa62236caff978456e3d32848c295f262edb494611e8d83734`). If the
   node key is ever rotated, the bot logs the new value at startup
   ("Set FEDERATION_ID=<hex> to match") — paste it into `/opt/dreggnet/.env` and
   `docker compose up -d dreggnet-discord-bot` again.

### The OAuth invite URL (add the bot to the Discord server)

Replace `<APP_ID>` with the Application ID. The bot needs `bot` +
`applications.commands` scopes; the permission integer below grants channel
management + messaging + reactions (the per-user semi-private channels):

```
https://discord.com/api/oauth2/authorize?client_id=<APP_ID>&scope=bot%20applications.commands&permissions=2416012368
```

Open it as a server admin, pick the DreggNet server, **Authorize**. (Permission
bits `2416012368`: Manage Channels + Manage Roles — needed to set the per-user
channel permission overwrites — View Channels, Send Messages, Manage Messages,
Embed Links, Read Message History, Add Reactions, Use Slash Commands. Tighten or
widen in the developer portal as desired.)

---

## 5. The admin webportal — behind Caddy

The bot's axum server exposes `/admin` (a server-rendered monitoring dashboard:
users→cells, semi-private channels, recent Hermes verdicts/receipts, cap records).
It is reached through Caddy with **defence in depth**:

1. Caddy `handle /admin*` reverse-proxies to `dreggnet-discord-bot:8080`, behind
   the existing **basic-auth** (ember / pug).
2. The bot's `ADMIN_TOKEN` gates it again underneath (Bearer header or `?token=`).

```sh
# real domain (once DNS + Let's Encrypt are live):
curl -u ember:<pw> 'https://dreggnet.fg-goose.online/admin?token=<ADMIN_TOKEN>'
# raw IP / pre-DNS (self-signed):
curl -k -u ember:<pw> 'https://34.224.208.52/admin?token=<ADMIN_TOKEN>'
```

No `ADMIN_TOKEN` set → the portal returns 404 (disabled). Wrong token → 401.

---

## 6. The mini-devnet shape

```
   community ── Discord ──► dreggnet-discord-bot ──► dregg-node (edge, solo) ──► chain
                                  │                        ▲
                                  └── /admin (Caddy) ──────┘
                          headscale overlay 100.64.0.0/10
   AWS edge box  ◄──────────────── mesh ────────────────►  persvati (compute backend)
   (stable IP, node + gateway + bot)                       (owned-sandbox exec + STARK proving)
```

- **Edge box** — the always-on public face: the `federation-size 1` (solo) dregg
  node, the gateway, Caddy (TLS + basic-auth), headscale, and the bot. Every user
  cell + turn the bot submits lands on **this** node's chain.
- **persvati** — joins the headscale tailnet as the **compute backend** (the heavy
  owned-sandbox lease execution + memory-hungry STARK proving live here, off the small
  edge box). It is **compute, not a second consensus node** today: the edge node
  stays solo (`--federation-size 1`), persvati contributes cycles over the mesh.
  See `deploy/ARCHITECTURE-COMPUTE-BACKEND.md`.
- **Peering option (future).** To make it a true 2-node consensus federation,
  rebuild both nodes with `--federation-size 2` and matching `--node-index 0/1`
  and point their `--gossip-port` peers at each other over the tailnet
  (`100.64.0.x:9420`). Left solo for now — the bot only needs one healthy node to
  serve the community, and solo keeps the federation signing domain simple.

### What the community can do once the bot is live

- **Open a channel** — each user gets a semi-private per-user channel + a
  deterministically derived dregg cipherclerk and **cell** on the edge node.
- **Drive a Hermes** — a channel message becomes a cap-gated, **metered**,
  receipted dregg turn through the proven `ToolGateway`, bounded by the user's own
  cell (the confined per-user agent loop).
- **See cells** — `/explorer`, `/status`, `/history`, `/activity`, the deos
  surface (cap-gated affordances as Discord buttons, transclusion into embeds),
  and the `/admin` dashboard for the operator.

---

## 7. Proven vs. needs ember's real Discord token

**Proven / in place:**
- Bot builds native linux/amd64 (`--features dregg-sdk/no-lean-link`), runtime
  image wraps the binary.
- `dreggnet-discord-bot` service is in the staging compose (`docker compose config`
  validates) with the `bot-data` volume and full env wiring to the live node.
- Caddy routes `/admin*` to the bot behind basic-auth; `ADMIN_TOKEN` underneath.
- The edge dregg-node is healthy; the bot's node preflight + cell materialization
  path is exercised by the dry-token bring-up (it reaches the node and starts the
  HTTP surface before the Discord gateway step).
- A **dry/fake** `DISCORD_TOKEN` brings the container up to the Discord-connect
  step and then fails cleanly on the bad token — proving every layer below Discord.

**The one blocker — ember's real Discord token:**
- The actual Discord gateway connection + slash-command registration needs a real
  `DISCORD_TOKEN` (+ `DISCORD_APP_ID`, and `ADMIN_DISCORD_ID` to pin the admin).
  Drop them in `/opt/dreggnet/.env` and `docker compose up -d
  dreggnet-discord-bot` (§4). That single step takes it live.
