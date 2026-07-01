# SECRETS — the edge `.env`, supplying values, rotation

Where the live secrets live, how to put a value on the box **without printing it**
into a log/history, what the discord secrets are (and the `FEDERATION_ID` that
must match the node), and the rotation lessons — including the one where an
authkey leaked into a committed doc.

**Rule zero: live secrets are never committed.** The repo's `.env.example` is a
template with empty secret fields; the real `/opt/dreggnet/.env` is on the box
only. Every key/password below is regenerated or handed out of band.

## The edge `.env` is root-owned

`/opt/dreggnet/.env` (and the headscale data dir) are **owned by root**, so every
`docker compose …` on the edge is `sudo docker compose …`, and editing the `.env`
needs root:

```sh
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>
sudo -e /opt/dreggnet/.env          # sudoedit — edit in place as root
```

## Supplying a secret without printing it

Don't `echo SECRET=… >> .env` (it lands in shell history and scrollback). Prefer
`sudoedit` (above), or for a value coming from your Mac, **scp a fragment, merge,
shred**:

```sh
# on the Mac — write the line(s) to a temp file (not into a command):
printf 'DISCORD_TOKEN=%s\n' "$TOKEN" > /tmp/frag.env
scp -i ~/.ssh/dreggnet-staging.pem /tmp/frag.env ubuntu@<EDGE_HOST>:/tmp/frag.env
shred -u /tmp/frag.env              # remove the local copy

# on the box — merge into the root-owned .env, then shred the fragment:
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST>
sudo sh -c 'cat /tmp/frag.env >> /opt/dreggnet/.env && shred -u /tmp/frag.env'
cd /opt/dreggnet && sudo docker compose up -d <service>
```

## The discord secrets (the bot go-live)

The bot exits 1 without the first three, so until they're set it won't stay up.
All in `/opt/dreggnet/.env`:

| key | what it is | how to get / generate |
|---|---|---|
| `DISCORD_TOKEN` | the bot token | Discord developer portal → your app → **Bot → Reset Token**. Enable the **Message Content Intent**. |
| `DISCORD_APP_ID` | the numeric Application ID | developer portal → General Information |
| `BOT_SECRET` | 64 hex chars (32 bytes); the **stable seed** for every user's deterministic cipherclerk | `openssl rand -hex 32` — **generate ONCE and keep it stable** (changing it re-derives everyone's identity) |
| `ADMIN_DISCORD_ID` | ember's numeric Discord user id (pins the admin) | right-click your name → Copy User ID (Developer Mode on) |
| `ADMIN_TOKEN` | gates the bot's `/admin` under Caddy (defence in depth) | `openssl rand -hex 24`; unset → `/admin` returns 404 |
| `FEDERATION_ID` | the executor signing domain — **must match the node** (see below) | `blake3(node_public_key)`; the bot logs the right value at startup |
| `DREGG_BOT_IMAGE` | the loaded bot image ref | `dregg-discord-bot:staging` |

Bring it up:

```sh
cd /opt/dreggnet
sudo docker compose up -d dreggnet-discord-bot
sudo docker compose logs -f dreggnet-discord-bot
#   db connected → node preflight (node OK: mode=… ) → cell materialized →
#   HTTP read surface on 0.0.0.0:8080 → "Bot connected as <name>" → commands registered
```

### `FEDERATION_ID` must match the node the bot submits to

`FEDERATION_ID` is the executor signing domain — `blake3(node_public_key)`. If it
is wrong/unset, **transfers fail with an Ed25519 error**. The value depends on
which node the bot points at (`DEVNET_URL`):

- Against the **solo** edge node, it is `blake3(<solo node pubkey>)` — e.g.
  `<FEDERATION_ID>` =
  `blake3(<EDGE_NODE_PUBKEY_PREFIX>…)`.
- Against the **2-node federation**, it is the committee `federation_id`
  (`4cf29683…`, FEDERATION.md).

**If the node key is rotated**, the bot logs the new value at startup
(`Set FEDERATION_ID=<hex> to match`) — paste it into the `.env` and
`sudo docker compose up -d dreggnet-discord-bot` again.

Full go-live runbook (the OAuth invite URL, the permission integer): `deploy/staging/MINI-DEVNET.md`.

## The basic-auth passwords

- **Operator surface** (`dreggnet.example.com`): a single shared bcrypt
  account `operator` in the Caddyfile; plaintext handed out of band. (Doc drift:
  `USING-STAGING.md` lists `ember`/`operator` — the Caddyfile is authoritative.)
- **Ops dashboard** (`ops.dreggnet.example.com`): a **separate** `admin`
  account — a distinct credential so the admin pane isn't reachable with the
  public operator password (OPS-DASHBOARD.md).

Both rotate the same way (the password is **not** an env var — it's bcrypt-hashed
in the Caddyfile):

```sh
sudo docker compose exec caddy caddy hash-password --plaintext '<new>'
# paste the $2a$... hash into the matching block in Caddyfile, then:
sudo docker compose up -d caddy        # (or restart caddy)
```

## Key rotation + the leak lesson

**The lesson:** a live headscale **pre-auth key was once pasted into a committed
doc** (`FABRIC-JOIN.md` / `ARCHITECTURE-COMPUTE-BACKEND.md` carried real authkey
values). Those have since been **scrubbed to placeholders and the keys rotated**.
The standing rule that came out of it:

- **Never commit a live credential** — authkeys, tokens, passwords, private keys.
  Docs carry **placeholders + the regenerate command**, never the value.
- If a secret reaches a commit (or any shared surface), treat it as compromised:
  **scrub the text AND rotate the secret** — scrubbing alone is not enough once
  it's in git history.
- **headscale authkeys:** regenerate on the edge (MESH.md); expire old ones with
  `headscale preauthkeys expire <key>`.
- **`node.key` (a node's Ed25519 identity):** rotating it changes the node's
  public key → changes `federation_id` → needs a committee re-roll (FEDERATION.md)
  and a `FEDERATION_ID` update for the bot. Rotate deliberately, not casually.
- **`BOT_SECRET`:** rotating it re-derives every user's cipherclerk — effectively
  a reset. Keep it stable.

## See also

- MESH.md — minting/expiring headscale authkeys.
- DEPLOY.md — the Caddy blocks the basic-auth lives in.
- FEDERATION.md — `federation_id` derivation + the committee re-roll.
- `deploy/staging/MINI-DEVNET.md` — the full discord go-live.
</content>
