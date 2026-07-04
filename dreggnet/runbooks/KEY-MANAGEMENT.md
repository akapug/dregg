# KEY-MANAGEMENT — the credential lifecycles

Every secret the fabric holds, its lifecycle (generate → store → back up →
rotate), and what rotating each one *costs* (some are free, some force a committee
re-roll). This is the lifecycle companion to `SECRETS.md` (which is where the
secrets *live* on the box + how to put a value there without leaking it).

Three credential families:

1. **Validator keys** (`node.key`) — a node's consensus identity.
2. **Node / bot auth** — the bearer token that gates turn submission.
3. **headscale authkeys** — the mesh join credentials.

**Rule zero (from `SECRETS.md`): live secrets are never committed.** Docs carry the
*regenerate command*, never the value. A secret that reaches a commit or any shared
surface is **compromised** — scrub the text **and** rotate the secret.

---

## 1. Validator key (`node.key`) — the consensus identity

A `node.key` is an **Ed25519 keypair**. The private half is the node's signing
identity (it signs blocks + finalization votes); `blake3(public_key)` is its gossip
`node_id`; the **public** half sits in `genesis.json` and defines the validator's
slot in the committee (and thus contributes to `federation_id`).

### Generate

Two ways:

```sh
# (a) let the node generate one on first run — it writes node.key into its data
#     dir, then read the PUBLIC half back:
curl -s http://localhost:8420/api/node/identity   # → { "public_key": "<hex>", ... }

# (b) generate the whole committee centrally (the re-roll path) — emits
#     node-0..N.key + genesis.json + prints the federation_id:
docker run --rm -v "$PWD/out:/out" dregg-node:staging genesis --validators 5 --output /out
```

> **No standalone `gen-validator-key` subcommand is wired today** (honest TODO).
> The two paths above are how keys come into being: per-node on first run, or as a
> set via `genesis --validators N`. A dedicated `gen-validator-key` would be a nice
> affordance; until it exists, use (a) or (b).

### Where it lives

In the node's **data dir**, as `node.key`:

- node-a / a homelab box: `/var/lib/dregg-node/data/node.key`.
- the edge: under the node-data volume in `/opt/dreggnet` (root-owned — `sudo`).

It sits next to `genesis.json` (the committee) and `dregg.redb` (the ledger). The
key is **identity**, genesis is **committee**, the redb is **ledger** — keep them
straight: only the ledger is disposable (`DISASTER-RECOVERY.md`).

### Back up — this is the one that matters

A backed-up `node.key` turns a lost box into a **non-event**: restore the file,
restart, the identity is intact, no re-roll. Without a backup, a lost key forces a
committee re-roll (`DISASTER-RECOVERY.md` §A). Back up the **private** key
securely, out of band (never to the repo, never to a shared surface):

```sh
# copy node.key + genesis.json to secure offline storage (encrypted at rest):
cp -a data/node.key      ~/secure-backup/node.key.<hostname>
cp -a data/genesis.json  ~/secure-backup/genesis.json
```

Share only the **public** key with the committee (it goes in `genesis.json`); the
private `node.key` **never leaves the box** except to your own secure backup.

### Rotate — costs a committee re-roll

Rotating `node.key` changes the public key → changes `federation_id` → needs a
**static re-roll** (`COMMITTEE-CHANGE.md`) and a bot `FEDERATION_ID` update
(`SECRETS.md`). So **rotate deliberately, not casually** — only on compromise or a
deliberate identity change. The dance:

1. Generate the new `node.key` (above).
2. Re-roll: new `genesis.json` with the new public key replacing the old, new
   `federation_id`, distribute, restart all `--federation-mode full`.
3. Re-point the bot's `FEDERATION_ID` to the new committee id.

If the key is **compromised**, also ensure the old public key is **evicted** from
the committee in the re-roll (don't just add the new one alongside).

---

## 2. Node bearer token — turn-submit auth

Turn submission to the node is gated by a **bearer token** (the node accepts a
signed turn only from a holder of the configured token; read endpoints like
`/status`, `/api/cell/{id}` are open). This is how the **bot** is authorized to
submit on behalf of the community without every user holding node credentials.

### How it works

- The node is configured with a submit token; a submitter presents it as a
  `Authorization: Bearer <token>` on the turn-submit endpoint.
- The **bot holds one** — it is the authorized submitter for the community front
  door. The bot signs each user's turn with that user's deterministic cipherclerk
  key (derived from `BOT_SECRET` — §nothing rotates that casually) and submits over
  the authorized channel.
- Read-only surfaces stay open so the ops dashboard + the portal can observe
  without a credential.

### Lifecycle

Generate a fresh random token, place it in the node config + the bot's `.env`
(`SECRETS.md` §supplying a secret without printing it), restart both:

```sh
openssl rand -hex 32                       # a fresh submit token
# set it on the node (its config/env) AND in the bot's .env, then:
sudo docker compose up -d dregg-node dreggnet-discord-bot
```

> **The exact env var name for the submit token is node-config-specific** — read it
> from the deployed node's config / `.env` rather than assuming; the bot's
> submitter credential is alongside `DEVNET_URL` / `FEDERATION_ID` in
> `/opt/dreggnet/.env`. (Honest TODO: name + document the canonical submit-token env
> var here once confirmed on the box — `SECRETS.md`'s discord table is the current
> source.) Distinct from `ADMIN_TOKEN` (which gates the bot's `/admin` under Caddy)
> and `OPS_ADMIN_TOKEN` (the optional ops app-layer gate).

Rotating the submit token is **cheap** (no re-roll) — just keep the node and the
bot in sync; a mismatch means the bot's submissions are rejected (the bot logs the
auth failure on preflight).

---

## 3. headscale authkeys — the mesh join credential

A pre-auth key authorizes a box to join the headscale overlay
(`tailscale up --authkey=…`). Minted on the edge; **single-purpose, rotate freely.**

### Mint + tag (on the edge — full detail `MESH.md`)

```sh
ssh -i ~/.ssh/dreggnet-staging.pem ubuntu@<EDGE_HOST> ; cd /opt/dreggnet
# reusable, 30-day, tagged to a role at mint time (--user wants the NUMERIC id):
sudo docker compose exec headscale \
  headscale preauthkeys create --user 1 --reusable --expiration 720h --tags tag:compute
```

### Lifecycle + the leak lesson

- **Hand it out of band** — never paste an authkey into chat, a commit, or a doc.
- **Expire after use** for single-use hygiene:
  `headscale preauthkeys expire <key>`.
- **The leak lesson (real):** a live pre-auth key was once pasted into a committed
  doc (`FABRIC-JOIN.md` / `ARCHITECTURE-COMPUTE-BACKEND.md` carried real values).
  Those were **scrubbed to placeholders AND the keys rotated** — because scrubbing
  alone is not enough once a secret is in git history. The standing rule: docs carry
  **placeholder + the regenerate command**, never the value (`SECRETS.md`).
- Rotating an authkey is **free** — it only affects *future* joins; already-enrolled
  nodes keep their WireGuard keys (a node's overlay identity is independent of the
  authkey that admitted it).

---

## Rotation cost summary

| credential | rotate cost | when to rotate |
|---|---|---|
| `node.key` (validator) | **high** — forces a committee re-roll + bot `FEDERATION_ID` update | compromise, deliberate identity change |
| node submit / bot bearer token | low — sync node + bot, restart | compromise, routine hygiene |
| headscale authkey | free — affects future joins only | after every use; on any leak |
| `BOT_SECRET` | **do not** — re-derives every user's identity (a reset) | only on a deliberate community reset |
| basic-auth passwords (`operator`, `admin`) | low — bcrypt in the Caddyfile | routine; see SECRETS.md |

(`BOT_SECRET` and the basic-auth passwords are detailed in `SECRETS.md` — they live
on the box, not in this lifecycle doc, but the rule "generate once, keep stable" for
`BOT_SECRET` is load-bearing: changing it resets everyone's cipherclerk identity.)

## See also

- SECRETS.md — where the secrets live (root-owned `.env`), supplying a value without
  leaking it, the discord secrets table, the basic-auth password rotation.
- COMMITTEE-CHANGE.md — the re-roll a `node.key` rotation forces.
- DISASTER-RECOVERY.md — lost `node.key` recovery; why a backup is the difference.
- MESH.md — minting / expiring headscale authkeys, the overlay map.
- FEDERATION.md — how `node.key`'s public half fixes the `federation_id`.
