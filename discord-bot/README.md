# dregg-discord-bot

Discord bot for the dregg devnet — custodial cipherclerks, transfers,
explorer, presence attestation, CapTP, governance, queues, names,
federation.

This crate was promoted out of `apps/` and now lives at the workspace
toplevel (`/discord-bot`), as a peer of `node/`, `sdk/`, `app-framework/`
etc. — it is not an app, it is a *consumer of* the canonical dregg
SDK surface.

## Cipherclerk handle

Per-user cipherclerks are backed by the canonical
[`dregg_app_framework::AppCipherclerk`](../app-framework/src/cipherclerk.rs) over
[`dregg_sdk::AgentCipherclerk`](../sdk/src/cipherclerk.rs). Each Discord user is
mapped to a deterministic Ed25519 identity:

```
seed = BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret || discord_user_id)
agent = AgentCipherclerk::from_key_bytes(seed)
cclerk = AppCipherclerk::new(agent, federation_id)
```

The old in-crate `DerivedWallet` (BLAKE3-only "public key", bespoke
cell-id domain) is gone. `/send` and `/tip` submit a canonical
Ed25519-signed `SignedTurn` to `POST /api/turns/submit-signed` (postcard
body) — verified end-to-end against a live node (see
`examples/devnet_transfer_smoke.rs`). The `UserCipherclerk::legacy_secret`
/ `sign_legacy` BLAKE3-MAC path remains only for pre-canonical deployments.

**Federation-id signing domain.** Action signatures are bound to the bot's
configured `FEDERATION_ID`, and the node verifies each action against the
target cell's public key under the executor's federation id. On a **solo**
devnet that id is `blake3(node_operator_pubkey)`; on a **full** federated
devnet it is the configured federation id. The operator MUST set the bot's
`FEDERATION_ID` to match the node's, or every transfer is rejected with
"Ed25519 signature verification failed". A faucet-materialized cell also
needs its real public key (`/api/faucet` with `public_key`), which
`/cipherclerk create` already supplies.

## Slash commands

### Active

- **Cipherclerk**: `/cipherclerk create | balance | address | export`
- **Transfer**: `/send <@user> <amount>`, `/tip <@user> <amount>`
- **Gallery** (apps/gallery): `/gallery list | auctions | bid | mybids`
- **Identity** (apps/identity): `/credential issue | verify | list`
- **Presence**: `/presence status | attest | verify | history` — signed
  proof-of-online attestations usable as dischargeable caveats
- **Status**: `/status`, `/proof verify`, `/metrics`
- **Social**: `/faucet`, `/leaderboard`, `/history`
- **Starbridge dashboard**: `/dregg` opens app cards, buttons, an app picker,
  and modal forms for the checked-in Starbridge identity, nameservice,
  governed-namespace, and subscription flows.
- **Explorer**: `/explorer feed | cell | turn | block | note | proof |
  factory | search | stats | recent | watch | unwatch`
- **CapTP** (bot as capability peer): `/cap-share`, `/cap-accept`,
  `/cap-delegate`, `/cap-list`, `/cap-revoke`
- **Queue** (programmable queues mounted under
  `/discord/<guild>/<name>`): `/queue-create | publish | subscribe |
  status | mount`
- **Governance** (apps/governed-namespace): `/gov-propose | vote |
  status | routes`
- **Names** (apps/nameservice): `/name-register | resolve | whois`
- **Federation**: `/setup-federation`, `/link-cipherclerk`, `/unlink-cipherclerk`

External `/link-cipherclerk` records are pending until ownership is proven.
Hosted `/cipherclerk create` identities remain the only identities the bot can
sign transfers and CapTP management commands for.

### Retired (apps deleted from workspace)

The following commands were removed in the post-relocation cleanup
because their target apps (`amm`, `lending`, `orderbook`, `stablecoin`,
`dao-treasury`, `prediction-market`) are no longer workspace members:

- `/swap`, `/pool`, `/lend supply | borrow | status` — AMM/lending
- `/order buy | sell | cancel`, `/book`, `/trades` — orderbook

Per the project's "improve don't degrade" stance these slash names
were deleted outright rather than left as "not yet ported" placeholder
stubs. If/when these apps return as `starbridge-apps/<name>`, the
commands can be reintroduced against the new endpoints.

## Configuration

Environment variables (see `src/config.rs`):

| Var              | Required | Description                                  |
| ---------------- | -------- | -------------------------------------------- |
| `DISCORD_TOKEN`  | yes      | Discord bot token                            |
| `DISCORD_APP_ID` | yes      | Discord application id (u64)                 |
| `BOT_SECRET`     | yes      | 64 hex chars (32 bytes) — master key seed    |
| `DEVNET_URL`     | no       | defaults to `https://devnet.dregg.fg-goose.online` |
| `DATABASE_URL`   | no       | defaults to `sqlite:bot.db`                  |

## Build

```bash
cargo build -p dregg-discord-bot
```
