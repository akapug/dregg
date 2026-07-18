# Discord Activities Integration — Design

**Status: DESIGN (2026-07-18). Nothing here is built yet.** The direct parallel of
`docs/TELEGRAM-MINIAPP-DESIGN.md`: serve the SAME `dreggnet-web` arcade as a native Discord
**Activity** (Discord's Embedded App SDK), with Discord OAuth giving a **server-verified Discord
uid** — the analog of Telegram's HMAC-verified initData — deriving the **SAME custodial identity
the Discord bot already uses** (`seed_for(bot_secret, uid)` under `"dregg-discord-bot-v1"`), so
Activity turns land with verified `Attribution::Signed` provenance and the Activity is a clean
in-app place to run the cross-platform **link ceremony** (no browser extension needed).

Facts in this doc are split into **[verified]** (read from Discord's docs / our code on
2026-07-18) and **[needs-testing]** (plausible, unconfirmed until a dev-mode Activity runs).
Ground-truth code read for this design: `dreggnet-web/src/lib.rs` (`CatalogState`,
`catalog_router`, `make_app_parts_with_descent`), `dreggnet-web/src/telegram_miniapp.rs` +
`tg_link_page.rs`, `discord-bot/src/cipherclerk.rs`, `discord-bot/src/config.rs`,
`webauth-core/src/{link_claim,link_registry,challenge}.rs`.

---

## 1. How a Discord Activity works (platform facts)

**The iframe + SDK** [verified]: an Activity is a web app loaded in a sandboxed iframe inside
the Discord client (desktop, mobile, and web). The page talks to the surrounding client
exclusively over `postMessage`, abstracted by the npm package **`@discord/embedded-app-sdk`**
(`new DiscordSDK(CLIENT_ID)` → `await sdk.ready()`; then typed commands + event subscriptions).
The SDK exposes `sdk.instanceId`, `sdk.channelId`, `sdk.guildId`,
`commands.getInstanceConnectedParticipants()` and the `ACTIVITY_INSTANCE_PARTICIPANTS_UPDATE`
event — every user who joins the same launch shares one `instance_id` (this is the multiplayer
join key).

**Launch** [verified]: enabling Activities on the app auto-creates a default **Entry Point
command** ("Launch", type `4` = `PRIMARY_ENTRY_POINT`) surfaced in the **App Launcher** in
chat. Its default handler `DISCORD_LAUNCH_ACTIVITY (2)` makes Discord launch the iframe with no
bot code at all; switching to `APP_HANDLER (1)` lets our existing serenity bot receive the
interaction and respond with the `LAUNCH_ACTIVITY` interaction callback (type `12`) — i.e. any
slash command or button the bot already owns can become a launch surface later.

**The proxy + CSP** [verified]: the iframe is served from
`https://<client_id>.discordsays.com/…` — Discord's proxy (Cloudflare Workers) fronting **URL
Mappings** configured in the Developer Portal (Activities → URL Mappings, `prefix → target
host`; the root mapping `/` → our origin). The iframe's CSP restricts network egress to that
proxy domain: any fetch/script/img to an external origin fails with `blocked:csp`. External
resources must either get their own URL mapping (client code then calls
`/.proxy/<prefix>/…`; the SDK's `patchUrlMappings()` monkeypatches `fetch`/`WebSocket`/XHR to
rewrite them) or be served same-origin. The proxy passes WebSockets; WebRTC/WebTransport are
not supported. Cookies need `SameSite=None; Partitioned` to survive — we deliberately use none
on this surface. [needs-testing]: sources conflict on whether the `/.proxy/` prefix is still
mandatory for non-root mappings (a recent policy change reportedly allows direct paths); our
design sidesteps it by serving **everything same-origin** under the root mapping.

**Identity — the OAuth2 flow inside the Activity** [verified]:

```
client                                server (dreggnet-web)              Discord
──────                                ─────────────────────              ───────
sdk.ready()
sdk.commands.authorize({client_id,
  response_type:'code', prompt:'none',
  scope:['identify']})  ──► consent UI (once per user) ──►  { code }
POST /da/token { code }  ───────────► exchange code + client_secret ──► POST /api/oauth2/token
                                      → { access_token }
                                      GET /api/users/@me (Bearer) ────► { id, username, … }
                                      ← the VERIFIED Discord uid,
                                        from Discord's own API
        ◄── { access_token, ticket, custodial_pubkey_hex }
sdk.commands.authenticate({access_token})   // completes the SDK handshake client-side
```

`authenticate` returns `{ access_token, user{id, username, global_name, avatar, …}, scopes,
expires, application }` — but that response lives in the **client** and is display-only for us,
exactly like Telegram's `initDataUnsafe`. The server's trust root is its OWN exchange +
`/users/@me` round-trip: the uid is asserted by Discord's API to the holder of our
`client_secret`, never by the client.

**The audience trap** [verified, standard OAuth]: if a server ever accepts a client-*presented*
access token instead of exchanging the code itself, it MUST check the token was minted for OUR
application (`GET /oauth2/@me` → `application.id == our client_id`) — otherwise any attacker
who got a victim to authorize a *different* app could replay that token here (confused deputy).
We avoid the class entirely: the server only ever trusts tokens it minted via its own
`client_secret`.

---

## 2. The identity model — the initData analog, made per-request

Telegram hands the page a **self-contained HMAC envelope** (initData) that the server
re-validates statelessly on every request. Discord's OAuth gives no such envelope — verifying
an access token requires a Discord API round-trip. So the server verifies ONCE (at `/da/token`)
and then mints its own stateless envelope, restoring the exact `/tg/*` shape:

**The activity ticket.** After the code exchange proves the uid, the server issues
`ticket = base64url( uid ‖ minted_at ‖ nonce ‖ HMAC_SHA256(ticket_key, uid ‖ minted_at ‖ nonce) )`
with `ticket_key = derive("dregg-discord-activity-ticket-v1", BOT_SECRET)` — domain-separated
from the signing seed and from the link-challenge key. The client attaches it to every
state-touching request in **`X-Dregg-Activity-Ticket`** (a header, never a URL — bearer-like,
never logged; the verified uid + `minted_at` are logged instead). Validation is a pure function
(`validate_ticket_at(key, ticket, now, max_age)`) mirroring `validate_init_data_at`: parse
gates (400) → constant-time HMAC (403) → freshness window + future-skew (403) → only then the
uid, the ONLY trusted Discord identity on the surface. Same refusal taxonomy, same audit emits
(both polarities on one correlation id), same test families (accept vector + every tamper class
named; the fixtures write themselves from the TG suite).

Freshness: default 24 h (`DISCORD_ACTIVITY_TICKET_MAX_AGE_SECS`), matching the Mini App's
session-lifetime argument. Re-auth on expiry is silent for a returning user:
`authorize({prompt:'none'})` re-issues a code without UI once consent exists [verified].

**Honest attestation statement** (unchanged from `/tg`): Discord's OAuth attests the HUMAN
(this uid completed the flow within the window); the server signs the turn with the key it
CUSTODIANS for that human. The signature proves what signatures prove; the ticket gate is what
binds the human to the key on each request. Rung 2 (client-held keys) is the same follow-up as
on Telegram — the verifier (`advance_signed`) does not change.

---

## 3. The SAME custodial identity — and the one extraction it forces

The Activity's verified uid must derive **byte-for-byte the identity the Discord bot already
attributes** (`discord-bot/src/cipherclerk.rs`):

```
seed = BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret ‖ discord_user_id_le)   // seed_for
identity = TurnSigner::from_seed(seed).identity()      // == UserCipherclerk pubkey, hex
```

Same `BOT_SECRET` (the bot's env, `discord-bot/src/config.rs`), same domain string, same
LE-u64 uid bytes → the Activity player IS the in-chat player, exactly as
`telegram_miniapp::identity_for` reuses `TelegramCipherclerk::derive`.

**The extraction**: `dreggnet-web` CANNOT depend on `dregg-discord-bot` — it is an EXCLUDED
workspace (the sqlx `libsqlite3-sys` links conflict named in `dreggnet-web/Cargo.toml`). And a
mirror of `seed_for` is the drift class the TG surface was explicitly built to avoid ("CALLED,
never mirrored"). So the ONE derivation moves into a small root-workspace crate —
**`dreggnet-discord-identity`** (`seed_for`, the domain constant, `op_token` if wanted) — with
`discord-bot` re-exporting it (one impl, two callers, zero identity drift; the
`dreggnet-telegram` pattern, including a parity pin test on both sides). This is the only
change the design makes outside `dreggnet-web`.

Ops coupling, named: `BOT_SECRET` (+ `DISCORD_CLIENT_ID`, `DISCORD_CLIENT_SECRET`) reach the
`dreggnet-web` process — the same shared-credential co-tenancy §2 of the TG design pinned (web
+ bot on one box, one operator, ONE trust domain). The surface mounts iff all are set
(`discord_activity_from_env`, one log line either way), so every existing deployment is
untouched.

---

## 4. Architecture — the `/da` scope beside `/tg`

One new module `dreggnet-web/src/discord_activity.rs` + a static-assets sibling; mounted in
`make_app_parts_with_descent` beside the TG mount, driving the SAME `Arc<CatalogState>` (one
registry, three trust stories, never one handler).

```
GET  /da                                  — Activity shell (static HTML+JS; no auth to serve)
GET  /da/static/{sdk.js, noble-ed25519.js}— vendored pinned bundles (same-origin; see §6)
POST /da/token                            — {code} → OAuth exchange → /users/@me → mint ticket
                                            → { access_token, ticket, custodial_pubkey_hex }
GET  /da/offerings                        — catalog fragment for the VERIFIED viewer (ticket hdr)
GET  /da/offerings/{key}/session/{id}     — validate → ensure_open_as(Asserted ident) → render_for
POST /da/offerings/{key}/session/{id}/act — validate → derive signer → atomic custodial advance
                                            → verified Signed turn (the post_tg_act body, verbatim
                                            shape: ONE HostThread job, floor-read → sign at the
                                            expected counter → advance_signed; no TOCTOU)
GET  /da/link/challenge                   — ticket-authed; challenge + exact claim fields
GET  /da/link                             — the link-ceremony page (platform: "discord")
POST /da/link                             — verify_link_claim → FileLinkStore.record
```

`DiscordActivityState` (the `TgMiniAppState` analog): `{ catalog: Arc<CatalogState>, client_id,
client_secret, bot_secret: [u8;32], ticket_key: [u8;32], max_age_secs }`.

The Rosetta row, for orientation:

| Telegram Mini App | Discord Activity |
|---|---|
| `TgMiniAppState` | `DiscordActivityState` |
| initData (HMAC envelope from Telegram) | OAuth code exchange → server-minted ticket |
| `X-Telegram-Init-Data` | `X-Dregg-Activity-Ticket` |
| `validate_init_data_at` (pure, gate-ordered) | `validate_ticket_at` (pure, gate-ordered) |
| `TelegramCipherclerk::derive` / `seed_for` | `dreggnet-discord-identity::seed_for` |
| `telegram-web-app.js` (external script) | vendored `@discord/embedded-app-sdk` bundle |
| `initDataUnsafe` (display only) | `authenticate` response `user` (display only) |
| bot `web_app` deep-link buttons | Entry Point command / App Launcher (boots `/` root) |
| chat-scoped shared session `tg:{chat}` | instance-scoped shared session `dai:{instance_id}` |
| personal default session `tg-{key}-{ident16}` | `da-{key}-{ident16}` |

The shell differs from `/tg` in three welcome ways: no cold-deep-link special case (the iframe
always boots the root mapping, so the header-less document-GET soft path isn't needed — launch
context arrives as query params/SDK properties instead), no BackButton API (in-page nav only),
and no themeParams (the site's own dark style serves; Discord provides no theme bridge).
Everything else — fragment fetches with the header, the form-submit interceptor rewriting
`/offerings/...` POSTs onto the `/da` twin — is the TG shell script with the header renamed.

**`instance_id` is the multiplayer gift** [verified: shared per launch, participants queryable
+ evented]: a session id `dai:{instance_id}` puts everyone who joined the same launch in the
same seat-claiming session — `tug` (via `seated::SeatedTug`) and `automatafl` (native seats)
become *actually multiplayer in a Discord voice channel* with zero game-crate changes. Ship the
personal-session catalog first; the instance-shared session is the fast follow. (There is
reportedly a server-side "Get Activity Instance" API for validating a claimed instance_id —
[needs-testing]; until verified, treat client-supplied instance_id as an unverified session
*label*, exactly like a `/offerings` session id today, never an identity input.)

---

## 5. The link ceremony in the Activity — the passkey home

`webauth_core::link_claim` was BUILT for this: the canonical message is platform-tagged, the
crate's own tests already exercise `platform = "discord"`, and `verify_link_claim` +
`FileLinkStore` are frontend-agnostic. The server half is `post_tg_link` with three literals
changed (`"discord"`, the uid from the ticket, a `"dregg-discord-link-claim-v1"`-derived
challenge key — note the bot's `/link-prove` already occupies
`"dregg-discord-link-challenge-v1"` for its older deterministic-challenge ceremony; the
Activity uses the nonce'd `webauth_core::challenge` scheme that fixes that ceremony's replay
wound, so a distinct domain string keeps the two auditable apart). Records land in the SAME
`links.tsv` (`DREGG_LINK_DIR`) the bot and `/tg/link` write — a link made in the Activity
resolves on Telegram and vice versa, collapsing Discord-you and Telegram-you into one human via
root key K.

The page is `tg_link_page.rs` restructured for the Activity shell, with its three signing paths
re-graded for the iframe:

- **Passphrase custody** (PBKDF2 + AES-GCM in `localStorage`) — WebCrypto only, no WebAuthn:
  should work in the iframe [needs-testing only for localStorage partitioning — the proxy
  origin `<client_id>.discordsays.com` is stable, so wrapped keys persist per-device].
- **Passkey PRF custody** — WebAuthn in a cross-origin iframe requires the embedder to grant
  `publickey-credentials-get/create` permission policy; whether Discord's iframe does is
  UNKNOWN [needs-testing, the single biggest unknown of the ceremony]. If blocked, the
  passphrase path is the primary and the page says so honestly.
- **Relay (paste a signature)** — always works; zero in-page key handling.

Either way this is a real win over the status quo: the link ceremony gets an in-Discord home
with NO browser extension, matching the Telegram side.

---

## 6. Assets under CSP — vendor, don't map

`tg_link_page.rs` imports `@noble/ed25519@2.1.0` from `esm.sh`; the `/tg` shell loads
`telegram-web-app.js` from `telegram.org`. Inside the Activity iframe both would die with
`blocked:csp` [verified class]. The design's answer is uniform: **no external origins at all**.

- **`@discord/embedded-app-sdk`**: build a pinned single-file browser bundle ONCE (esbuild),
  commit it as a static asset, serve at `/da/static/discord-sdk.js`. `dreggnet-web` has no JS
  build pipeline and this keeps it that way (the alternative — a URL mapping onto esm.sh — adds
  a moving external dependency and the `/.proxy/` ambiguity for zero gain).
- **`@noble/ed25519`**: same treatment for the `/da/link` page (`/da/static/noble-ed25519.js`).
  The `/tg` page can keep its esm.sh import; only the `/da` twin needs the vendored copy.
- Everything else the catalog serves — `crate::STYLE`, sprites (`/sprite/...`), fragments,
  forms — is already same-origin and passes the proxy untouched.

[needs-testing]: inline `<script>` blocks under Discord's iframe CSP. Activities commonly ship
inline bootstrap code and the CSP is documented as a *network* egress policy, so this is
expected to work — but it is exactly the kind of assumption Step 0 (§8) exists to check before
any identity code is written.

---

## 7. What's REUSABLE as-is vs what's NEW

**Reused, unmodified:**
- The whole catalog surface: `CatalogState` / `HostThread` / `OfferingHost`,
  `render_offering_response`, `wants_fragment`, `esc`, `STYLE`, the offering registry (games +
  council + market + the non-game five) — one host, all surfaces.
- The custodial-Signed advance: `TurnSigner::from_seed` + `signed_counter` floor-read +
  `advance_signed` inside ONE host job — `post_tg_act`'s body is the template, status mapping
  and the "verifier refusal here is a server bug" discipline included.
- `webauth_core` entire: `challenge` (ticket freshness could even reuse its shape),
  `link_claim` (already platform-tagged for `"discord"`), `link_registry` (same `links.tsv`,
  cross-platform resolution for free).
- The audit emitter + metrics (`audit.rs`, `metrics.rs`) — new `surface` label values, same
  envelope; the initData accept/refuse two-polarity pattern carries over to the ticket gate.
- The identity derivation itself (`seed_for`) — reused byte-for-byte, just relocated (§3).
- The Signed-attribution seam and verifier — untouched; `act_signed` remains the rung-2 path.

**New to build:**
1. `dreggnet-discord-identity` extraction crate (+ `discord-bot` re-export + parity pin test).
2. `dreggnet-web/src/discord_activity.rs`: `DiscordActivityState`, the pure ticket
   mint/validate pair with its tamper-class test family, `/da/token` (the one outbound HTTP
   call-site in `dreggnet-web` — needs a blocking-safe HTTP client dep for
   `oauth2/token` + `users/@me`), the `/da` routes, the shell page.
3. `/da/link` page variant (vendored noble, ticket header, `"discord"` platform).
4. Vendored JS bundles (SDK + noble), committed pinned.
5. Portal + ops: enable Activities, URL mapping `/` → the serving origin (the hbox
   `tailscale funnel` host), `DISCORD_CLIENT_ID`/`DISCORD_CLIENT_SECRET`/`BOT_SECRET` env into
   the web unit, Entry Point command left at its zero-code default.

---

## 8. Small first step vs the full version

**Step 0 — the empirical probe (near-zero code, high information):** enable Activities on the
dev app, map `/` → the existing funnel origin, launch the EXISTING catalog in the iframe. No
verified identity yet (cookie-`Asserted` attribution, exactly what the public web serves
today). This answers the [needs-testing] pile cheaply and in one afternoon: inline scripts
under CSP, forms/fragments through the proxy, sprites, style, mobile rendering, proxy latency.
No commitment is made until the unknowns are facts.

**Step 1 — the TG-parity milestone (the real deliverable):** §3 extraction + §4 `/da` surface
+ vendored SDK. Exit criterion, same as the Mini App's: a turn landed from inside Discord shows
`Attribution::Signed` under the SAME pubkey `/cipherclerk` shows in-chat, and the move-log +
replay verify agree.

**Step 2 — the link ceremony:** `/da/link` with passphrase + relay paths; passkey-PRF enabled
iff the Step-0/1 device test shows WebAuthn is permitted in the iframe.

**Full version:** instance-shared multiplayer sessions (`dai:{instance_id}` + participants
events for presence), bot-side `LAUNCH_ACTIVITY` buttons on game embeds (serenity support for
callback type 12 — [needs-testing]; the default Entry Point command needs nothing), rung-2
client-held keys via the existing `act_signed` wire, and — once the arcade is worth
discovering — Discord app verification for App Discovery listing (unverified apps run fine in
servers where the app is installed [verified]; discovery/promotion is the only thing gated).

---

## 9. Threat model (what each gate refuses)

- **A forged/absent ticket** → 401/400/403 at the pure validator; no identity derived, no
  session opened, no turn landed (the anti-ghost invariant, TG-identical).
- **A client-claimed uid** (query param, JSON body, the SDK's client-side `user` object) →
  never an identity input on `/da/*`; the only uid is the ticket's, which required our
  `client_secret` round-trip to Discord to mint.
- **A token minted for another app** (confused deputy) → structurally impossible on the main
  path (server-side exchange only); if a client-presented-token path is ever added, the
  `/oauth2/@me` application-id check is mandatory.
- **Replay of a stale ticket** → freshness window + future-skew, same as initData; a stolen
  ticket within its window can drive turns as that user (bearer semantics — identical exposure
  to a stolen initData string; header-only + never-logged is the mitigation, rung 2 the cure).
- **A forged link claim** → `verify_link_claim`'s gates (nonce'd challenge freshness →
  canonical bytes → `verify_strict`), already pinned byte-for-byte by the webauth tests.
- **The Discord proxy itself** sits in the request path (TLS terminates at Discord's edge) —
  named honestly: in-Activity traffic is readable by Discord infrastructure, the same trust
  already extended to Telegram's web-view for `/tg`. Nothing secret rides the wire that Discord
  could not already derive from operating the platform.

## 10. Open questions (the honest ledger)

1. Inline-script CSP + localStorage persistence in the iframe — Step 0 answers.
2. WebAuthn/PRF permission in the iframe — decides the passkey path's fate (§5).
3. `/.proxy/` prefix current policy — moot for us (all same-origin) but should be pinned in
   the setup doc when written.
4. serenity's support for interaction callback type 12 (`LAUNCH_ACTIVITY`) — only blocks the
   *bot-button* launch sugar, not the Activity.
5. "Get Activity Instance" server API existence/shape — gates whether `dai:{instance_id}`
   session labels can be server-validated or stay advisory.
6. Access-token lifetime vs ticket window (Discord tokens run ~7 days; `prompt:'none'`
   re-auth is the assumed refresh) — confirm the silent path on desktop AND mobile clients.
