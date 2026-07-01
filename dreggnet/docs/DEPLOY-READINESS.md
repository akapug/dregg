# DreggNet — Deploy Readiness: live-vs-built, auth posture, ordered plan

_Audited 2026-06-30 (read-only on the live edge `<EDGE_HOST>` + the repos). No
live restarts/edits were made. Image dates are UTC from `docker images`; commit
times are the repo's `git log`. The node-a rebuild was left undisturbed._

---

## 0. TL;DR verdict

- **Is it password-protected?** YES for every operator/admin/gateway surface. The
  live public web (`:443`) answers `401` on the raw IP and every sensitive vhost
  sits behind HTTP **basic-auth** (two distinct bcrypt passwords: `operator` for the
  operator/gateway surface, `admin` for the ops dashboard). The public
  portal and `*.example.com` sites are intentionally open read-only; the custodial
  `/api/op` is hard-`403`'d on the public portal.
- **Is cap-auth (webauth) the live default?** NO. The live edge runs the older
  **basic-auth** Caddyfile (dated Jun 29). The `webauth` forward-auth service is
  **built in the repo but not deployed** — there is no `webauth` container on the
  box. The census flag "webauth not the live default" is CONFIRMED; the live
  reality is not even break-glass-webauth, it's plain basic-auth.
- **Is the cipherclerk extension wired to live login?** NO. The extension is a
  real turn-signing wallet that talks to a **node** (`/api/turns/submit-signed`),
  not to the webauth cap-account login. There is no `dga1_`/forward-auth login
  path in the extension, and its default node URL (`devnet.dregg.example.com`)
  is not a vhost the live edge serves.
- **Anything wide open?** No sensitive HTTP surface is reachable unauthenticated
  from the internet. One defense-in-depth gap: the node's `:8420` API is published
  on the host as `0.0.0.0:8420` (bypasses Caddy), but the AWS security group
  filters it — externally it times out (`000`), only loopback answers (`200`).
- **The gap in one line:** almost everything built THIS SESSION (the wired
  gateway, the autonomous provider, console/status/landing, cap-auth default, the
  attach hosting, the bot rebuild) is **NOT on the box**. The live runtime images
  are Jun-29; the session's wire-up commit is Jun-30 19:32 UTC — the live gateway
  predates it by ~1.5 days. Only the **node** was rebuilt to Jun-30 (`n5`).
- **Single biggest blocker to going fully live:** a **reviewed-go redeploy** of the
  edge — ship the session's runtime image (wired gateway + provider + console +
  status + landing + webauth) and swap the live Caddyfile from basic-auth to the
  repo's `forward_auth` (webauth) Caddyfile. Everything else is downstream of that
  one edge action. It is gated on an ember/reviewed-go decision + finalizing n=5.

---

## 1. What is ACTUALLY live (edge `<EDGE_HOST>`, `docker ps` @ ~2026-06-30 21:00 UTC)

| Service (container) | Image | Built (UTC) | State | Exposure |
|---|---|---|---|---|
| **dregg-node** | `dregg-node:n5` | **2026-06-30 17:24** | Up 3h, healthy | `0.0.0.0:8420` tcp + `0.0.0.0:9420` udp (SG-filtered ext) |
| **discord-bot** | `dregg-discord-bot:staging` | **2026-06-29 07:29** | Up 4h | internal `:8080` (via Caddy) |
| **gateway** | `dreggnet-runtime:staging` | **2026-06-29 07:33** | Up 7h, healthy | internal `:8080` only |
| **ops** | `dreggnet-runtime:staging` | 2026-06-29 07:33 | Up 7h, healthy | internal `:8090` |
| **dreggnet** (cli sidecar) | `dreggnet-runtime:staging` | 2026-06-29 07:33 | Up 7h | `sleep infinity` |
| caddy | `caddy:2` | 2026-06-22 | Up 7h, healthy | `0.0.0.0:80`, `0.0.0.0:443` |
| postgres | `postgres:16-bookworm` | — | Up 7h, healthy | internal `:5432` |
| headscale | `headscale/headscale:stable` | — | Up 7h | `0.0.0.0:3478/udp`, `127.0.0.1:8080` |
| obs: grafana | `grafana:11.3.0` | — | Up 7h, healthy | **`127.0.0.1:3000`** |
| obs: prometheus | `prom/prometheus:v2.55.1` | — | Up 7h, healthy | **`127.0.0.1:9090`** |
| obs: alertmanager | `prom/alertmanager` | — | Up 7h, healthy | **`127.0.0.1:9093`** |
| obs: node-exporter / blackbox / json-exporter / alert-sink | — | — | Up 7h | internal only |

**NOT running (built in repo, absent on the box):** `webauth`, `provider` (the W3
autonomous provider loop), `landing`, `status`, `console`, `attach`/`agent-host`.

**The node (`n5`):** `run --federation-size 5 --federation-mode full` with peers
over the tailnet (`100.64.0.2..4:9420`), `--enable-faucet`. `DREGG_FINALITY_GATE=0`
(**finality gate OFF**), `DREGG_PROVE_TURNS=0` (proving off). `n5` is a Jun-30
rebuild (newer than `n4`/`staging`, both Jun-29), but it predates the session's
later gateway wire-up and is **not** the still-compiling node-a rebuild.

### Built-this-session vs actually-deployed (the blunt gap)

The session's serving-stack work landed in commits from **Jun-30 15:32 UTC
onward** (`1c5be35` gateway trust-rail wire-up → … → `ad77752`). **Every runtime
image on the box (`dreggnet-runtime:staging`, `dregg-discord-bot:staging`) was
built Jun-29** — a day-and-a-half before the wire-up. Therefore:

- **Gateway = the OLD, UN-WIRED gateway.** The live `dreggnet-runtime:staging`
  (Jun-29 07:33) predates `1c5be35` "wire the LEASE-1a trust rail LIVE" (Jun-30
  19:32). The funding/guard/provider wire-up is **not** in the running binary.
- **Bot = stale Jun-29.** Matches the flagged "stale 06-29".
- **ops + cli sidecar = stale Jun-29** (same image as the gateway).
- **Node = Jun-30 `n5`** — the only component rebuilt this session, but not the
  freshest (node-a is compiling a newer one).
- **provider / console / status / landing / webauth / attach = never deployed.**

---

## 2. The REAL auth posture (live `/opt/dreggnet/Caddyfile`, dated Jun 29 09:00)

The live Caddy config is the **basic-auth** generation. External probes confirm it
is enforcing: `https://<EDGE_HOST>/` → **401**, `http://…:80/` → **308**
(redirect to https).

| Route / vhost | Auth on the LIVE box | Verdict |
|---|---|---|
| `portal.example.com` (static portal + `/pkg` wasm LC) | none (public read-only, by design) | OK |
| `portal…/api/*`, `/observability/*` → bot read surface | none (public read-only) | OK |
| `portal…/api/op` (custodial signing) | hard **`403`** on the public portal | OK (belt+suspenders) |
| `*.example.com` (published minisites) | none (publish was the cap-gated step) | OK by design |
| `dreggnet.example.com` (gateway machines API + bot `/admin`) | **basic-auth `operator`** (+ bot `ADMIN_TOKEN` under `/admin*`) | Protected |
| `ops.dreggnet.example.com` (ops `:8090`) | **basic-auth `admin`** (2nd, distinct cred) | Protected |
| `grafana.dreggnet.example.com` | Grafana's own admin login (no Caddy gate) | Protected (app-level) |
| `headscale.…` | none at Caddy (Noise + preauth keys) | OK by design |
| raw-IP fallback `<EDGE_HOST>` / `localhost` | **basic-auth `operator`** (except `/portal-preview/*`) | Protected |

**Nothing sensitive is unauthenticated on the public HTTP interface.** Prometheus,
Alertmanager, Grafana, and the headscale control API are bound to **loopback**
(`127.0.0.1`) — reachable only via SSH tunnel, not the internet.

### The one open flank — node `:8420` bound host-wide

`docker-proxy` publishes the node as `0.0.0.0:8420` (and `0.0.0.0:9420/udp`),
i.e. it bypasses Caddy and the basic-auth gate entirely. In practice the **AWS
security group blocks 8420 inbound** — an external `curl` (from my laptop *and*
from the box hitting its own public IP) times out (`000`), while `localhost:8420`
answers `200`. So the node API is **not internet-reachable today**. But the host
bind is `0.0.0.0`, not loopback/overlay, so it is unauthenticated to anything that
reaches the host on 8420 (a future SG change, a co-tenant, a misconfig). The
finality gate is also OFF (`DREGG_FINALITY_GATE=0`). **Finding:** bind the node
API to the loopback/tailnet (`127.0.0.1`/`100.64.x`) and reach it via Caddy/overlay
instead of publishing `0.0.0.0:8420`; the P2P `9420/udp` is the only port that
needs to be public.

### webauth / break-glass

The repo's INTENDED `deploy/staging/Caddyfile` uses `forward_auth webauth:8099`
(cap-auth via `dga1_` dregg capabilities) on `console`/`ops`/`grafana`/the
operator + gateway-admin surfaces, with `DREGG_WEBAUTH_BREAK_GLASS` as an override.
**None of that is live** — the box runs basic-auth and has no `webauth` container.
So the census flag is accurate and, if anything, understated: the live posture is
basic-auth, and the webauth-with-break-glass generation was never deployed. When
webauth IS deployed, the break-glass override must be cleared before it is called
"cap-auth as default" (it admits without a credential — `webauth/src/lib.rs:85`).

---

## 3. Cap-auth + the cipherclerk extension

**The extension (`breadstuffs/extension`, "Dragon's Egg Cipherclerk", MV3
Chrome+Firefox) is a real, well-built turn-signing wallet — but it is NOT wired to
the live cap-account login.**

What it does: named Ed25519 identity profiles (BIP39 recovery, PBKDF2+AES-256-GCM
at rest, auto-lock), authorization-first `signTurnV3` (renders every effect before
releasing a signature, nonce-bound confirm popup), submits the `SignedTurn`
envelope to a **node** via `POST /api/turns/submit-signed`, and tails the node's
`GET /api/events/stream` SSE for receipts.

What it does NOT do (the gap to "log in to the live cloud with the wallet"):

- **No cap-account login flow.** There is no `dga1_` forward-auth / `.dregg-auth`
  / `/login` / webauth call anywhere in `extension/src`. The wallet signs *turns
  to a node*; it does not mint/present a `dga1_` capability to a `forward_auth`
  gate to get admitted to console/ops/gateway. The "sign a `dga1_` credential and
  authenticate to the live webauth forward-auth end-to-end" flow is **not built
  into the extension**.
- **Its default endpoint isn't the live edge.** Default node URL is
  `https://devnet.dregg.example.com` (`extension/settings-script.js`) /
  `https://${devnetDomain()}` — a domain the live edge Caddy does not serve.
- **And even if it did, webauth isn't deployed** (see §2), so there is no live
  `forward_auth` for a `dga1_` cap to authenticate against.

**Gap to "log in to the live cloud with the wallet extension":** (a) deploy
`webauth` + swap in the `forward_auth` Caddyfile; (b) add a cap-account login flow
to the extension (mint/present a `dga1_` cap to `/.dregg-auth/login`, hold the
session cookie webauth sets); (c) point the extension at a real live domain that
the edge serves. Today the wallet↔node signing path is real; the wallet↔cloud
login path is not.

---

## 4. Ordered deploy plan — getting THIS SESSION's work live

Gate legend: **NOW** = deployable immediately (built, green) · **n5** = gated on
finalizing the n=5 federation · **KEY** = needs a secret/key (Hermes / Stripe /
Discord) · **RG** = **reviewed-go** live-edge action (a human-reviewed redeploy /
config swap on the box) · **EMBER** = an ember product/policy decision.

**Critical path (do in order):**

1. **[RG] Build + ship the session's runtime image to the edge.** Cross-build
   `dreggnet-runtime` at HEAD (`dev`, `ad77752`) so the box gets the **wired
   gateway** (`1c5be35`), **provider** (W3 autonomous loop), **console**,
   **status**, **landing**, and the **cli** — all one image. This closes the
   biggest live-vs-built gap. _Gated on: a reviewed-go redeploy; the same
   Lean-capable builder story as the node._
2. **[RG] Deploy `webauth` + swap the live Caddyfile to the `forward_auth`
   generation** (`deploy/staging/Caddyfile`). This makes **cap-auth the default**.
   Precondition: **clear `DREGG_WEBAUTH_BREAK_GLASS`** so break-glass is not left
   on (else it is not really cap-auth). Add the `console`/`status`/`landing`
   vhosts on `example.com`. _Gated on: RG + a decision to cut over from
   basic-auth._
3. **[RG] Rebuild the bot** (currently stale Jun-29) from HEAD and reload; keep it
   token-gated (below). Also re-point its read-surface routes if §1 changes.
4. **[NOW/RG] Ship the freshest node** once the node-a rebuild finishes
   (supersede `n5`). Fold in the `:8420` bind hardening (loopback/tailnet, not
   `0.0.0.0`) as part of the same compose edit.

**Parallel / independent:**

- **[KEY] Discord bot go-live** — requires `DISCORD_TOKEN` / `DISCORD_APP_ID` /
  `ADMIN_DISCORD_ID` / `BOT_SECRET` (all present in the live `.env` today, so the
  bot is already running; a rebuild just needs them to stay set).
- **[RG/EMBER] SSH-attach hosting (`agent-host` sshd) + portal web attach
  (`attach`).** Built this session (`405e7a5`, `32d76ae`) and already hardened
  (`1602c00` killed the forgeable break-glass; `ad77752` forbids raw shell on the
  key-holding host until per-tenant OS isolation). **The `attach` vhost is
  commented out in the repo Caddyfile** pending the header-strip discipline
  (`deploy/staging/Caddyfile:201-234`). _Gated on: RG + the per-tenant isolation
  ember-decision before exposing raw-shell attach._
- **[KEY/EMBER] Billing (Stripe) + any Hermes-key surfaces** — gated on the
  respective keys and an ember go decision; not on the critical path to "live".
- **[n5] Finality gate ON** (`DREGG_FINALITY_GATE=1`) + optionally
  `DREGG_PROVE_TURNS=1` (needs t3.medium+ RAM) — gated on finalizing the n=5
  federation and choosing an audit-grade posture.
- **[NOW] cipherclerk extension → live login** — see §3(a-c). The extension itself
  can be pointed at a live domain now; the end-to-end cap-login needs webauth live
  (step 2) plus a login flow added to the extension (EMBER: is that in scope?).

**Single biggest blocker:** step 1+2 — a **reviewed-go edge redeploy** that ships
the session's runtime image and cuts Caddy over from basic-auth to webauth
`forward_auth`. Until that one action, the wired gateway, the provider, console,
status, landing, and cap-auth-as-default are all built-but-dark, and the extension
has no live cap-login to authenticate against.

---

## 5. Findings summary

1. **Live serving stack is ~1.5 days stale of the session's work** — the gateway
   on the box predates the trust-rail wire-up; provider/console/status/landing/
   webauth were never deployed. (§1)
2. **Auth IS on** — basic-auth on all operator/admin/gateway surfaces, ops behind a
   second distinct password, monitoring on loopback. Public portal is
   intentionally read-only; `/api/op` is `403`'d. (§2)
3. **Cap-auth is NOT the live default** — basic-auth is; `webauth` isn't deployed.
   (§2)
4. **cipherclerk is a real node-signing wallet, not a cloud-login client** — no
   `dga1_`/forward-auth flow, default endpoint isn't the live edge. (§3)
5. **Node `:8420` is bound `0.0.0.0`** (Caddy-bypassing); saved today only by the
   AWS SG. Rebind to loopback/tailnet. Finality gate is OFF. (§2)
