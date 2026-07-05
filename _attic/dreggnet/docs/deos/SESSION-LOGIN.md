# DreggNet cap-auth — the SESSION LOGIN contract

_The wire contract a login client (the cipherclerk extension, a CLI, a browser)
implements to sign in to a DreggNet cap-gated surface against `dreggnet-webauth`.
Grounded to `webauth/src/{server.rs,challenge.rs,lib.rs,cred.rs}` at HEAD._

The extension is a **sibling lane**: this document is the exact protocol it codes
its client against. Nothing here needs the extension — the browser login page
(`GET /.dregg-auth/login`) implements the identical protocol as its no-extension
fallback (paste, or one-click when a wallet is injected).

---

## 0. The shape in one paragraph

A DreggNet operator/customer holds a **`dga1_` capability** (an offline-verifiable
ed25519 caveat-chain token — see `webauth/src/cred.rs`) in their wallet, minted by
the control-plane issuer (`dregg-authctl mint-session`, carrying a stable `acct`
subject + the granted caps + a short expiry). To sign in they prove **active
possession** of that capability against a fresh server challenge, and webauth sets
a **session cookie** (the capability itself, HttpOnly/Secure, Max-Age-bounded).
Caddy's `forward_auth` then verifies that session against the required capability
on every request — 2xx admit / 401 / 403. **No password anywhere.**

---

## 1. Endpoints (all under the PUBLIC login base, default `/.dregg-auth`)

Caddy maps `/.dregg-auth/*` to webauth with the prefix stripped, so from the
client's view the paths below are prefixed with the login base
(e.g. `GET https://ops.dreggnet.example.com/.dregg-auth/login/challenge`).

### 1.1 `GET /login/challenge` → the proof-of-possession nonce

Response `200 application/json`:

```json
{
  "challenge": "<base64url(nonce16‖exp8)>.<hex(keyed_blake3_tag)>",
  "not_after": 1782869999,
  "alg": "ed25519-pop",
  "context_hex": "64726567672d776562617574682d..."
}
```

* `challenge` — an opaque, **stateless, server-authenticated** string. The client
  does not parse it; it signs it and sends it back. It self-expires (~120 s).
* `context_hex` — hex of the domain-separation tag
  `dregg-webauth login challenge v1` (`challenge::LOGIN_CHALLENGE_CTX`). The
  client prepends these bytes before signing (see §2).

### 1.2 `POST /login` → present + get a session

Content-Type `application/x-www-form-urlencoded`. Fields:

| field        | required | meaning                                                        |
|--------------|----------|----------------------------------------------------------------|
| `credential` | yes      | the `dga1_…` capability string                                  |
| `challenge`  | PoP mode | the exact `challenge` string from §1.1                          |
| `signature`  | PoP mode | hex of the 64-byte ed25519 signature (see §2)                   |
| `rd`         | no       | post-login redirect path (browser; same-site `/…` only)        |
| `format`     | no       | `json` to force a JSON response (else driven by `Accept`)       |

**Two modes.** With `challenge`+`signature` → **proof-of-possession** (the
extension contract; anti-replay). With only `credential` → **paste fallback** (no
PoP). In BOTH modes, if webauth has an issuer root configured it verifies the
credential's signature **chain** under that root and refuses an expired one before
issuing a session — a forged/foreign/stale token never mints a session.

Response, extension/API (`Accept: application/json` or `format=json`):

```
200 OK
Set-Cookie: dregg_session=<dga1_…>; Path=/; HttpOnly; Secure; SameSite=Lax; Max-Age=86400; Domain=.dreggnet.example.com
{"session":"<dga1_…>","subject":"dregg:<account-id>","expires":1782956399}
```

Response, browser: `302` to `rd` with the same `Set-Cookie`.

Failure: `400` (malformed), `401` (challenge stale/foreign, PoP failed, forged
issuer, expired) — JSON `{"error":"…"}` or an HTML retry page.

### 1.3 `GET /logout` → clear the session cookie (302).
### 1.4 `GET /healthz` → `200 ok` (always open; the compose healthcheck).

---

## 2. The signature (proof of possession)

The client proves it holds the capability's **bearer tail key** — the ed25519 key
whose public half is the credential's last-block `next_pub`
(`Credential::proof_public`), i.e. the key that would sign a further attenuation.

```
message   = LOGIN_CHALLENGE_CTX_bytes ‖ challenge_string_bytes
          = bytes("dregg-webauth login challenge v1") ‖ bytes(challenge)
signature = ed25519_sign(bearer_tail_key, message)          # 64 bytes
```

Send `signature` as 128 lowercase hex chars. webauth verifies it with
`cred::verify_pop(credential.proof_public(), message, signature)`. The wallet
already holds this key (it is the credential's carried `proof_seed`); signing the
challenge is a pure local ed25519 sign, no node round-trip.

**Reference (client side, using the crate):**

```rust
let sig = credential.sign_challenge(&challenge::signing_message(&challenge));
// post credential.encode(), challenge, hex(sig)
```

---

## 3. Presenting the session afterwards

The session is the `dga1_` in the `dregg_session` cookie. A **browser** sends it
automatically (Domain-scoped to the parent, so one login covers every gated
subdomain). A **non-browser client** may present it any of three ways (webauth
checks in this order — `server::extract_credential`):

1. `Cookie: dregg_session=<dga1_…>`
2. `X-Dregg-Credential: <dga1_…>`
3. `Authorization: Bearer <dga1_…>`

On `/auth` webauth answers:

| status | meaning                                                                       |
|--------|-------------------------------------------------------------------------------|
| `200`  | admitted; sets `X-Dregg-Subject: dregg:<acct>`, `X-Dregg-Cap`, `X-Dregg-Auth` |
| `401`  | no / malformed / forged / **expired** / **revoked** session → (re-)login      |
| `403`  | a genuine, live session that **lacks the surface's capability** (re-login won't help) |

**Identity is never client-supplied.** webauth derives `X-Dregg-Subject` from the
verified credential only; Caddy additionally strips any inbound `X-Dregg-*` header
before the `forward_auth` subrequest (`Caddyfile.capauth`
`(dregg_strip_forged_identity)`), so a client cannot forge its subject.

---

## 4. The browser wallet API (optional, for one-click login)

The login page offers one-click sign-in when a wallet injects `window.dregg`:

```ts
window.dregg.presentCredential({ origin: string }): Promise<string>   // → "dga1_…"
window.dregg.signChallenge({ credential: string, challenge: string }): Promise<string>  // → hex sig
```

`signChallenge` MUST sign exactly the §2 message (domain tag ‖ challenge) with the
credential's bearer tail key and return lowercase hex. If only `presentCredential`
is available the page submits the credential without PoP (paste-equivalent).

---

## 5. Where the session credential comes from (issuance)

The wallet's `dga1_` session is minted by the control-plane issuer:

```
dregg-authctl mint-session --seed <issuer-seed> \
  --inception <account-inception-pubkey-hex> --caps ops-admin[,…] --ttl 86400
```

It carries a stable `acct` account id (`webauth/src/account_id.rs`) so re-issuing
(rotation / guardian recovery / a fresh login) yields the **same** subject — the
account and its resources survive. Revoke a leaked session by its **tail**, or an
account wholesale by its **subject**, via `dregg-authctl revoke` →
`DREGG_WEBAUTH_REVOKED` / the revocation file (§ config below). Account key
rotation/recovery happen on the substrate identity cell whose id IS the `acct`
(the depend-on-substrate weld, `docs/ACCOUNT-IDENTITY-WELD.md`).

---

## 6. webauth configuration (env) the deploy sets

| var | meaning |
|---|---|
| `DREGG_WEBAUTH_ROOT_PUBKEY` | issuer pubkey every session verifies under (REQUIRED; unset ⇒ every cap check denies) |
| `DREGG_WEBAUTH_HOST_CAPS` | `host=cap,…` fallback cap map (the `forward_auth ?cap=` wins) |
| `DREGG_WEBAUTH_COOKIE_DOMAIN` / `_LOGIN_BASE` / `_COOKIE_NAME` | cookie scope, public login base, cookie name |
| `DREGG_WEBAUTH_SESSION_TTL` | session default expiry + cookie Max-Age cap (default 24h) |
| `DREGG_WEBAUTH_CHALLENGE_KEY` / `_CHALLENGE_TTL` | challenge MAC key (share across replicas) + lifetime |
| `DREGG_WEBAUTH_REVOKED` / `_REVOKED_FILE` | the revocation deny-set (tails and/or `dregg:` subjects) |
| `DREGG_WEBAUTH_BREAK_GLASS` | operator override (`X-Dregg-Break-Glass`); **CLEAR at cutover** or it is not really cap-auth |

---

## 7. Turning cap-auth ON (the redeploy flip)

Nothing here changes the live box. The flip is:

1. Ship the runtime image containing `dreggnet-webauth` (already the compose
   `webauth` service, `expose: 8099`, internal-only — never host-published).
2. Set `DREGGNET_CADDYFILE=./Caddyfile.capauth` in `deploy/staging/.env` (the
   hardened forward_auth generation) and `docker compose up -d caddy webauth`.
3. **Clear `DREGG_WEBAUTH_BREAK_GLASS`** so break-glass is not left on.
4. Bootstrap: `dregg-authctl keygen` → set `DREGG_WEBAUTH_ROOT_PUBKEY`; mint an
   operator session; log in once at `https://ops.…/.dregg-auth/login`.

Rollback is a one-line revert of `DREGGNET_CADDYFILE`.
