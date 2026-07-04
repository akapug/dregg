# STRIPE-SETUP — stand up the USD-credit rail (Stripe sandbox)

The end-to-end setup for the **Stripe → conserving-mint** rail: a real signed
Stripe `payment_intent.succeeded` webhook is verified and mirrored into dregg as a
conserved USD-credit cell. This runbook takes a stranger from *nothing* to *a test
payment minted the agent's credit* on a **Stripe sandbox / test-mode** account.

Everything here is the SANDBOX path. The sandbox→live cutover is its own checklist
in [STRIPE-OPS.md](STRIPE-OPS.md#go-live-checklist-sandboxlive); this runbook flags
the one or two places live differs as you reach them.

## What you are wiring

```
  Stripe (test mode)                                    your machine
  ┌────────────────────┐   stripe listen --forward-to   ┌──────────────────────────┐
  │ payment_intent.     │ ─────────────────────────────►│ dreggnet-stripe-receiver │
  │ succeeded  (signed) │      localhost:4242/webhook    │  :4242/webhook           │
  └────────────────────┘                                 │   verify (HMAC-SHA256)   │
        ▲  whsec_…  (the signing secret = the verifying key)    │   → Effect::Mint     │
        │                                                 │   conserved USD-credit   │
   stripe trigger / a real test card                      └──────────────────────────┘
```

The receiver runs **breadstuffs' genuine `dregg-bridge::stripe_mirror`** verify+mint
path — the same `StripeMirrorState` the bridge test suite exercises. The verify is
the real Stripe scheme (HMAC-SHA256 over `"{t}.{body}"`, constant-time compared,
replay-window, amount/currency bounds, consume-once dedup on the payment-intent id).
A forged signature, a stale timestamp, a wrong currency, or a replayed payment is
refused exactly as the substrate refuses it.

- Receiver source: `demo/stripe-receiver/src/main.rs` (a pure-`std` HTTP/1.1 endpoint).
- The verify+mint primitive: `~/dev/breadstuffs/bridge/src/stripe_mirror.rs`.
- The one-shot driver/helper: `demo/stripe-trigger.sh` (`--live` prints the exact CLI).

---

## 0. Prerequisites

- A **Stripe account in test mode** (the sandbox). No real money moves; test cards
  and the CLI's fake events are used throughout.
- The **Stripe CLI** — `brew install stripe/stripe-cli/stripe` (or
  <https://stripe.com/docs/stripe-cli>). Used for `stripe login`, `stripe listen`
  (forwards Stripe → your localhost AND prints the webhook secret), and
  `stripe trigger` (fires a real signed test event).
- A **breadstuffs checkout** at `~/dev/breadstuffs` (override with `BREADSTUFFS_DIR`).
  The receiver links its real `stripe_mirror` from there and reuses breadstuffs'
  warm `target/`, so the heavy dregg crates are not recompiled.
- `openssl` + `curl` (only for the offline fixture path in step 6b).

---

## 1. Get the Stripe test keys

```sh
stripe login           # opens the browser; authorizes the CLI against your account
stripe config --list   # confirms you are pointed at the test-mode account
```

The CLI now holds your **test-mode** API key. You do **not** need to paste a
secret API key into the receiver — the receiver verifies webhooks, it does not call
the Stripe API. The only secret the receiver needs is the **webhook signing secret**
(`whsec_…`), which `stripe listen` mints in the next step.

> **Live note.** In live mode you create a real webhook endpoint in the Stripe
> Dashboard (Developers → Webhooks) and read its `whsec_…` there; the CLI `listen`
> secret is sandbox-only. See the go-live checklist.

---

## 2. Start `stripe listen` — this prints the webhook secret

In a dedicated terminal, point Stripe's event stream at the receiver's endpoint:

```sh
stripe listen --forward-to localhost:4242/webhook
```

It prints, on the first line, the **webhook signing secret** for this session:

```
> Ready! Your webhook signing secret is whsec_xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx (^C to quit)
```

Copy that `whsec_…` value — it is the receiver's **verifying key** (`STRIPE_WEBHOOK_SECRET`).
Leave `stripe listen` running; it is the bridge that forwards every Stripe event to
`localhost:4242/webhook` and signs it the way Stripe's servers do.

> The `whsec_…` from `stripe listen` is **stable per CLI install** — it does not
> rotate every run, but treat it as a secret all the same (it is the key that
> authorizes a mint). Handling: [SECRETS.md](SECRETS.md).

---

## 3. Configure + run the receiver

The receiver reads its config from env. The only **required** var is the secret.

| env var | default | meaning |
|---|---|---|
| `STRIPE_WEBHOOK_SECRET` | — (**required**) | the `whsec_…` from `stripe listen`. The verifying key. (`DREGG_STRIPE_SECRET` is the fixture-mode alias.) |
| `DREGG_STRIPE_PORT` | `4242` | the listen port (must match the `--forward-to` port) |
| `DREGG_STRIPE_CURRENCY` | `usd` | accepted ISO-4217 currency; other currencies are refused |
| `DREGG_STRIPE_MIN_CENTS` | `50` | dust floor — a payment below this is refused (`BelowMin`) |
| `DREGG_STRIPE_MAX_CENTS` | `100000000` | per-payment ceiling — above this is refused (`AboveMax`) |
| `DREGG_STRIPE_ASSET` | `cd…cd` (32×`0xCD`) | hex32 USD-credit issuer-well / token id to mint into |
| `DREGG_STRIPE_NO_CLOCK` | (unset) | if set, skip the replay-window timestamp check (only for replaying an old recorded fixture) |

Build + run it (a second terminal, alongside `stripe listen`):

```sh
# Build into breadstuffs' warm target (reuses the heavy dregg crates):
cd ~/dev/DreggNet/demo/stripe-receiver
CARGO_TARGET_DIR=~/dev/breadstuffs/target cargo build

# Run it with the whsec_… from step 2:
STRIPE_WEBHOOK_SECRET=whsec_xxxxxxxxxxxx \
  ~/dev/breadstuffs/target/debug/dreggnet-stripe-receiver
```

On start it prints its config and the endpoint to point Stripe at:

```
dreggnet-stripe-receiver listening on http://127.0.0.1:4242/webhook
  currency=usd  bounds=[50, 100000000] cents  clock_check=true
  point Stripe at it:  stripe listen --forward-to localhost:4242/webhook
  (every event is verified + minted by the real dregg-bridge stripe_mirror)
```

> **Shortcut:** `demo/stripe-trigger.sh --live` builds the receiver and prints the
> exact `STRIPE_WEBHOOK_SECRET=… <receiver>`, `stripe listen`, and `stripe trigger`
> commands wired together — a copy-paste of steps 2–4 for your own test key.

Health probe (any terminal): `curl -s http://localhost:4242/health` → `{"ok":true}`.

---

## 4. The mint convention — `metadata.dregg_recipient` + amount

A Stripe payment only mints if it carries **which dregg cell to credit**. The
mirror reads it from the payment object's metadata:

- `metadata.dregg_recipient` — the **64-char hex** of the 32-byte dregg `CellId`
  to credit. (Missing or malformed → refused `MissingOrBadRecipient`.)
- `amount` — the cents that cleared (e.g. `2500` = $25.00). Minted 1:1 as
  USD-credit cents, subject to `[min,max]` bounds.
- `currency` — must equal `DREGG_STRIPE_CURRENCY` (`usd`). (Mismatch → `WrongCurrency`.)

The agent sets `metadata.dregg_recipient` when it **creates** the PaymentIntent so
the mirror knows which cell funded itself. The demo recipient is the all-`01` cell:

```
0101010101010101010101010101010101010101010101010101010101010101
```

---

## 5. Fire a test payment

With `stripe listen` (step 2) and the receiver (step 3) both running, fire a real
signed test event from a third terminal:

```sh
stripe trigger payment_intent.succeeded \
  --add payment_intent:metadata.dregg_recipient=0101010101010101010101010101010101010101010101010101010101010101 \
  --add payment_intent:amount=2500 \
  --add payment_intent:currency=usd
```

Stripe creates a genuine test PaymentIntent, fires the signed
`payment_intent.succeeded` webhook, `stripe listen` forwards it to the receiver,
and the receiver runs the real verify+mint.

> A real test **card** works too: any Checkout/Payment using `4242 4242 4242 4242`
> (Stripe's test card) whose PaymentIntent carries the `dregg_recipient` metadata
> fires the same webhook through the same path.

---

## 6. Confirm the conserving mint landed

### 6a. The live path (what step 5 produced)

The receiver prints the mint on stdout:

```
✓ MINTED  2500 cents  →  recipient CellId(0101…0101)
    real kernel effect: Mint { target: CellId(0101…), slot: 0, amount: 2500 }
    agent credit now: 2500 cents  (mirror live_supply=2500, backing=2500)
```

`live_supply == backing` (`2500 == 2500`) is the **conservation invariant** —
circulating USD-credit never exceeds the cents Stripe attested. The HTTP response
body echoes it: `{"minted":true,"amount_cents":2500,"running_credit_cents":2500}`.

Re-fire the **same** event (Stripe retries; it also fires a sibling
`charge.succeeded`). The receiver dedups on the payment-intent id:

```
✗ REFUSED  payment_intent_id already mirrored (double-mint prevented)
```

No second mint — `live_supply` stays `2500`. This is the consume-once nullifier
(`payment_nullifier(asset, payment_intent_id)`) doing its job.

### 6b. The offline self-check (no Stripe account needed)

To prove the whole verify+mint+dedup+forgery-refusal path with zero external
dependencies, run the fixture driver — it self-signs a recorded event the way
Stripe does, POSTs it, then shows a retry deduped and a forgery refused:

```sh
cd ~/dev/DreggNet
demo/stripe-trigger.sh          # fixture mode: offline, real verify+mint
```

Expected tail: `✓ a real signed Stripe event minted conserved USD-credit; a retry
deduped; a forgery refused.`

---

## 7. You're up — what's next

A stranger who has reached here has a working **sandbox** rail: a real signed
Stripe event mints conserved USD-credit to a dregg cell, retries dedup, forgeries
refuse.

- To **operate + monitor** the rail (the conservation invariant on the ops
  dashboard, the refund/dispute workflows, the incident trees, the
  receiver-down/duplicate-mint/breach diagnostics): **[STRIPE-OPS.md](STRIPE-OPS.md)**.
- To go from sandbox to **real money**: the
  [go-live checklist](STRIPE-OPS.md#go-live-checklist-sandboxlive) — live keys, the
  production HTTPS endpoint, and the committed `bridge_mint_against_lock` path that
  replaces the demo receiver's in-process applier (per `docs/MORNING-REVIEW.md`).

## See also

- [STRIPE-OPS.md](STRIPE-OPS.md) — monitor / workflows / incidents / go-live.
- [SECRETS.md](SECRETS.md) — handling the `whsec_…` and other secrets without printing them.
- [OPS-DASHBOARD.md](OPS-DASHBOARD.md) — where the bridge panel surfaces mints + conservation.
- `docs/HACKATHON-DEMO.md` — the earn→pay-Stripe→spend→run story this rail anchors.
- `~/dev/breadstuffs/bridge/src/stripe_mirror.rs` — the verify+mint primitive (the what-is).
