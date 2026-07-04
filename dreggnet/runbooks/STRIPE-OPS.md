# STRIPE-OPS — operating the USD-credit rail (Stripe mirror)

The operational runbook for the **Stripe → conserving-mint** rail: how to monitor
it, the per-event workflows (payment / refund / dispute), the incident diagnostics
(symptom → diagnose → cause → fix → escalate), and the sandbox→live checklist.

This is the doing-companion to [STRIPE-SETUP.md](STRIPE-SETUP.md) (which stands the
rail up) and to `docs/MONITORING.md` §2b (what the bridge signals *mean*). The
conservation invariant here is the same one [INCIDENT-RESPONSE.md §5](INCIDENT-RESPONSE.md)
pages on — this runbook is the Stripe-specific deep dive.

## The rail in one breath

```
  Stripe payment clears ─► signed webhook ─► verify (HMAC) ─► Effect::Mint ─► $DREGG-credit cell
                                                  │
                            consume-once nullifier(asset, payment_intent_id)  ← at-most-once mint
                            invariant:  live_supply ≤ total_verified_payments  ← conservation
```

**The core safety property:** circulating USD-credit (`live_supply`) never exceeds
the cents Stripe attested as cleared (`total_verified_payments`). A breach is a
**critical money bug** — halt first, investigate second.

Trust model (honest): this is a **trusted-oracle** mirror. dregg trusts that a
valid `Stripe-Signature` means *Stripe said this payment succeeded*; it does not
independently verify the card network. The webhook secret is the verifying key; the
payment-intent id is the replay nonce. Full threat model:
`~/dev/breadstuffs/bridge/src/stripe_mirror.rs` (the trust-model header) +
`docs/RED-TEAM-FINDINGS.md` (BR-1/BR-2/BR-3).

---

## 1. Monitor the rail

### What to watch

| signal | healthy | where |
|---|---|---|
| **conservation** | `live_supply ≤ total_verified_payments` (per asset) | ops Bridge panel / receiver stdout |
| **mints** | each verified payment → exactly one mint | ops Bridge panel `mints_observed`, node event feed |
| **double-mint rejected** | a counter that *rises* (the gate working) — never a *successful* double-mint | relayer status (when configured) |
| **receiver reachable** | `/health` → `{"ok":true}` | `OPS_STRIPE_RECEIVER_URL` probe |

### The ops dashboard Bridge panel

The single pane is `dreggnet-ops` (the admin dashboard,
[OPS-DASHBOARD.md](OPS-DASHBOARD.md)). Its **Bridge** tab (`ops/src/bridge.rs`,
rendered by `ops/src/render.rs`) observes the Stripe mirror in three tiers:

1. **Node-derived activity (always on).** Mint/burn kernel effects from the node's
   committed-event feed — `mints_observed`, `last_mint_at`, recent activity. This is
   live-readable today without any extra config. (Honest gap: the events feed carries
   a mint's *kind* but not its *amount*.)
2. **Conservation + double-mint (`OPS_BRIDGE_URL`).** When a relayer status endpoint
   is configured, it serializes the `StripeMirrorState` — `total_verified_payments`,
   `live_supply`, the `conserved` flag, the double-mint-rejected count. **Absent →
   conservation is reported `un-observed`, never a false all-clear.**
3. **Receiver reachability (`OPS_STRIPE_RECEIVER_URL`).** A plain `GET` to the
   receiver's `/health`. Stripe-receiver-down shows as `stripe_reachable: false`.

Read it:

```sh
# the Bridge slice of the aggregated snapshot (the admin pane — OPS-DASHBOARD.md):
curl -fsS -u admin:<pw> https://ops.dreggnet.example.com/api/snapshot \
  | jq '.bridge'
#   → { configured, stripe_reachable, ledgers:[{rail:"stripe", live_supply,
#       locked_or_backing, conserved, ...}], mints_observed, conservation_ok,
#       conservation_observed, breach_detected, double_mint_rejected, notes }
```

Configure the Stripe legs on the ops container (compose env, `docs/MONITORING.md`
§env-table):

```
OPS_STRIPE_RECEIVER_URL=http://<receiver-host>:4242/health   # receiver liveness
OPS_BRIDGE_URL=http://<relayer-host>:<port>/status           # conservation source (when a relayer is wired)
```

### The admin portal History

The webapp admin portal's economy/compute **History** view shows the minted
USD-credit landing in cells over time (the user-facing companion to the operator
Bridge panel). For the raw kernel truth, read the node event feed directly:

```sh
curl -s http://100.64.0.1:8420/api/events \
  | jq '[.[] | select(.kind|test("mint|bridgemint|burn"))]'
```

### The receiver's own line

When you run the receiver directly (sandbox), every event prints its disposition on
stdout — the cheapest live monitor:

```
✓ MINTED  2500 cents → recipient CellId(0101…)   (mirror live_supply=2500, backing=2500)
✗ REFUSED  payment_intent_id already mirrored (double-mint prevented)
✗ REFUSED  no v1 signature matched the body (forged or wrong secret)
```

`live_supply == backing` after each mint is conservation holding.

---

## 2. Workflows

### A payment comes in (the happy path)

1. Agent creates a Stripe PaymentIntent with `metadata.dregg_recipient=<hex32 cell>`
   and the amount (cents).
2. Payment clears → Stripe fires a signed `payment_intent.succeeded` (and a sibling
   `charge.succeeded`) → forwarded to the receiver's `/webhook`.
3. Receiver runs the real `stripe_mirror`: verify HMAC → check currency / `[min,max]`
   bounds → derive `payment_nullifier(asset, payment_intent_id)` → mint **once**.
4. `Effect::Mint { target, slot:0, amount }` credits the cell; `live_supply +=
   amount`, `total_verified_payments += amount`. Conservation holds (Σδ=0).
5. The sibling `charge.succeeded` and any Stripe retries share the payment-intent id
   → deduped, no double-mint.

Verify it landed: STRIPE-SETUP.md §6, or the Bridge panel `mints_observed` ticks +
the History view shows the credit.

### A refund

A Stripe **refund** does *not* automatically un-mint — the mirror mints on
`payment_intent.succeeded`/`charge.succeeded` only; it does **not** subscribe to
`charge.refunded`. The minted USD-credit is already circulating in dregg.

Operationally, a refund is a **burn** of the corresponding credit:

- The honest current state: the receiver is mint-only (verify→mint). There is no
  automatic refund→burn wired. A refund therefore requires an operator burn of the
  refunded cell's credit to keep `live_supply` tracking the true backing.
- The burn primitive exists in the substrate (`Effect::Burn`, the self-redeem /
  cap-gated split — see the supply model in breadstuffs). A refund→burn relayer is
  the named follow-up (it belongs with the committed `bridge_mint_against_lock`
  go-live path, below; track it in HORIZONLOG).
- Until that is wired: when Stripe issues a refund, **record it** (the
  payment-intent id, the cents) and burn the matching credit so the Bridge panel's
  `live_supply` does not over-state the real backing. Do not leave a refunded
  payment's credit circulating silently.

> Why mint-only is safe today: minting strictly *under* the attested backing keeps
> the invariant `live ≤ backing` true. A refund makes the real backing *smaller*, so
> until the burn lands, `live_supply` can transiently exceed the *true* (post-refund)
> backing even though the recorded `total_verified_payments` still includes it. Treat
> an un-burned refund as a conservation drift to reconcile, not a silent loss.

### A dispute (chargeback)

A `charge.dispute.created` (chargeback) is the adversarial case — the payer claims
the payment was not theirs. Like a refund, the mirror does not auto-handle it.

- **Freeze first.** A dispute means the backing for that payment is *contested*. Do
  not let the credit be spent onward while it is in dispute. If the credit cell is
  still funded, treat it as suspect.
- **Record** the dispute (payment-intent id, amount, reason) against the original
  mint receipt.
- **On a lost dispute** (funds reversed by Stripe), the backing for that payment is
  gone — burn the corresponding credit (same mechanism as a refund) to restore
  `live_supply ≤ true backing`. If the credit was already spent, that is a realized
  loss to escalate (loop ember) — the trusted-oracle leg failed for that payment.
- **On a won dispute**, no action — the mint stands.

> Disputes and refunds are the two ways the *trusted oracle* (Stripe) retracts an
> attestation after the fact. The mint path is at-most-once and conserving; the
> retract path (burn-on-refund/lost-dispute) is the named operational follow-up that
> the go-live committed path must carry. Until then, reconcile manually and never let
> contested credit be spent.

---

## 3. Incident diagnostics

Symptom → diagnose → cause → fix → escalate. The receiver returns HTTP `200` even on
a refusal (so the Stripe CLI does not spin on retries) — the disposition is in the
JSON body + on stdout, so **read the receiver log / response body**, not the HTTP code.

### 3.1 A webhook signature fails (`SignatureMismatch`)

**Symptom.** `✗ REFUSED  no v1 signature matched the body (forged or wrong secret)`
on every event; nothing mints.

**Diagnose.** Almost always the **wrong webhook secret**, not an attack.

```sh
# Is the receiver's secret the SAME whsec_… that stripe listen is currently using?
echo "$STRIPE_WEBHOOK_SECRET"          # the receiver's
# compare against the line stripe listen printed: "Your webhook signing secret is whsec_…"
```

**Causes + fix.**

- **Stale secret.** `stripe listen` was restarted, or the receiver was started with
  an old `whsec_…`. Fix: copy the current `whsec_…` from the running `stripe listen`
  into `STRIPE_WEBHOOK_SECRET` and restart the receiver (STRIPE-SETUP.md §2–3).
- **Body re-serialization.** The HMAC is over the *exact raw bytes* Stripe sent. If
  anything between Stripe and the receiver re-serializes the JSON (a proxy, a
  body-parsing middleware), the signature breaks. Fix: the receiver must verify
  against the **raw body** — it does (`process_webhook` reads `Content-Length` bytes
  verbatim); ensure nothing upstream rewrites the body.
- **A genuine forgery.** If the secret is correct and the body is untouched, a
  refusal means someone POSTed an unsigned/wrongly-signed event — the gate working.
  No mint happened (the refusal *is* the protection). Note it; escalate only if
  sustained/targeted.

**Escalate** only if the secret + raw-body are verified correct and refusals
continue — that points at a Stripe-side or middleware bug. A single forgery refusal
is not an incident; it is the design.

### 3.2 A duplicate mint / a payment minted twice (`DuplicatePayment`)

**Symptom.** Either you see `✗ REFUSED  payment_intent_id already mirrored` (the gate
working — **not** an incident), OR `live_supply` rose by *more* than a payment's
worth (a real double-mint — an incident).

**Diagnose.** The consume-once nullifier is
`payment_nullifier(asset, payment_intent_id)`. Stripe deliberately re-delivers and
fires sibling events; deduping on the payment-intent id is **load-bearing**.

- **The refusal is normal.** A retry, or the sibling `charge.succeeded`, sharing the
  payment-intent id is *supposed* to be refused. `live_supply` unchanged → healthy.
- **A real double-mint** (live_supply over-rose) means the nullifier gate was
  bypassed — e.g. **two relayer processes each with their own in-RAM `seen_payments`
  cache**. The in-RAM set is a per-relayer *fast-reject cache*, **not** the global
  authority. The authoritative gate is the committed `note_nullifiers` set
  (`dregg_turn::executor::bridge_ledger`), reached via the committed
  `bridge_mint_against_lock` path. The demo receiver's in-process applier is
  single-owner (a sequential accept loop), so it cannot double-mint *itself*; two
  receivers against the same asset *could* without the committed gate.

**Fix.** Run **one** receiver per asset in the sandbox (it is single-owner by
construction). For multi-relayer / production, route mints through the committed
`bridge_mint_against_lock` (go-live checklist) so the global `note_nullifiers` set is
the at-most-once authority regardless of how many relayers race the same payment.

**Escalate** a *real* double-mint (live_supply over-rose) immediately — it is a
conservation breach (§3.4), money loss.

### 3.3 A payment did not mint (refused for a non-signature reason)

**Symptom.** `✗ REFUSED  <reason>` where reason is not a signature mismatch.

**Diagnose by the reason string** (`StripeMirrorError`):

| reason | cause | fix |
|---|---|---|
| `no valid metadata.dregg_recipient cell id` | the PaymentIntent had no / malformed `dregg_recipient` | the agent must set `metadata.dregg_recipient=<64-hex cell>` at PaymentIntent creation (STRIPE-SETUP.md §4) |
| `payment currency X != mirror currency usd` | currency mismatch | fire `usd` (or set `DREGG_STRIPE_CURRENCY` to match) |
| `amount below the mirror minimum` | amount < `DREGG_STRIPE_MIN_CENTS` (default 50) | charge ≥ the dust floor, or lower the floor |
| `amount above the per-payment maximum` | amount > `DREGG_STRIPE_MAX_CENTS` | governance / raise the ceiling deliberately |
| `webhook timestamp too old: …` | the event's `t=` is outside the 5-min replay window | clocks skewed, or replaying an old recorded fixture → set `DREGG_STRIPE_NO_CLOCK` *only* for fixtures, never live |
| `unhandled Stripe event type: …` | not `payment_intent.succeeded` / `charge.succeeded` | expected — the mirror mints only on those two; ignore |

**Escalate** only if a *valid* payment (right metadata, currency, bounds, fresh
timestamp) is refused — that is a receiver/substrate bug.

### 3.4 A conservation breach (`live_supply > total_verified_payments`) — PAGE

**Symptom.** The Bridge panel shows `conservation_ok: false` /
`breach_detected: true` (`dreggnet_ops_bridge_conservation_ok == 0`), or the receiver
shows `live_supply` exceeding `total_verified_payments`. More USD-credit circulates
than Stripe attested.

**This is the critical case — STOP MINTING FIRST, then investigate** (same protocol
as [INCIDENT-RESPONSE.md §5](INCIDENT-RESPONSE.md)):

```sh
# 1. HALT the mint side — stop the receiver / relayer process so no further mint
#    draws against unbacked payments:
#    (kill the dreggnet-stripe-receiver process / its unit)

# 2. capture evidence — the minted side from the node's committed-event feed:
curl -s http://100.64.0.1:8420/api/events \
  | jq '[.[] | select(.kind|test("mint|bridgemint|burn"))]'

# 3. snapshot the mirror conservation quantities (when a relayer status is wired):
curl -s "$OPS_BRIDGE_URL/status" | jq   # total_verified_payments vs live_supply
```

**Diagnose.** Compare the minted side (kernel mints) against the verified Stripe
payments (`total_verified_payments`). A genuine `live_supply > backing` confirms it.
Likely causes: a double-mint that bypassed the committed nullifier gate (§3.2,
multiple relayers without `bridge_mint_against_lock`), or an un-burned refund/lost
dispute inflating `live` relative to *true* backing (§2). The committed
`note_nullifiers` gate makes a double-mint *supposed to be* impossible — a real
firing is a kernel/relayer bug, not a known-latent issue (BR-2/BR-3 are fixed in the
bridge crate, `docs/RED-TEAM-FINDINGS.md`).

**Escalate immediately** — a real conservation breach is money loss. Freeze the
receiver/relayer, preserve all mint receipts + the Stripe payment record, loop ember,
treat as a CRITICAL security incident.

### 3.5 The receiver is down (`stripe_reachable: false`)

**Symptom.** Bridge panel `stripe_reachable: false`; `stripe listen` shows delivery
failures (connection refused); payments clear on Stripe but no mint lands.

**Diagnose + fix.**

```sh
curl -s http://localhost:4242/health        # → {"ok":true} if up; refused if down
# is the process alive? is the port bound?  (sandbox: it's a foreground process)
```

- **Process died / not started.** Restart it (STRIPE-SETUP.md §3). It is a single
  sequential accept loop — restart is safe and stateless across the *committed* gate
  (the in-RAM `seen_payments` cache is rebuilt; the authority is committed state).
- **Port mismatch.** `stripe listen --forward-to localhost:<port>` must match
  `DREGG_STRIPE_PORT`.
- **No data lost — Stripe retries.** Stripe re-delivers failed webhooks for up to ~3
  days. Once the receiver is back, the queued events arrive and mint; the nullifier
  dedups any that partially landed. **Bring it back up; do not panic about the gap.**

**Escalate** only if it will not stay up (a crash loop) — capture the stderr and
treat as a receiver bug.

### Escalation summary

| symptom | first move | page? | escalate when |
|---|---|---|---|
| signature fails | check the `whsec_…` matches `stripe listen` | no | secret+raw-body correct, still failing |
| dup-mint refusal | confirm it's the gate (live_supply unchanged) | no | a *real* double-mint (→ breach) |
| `live` over-rose | **halt minting**, capture receipts | **yes** | always — money loss |
| valid payment refused | read the reason string | no | a correct payment is refused |
| receiver down | restart; Stripe retries fill the gap | no | crash loop |

---

## 4. Go-live checklist (sandbox → live)

The sandbox proves the path; live moves **real money**. Per `docs/MORNING-REVIEW.md`
(the Stripe reviewed-go entry), this is the deliberate cutover.

- [ ] **Live API context.** Switch the Stripe account to **live mode**. Create a
      real webhook endpoint in the Dashboard (Developers → Webhooks) pointed at your
      production URL; the `stripe listen` CLI secret is sandbox-only.
- [ ] **Live webhook secret.** Read the live endpoint's `whsec_…` from the Dashboard
      and set `STRIPE_WEBHOOK_SECRET` from it. Handle it like any live secret
      ([SECRETS.md](SECRETS.md) — the root-owned `.env`, never printed, never
      committed). Rotate on the live endpoint, not via the CLI.
- [ ] **Production endpoint behind TLS.** The webhook endpoint must be a public
      HTTPS URL terminated by Caddy ([DEPLOY.md](DEPLOY.md)). The demo receiver is a
      plaintext localhost `:4242` listener — front it with the edge's TLS, or move
      the verify+mint behind the production gateway. Stripe will not deliver to plain
      HTTP in live mode.
- [ ] **The committed mint path, not the demo applier.** The demo receiver applies
      the mint **in-process** (a single-owner RAM `StripeMirrorState`). For real
      money, route through the **committed `bridge_mint_against_lock`** path
      (`verify_payment` → `dregg_turn::executor::bridge_ledger::bridge_mint_against_lock`),
      so the global committed `note_nullifiers` set — not a per-relayer in-RAM cache —
      is the at-most-once authority. This is the SOUND multi-relayer path: any number
      of relayers / webhook retries may race one payment and exactly one wins.
- [ ] **Refund / dispute handling wired.** Land the `charge.refunded` /
      `charge.dispute.created` → burn relayer (§2) before live volume, so a retracted
      Stripe attestation un-mints its credit. Until then, reconcile manually and
      freeze contested credit.
- [ ] **Conservation observed, not un-observed.** Wire `OPS_BRIDGE_URL` to the live
      relayer status so the Bridge panel actually *observes* conservation (live ≤
      backing) and `bridge_conservation_breach` can page — not silently `un-observed`.
      Set `OPS_STRIPE_RECEIVER_URL` to the live receiver's `/health`.
- [ ] **Bounds reviewed.** Confirm `DREGG_STRIPE_MIN_CENTS` / `DREGG_STRIPE_MAX_CENTS`
      for live amounts; above `MAX` is refused by design (governance gate).
- [ ] **Red-team review re-read.** `docs/RED-TEAM-FINDINGS.md` (BR-1/BR-2/BR-3) — the
      trusted-oracle leg, the forgeable-lock and once-vacuous-conservation fixes — is
      the live threat model. The verify+mint code is the same in sandbox and live; the
      money is what changes.

## See also

- [STRIPE-SETUP.md](STRIPE-SETUP.md) — stand the rail up (keys, secret, run, test).
- [INCIDENT-RESPONSE.md](INCIDENT-RESPONSE.md) §5 — the cross-rail bridge-breach first-responder tree.
- [OPS-DASHBOARD.md](OPS-DASHBOARD.md) — the admin pane the Bridge panel lives in.
- [SECRETS.md](SECRETS.md) / [KEY-MANAGEMENT.md](KEY-MANAGEMENT.md) — the `whsec_…` lifecycle.
- `docs/MONITORING.md` §2b — the coin-bridge panel + the `bridge_*` alert definitions.
- `docs/MORNING-REVIEW.md` — the Stripe reviewed-go entry (the go-live decision).
- `docs/RED-TEAM-FINDINGS.md` — the bridge threat model (BR-1/2/3).
- `~/dev/breadstuffs/bridge/src/stripe_mirror.rs` — the verify+mint primitive (the what-is).
