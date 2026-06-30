# Acme Test-as-a-Service — the autonomous business you can audit

One agent runs a tiny automated service business: a customer pays it, it runs the
customer's test job, it pays the vendors (compute / SaaS) it used, it forks a
sub-agent to scale — and the **entire P&L is one cryptographic receipt chain you
can re-verify yourself, offline, trusting no host**.

Built on [`dregg-agent`](../) — the open-source (AGPL), substrate-only,
cap-bounded / budget-bounded / receipted autonomous-agent runtime. No cloud, no
private control plane.

## Run it (one command)

```sh
bash demo/business.sh
```

That's it. It builds once, then runs the five beats with narrated banners, writes
`demo/run.json` (the P&L), re-witnesses the whole run, and shows a tampered line
caught. **Deterministic and offline by default** (a recorded brain + a recorded
signed webhook) — no API key, no network, so it always films cleanly. Fits in
well under three minutes.

## What the judge sees, beat by beat

1. **EARN** — a customer pays Acme. A recorded, **genuinely signed** Stripe
   `payment_intent.succeeded` webhook is verified the real Stripe way
   (HMAC-SHA256 over `{t}.{body}`, replay window, currency/amount bounds) and
   mints conserved, receipted USD-credit. A **retry is deduped**; a
   **forged-signature** webhook is **refused**.
2. **FUND** — the minted cents become the agent's budget ceiling (USD-cents
   denominated). Earned money is now spendable: the P&L loop is closed.
3. **OPERATE** — the agent (an OpenAI-compatible "Hermes/Nemotron" brain, on the
   recorded transport here) runs the customer's test suite. The verdict is bound
   into the receipt with a witnessed `(command · code_root · result)`, so a forged
   "tests passed" is caught on re-witness.
4. **SPEND** — the agent pays its vendors via the **budget-gated, variable-amount
   Stripe-out spend tool** (`stripe_pay`) — the differentiator primitive. Each
   spend's dollar amount is **drawn from the budget cell**, so two spends succeed
   and an **over-ceiling spend is refused in-band, before any money moves**. The
   budget is a theorem about the cell, not a watchdog.
5. **SCALE** — `deploy_subagent` forks a sub-agent with an **attenuated budget +
   a narrower cap bundle** it provably cannot exceed: an over-budget spend AND an
   out-of-bundle call are both refused (no-amplify, both axes).
6. **PROVE** — `dregg-agent-business verify run.json` re-witnesses the WHOLE P&L
   offline: the earn mint chain, the agent + sub-agent receipt chains, the
   witnessed QA, and the P&L arithmetic — host untrusted. Then we tamper one line
   (`--tamper` flips a spend amount) and the proof **rejects it** (`BadSignature`).

## The `run.json` P&L

```jsonc
{
  "business": "Acme Test-as-a-Service",
  "earn":     { "minted_cents": 5000, "events": [...], "receipts": [ /* signed mint chain */ ] },
  "agent_run":    { /* OPERATE + SPEND: one signed receipt chain */ },
  "subagent_run": { /* SCALE: attenuated, bounded */ },
  "pnl": { "earned_cents": 5000, "vendor_spend_cents": 3000, "ops_metering_cents": 2,
           "net_cents": 1998, "budget_cents": 5000, "headroom_cents": 1998 }
}
```

Every figure is recomputable from the chains; `net = budget − consumed = the
un-drawn headroom` (the hard bound on everything the agent *could* still have
done).

## Upgrade to a live model (`--live`)

The brain drives **any OpenAI-compatible endpoint**. With a key present, point it
at a real model — the demo does **not** depend on it (the recorded path is the
filmable default):

```sh
# NVIDIA Nemotron 3 Ultra (free key from build.nvidia.com):
export NVIDIA_API_KEY=nvapi-...
bash demo/business.sh --live

# or the Nous Portal (Hermes):
export NOUS_PORTAL_KEY=...
target/debug/dregg-agent-business run --live \
  --llm-base http://127.0.0.1:8645/v1 --llm-model hermes-agent
```

The `--live` path is behind the `live-brain` cargo feature (the script enables it
automatically). The BYO key reaches only the provider's `Authorization: Bearer`
header — never a request body, a receipt, the report, or a log. If no key is set,
`--live` falls back to the offline path with a notice.

## Verify it yourself

```sh
target/debug/dregg-agent-business verify demo/run.json          # re-witness (green)
target/debug/dregg-agent-business verify --tamper demo/run.json # one line flipped → caught
```

Nothing in the demo claims more than the code runs: the verify logic (Stripe
signature, receipt chains, witnessed re-execution, budget bound) is genuine; only
the *transport* is recorded (the signed webhook fixture and the brain transcript)
so the filmed run is deterministic.
