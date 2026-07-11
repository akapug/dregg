# x402: a distribution surface, not a model (assessment + verdict)

*2026-07-11. Written after reading the v2 spec + reference impls (`~/src/x402`,
`coinbase/x402`, Apache-2.0). Prompted by a suggestion that x402 is "well aligned"
with dregg. Verdict: engage only as a thin compatibility face, deferred — do NOT
adopt its model.*

## What x402 actually is

An open standard (Linux Foundation as of 2026-04, backed by Coinbase + Cloudflare,
MCP integration) for paying for an HTTP resource / tool-call. Three layers:

- **Types** — `PaymentRequirements` (scheme, network, amount, asset, payTo,
  maxTimeoutSeconds, extra), `PaymentPayload`, `SettlementResponse`, `VerifyResponse`.
- **Logic** = *scheme × network*. Schemes: `exact` (pay an exact amount), `upto`
  (pay up to a max, settle the actual — metered), `batch-settlement`. Networks are
  CAIP-2 (`eip155:8453`, `solana:…`; non-blockchain allowed, e.g. `ach:us`).
- **Transport** — HTTP (also MCP, A2A).

Flow: server returns `402` + an `accepts[]` array → client signs a scheme-specific
authorization (for `exact` EVM: an **EIP-3009 `transferWithAuthorization`**, gasless —
the payer signs, the *facilitator* submits and pays gas) → a **facilitator** runs
`POST /verify` then `POST /settle`, broadcasts the transfer, returns a tx hash. A
Bazaar (discovery marketplace of monetized resources) sits on top.

The load-bearing fact: **the facilitator is an explicitly *trusted* third party** —
the spec says resource servers "delegate blockchain operations to *trusted* third
parties." Settlement is a plain, public on-chain transfer; the receipt is a tx hash
you trust the facilitator to have produced honestly.

## Why it is technically *behind* what dregg already has

On every axis that matters, dregg is strictly more capable:

| Axis | x402 | dregg (already built) |
|---|---|---|
| Settlement trust | trusted facilitator + a tx hash | proof-carrying receipt (a verified turn); trust no one |
| Privacy | fully public transfers | shielded pool — payer/amount hidden |
| Custody | non-custodial by convention (facilitator submits) | non-custodial by construction + conservation/non-amplification proven |
| Metering (`upto`) | scheme sketch | the metered ToolGateway (`calls_made`), shipped |
| Batch (`batch-settlement`) | scheme sketch | the ring / intent settlement engine, with atomic proof |
| Verification | none (re-query the chain, or trust) | the whole verification backend (light clients, settlement proofs) |

There is nothing to *learn* from x402: the HTTP-402 framing is a UX convention,
CAIP-2 is standard addressing, and the gasless signed-authorization pattern dregg
already has (the payer authorizes, a relayer submits the turn).

## The only legitimate reason to engage: distribution

x402 is not a technical advance; it is a *coordination* win. Its value to dregg is
purely that it may become the default doorway agents, servers, and MCP tools use to
pay. If it reaches critical mass and dregg does not speak it, dregg's superior
settlement is an island the ecosystem cannot reach.

## The correct posture (if/when adoption warrants)

Identical to the interop adapters (`INTERCHAIN-ADAPTERS-DESIGN.md`): **speak the
interface, keep the internals.** dregg would put out a thin **x402-compatible face**
— a *facilitator* (`/verify`, `/settle`, `/supported`) whose settle runs a dregg turn
and returns a proof-carrying (optionally private) receipt, plus a CAIP-2 dregg
*network* exposing `$DREGG` / shielded-pool assets as an x402 `asset`. dregg would be
"the trustless, private facilitator" *in* x402 — the same "don't trust, prove" edge
the Hyperlane ISM / LayerZero DVN apply to messaging, aimed at the payment layer.
This is a thin adapter over primitives that already exist; it does **not** change
dregg's model.

Composable roles, most-dreggic first: (1) proof-carrying + private **facilitator**
(the only role no competitor can fill); (2) a dregg **network + scheme** (the `$DREGG`
rail — any x402 server accepts it by adding the network to `accepts[]`); (3) map the
`upto` / `batch-settlement` schemes onto dregg's existing metered / ring primitives;
(4) table-stakes: dregg services become 402-charging resource servers and dregg
agents become x402 clients (ecosystem + Bazaar interop).

## Verdict: deferred, low priority

Note it and move on. Do NOT pull focus from the real frontier (batch-STARK →
proof-bound settlement, the light clients) to chase a weaker standard, and do NOT
compromise dregg's model to match it. Revisit only if x402 demonstrably becomes the
dominant agent-payment interface — at which point the thin facilitator/network
adapter above is the whole play, and it stays thin.

## CoinVoyage (the product that prompted this)

A closed, non-custodial cross-chain payment *orchestrator* that chains existing
providers (Uniswap/Jupiter/Cetus AMMs, CCTP, ChangeNow), tracked by webhooks, with
"trust the backend to refund on failure" and no proofs — i.e. the trusted-aggregator
model dregg exists to replace. Not a technical fit at any layer. The most it could
ever be is a merchant-facing frontend that routes buyers to pay a dregg merchant
(a channel), never an integration. It supports x402, which is the only reason it
surfaced here; engage with the *standard*, never the product.
