# Intents as the app-communication layer

Apps in dregg coordinate by posting **declarative intents** that get matched,
solved, and **atomically settled** — not by bespoke point-to-point wiring. An app
(or a user through an app) does not call another app and hand it value. It states
what it offers and what it wants; a solver matches the posted intents into a ring;
and the ring settles all legs or none, with conservation (Σδ=0) proven across every
participating app cell.

This document grounds what the intent machinery already is, why it was never wired
to apps, the design for apps-communicate-via-intents, and the prototype that closes
the gap.

## What the intent system is (grounded)

Two layers exist today, both real, neither connected to an app's `CellProgram`.

**The ring solver + verified settlement** (`intent/src/solver.rs`,
`intent/src/verified_settle.rs`). The matching/settlement core:

- `ExchangeSpec { offer_asset, offer_amount, want_asset, want_min_amount, … }`
  (`solver.rs:24`) — a declarative "I have X, I want Y".
- `IntentNode { intent_id, exchange, creator, expiry }` (`solver.rs:38`) — a posted
  intent in the solver graph, anchored to an anonymous `CommitmentId`.
- `RingSolver::solve_best(&[IntentNode], now) -> Option<RingTrade>` (`solver.rs:440`)
  — Johnson's-algorithm cycle detection (bounded ring size) that finds a ring A→B→…→A
  where each party's offer covers the next party's want. Produces
  `RingTrade { participants, settlements: Vec<Settlement>, score }` (`solver.rs:52`).
- `Settlement { from, to, asset, amount }` (`solver.rs:62`) — one transfer leg.
- `settle_ring_verified(k0, &[VerifiedLeg]) -> Result<VerifiedLedger, _>`
  (`verified_settle.rs:311`) — folds each leg through the verified per-asset
  transition `rec_exec_asset` (`verified_settle.rs:281`), **all-or-nothing** (any
  rejected leg aborts the whole ring — `LegRejected`), then **asserts conservation
  per touched asset** (`verified_settle.rs:340`, the Lean `settleRing_conserves`).
  On native builds each leg is also cross-checked against the real Lean executor
  export `dregg_record_kernel_step` and any drift fails closed.

**The trustless engine** (`intent/src/trustless.rs`). `TrustlessIntentEngine`
(`trustless.rs:893`) wraps the solver in a 7-layer protocol: threshold-encrypt
intents → consensus batch boundary → threshold decrypt → open solver competition →
STARK proof of solution validity → challenge window with bond slashing → atomic
settlement. `finalize_verified()` (`trustless.rs:1640`) lowers the winning rings to a
`SealedTurn` and runs them through `settle_fulfillment_verified`. This engine lives
in the **node** (`node/src/state.rs`) and is exposed over HTTP
(`POST /intents/trustless/submit`, `/share`; `GET …/status`).

## Why it was never wired to apps

The census is blunt: **zero `CellProgram` apps post an intent or act as a solver.**
The reasons are structural, not incidental:

1. **The on-ramp is the node, not the app.** The only way to reach the intent
   machinery is the node's HTTP surface. An app's `CellProgram` has no in-process
   call to "post an intent" or "be a solver". The trustless engine's full ceremony
   (threshold keys, decrypt shares, bonds, challenge windows) is node/federation
   infrastructure — far too heavy to be an app's coordination primitive.

2. **`RingTradeParticipant` is a bare trait with no coordinator.**
   `app-framework/src/ring_trade.rs` defines the trait an app implements —
   `exchange_offers() -> Vec<ExchangeSpec>`, `settle_leg(&Settlement)`,
   `rollback_leg(&Settlement)` — but **nothing ever called it.** There was no glue
   that collects participants' offers, drives the `RingSolver`, runs
   `settle_ring_verified`, and dispatches `settle_leg`/`rollback_leg` atomically. The
   trait was the half of a handshake whose other half was never written.

3. **Apps coordinate imperatively instead.** The shipped cross-app path is
   `invoke()` (`app-framework/src/invoke.rs`) — single-cell method dispatch that
   desugars to a `Transfer`/`SetField` against ONE cell. Useful, but it is
   point-to-point and imperative: an app must already know the exact cell, method,
   and effect. There was no declarative, multi-party, atomically-settled lane.

So the gap was exactly one missing object: a **coordinator** that turns posted
`RingTradeParticipant` offers into a solved, verified, atomically-settled ring —
the lightweight app-layer counterpart to the node's heavyweight trustless engine.

## The design: apps communicate via intents

The shape is three moves — post, match, settle — with refusal atomic at every step.

**Post.** An app exposes a declarative affordance by implementing
`RingTradeParticipant`. `exchange_offers()` returns the `ExchangeSpec`s the app
currently offers (gallery slots for credits, compute for tokens, a bounty payment
for fulfillment). The app's anonymous ring identity is a `CommitmentId` whose low
byte indexes the verified ledger cell.

**Match.** A `RingCoordinator` (`app-framework/src/ring_trade.rs`) collects every
participant's posted offers into `IntentNode`s and asks `RingSolver::solve_best` to
find a ring. No ring → atomic refusal (`CoordinationError::NoMatch`), nothing
settled. This is the declarative inversion: no app named another; the solver
discovered the coincidence of wants.

**Settle.** The coordinator projects the matched ring's `Settlement`s onto
`VerifiedLeg`s (the same `from.0[0]`/`to.0[0]`/asset/amount projection the verified
path uses) and runs `settle_ring_verified` **before touching any app**. This proves
Σδ=0 across every asset the ring moves. Only then does the coordinator drive each
touched app's `settle_leg`. If any app cannot honor its leg, every leg already
applied is rolled back (`rollback_leg`, reverse order) — `ParticipantFailed`,
all-or-none.

```text
 App A (Gallery)          RingCoordinator              App B (Patron)
   |  exchange_offers() -----> [intent nodes] <----- exchange_offers()  |
   |                            RingSolver.solve_best                    |
   |                                 | RingTrade (A→B slot, B→A credits) |
   |                       settle_ring_verified (Σδ=0, all-or-nothing)   |
   |   <---- settle_leg(slot) ------ | ------ settle_leg(credits) --->   |
   |        (rollback all on any leg failure — atomic refusal)          |
```

The coordinator owns no value. Value lives in the apps' cells; the coordinator only
matches posted intents and drives the verified atomic settlement across them. The
object-safe `RingParticipant` adapter lets **heterogeneous apps** (different concrete
types, different error types) ride one ring.

### Atomic-refusal guarantees

- **Unmatched** → `NoMatch`, returned before any `settle_leg`. Zero state change.
- **Non-conserving** → `NotConserving`, returned by the verified gate before any
  `settle_leg`. Zero state change. (The gate is load-bearing: it rejects an
  under-funded or value-leaking ring.)
- **App refuses a leg** → `ParticipantFailed`; every applied leg rolled back. No
  partial settlement.

## The prototype

`app-framework/tests/intent_coordination.rs` demonstrates two heterogeneous apps
coordinating end-to-end via a declarative intent:

- `Gallery` — offers a `GALLERY_SLOT`, wants `CREDIT`s (a creator's gallery cell).
- `Patron` — offers `CREDIT`s, wants a `GALLERY_SLOT` (a patron's wallet cell, a
  different type with a different error).

Neither app calls the other. Both post their `ExchangeSpec`; the `RingCoordinator`
matches the 2-ring and settles it atomically. The tests prove:

1. **Post → match → atomic settle**: the intent posts, the solver matches a 2-ring,
   both apps end with what they declared they wanted, and the verified post-ledger
   shows conservation over **both** assets (Σδ=0).
2. **Unmatched is refused atomically**: a patron who underbids composes no ring;
   `NoMatch` is returned and no app's state changes.
3. **A participant failure rolls back all legs**: a patron whose posted offer
   outruns its real wallet matches and passes the (abstractly-funded) verified gate,
   but its `settle_leg` fails — the gallery's already-applied slot debit is rolled
   back. No partial settlement survives.
4. **The verified Σδ=0 gate is load-bearing**: an over-funded/value-leaking leg set
   is rejected by `settle_ring_verified` (all-or-nothing), guarding the gate the
   coordinator relies on.

## Verdict and next rung

Apps can now communicate via intents inspiringly: declarative + matched + verified +
atomic, replacing imperative point-to-point `Transfer`. The previously-unused
`RingTradeParticipant` trait is wired to the `RingSolver` + `settle_ring_verified`
through the new `RingCoordinator`, and two heterogeneous apps coordinate over one
atomic ring with conservation proven across them.

The next rung to make **all** apps intent-speaking:

1. **A standard `RingTradeParticipant` impl on the app scaffold.** Today each app
   hand-writes the trait. Derive `exchange_offers`/`settle_leg`/`rollback_leg` from
   an app's declared assets + cell program, so any starbridge-app is a ring
   participant by default.
2. **Coordinator → real turns.** The prototype settles against the verified ledger
   projection. Wire `CoordinationReceipt` through `lowering::lower` + the app
   cipherclerk so the matched ring fires as a real signed compound `Turn` on the
   executor (the path `finalize_verified` already walks for the node), giving each
   coordination a light-client-checkable receipt.
3. **A posting affordance in the cockpit.** Surface "post an intent" as an app
   affordance (offer/want) and a "pending intents" view, so a user coordinates
   cross-app trades declaratively from within deos.
4. **Bridge to the trustless engine.** For cross-federation or adversarial settings,
   route the same posted `ExchangeSpec`s through `TrustlessIntentEngine` (encrypt →
   batch → solver competition → challenge) instead of the local coordinator — same
   declarative front door, stronger trust model.
