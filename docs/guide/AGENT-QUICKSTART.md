# Agent quickstart (for LLMs)

You are an agent. This page is how you **earn, spend, and run** on dregg in a few
lines. Every action you take is a verified turn that leaves a `TurnReceipt` —
proof, not a log line. Nothing here is a new kernel primitive; each call desugars
to an effect the kernel already verifies (a conserving `Effect::Transfer`, a
metered checkpoint, a cap-gated worker turn).

The runnable version of everything below is
[`sdk/examples/agent_business_loop.rs`](../../sdk/examples/agent_business_loop.rs)
(`cargo run -p dregg-sdk --example agent_business_loop`).

## The whole loop

```rust
use std::sync::{Arc, RwLock};
use dregg_sdk::{
    AgentCipherclerk, AgentRuntime, Attenuation, Charge, Effect,
    ExecutionLease, LeaseTerms, ToolGateway, ToolGrant,
};

// 0. Identity + a root capability token, in a service domain ("compute").
let mut cclerk = AgentCipherclerk::new();
let root = cclerk.mint_token(&[7u8; 32], "compute");
let runtime = AgentRuntime::new(Arc::new(RwLock::new(cclerk)), "compute");
let asset = runtime.native_asset();                 // the AssetId you spend in

// 1. PAY another agent — one conserving Transfer over the Payable rail.
let receipt = runtime.pay(provider, 1_000, asset)?;  // or pay_native(provider, 1_000)

// 2. Open + fund + RUN a durable, metered execution lease.
let mut lease = ExecutionLease::open(&runtime, &root, LeaseTerms::new(8))?;
lease.fund(&funder, 5_000)?;                          // conserving Transfer in
let step = lease.run(work_effects)?;                  // checkpoint += 1, metered
// step.step / step.remaining / step.receipt

// 3. PAY-PER-USE through a metered, capability-gated tool gateway.
let grant = ToolGrant { tool_id: 77, rate_limit: 3, deadline: 100, tool_method: "search".into() };
let mut gw = ToolGateway::admit_priced(&runtime, &root, grant, Some(Charge::new(500, provider, 10_000)))?;
let r = gw.invoke(77, /*now*/ 50, work_effects)?;     // rate-metered AND charged
// r.paid / r.calls_made / r.remaining / r.receipt
```

That is the entire economy surface. The sections below say where value comes
from, what each call really commits, and how to read your receipts.

## 1. Get credit (value enters from the outside)

Value enters your in-dregg economy as an ordinary `AssetId` you can then `pay`
with. Two real on-ramps exist (node/bridge side):

- **Stripe → USD-credit.** A verified Stripe webhook mirror-mints USD-credit to
  your cell: `StripeMirrorState::mint_against_webhook`
  (`bridge/src/stripe_mirror.rs:437`). The credit is an ordinary `AssetId`
  (`StripeMirrorConfig.asset`).
- **Solana / pump.fun $DREGG → bridged $DREGG.** A locked SPL `$DREGG` is
  mirror-minted in-dregg: `MirrorState::mint_against_lock`
  (`bridge/src/solana_mirror.rs`). The mirror's `MirrorConfig.asset` is the
  in-dregg `AssetId`.

Both bridges have an end-to-end test proving the funded asset then pays for a
lease/service over the **same** `resolve_pay` rail your `pay` uses —
`stripe_payment_funds_an_execution_lease` (`bridge/src/stripe_mirror.rs:814`) and
`bridged_dregg_pays_an_execution_lease` (`bridge/src/solana_mirror.rs:639`). To
your agent code, bridged $DREGG or USD-credit is just an `AssetId` argument to
`pay` — there is no special "bridged" code path.

## 2. Pay (`runtime.pay`)

```rust
let receipt = runtime.pay(to, amount, asset)?;   // any asset
let receipt = runtime.pay_native(to, amount)?;   // this cell's token_id
```

`pay` routes through the canonical `Payable` `pay` method (verified DFA router →
`Signature` cap-gate) and desugars to **exactly one conserving `Effect::Transfer`**
(per-asset Σδ=0). Source: `AgentRuntime::pay`
(`sdk/src/service_economy.rs:102`), over `dregg_payable::resolve_pay`. The
recipient is credited exactly `amount`; the only extra debit on you is the turn
fee.

## 3. Run a metered workload (`ExecutionLease`)

```rust
let mut lease = ExecutionLease::open(&runtime, &root, LeaseTerms::new(8))?;
lease.fund(&funder, 5_000)?;
let step = lease.run(work_effects)?;   // -> LeaseStep { receipt, step, remaining }
```

`open` spawns a cap-gated worker scoped to the run verb and installs the meter
program `FieldLte { step ≤ max_steps } ∧ Monotonic { step }` on the lease cell
(`sdk/src/service_economy.rs:328`, `lease_program` at `:267`). `fund` is a
conserving `Transfer` in. `run` advances the durable checkpoint (`step → step+1`)
and meters `work_effects` on **one** turn. A run past `max_steps` is rejected by
the **executor's** `FieldLte` (not an in-memory check), and the monotone gate
refuses any rewind — your durable progress is bound into the committed
transition.

The funder must hold value in the lease's asset (e.g. another worker the same
runtime spawned, sharing the domain `token_id`).

## 4. Pay-per-use, capability-gated and rate-metered (`ToolGateway`)

This is the "pay to access another agent's tool/model" market.

```rust
let grant = ToolGrant {
    tool_id: 77,          // the single allowlisted tool/MCP id (SCOPE)
    rate_limit: 3,        // at most N calls (RATE)
    deadline: 100,        // expiry height/clock (DEADLINE)
    tool_method: "search".into(),  // the executor verb the worker is scoped to
};
let mut gw = ToolGateway::admit_priced(
    &runtime, &root, grant,
    Some(Charge::new(/*price*/ 500, provider, /*budget*/ 10_000)),
)?;
gw.fund(&funder, 50_000)?;            // fund the consumer spend account (optional)
let r = gw.invoke(77, /*now*/ 50, work_effects)?;   // -> ToolReceipt
```

Each admitted `invoke` (`sdk/src/tool_gateway.rs:774`):

1. folds the whole mandate via `deleg_admit` (SCOPE ∧ DEADLINE ∧ RATE), the
   byte-faithful mirror of the proven Lean `delegAdmit` (`sdk/src/tool_gateway.rs:220`);
2. charges `price` consumer → `provider` as a real conserving `Transfer` (the
   same `Payable::pay` desugar) riding the metered turn, capped at `budget`;
3. advances the rate counter, gated by the executor's
   `FieldLte ∧ Monotonic` `mandate_program` backstop.

An out-of-mandate call is an **in-band refusal** (`Err(ToolCallError::Refused)`)
naming the leg that bit — no turn, no spend, no counter advance. An insolvent
consumer's call is rejected by the kernel's conservation check even with budget
head-room. There is also a non-blocking routed data plane
(`enqueue` → `drive_executor` → `resolve`) that charges identically.

For a single unmetered service call (route a method, optionally prepay in the
same turn) use `runtime.invoke_service` instead
(`sdk/src/service_economy.rs:199`). The gateway is the metered, budgeted front
door over the same value rail.

## 5. Read your receipts

Every committed turn returns a `TurnReceipt` (`turn/src/turn.rs:843`):

```rust
receipt.turn_hash;           // [u8;32]  content-address of the turn
receipt.pre_state_hash;      // [u8;32]  state root before
receipt.post_state_hash;     // [u8;32]  state root after
receipt.effects_hash;        // [u8;32]
receipt.computrons_used;     // u64      metered compute
receipt.action_count;        // usize
receipt.previous_receipt_hash; // Option<[u8;32]>  the chain link
receipt.agent;               // CellId   who authored it
```

Turns the agent authors chain into its receipt chain — each entry's
`receipt_hash()` is the next turn's `previous_receipt_hash`:

```rust
let cclerk = runtime.cipherclerk().read().unwrap();
for r in cclerk.receipt_chain() {
    println!("{} <- {:?}", hex(&r.turn_hash), r.previous_receipt_hash);
}
```

Lease and gateway turns chain on their own worker cells; their proofs are the
`receipt` field of `LeaseStep` / `ToolReceipt`.

## What's real, in all three SDKs

- **Rust SDK:** `pay`/`pay_native`, `invoke_service`, `ExecutionLease`
  (open/fund/run), `ToolGateway` (free + `admit_priced`, inline + routed).
  Desugar + end-to-end conservation/meter tests in `sdk/src/service_economy.rs`,
  `sdk/tests/tool_market_paid.rs`, `sdk/tests/tool_gateway_e2e.rs`. The Stripe
  and Solana bridge on-ramps are real with end-to-end tests (above).
- **TypeScript SDK (`@dregg/sdk`):** `runtime.pay`, `runtime.services.invoke`,
  `runtime.execution.lease` — hand-written TS that builds the SAME
  `Action`/`Effect` JSON the node verifies (the bytes `resolve_pay` /
  `resolve_invocation` produce; differential-tested vs the repo's `dregg-wasm`).
  Tested in `sdk-ts/test/service-economy.test.mjs`.
- **Python SDK (`dregg` pip):** `dregg.ServiceRuntime` — `pay` /
  `invoke_service` / `lease` `#[pyclass]` bindings forwarding to the in-process
  Rust `AgentRuntime` + `ExecutionLease` (the REAL verified executor: real
  committed receipts, the real verified desugar). Tested in
  `sdk-py/tests/test_service_economy.py`.

See [`SERVICE-ECONOMY-SDK.md`](SERVICE-ECONOMY-SDK.md) for the binding story and
the per-call → underlying-turn table.
