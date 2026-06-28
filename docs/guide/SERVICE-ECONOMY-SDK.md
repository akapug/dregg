# The service-economy SDK surface

Buy a service in a few lines, from any of the three SDKs, over the verified rail.

This is the developer onramp for dregg's service economy: pay another agent, call
a service paying through `Payable`, post a service request to an intent ring, and
run a workload under a durable, metered execution lease. Every call here is a
**thin wrapper that desugars to a primitive the kernel already verifies** — there
is no new kernel effect, no new commitment field, and no faking. A call you make
in TypeScript, Python, or Rust resolves to the same `Action`/`Effect` and rides
the same proof-carrying turn.

> **LLM agents:** start with [`AGENT-QUICKSTART.md`](AGENT-QUICKSTART.md) — the
> few-lines "earn / spend / run" flow. The runnable end-to-end loop is
> [`sdk/examples/agent_business_loop.rs`](../../sdk/examples/agent_business_loop.rs)
> (`cargo run -p dregg-sdk --example agent_business_loop`). This page is the full
> API surface and the per-call → underlying-turn mapping.

## The few-lines API (consistent across ts / py / rust)

```ts
// Pay another agent (Payable transfer — incl. bridged $DREGG, an ordinary asset).
await dregg.pay(provider, 1_000n, asset);

// Find + call a service, paying through Payable in the same turn.
const result = await dregg.services.invoke(cell, "render", args, { pay: { to: provider, amount: 250n, asset } });

// Post a service request to the intent ring (the want/offer half).
const promise = await dregg.intents.requestService({ want: serviceId, offer: 250n, asset });

// Open + fund + run a durable execution lease.
const lease = await dregg.execution.lease({ maxSteps: 8, asset });
await lease.fund(funder, 5_000n);
const step = await lease.run(effects);    // advances the durable checkpoint, metered
```

The shapes are identical in Python (`dregg.pay(...)`, `dregg.services.invoke(...)`,
`dregg.execution.lease(...)`) and Rust (`runtime.pay(...)`,
`runtime.invoke_service(...)`, `ExecutionLease::open(...)`).

## Each call → the real underlying turn/effect

The whole point is that this is an honest, thin layer. Here is exactly what each
call desugars to — the verified primitive it routes through, and where it lives.

| SDK call | Desugars to | Underlying primitive (file) |
| --- | --- | --- |
| `dregg.pay(to, amount, asset)` | one conserving `Effect::Transfer` (per-asset Σδ=0) via the `Payable` `pay` method | `dregg_payable::resolve_pay` (`dregg-payable/src/payable.rs:123`) |
| `dregg.services.invoke(cell, method, args, { pay })` | DFA-routed `Action` for `method` on `cell`, carrying the work effects, with the canonical pay `Transfer` prepended when `pay` is given | `dregg_payable::resolve_invocation` (`dregg-payable/src/routing.rs:245`) + `resolve_pay` |
| `dregg.execution.lease({ maxSteps, asset })` | a cap-gated worker scoped to the run verb + a `FieldLte { step ≤ maxSteps } ∧ Monotonic { step }` meter program installed on the lease cell | `AgentRuntime::spawn_sub_agent_scoped` (`sdk/src/runtime.rs:850`) + `lease_program` (`sdk/src/service_economy.rs`) |
| `lease.fund(funder, amount)` | one conserving `Effect::Transfer` into the lease cell | `SubAgent::execute` Transfer (`sdk/src/runtime.rs`) |
| `lease.run(effects)` | a `Monotonic`/`FieldLte`-gated `Effect::SetField` checkpoint advance (`step → step+1`) + the workload effects, metered through the cap-gated worker on one turn | `SubAgent::execute_method` (`sdk/src/runtime.rs:1194`) |
| `dregg.intents.requestService({ want, offer })` | an intent-ring node (offer payment, want the service-promise token), matched by `RingSolver` into a 2-cycle, settled atomically per-asset Σδ=0 | `ServicePromiseExchange` (`app-framework/src/service_promise.rs:419`) — node/app-framework side |

Two of these — the **intent ring / service-promise** and the standalone
**execution-lease app** — live ABOVE the SDK (they depend on
`dregg-app-framework`'s `AppCipherclerk`, which depends on `dregg-sdk`). The SDK is
the bottom layer and cannot depend on them without a cycle. So:

- `dregg.pay`, `dregg.services.invoke`, and `dregg.execution.lease`/`run` are
  implemented **inside the SDK**, over the primitives below the framework
  (`resolve_pay`, the DFA router, the cap-gated worker + `Monotonic`/`FieldLte`
  meter). The SDK lease desugars to the **same verified effect shapes** the
  upper-crate `starbridge-execution-lease` app's `advance_checkpoint` uses.
- `dregg.intents.requestService` is the ergonomic face of the app-framework's
  `ServicePromiseExchange` / `RingCoordinator`; its binding belongs in the
  app-framework / node layer, not the offline SDK core. It is **designed here,
  scaffolded above** — see "Status" below.

## Rust SDK — what is implemented (real, tested)

The Rust SDK (`sdk/`, crate `dregg-sdk`) is the bottom layer; the methods below
are inherent on `AgentRuntime` plus the `ExecutionLease` type
(`sdk/src/service_economy.rs`), re-exported at the crate root.

```rust
use dregg_sdk::{AgentRuntime, ExecutionLease, LeaseTerms, PayLeg, InvokeAuthority};

// 1. pay — the canonical Payable transfer.
let receipt = runtime.pay(provider, 1_000, asset)?;            // any asset
let receipt = runtime.pay_native(provider, 1_000)?;            // this cell's token_id

// 2. invoke a service, optionally paying through Payable in the same turn.
let (action, sig) = runtime.invoke_service_resolved(           // the pure, verified desugar
    cell, "render", args, work_effects, InvokeAuthority::None,
    Some(PayLeg::new(provider, 250, asset)),
)?;
let receipt = runtime.invoke_service(                          // signed + submitted
    cell, "render", args, work_effects, InvokeAuthority::None, Some(PayLeg::new(provider, 250, asset)),
)?;

// 3. a durable, metered execution lease.
let mut lease = ExecutionLease::open(&runtime, &root_token, LeaseTerms::new(8))?;
let _funded = lease.fund(&funder, 5_000)?;                     // conserving Transfer in
let step = lease.run(work_effects)?;                           // checkpoint += 1, metered
// step.step / step.remaining / step.receipt
```

Each is tested to desugar to the right verified turn/effect, in
`sdk/src/service_economy.rs`:

- `pay_desugars_to_one_conserving_payable_transfer` — `pay` routes through the
  canonical `Payable` interface (`method == pay`, the canonical `MethodSig`) and
  desugars to exactly one `Effect::Transfer`.
- `pay_commits_and_conserves_value` — end-to-end on the real executor: the
  recipient is credited exactly the amount; the only value sink beyond the
  conserved transfer is the payer's fee.
- `invoke_service_routes_method_and_refuses_unknown` — the method routes through
  the verified DFA router; an undeclared method is a fail-closed `UnknownMethod`.
- `invoke_service_prepends_canonical_pay_leg` — a paid invocation prepends exactly
  the canonical `resolve_pay` `Transfer` (caller → provider) ahead of the work.
- `lease_program_carries_ceiling_and_monotonic` — the installed meter is exactly
  `FieldLte { step ≤ maxSteps } ∧ Monotonic { step }`.
- `lease_open_fund_run_commits_and_advances_checkpoint` — open + fund (conserved)
  + two runs advance the durable checkpoint monotonically.
- `lease_run_past_ceiling_is_refused_by_the_executor` — a run past the capacity
  ceiling is rejected by the executor's `FieldLte` meter, and the refused run
  leaves the checkpoint untouched.

### Paid, capability-gated, rate-metered invocation: the `ToolGateway`

For the full "pay to access another agent's tool/model, capability-gated and
rate-metered" market, the SDK already ships the `ToolGateway`
(`sdk/src/tool_gateway.rs`): `ToolGateway::admit_priced` admits a worker under a
delegated mandate (scope + deadline + rate), and each `invoke` charges a per-call
price through the SAME `Payable::pay` desugar this facade's `pay` uses, riding the
metered turn. `dregg.services.invoke` above is the simple, single-call front door;
the `ToolGateway` is the metered, budgeted, routed data plane over the same value
rail.

```rust
use dregg_sdk::{ToolGateway, ToolGrant, Charge, ToolCallError};

// The grantor pins the mandate (scope + rate + deadline) and a per-call price.
let grant = ToolGrant {
    tool_id: 77,                  // SCOPE: the single allowlisted tool/MCP id
    rate_limit: 3,                // RATE:  at most N calls under this mandate
    deadline: 100,                // DEADLINE: refused when presented at now > deadline
    tool_method: "search".into(), // the executor verb the worker credential is scoped to
};
let mut gw = ToolGateway::admit_priced(          // `admit` for a free, rate-only mandate
    &runtime, &root, grant,
    Some(Charge::new(/*price*/ 500, provider, /*budget*/ 10_000)),
)?;
gw.fund(&funder, 50_000)?;                        // fund the consumer spend account (real funds)

// INLINE: gate + meter + charge + execute on one turn.
let r = gw.invoke(77, /*now*/ 50, work_effects)?; // -> ToolReceipt { receipt, calls_made, remaining, paid }

// An out-of-mandate call is an IN-BAND refusal (no turn, no spend, no counter advance):
match gw.invoke(99, 50, vec![]) {                 // wrong tool id
    Err(ToolCallError::Refused(why)) => eprintln!("refused: {why}"),
    _ => unreachable!(),
}

// ROUTED (non-blocking data plane): admit + enqueue -> drive elsewhere -> results-back.
let handle = gw.enqueue(77, 50, work_effects)?;   // -> RoutedHandle (an EventualRef-shaped promise)
gw.drive_executor(/*now*/ 51);                    // the execution environment drains + runs
let routed = gw.resolve(&handle)?;                // -> RoutedResult { tool_receipt, delivery }
```

| `ToolGateway` call | Desugars to | File |
| --- | --- | --- |
| `admit` / `admit_priced` | cap-gated worker scoped to `tool_method` + `mandate_program` (`FieldLte { calls_made ≤ rate_limit } ∧ Monotonic`) installed on the worker cell | `sdk/src/tool_gateway.rs:543` / `:564` |
| `fund(funder, amount)` | one conserving `Effect::Transfer` into the worker spend account | `sdk/src/tool_gateway.rs:628` |
| `invoke(tool, now, work)` | `deleg_admit` (= Lean `delegAdmit`) gate → metered `calls_made:c→c+1` `SetField` + the `Payable::pay` charge `Transfer` + `work` on one turn | `sdk/src/tool_gateway.rs:774`, `deleg_admit` `:220` |
| `enqueue` / `drive_executor` / `resolve` | same gate + charge, routed through the verified `PendingTurnRegistry` promise channel | `sdk/src/tool_gateway.rs:850` / `:941` / `:1059` |

`deleg_admit` is the byte-faithful Rust mirror of the proven Lean `delegAdmit`
(`metatheory/Dregg2/Apps/ToolAccessDelegation.lean`); the
`tool_gateway_admit_mirrors_lean_delegadmit` test pins the same decision vector the
Lean `#guard`s witness. End-to-end paid / insolvent / over-budget / routed tests:
`sdk/tests/tool_market_paid.rs`, `sdk/tests/tool_gateway_e2e.rs`.

### The intent ring / service-promise (node-side, real but above the SDK)

The other shape of the market is a posted intent ring: a provider posts a
`ServicePromise` (a service + the exact verified turn hash it will execute to
fulfill, a price, a window) and a consumer posts a `ServiceRequest` (the service
wanted + an offer). `ServicePromiseExchange::match_one` encodes both as ring
intents — the service as a synthetic promise-token asset, the payment as the real
asset — and asks the same verified `RingSolver` the asset ring uses for a 2-cycle.
The matched payment is escrowed; a `TurnReceipt` for the promised
`service_turn_hash`, signed by a trusted executor, fills the fulfillment hole and
releases the escrow (or it refunds after `timeout_height`).

```rust
// app-framework/src/service_promise.rs — node-side (depends on AppCipherclerk).
use dregg_app_framework::service_promise::{
    ServicePromise, ServiceRequest, ServicePromiseExchange, ServiceId,
};

let exchange = ServicePromiseExchange::new(/*max_ring_size*/ 2, /*now*/ 100, escrow, executor_keys);
let promise = ServicePromise {
    provider, service, service_turn_hash, payment_asset, price: 250, timeout_height: 1000,
};
let request = ServiceRequest { consumer, service, payment_asset, offer: 250 };
let matched = exchange.match_one(&promise, &request)?; // -> ServiceMatch (the verified 2-cycle leg)
```

`ServicePromise` / `ServiceRequest` / `ServiceMatch`:
`app-framework/src/service_promise.rs:125` / `:146` / `:159`;
`ServicePromiseExchange::match_one`: `:468`; the ring coordinator it rides:
`app-framework/src/ring_trade.rs` (`RingCoordinator`, `:183`). This surface is
**real and tested above the SDK** (it depends on `dregg-app-framework`'s
`AppCipherclerk`, which depends on `dregg-sdk`, so the SDK cannot re-export it
without a cycle). The `dregg.intents.requestService` facade in the few-lines table
is its designed ergonomic face at the node/app-framework layer.

## Paying with $DREGG (including bridged $DREGG)

In the dregg value model an asset **is** its issuer cell: `AssetId := issuer-cell`
(a 32-byte id). A cell holds value denominated in its own `token_id`, and two
cells interoperate in one asset by sharing a `token_id`. `pay` and the `PayLeg`
take an `AssetId`, so they pay in any asset uniformly.

Bridged `$DREGG` is **an ordinary `AssetId`**: the Solana/pump.fun `$DREGG` SPL
token is mirror-minted inside dregg by `dregg-bridge::solana_mirror`
(`bridge/src/solana_mirror.rs`), and the mirror's `MirrorConfig.asset` is the
`AssetId` of the in-dregg mirror token. Paying with bridged `$DREGG` is therefore
just `dregg.pay(to, amount, mirror_asset)` — the same single conserving
`Effect::Transfer`, routed identically (the bridge's own end-to-end test mints
bridged `$DREGG` and pays it through the `Payable` interface,
`bridged_dregg_pays_an_execution_lease`, `bridge/src/solana_mirror.rs:639`).

## Funding from the outside: Stripe USD-credit and $DREGG

Value enters an agent's economy from the real world as an ordinary in-dregg
`AssetId`, through one of two bridges:

- **Stripe → USD-credit.** A verified Stripe webhook mirror-mints USD-credit to
  the named cell with a real `Effect::Mint`: `StripeMirrorState::mint_against_webhook`
  (`bridge/src/stripe_mirror.rs:437`); the credit's `AssetId` is
  `StripeMirrorConfig.asset` (`:362`). End-to-end:
  `stripe_payment_funds_an_execution_lease` (`bridge/src/stripe_mirror.rs:814`)
  pays for a lease through the same `resolve_pay` rail.
- **Solana / pump.fun $DREGG → bridged $DREGG.** As above, via
  `MirrorState::mint_against_lock` (`bridge/src/solana_mirror.rs`).

In both cases the agent then just calls `dregg.pay(to, amount, that_asset)` — the
mirror's asset is not special-cased anywhere in the agent code.

## TypeScript SDK (`@dregg/sdk`) — binding story: HAND-WRITTEN

The TypeScript SDK (`sdk-ts/`, `@dregg/sdk`) is **hand-written TypeScript** over a
wire `NodeClient`, bundled with `tsup` (not generated from Rust). Its surface today
(`sdk-ts/src/index.ts`): `Identity`, `AgentRuntime`/`NodeClient`,
`TurnBuilder`/`AuthorizedTurn` → `Receipt`, the organ clients (`TrustlineClient`,
`ChannelsClient`, `MailboxClient`), `AttestedQuery`, the `program` constraint
language, and `Pg`/`DeployChecker`. (A separate `@dregg/sdk/wasm` playground is the
only wasm-bindgen-generated piece, in `wasm/`.)

So the service-economy surface in TS is **added by hand** as TypeScript that builds
the same turns the Rust facade does and posts them through `NodeClient`. It is
**SHIPPED** (`sdk-ts/src/service-economy.ts` + the `pay()` verb on `TurnBuilder`):

```ts
import { AgentRuntime, Identity } from "@dregg/sdk";

const runtime = new AgentRuntime(Identity.generate(), nodeUrl);

// pay → a Payable `pay` turn: method "pay", args [asset, field_from_u64(amount), to],
// carrying EXACTLY ONE conserving Transfer(from=me, to, amount).
await runtime.pay(provider, 1_000n, asset);

// services.invoke → route `method` on `cell`, prepend the pay Transfer if given.
await runtime.services.invoke(cell, "render", args, {
  pay: { provider, amount: 250n, asset },
  work: workEffects,
});

// execution.lease → drive the durable, metered run/fund turns against a lease cell.
const lease = runtime.execution.lease({ maxSteps: 8, leaseCell, asset });
await lease.fund(funder, 5_000n);     // one conserving Transfer into the lease cell
const step = await lease.run(work);   // SetField(slot 4, step+1) + work, on the run verb
```

Because the TS SDK already builds and signs turns client-side (the `TurnBuilder` →
`AuthorizedTurn` → `submit` shape), these are a `pay()` verb on `TurnBuilder`
(desugaring to the `Payable` `Transfer`) plus a `ServiceEconomy` namespace
(`runtime.pay` / `runtime.services.invoke` / `runtime.execution.lease`), each
producing the exact `Action`/`Effect` JSON the node executor verifies — the same
bytes the Rust `resolve_pay` / `resolve_invocation` produce. The differential
test (`sdk-ts/test/wire.test.mjs`, byte-equality vs the repo's `dregg-wasm` build)
keeps the encoding honest; `sdk-ts/test/service-economy.test.mjs` asserts each
method emits the right `Action`/`Effect` shape. Spawning the cap-gated worker and
installing the `FieldLte ∧ Monotonic` meter program is the cell-provisioning step
(the in-process Rust `ExecutionLease::open` does it locally; over the wire it is
done when the lease cell is provisioned — `leaseProgramConstraints` describes the
two teeth the cell's program enforces).

## Python SDK (`dregg` pip) — binding story: GENERATED (PyO3/maturin)

The Python SDK (`sdk-py/`, `dregg` on pip) is a **PyO3 extension generated from
Rust** via maturin (`bindings = "pyo3"`, module `dregg.dregg`). Its surface
(`sdk-py/src/lib.rs`) — `Identity`, `TurnBuilder`, `AuthorizedTurn`, `Receipt`, the
`Trustline`/`Channels`/`Mailbox` organ clients, the `program` constraint functions
— is each a `#[pyclass]`/`#[pymethods]`/`#[pyfunction]` over the Rust SDK.

The service-economy surface in Python is **SHIPPED** as `#[pyclass]` bindings in
`sdk-py/src/lib.rs` that **forward to the now-existing in-process Rust core**
(`dregg_sdk::AgentRuntime` + `ExecutionLease`). Unlike the wire `Identity →
turn(node) → submit` flow, the `ServiceRuntime` binding drives the REAL verified
kernel executor in-process, so `pay` / `lease` produce REAL committed
`TurnReceipt`s and `invoke_service` returns the REAL verified desugar — thin
forwards, no faking:

```python
import dregg

rt = dregg.ServiceRuntime()                 # a real in-process runtime (self-funded agent cell)

# pay → AgentRuntime::pay: one conserving Payable Transfer (per-asset Σδ=0).
recipient = rt.spawn()
rt.pay(recipient.cell_id, 1_000)            # -> TxReceipt

# invoke_service → AgentRuntime::invoke_service_resolved: the verified desugar
# (method routed through the DFA router; unknown method raises DreggRefused).
svc = rt.install_service_cell(["render"])
action = rt.invoke_service(svc, "render", pay=(svc, 250, rt.native_asset))
assert action["effects"][0]["kind"] == "transfer"   # the canonical pay leg

# lease → ExecutionLease::open/fund/run: the durable, metered checkpoint.
funder = rt.spawn()
lease = rt.lease(8)
lease.fund(funder, 5_000)
lease.run()                                 # advances the checkpoint; FieldLte∧Monotonic enforced
```

`ServiceRuntime` / `Worker` / `Lease` / `TxReceipt` are each a `#[pyclass]`
wrapping the real Rust type; `dregg.method_symbol(name)` exposes the routing
symbol. `sdk-py/tests/test_service_economy.py` is the Python twin of the Rust
facade's tests (conservation, routing + unknown-method refusal, the canonical pay
leg, checkpoint advance, and the executor refusing a run past the capacity
ceiling). Built green with `maturin develop` / `maturin build --release` (the
default `light`, kernel-free wheel — no Lean toolchain required).

## Status — real vs designed

- **Real, tested (Rust SDK):** `AgentRuntime::pay` / `pay_native`,
  `AgentRuntime::invoke_service_resolved` / `invoke_service`, `ExecutionLease`
  (`open`/`fund`/`run`) — all desugaring to verified primitives, with desugar +
  end-to-end conservation/meter tests (`sdk/src/service_economy.rs`, green under
  `cargo test -p dregg-sdk`). The metered/paid `ToolGateway` was already real.
  The whole loop runs end-to-end in
  [`sdk/examples/agent_business_loop.rs`](../../sdk/examples/agent_business_loop.rs)
  (`cargo run -p dregg-sdk --example agent_business_loop`).
- **Real, above the SDK:** the intent-ring `ServicePromiseExchange` /
  `RingCoordinator` and the standalone `starbridge-execution-lease` app
  (`app-framework/`, `starbridge-apps/execution-lease/`). The
  `dregg.intents.requestService` facade is the designed ergonomic face of these;
  it belongs in the app-framework/node layer.
- **Shipped (TypeScript):** the `ServiceEconomy` namespace + the `pay()` verb on
  `TurnBuilder` (`sdk-ts/src/service-economy.ts`, `sdk-ts/src/turns.ts`) —
  `runtime.pay` / `runtime.services.invoke` / `runtime.execution.lease`, each
  producing the exact `Action`/`Effect` JSON the node verifies (the same bytes
  `resolve_pay` / `resolve_invocation` produce; the differential wire test keeps
  the encoding honest). Tested in `sdk-ts/test/service-economy.test.mjs` (green
  under `npm test`). The cap-gated-worker spawn + meter-program install is the
  cell-provisioning step; the wire SDK drives the verified `run`/`fund` turns.
- **Shipped (Python):** the `ServiceRuntime` / `Worker` / `Lease` / `TxReceipt`
  `#[pyclass]` bindings (`sdk-py/src/lib.rs`) forwarding to the in-process Rust
  `AgentRuntime` + `ExecutionLease` — `pay` / `invoke_service` / `lease` over the
  REAL verified executor (real committed receipts, the real verified desugar).
  Tested in `sdk-py/tests/test_service_economy.py` (green under `pytest`; built
  with `maturin develop` / `maturin build --release`).
