// The service-economy surface: pay / services.invoke / execution.lease emit
// the SAME Action/Effect JSON the node verifies — byte-for-byte what the Rust
// facade (`sdk/src/service_economy.rs` → `dregg_payable::resolve_pay` /
// `resolve_invocation`) desugars to. These assertions are offline: a pinned
// federation id lets `.sign()` run without a node, and `.action()` exposes the
// exact signed action for inspection.

import { test } from "node:test";
import assert from "node:assert/strict";

import { hex, sdk } from "./helpers.mjs";

const PINNED_FED = Uint8Array.from({ length: 32 }, () => 3);

function bytes(fill) {
  return Uint8Array.from({ length: 32 }, () => fill);
}

async function makeRuntime() {
  const { AgentRuntime, Identity } = await sdk();
  const identity = Identity.fromKeyBytes(Uint8Array.from({ length: 32 }, (_, i) => 0x11 + i));
  // Pin the federation id so .sign() needs no node round trip.
  const runtime = new AgentRuntime(identity, "http://127.0.0.1:1", { federationId: PINNED_FED });
  return { runtime, identity };
}

test("pay desugars to method=pay + pay_args + one conserving Transfer", async () => {
  const { symbol, fieldFromU64 } = await sdk();
  const { runtime, identity } = await makeRuntime();
  const to = bytes(9);
  const asset = bytes(0xaa);

  const authorized = await runtime.services.payTurn(to, 500n, asset).sign();
  const action = authorized.action();

  // method == symbol("pay"); target == the payer (the acting cell).
  assert.equal(hex(action.method), hex(symbol("pay")), "method must be the Payable `pay` symbol");
  assert.equal(hex(action.target), identity.cellIdHex(), "target is the payer cell");

  // args == [asset, field_from_u64(amount), to] (the pay_args witness).
  assert.equal(action.args.length, 3);
  assert.equal(hex(action.args[0]), hex(asset), "args[0] = asset");
  assert.equal(hex(action.args[1]), hex(fieldFromU64(500n)), "args[1] = field_from_u64(amount)");
  assert.equal(hex(action.args[2]), hex(to), "args[2] = to");

  // exactly one conserving Transfer (caller -> to, amount).
  assert.equal(action.effects.length, 1, "pay desugars to one effect");
  const e = action.effects[0];
  assert.equal(e.kind, "transfer");
  assert.equal(hex(e.from), identity.cellIdHex(), "the caller pays");
  assert.equal(hex(e.to), hex(to));
  assert.equal(e.amount, 500n);
});

test("runtime.pay() builder twin is identical (the few-lines front door)", async () => {
  const { symbol } = await sdk();
  const { runtime } = await makeRuntime();
  const a = (await runtime.turn().pay(bytes(7), 12n, bytes(8)).sign()).action();
  assert.equal(hex(a.method), hex(symbol("pay")));
  assert.equal(a.effects.length, 1);
  assert.equal(a.effects[0].kind, "transfer");
});

test("services.invoke routes the method, args, and prepends the canonical pay leg", async () => {
  const { symbol } = await sdk();
  const { runtime, identity } = await makeRuntime();
  const cell = bytes(0x55);
  const provider = bytes(0x66);
  const asset = bytes(0xcc);
  const arg0 = bytes(1);
  const work = [{ kind: "setField", cell, index: 0, value: bytes(2) }];

  const authorized = await runtime.services
    .invokeTurn(cell, "render", [arg0], { pay: { provider, amount: 250n, asset }, work })
    .sign();
  const action = authorized.action();

  // target = the service cell; method = symbol("render"); args carried through.
  assert.equal(hex(action.target), hex(cell), "target is the service cell");
  assert.equal(hex(action.method), hex(symbol("render")));
  assert.equal(action.args.length, 1);
  assert.equal(hex(action.args[0]), hex(arg0));

  // effect 0 = the canonical pay Transfer (caller -> provider); effect 1 = work.
  assert.equal(action.effects.length, 2, "pay leg + work");
  const pay = action.effects[0];
  assert.equal(pay.kind, "transfer");
  assert.equal(hex(pay.from), identity.cellIdHex(), "the caller pays");
  assert.equal(hex(pay.to), hex(provider), "the provider is paid");
  assert.equal(pay.amount, 250n);
  assert.equal(action.effects[1].kind, "setField");
});

test("services.invoke without a pay leg carries only the work (no transfer)", async () => {
  const { symbol } = await sdk();
  const { runtime } = await makeRuntime();
  const cell = bytes(0x55);
  const a = (await runtime.services
    .invokeTurn(cell, "render", [], { work: [{ kind: "setField", cell, index: 0, value: bytes(2) }] })
    .sign()).action();
  assert.equal(hex(a.method), hex(symbol("render")));
  assert.equal(a.effects.length, 1);
  assert.equal(a.effects[0].kind, "setField");
});

test("lease.run advances the durable checkpoint (SetField on slot 4) + meters work", async () => {
  const { symbol, fieldFromU64 } = await sdk();
  const { LEASE_STEP_SLOT, DEFAULT_LEASE_METHOD, leaseProgramConstraints } = await sdk();
  const { runtime } = await makeRuntime();
  const leaseCell = bytes(0x77);
  const lease = runtime.execution.lease({ maxSteps: 2, leaseCell, asset: bytes(0xdd) });

  // The meter program shape: FieldLte{slot4 <= 2} ∧ Monotonic{slot4}.
  const meter = leaseProgramConstraints(2);
  assert.equal(meter.length, 2);
  assert.equal(meter[0].kind, "fieldLte");
  assert.equal(meter[0].index, LEASE_STEP_SLOT);
  assert.equal(hex(meter[0].value), hex(fieldFromU64(2)));
  assert.equal(meter[1].kind, "monotonic");
  assert.equal(meter[1].index, LEASE_STEP_SLOT);

  // run 1: SetField(leaseCell, slot4, 1) ++ work, on the run verb.
  const work = [{ kind: "setField", cell: leaseCell, index: 0, value: bytes(0xee) }];
  const a1 = (await lease.runTurn(work).sign()).action();
  assert.equal(hex(a1.target), hex(leaseCell), "the run targets the lease cell");
  assert.equal(hex(a1.method), hex(symbol(DEFAULT_LEASE_METHOD)));
  assert.equal(a1.effects.length, 2, "checkpoint advance + work");
  const cp = a1.effects[0];
  assert.equal(cp.kind, "setField");
  assert.equal(hex(cp.cell), hex(leaseCell));
  assert.equal(cp.index, LEASE_STEP_SLOT);
  assert.equal(hex(cp.value), hex(fieldFromU64(1)), "step -> 1");
  assert.equal(a1.effects[1].kind, "setField");
});

test("lease.fund is one conserving Transfer into the lease cell", async () => {
  const { runtime } = await makeRuntime();
  const leaseCell = bytes(0x77);
  const funder = bytes(0x88);
  const lease = runtime.execution.lease({ maxSteps: 4, leaseCell });

  const a = (await lease.fundTurn(funder, 5_000n).sign()).action();
  assert.equal(a.effects.length, 1);
  const e = a.effects[0];
  assert.equal(e.kind, "transfer");
  assert.equal(hex(e.from), hex(funder), "funder pays");
  assert.equal(hex(e.to), hex(leaseCell), "the lease cell is funded");
  assert.equal(e.amount, 5_000n);
});
