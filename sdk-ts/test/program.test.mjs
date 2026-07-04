// Cell-program atoms: content addressing (same program → same factory_vk;
// different program → different vk) and the anyOf/not/implies composition
// shapes, mirroring sdk/src/program.rs's tests.

import { test } from "node:test";
import assert from "node:assert/strict";

import { sdk } from "./helpers.mjs";

const pk = (n) => Uint8Array.from({ length: 32 }, () => n);

test("programmed descriptor is content-addressed", async () => {
  const { program } = await sdk();
  const a = program.programmedCellDescriptor([program.senderIs(pk(1)), program.balanceGte(10n)]);
  const a2 = program.programmedCellDescriptor([program.senderIs(pk(1)), program.balanceGte(10n)]);
  const b = program.programmedCellDescriptor([program.senderIs(pk(2)), program.balanceGte(10n)]);
  assert.equal(a.factoryVkHex, a2.factoryVkHex);
  assert.notEqual(a.factoryVkHex, b.factoryVkHex);
  assert.notEqual(a.childProgramVkHex, b.childProgramVkHex);
  assert.equal(a.stateConstraints.length, 2);
  assert.equal(a.creationBudget, 1);
});

test("the builder sugar produces the same descriptor as the direct fn", async () => {
  const { program } = await sdk();
  const direct = program.programmedCellDescriptor([program.writeOnce(0), program.senderInSlot(1)]);
  const built = new program.CellProgramBuilder()
    .require(program.writeOnce(0))
    .require(program.senderInSlot(1))
    .descriptor();
  assert.equal(direct.factoryVkHex, built.factoryVkHex);
  assert.equal(direct.childProgramVkHex, built.childProgramVkHex);
});

test("all five actor atoms + slot freezes are expressible and orderly", async () => {
  const { program } = await sdk();
  const constraints = [
    program.senderIs(pk(7)),
    program.senderInSlot(2),
    program.balanceGte(100n),
    program.balanceLte(1_000_000n),
    program.preimageGate(3, "blake3"),
    program.preimageGate(4, "poseidon2"),
    program.immutable(0),
    program.writeOnce(1),
  ];
  const d = program.programmedCellDescriptor(constraints);
  assert.equal(d.stateConstraints.length, 8);
  // Order is semantic for the content address.
  const reordered = program.programmedCellDescriptor([...constraints].reverse());
  assert.notEqual(d.factoryVkHex, reordered.factoryVkHex);
});

test("implies(P, Q) is the canonical anyOf([not(P), Q]) encoding", async () => {
  const { program } = await sdk();
  const p = program.simple.senderIs(pk(5));
  const q = program.simple.balanceLte(0n);
  const derived = program.implies(p, q);
  assert.equal(derived.kind, "anyOf");
  assert.equal(derived.variants.length, 2);
  assert.equal(derived.variants[0].kind, "not");
  assert.equal(derived.variants[0].inner.kind, "senderIs");
  assert.equal(derived.variants[1].kind, "balanceLte");

  const open = program.anyOf([program.simple.not(p), q]);
  assert.equal(
    program.programmedCellDescriptor([derived]).factoryVkHex,
    program.programmedCellDescriptor([open]).factoryVkHex,
    "implies must be byte-identical to its open-coded form",
  );
});

test("double negation is unrepresentable (the Rust type shape)", async () => {
  const { program } = await sdk();
  const p = program.simple.senderIs(pk(1));
  assert.throws(() => program.simple.not(program.simple.not(p)), /not representable/);
});

test("the per-slot actor binding composes: anyOf([immutable, senderIs])", async () => {
  const { program } = await sdk();
  const binding = program.anyOf([program.simple.immutable(0), program.simple.senderIs(pk(3))]);
  const d = program.programmedCellDescriptor([binding]);
  assert.match(d.factoryVkHex, /^[0-9a-f]{64}$/);
  assert.match(d.childProgramVkHex, /^[0-9a-f]{64}$/);
});
