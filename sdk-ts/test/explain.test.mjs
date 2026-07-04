// explain: totality over the modeled effect corpus + the [sem] tag's
// injectivity-on-semantics (equal text ⇒ equal canonical hash, because the
// tag IS the hash the executor/circuit bind).

import { test } from "node:test";
import assert from "node:assert/strict";

import { hex, raw, sdk } from "./helpers.mjs";

const cell = (n) => Uint8Array.from({ length: 32 }, () => n);

async function effectCorpus() {
  const rawMod = await raw();
  return [
    { kind: "setField", cell: cell(1), index: 2, value: rawMod.fieldFromU64(7n) },
    { kind: "transfer", from: cell(1), to: cell(2), amount: 5n },
    {
      kind: "grantCapability",
      from: cell(1),
      to: cell(2),
      cap: { target: cell(9), slot: 3, permissions: { kind: "signature" } },
    },
    { kind: "revokeCapability", cell: cell(1), slot: 4 },
    { kind: "emitEvent", cell: cell(1), topic: cell(3), data: [cell(0x11)] },
    { kind: "incrementNonce", cell: cell(1) },
    { kind: "createCell", publicKey: cell(1), tokenId: cell(2), balance: 100n },
  ];
}

test("explainEffect is total over the corpus and carries the faithfulness tag", async () => {
  const { explainEffect } = await sdk();
  for (const effect of await effectCorpus()) {
    const s = explainEffect(effect);
    assert.ok(s.length > 0, `empty rendering for ${effect.kind}`);
    assert.ok(s.includes("[sem "), `missing faithfulness tag for ${effect.kind}: ${s}`);
  }
});

test("explainEffect is injective on semantics over the corpus", async () => {
  const { explainEffect } = await sdk();
  const rawMod = await raw();
  const corpus = await effectCorpus();
  for (let i = 0; i < corpus.length; i++) {
    for (let j = 0; j < corpus.length; j++) {
      if (i === j) continue;
      if (hex(rawMod.effectHash(corpus[i])) !== hex(rawMod.effectHash(corpus[j]))) {
        assert.notEqual(
          explainEffect(corpus[i]),
          explainEffect(corpus[j]),
          `distinct-semantics effects #${i} and #${j} rendered identically`,
        );
      }
    }
  }
});

test("the sem tag discriminates when the prose collides", async () => {
  const { explainEffect } = await sdk();
  const rawMod = await raw();
  // Two grants identical in everything the PROSE shows (target + slot +
  // from + to) but differing in a semantic field the prose elides
  // (expiresAt rides the postcard wire, not the rendering).
  const base = {
    kind: "grantCapability",
    from: cell(1),
    to: cell(2),
    cap: { target: cell(9), slot: 3, permissions: { kind: "signature" } },
  };
  const withExpiry = {
    ...base,
    cap: { ...base.cap, expiresAt: 99n },
  };
  // NOTE: Effect::hash for GrantCapability binds target+slot only (the cap
  // attenuation fields live in the postcard encoding / executor gates), so
  // these two have the SAME canonical effect hash — and therefore the same
  // rendering is FAITHFUL, exactly as in Rust.
  assert.equal(hex(rawMod.effectHash(base)), hex(rawMod.effectHash(withExpiry)));
  assert.equal(explainEffect(base), explainEffect(withExpiry));

  // Whereas a slot change (semantic) changes both hash and rendering.
  const otherSlot = { ...base, cap: { ...base.cap, slot: 4 } };
  assert.notEqual(hex(rawMod.effectHash(base)), hex(rawMod.effectHash(otherSlot)));
  assert.notEqual(explainEffect(base), explainEffect(otherSlot));
});

test("explainAction carries the action-level sem tag; auth mode changes it", async () => {
  const { explainAction } = await sdk();
  const rawMod = await raw();
  const action = rawMod.unsignedActionNamed(cell(1), "execute", [
    { kind: "incrementNonce", cell: cell(1) },
  ]);
  const rendered = explainAction(action);
  assert.ok(rendered.includes(hex(rawMod.actionHash(action))));
  assert.ok(rendered.includes("NO authorization (unchecked"));

  const signed = {
    ...action,
    authorization: { kind: "signature", r: cell(0xaa), s: cell(0xbb) },
  };
  assert.ok(explainAction(signed).includes("an Ed25519 signature"));
  assert.notEqual(explainAction(signed), rendered, "authorization is semantic");
});

test("explainTurn / renderTurn walks the forest and names agent, nonce, fee", async () => {
  const { explainTurn, renderTurn } = await sdk();
  const rawMod = await raw();
  const action = rawMod.unsignedActionNamed(cell(1), "execute", [
    { kind: "transfer", from: cell(1), to: cell(2), amount: 5n },
  ]);
  const turn = {
    agent: cell(1),
    nonce: 3n,
    roots: [{ action, children: [] }],
    fee: 10n,
    memo: "hello",
  };
  const s = explainTurn(turn);
  assert.equal(renderTurn, explainTurn);
  assert.ok(s.includes("Turn by agent"));
  assert.ok(s.includes("(nonce 3, fee 10)"));
  assert.ok(s.includes('memo "hello"'));
  assert.ok(s.includes("1 action(s) in the call forest"));
  assert.ok(s.includes("transfer 5 computrons"));
});
