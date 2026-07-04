// The wire differential — the drift killer.
//
// Builds a turn in TS, hands the SAME turn (serde-JSON form) to the repo's
// own dregg-wasm build (the actual Rust dregg-turn/dregg-sdk code), and
// asserts BYTE EQUALITY between:
//
//   - the TS postcard `Turn` encoding and the Rust `postcard::to_allocvec`,
//     including the per-action Ed25519 `Authorization::Signature` produced
//     over the canonical federation-bound signing message
//     (`dregg-action-sig-v2`) — Ed25519 is deterministic, so equal bytes
//     mean equal signing preimages and equal key derivation;
//   - the TS `turnHash` and the Rust canonical `Turn::hash` (v3).
//
// Any drift in the postcard layout, the effect/action hash preimages, the
// signing message, or the hash domains fails here.

import { test } from "node:test";
import assert from "node:assert/strict";

import { loadWasmOracle, hex, raw } from "./helpers.mjs";

const cell = (n) => Uint8Array.from({ length: 32 }, () => n);
const arr = (b) => Array.from(b);

/** serde-JSON form of the TS effect union (externally tagged Rust enum). */
function effectToJson(e) {
  switch (e.kind) {
    case "setField":
      return { SetField: { cell: arr(e.cell), index: e.index, value: arr(e.value) } };
    case "transfer":
      return { Transfer: { from: arr(e.from), to: arr(e.to), amount: Number(e.amount) } };
    case "grantCapability":
      return {
        GrantCapability: {
          from: arr(e.from),
          to: arr(e.to),
          cap: {
            target: arr(e.cap.target),
            slot: e.cap.slot,
            permissions: "Signature",
            breadstuff: e.cap.breadstuff ? arr(e.cap.breadstuff) : null,
            expires_at: e.cap.expiresAt !== undefined ? Number(e.cap.expiresAt) : null,
            stored_epoch: e.cap.storedEpoch !== undefined ? Number(e.cap.storedEpoch) : null,
          },
        },
      };
    case "revokeCapability":
      return { RevokeCapability: { cell: arr(e.cell), slot: e.slot } };
    case "emitEvent":
      return { EmitEvent: { cell: arr(e.cell), event: { topic: arr(e.topic), data: e.data.map(arr) } } };
    case "incrementNonce":
      return { IncrementNonce: { cell: arr(e.cell) } };
    case "createCell":
      return { CreateCell: { public_key: arr(e.publicKey), token_id: arr(e.tokenId), balance: Number(e.balance) } };
    default:
      throw new Error(`no JSON form for ${e.kind}`);
  }
}

function actionToJson(a) {
  return {
    target: arr(a.target),
    method: arr(a.method),
    args: a.args.map(arr),
    authorization: "Unchecked",
    preconditions: { cell_state: null, network: null, valid_while: null, witnessed: [] },
    effects: a.effects.map(effectToJson),
    may_delegate: "None",
    commitment_mode: "Full",
    balance_change: a.balanceChange !== undefined ? Number(a.balanceChange) : null,
    witness_blobs: [],
  };
}

function turnToJson(t) {
  return {
    agent: arr(t.agent),
    nonce: Number(t.nonce),
    call_forest: {
      roots: t.roots.map((r) => ({ action: actionToJson(r.action), children: [], hash: arr(new Uint8Array(32)) })),
      forest_hash: arr(new Uint8Array(32)),
    },
    fee: Number(t.fee),
    memo: t.memo ?? null,
    valid_until: t.validUntil !== undefined ? Number(t.validUntil) : null,
    previous_receipt_hash: t.previousReceiptHash ? arr(t.previousReceiptHash) : null,
    depends_on: (t.dependsOn ?? []).map(arr),
    conservation_proof: null,
    sovereign_witnesses: {},
    execution_proof: null,
    execution_proof_cell: null,
    execution_proof_new_commitment: null,
    custom_program_proofs: null,
    effect_binding_proofs: [],
    cross_effect_dependencies: [],
    effect_witness_index_map: [],
  };
}

function richEffects(rawMod, acting) {
  const { symbol } = rawMod;
  return [
    { kind: "setField", cell: acting, index: 3, value: rawMod.fieldFromU64(77n) },
    { kind: "transfer", from: acting, to: cell(9), amount: 12345n },
    {
      kind: "grantCapability",
      from: acting,
      to: cell(8),
      cap: { target: cell(7), slot: 2, permissions: { kind: "signature" }, expiresAt: 900n },
    },
    { kind: "revokeCapability", cell: acting, slot: 5 },
    { kind: "emitEvent", cell: acting, topic: symbol("ping"), data: [rawMod.fieldFromU64(1n), rawMod.fieldFromU64(2n)] },
    { kind: "incrementNonce", cell: acting },
    { kind: "createCell", publicKey: cell(0xaa), tokenId: cell(0xbb), balance: 500n },
  ];
}

test("differential: TS signed turn bytes + canonical hash == Rust (via dregg-wasm)", async () => {
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x10 + i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = Uint8Array.from({ length: 32 }, () => 0x42);

  // A turn that exercises every modeled effect + the optional turn fields.
  const effects = richEffects(rawMod, agent);
  const unsigned = rawMod.unsignedActionNamed(agent, "execute", effects);
  const signedAction = identity.signAction(unsigned, federationId);

  const turn = {
    agent,
    nonce: 7n,
    roots: [{ action: signedAction, children: [] }],
    fee: 10_000n,
    memo: "differential",
    validUntil: 1765432100n,
    previousReceiptHash: cell(0x33),
    dependsOn: [cell(0x44)],
  };

  // Oracle path: same turn, UNSIGNED, in serde-JSON; wasm signs it through
  // the canonical Rust path and re-encodes as postcard.
  const unsignedTurn = { ...turn, roots: [{ action: unsigned, children: [] }] };
  const jsonBytes = new TextEncoder().encode(JSON.stringify(turnToJson(unsignedTurn)));
  const oracle = wasm.sign_turn_v3(jsonBytes, seed32, federationId);

  assert.equal(oracle.signer_pubkey, identity.publicKeyHex, "key derivation drift");

  const tsBytes = rawMod.encodeTurn(turn);
  assert.equal(
    hex(tsBytes),
    hex(Uint8Array.from(oracle.turn_bytes)),
    "postcard Turn encoding drifted from Rust (or the action signature / signing message differs)",
  );

  assert.equal(
    rawMod.turnHashHex(turn),
    oracle.turn_id,
    "canonical Turn::hash (v3) drifted from Rust",
  );
});

test("differential: minimal single-effect turn (all options None)", async () => {
  const wasm = await loadWasmOracle();
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => 0x77 - i);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const federationId = new Uint8Array(32);

  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [
    { kind: "incrementNonce", cell: agent },
  ]);
  const signedAction = identity.signAction(unsigned, federationId);
  const turn = { agent, nonce: 0n, roots: [{ action: signedAction, children: [] }], fee: 0n };

  const jsonBytes = new TextEncoder().encode(
    JSON.stringify(turnToJson({ ...turn, roots: [{ action: unsigned, children: [] }] })),
  );
  const oracle = wasm.sign_turn_v3(jsonBytes, seed32, federationId);

  assert.equal(hex(rawMod.encodeTurn(turn)), hex(Uint8Array.from(oracle.turn_bytes)));
  assert.equal(rawMod.turnHashHex(turn), oracle.turn_id);
});

test("the SignedTurn envelope verifies and frames as turn ++ sig ++ signer", async () => {
  const rawMod = await raw();
  const { Identity } = await import("../dist/index.mjs");

  const seed32 = Uint8Array.from({ length: 32 }, (_, i) => i * 3);
  const identity = Identity.fromKeyBytes(seed32);
  const agent = identity.cellId();
  const unsigned = rawMod.unsignedActionNamed(agent, "execute", [
    { kind: "incrementNonce", cell: agent },
  ]);
  const action = identity.signAction(unsigned, new Uint8Array(32));
  const turn = { agent, nonce: 1n, roots: [{ action, children: [] }], fee: 100n };

  const envelope = identity.signTurnEnvelope(turn);
  const turnBytes = rawMod.encodeTurn(turn);
  assert.equal(envelope.length, turnBytes.length + 1 + 64 + 1 + 32);
  assert.equal(hex(envelope.subarray(0, turnBytes.length)), hex(turnBytes));
  assert.equal(envelope[turnBytes.length], 0x40, "varint(64) before the signature");
  assert.equal(envelope[turnBytes.length + 65], 0x20, "varint(32) before the signer");
  const sig = envelope.subarray(turnBytes.length + 1, turnBytes.length + 65);
  const signer = envelope.subarray(turnBytes.length + 66);
  assert.equal(hex(signer), identity.publicKeyHex);
  // The envelope signature is over the canonical Turn::hash (v3) — exactly
  // what post_submit_signed_turn re-derives and verifies.
  assert.ok(rawMod.ed25519Verify(identity.publicKey, rawMod.turnHash(turn), sig));
});
