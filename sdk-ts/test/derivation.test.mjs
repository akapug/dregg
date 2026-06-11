// THE golden key-derivation vector — the constellation pin.
//
//   blake3::derive_key("dregg/0", seed64) -> 32-byte Ed25519 seed -> pubkey
//
// The SAME vector is pinned in:
//   - sdk/src/profiles.rs        (Rust SDK)
//   - cli/src/commands/id.rs     (CLI)
//   - extension/test/derivation.test.mjs (browser extension)
//   - here                       (TS SDK)
//
// seed   = 000102...3f (64 bytes)
// pubkey = 335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a
//
// If ANY implementation drifts, its golden test fails alongside these.

import { test } from "node:test";
import assert from "node:assert/strict";

import { hex, sdk } from "./helpers.mjs";

test("golden vector: seed 00..3f -> pubkey 335840a9..8b9a", async () => {
  const { Identity } = await sdk();
  const seed = Uint8Array.from({ length: 64 }, (_, i) => i);
  const identity = Identity.fromSeed(seed);
  assert.equal(
    identity.publicKeyHex,
    "335840a9ca2a7a62bcfb83e3df15933c7e091c2dfd9083c26d93a8c468058b9a",
    "TS SDK key derivation diverged from the Rust SDK / CLI / extension profile stores",
  );
});

test("identity derivation is deterministic, path- and seed-sensitive", async () => {
  const { Identity } = await sdk();
  const seed = Uint8Array.from({ length: 64 }, (_, i) => i);
  const a = Identity.fromSeed(seed);
  const b = Identity.fromSeed(seed);
  assert.equal(a.publicKeyHex, b.publicKeyHex);
  const sub = Identity.fromSeed(seed, "dregg/1");
  assert.notEqual(sub.publicKeyHex, a.publicKeyHex);
  const tweaked = seed.slice();
  tweaked[63] ^= 0xff;
  assert.notEqual(Identity.fromSeed(tweaked).publicKeyHex, a.publicKeyHex);
});

test("agent cell id matches CellId::derive_raw(pk, blake3('default'))", async () => {
  const { Identity } = await sdk();
  const { deriveCellId, defaultTokenId, blake3 } = await import("../dist/raw.mjs");
  const seed = Uint8Array.from({ length: 64 }, (_, i) => i);
  const identity = Identity.fromSeed(seed);
  assert.equal(hex(defaultTokenId()), hex(blake3("default")));
  assert.equal(identity.cellIdHex(), hex(deriveCellId(identity.publicKey)));
  assert.equal(identity.cellId().length, 32);
});
