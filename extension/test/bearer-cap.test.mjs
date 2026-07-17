// Bearer-cap delegator-identity pin — the falsifier for the createBearerCap
// key-derivation bug (extension/src/background.ts `dregg:createBearerCap`).
//
// THE MECHANISM: the wasm `create_bearer_cap(delegator_signing_key_hex, ...)`
// treats its FIRST argument as a 32-byte Ed25519 *signing seed* (secret):
//
//   let signing_key   = SigningKey::from_bytes(&hex_decode_32(arg));
//   let delegator_pubkey = signing_key.verifying_key().to_bytes();   // cap identity
//   let signature        = signing_key.sign(&binding);               // cap token
//
// (wasm/src/privacy.rs::create_bearer_cap). So the delegator identity a cap is
// issued under is `verifying_key(from_bytes(arg))`. ed25519 accepts ANY 32
// bytes as a seed, so passing the WRONG bytes never throws — it silently issues
// the cap under an unrelated identity.
//
// THE BUG (pre-fix): background.ts hex-encoded `cc.publicKey` and passed THAT.
// The cap was then issued under `verifying_key(publicKey_bytes)` — a key
// derived from PUBLIC material, so (a) it is NOT the user's identity and
// (b) anyone who knows the user's public key can reconstruct the exact same
// "delegator" key and forge caps under it. No secret is involved at all.
//
// THE FIX: hex-encode `cc.secretKey` (the real 32-byte seed) so the cap is
// issued under `verifying_key(seed) == cc.publicKey` — the user's real identity,
// provable only by the holder of the seed.
//
// This test grounds the mechanism with node:crypto (independent of the wasm),
// exactly as offering-sign.test.mjs / derivation.test.mjs ground their pins.

import { test } from "node:test";
import assert from "node:assert/strict";
import { createPrivateKey, createPublicKey, sign as edSign, verify as edVerify } from "node:crypto";

const PKCS8_ED25519_PREFIX = Buffer.from("302e020100300506032b657004220420", "hex");
const SPKI_ED25519_PREFIX = Buffer.from("302a300506032b6570032100", "hex");

// The EXACT hex encoding background.ts applies to a key `number[]` before
// handing it to the wasm (`Array.from(x).map(b => b.toString(16).padStart(2,"0")).join("")`).
function keyHex(bytes) {
  return Array.from(bytes).map((b) => b.toString(16).padStart(2, "0")).join("");
}

// The wasm's `SigningKey::from_bytes(seed)` (RFC 8032): a 32-byte seed → keypair.
// Returns the private key object plus the 32-byte verifying (public) key —
// i.e. the delegator identity the wasm would stamp onto a cap seeded by `seed`.
function keypairFromSeed(seed) {
  assert.equal(seed.length, 32, "ed25519 seed is 32 bytes");
  const privateKey = createPrivateKey({
    key: Buffer.concat([PKCS8_ED25519_PREFIX, Buffer.from(seed)]),
    format: "der",
    type: "pkcs8",
  });
  const spki = createPublicKey(privateKey).export({ format: "der", type: "spki" });
  const verifyingKey = spki.subarray(SPKI_ED25519_PREFIX.length); // 32 bytes
  return { privateKey, verifyingKey };
}

// A representative cipherclerk keypair: a 32-byte seed is the SECRET key; its
// verifying key is the user's real identity (`cc.publicKey`).
const seed = Uint8Array.from({ length: 32 }, (_, i) => i); // 00..1f
const { privateKey: realPriv, verifyingKey: realIdentity } = keypairFromSeed(seed);
const cc = { secretKey: Array.from(seed), publicKey: Array.from(realIdentity) };

test("the FIX seeds the cap with cc.secretKey → delegator identity == the user's real public key", () => {
  // background.ts (fixed) passes hex(cc.secretKey) as delegator_signing_key_hex.
  const delegatorKeyHex = keyHex(cc.secretKey);
  assert.equal(delegatorKeyHex.length, 64, "32-byte seed → 64 hex chars");

  // The wasm derives the delegator identity as verifying_key(from_bytes(arg)).
  const argBytes = Buffer.from(delegatorKeyHex, "hex");
  const { verifyingKey: delegatorIdentity } = keypairFromSeed(argBytes);

  // The cap is issued under the user's REAL identity.
  assert.deepEqual(
    Array.from(delegatorIdentity),
    Array.from(realIdentity),
    "fixed create_bearer_cap issues under cc.publicKey (the user's real key)",
  );

  // And the token is a real signature by the user's secret key: it verifies
  // under the real identity, which only the seed-holder could have produced.
  const binding = Buffer.from("a canonical bearer-cap binding");
  const token = edSign(null, binding, realPriv);
  const pub = createPublicKey({
    key: Buffer.concat([SPKI_ED25519_PREFIX, Buffer.from(realIdentity)]),
    format: "der",
    type: "spki",
  });
  assert.equal(edVerify(null, binding, pub, token), true, "token verifies under the real identity");
});

test("the BUG seeded the cap with cc.publicKey → garbage, publicly-reconstructable identity", () => {
  // The pre-fix code passed hex(cc.publicKey) as the "signing seed".
  const buggyKeyHex = keyHex(cc.publicKey);

  // The wasm would derive the delegator as verifying_key(from_bytes(publicKey)).
  const { verifyingKey: buggyIdentity } = keypairFromSeed(Buffer.from(buggyKeyHex, "hex"));

  // It is NOT the user's identity — the cap is disconnected from the real key.
  assert.notDeepEqual(
    Array.from(buggyIdentity),
    Array.from(realIdentity),
    "buggy cap is issued under a key unrelated to the user",
  );

  // Worse: it is derived entirely from PUBLIC bytes, so anyone holding the
  // user's public key reconstructs the exact same "delegator" key — the cap's
  // authority is forgeable by any observer, not secured by any secret.
  const attackerKnowsOnly = Array.from(realIdentity); // public info
  const { verifyingKey: attackerReconstruction } = keypairFromSeed(Buffer.from(attackerKnowsOnly));
  assert.deepEqual(
    Array.from(attackerReconstruction),
    Array.from(buggyIdentity),
    "an attacker with only the public key reconstructs the buggy delegator key",
  );
});

test("the two code paths pass DIFFERENT bytes to the wasm (the fix is not a no-op)", () => {
  // Sanity: secretKey and publicKey differ, so the fix genuinely changes the
  // argument the wasm receives (a keypair whose seed happened to equal its
  // pubkey would be astronomically unlikely and is not this keypair).
  assert.notDeepEqual(cc.secretKey, cc.publicKey);
  assert.notEqual(keyHex(cc.secretKey), keyHex(cc.publicKey));
});
