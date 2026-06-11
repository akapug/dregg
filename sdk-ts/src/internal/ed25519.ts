/**
 * Ed25519 via node:crypto (RFC 8032; deterministic signatures).
 *
 * Node-target: the SDK's signing paths run where `node:crypto` exists.
 * The PKCS8/SPKI DER framing is fixed-prefix for Ed25519, so we wrap raw
 * 32-byte seeds / public keys without an ASN.1 library.
 */

import { createPrivateKey, createPublicKey, sign as cryptoSign, verify as cryptoVerify } from "node:crypto";
import type { KeyObject } from "node:crypto";

/** PKCS8 DER prefix for an Ed25519 private key (RFC 8410). */
const PKCS8_PREFIX = Uint8Array.from([
  0x30, 0x2e, 0x02, 0x01, 0x00, 0x30, 0x05, 0x06,
  0x03, 0x2b, 0x65, 0x70, 0x04, 0x22, 0x04, 0x20,
]);

/** SPKI DER prefix for an Ed25519 public key. */
const SPKI_PREFIX = Uint8Array.from([
  0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00,
]);

function privateKeyFromSeed(seed32: Uint8Array): KeyObject {
  if (seed32.length !== 32) throw new Error("ed25519 seed must be 32 bytes");
  const der = Buffer.concat([PKCS8_PREFIX, seed32]);
  return createPrivateKey({ key: der, format: "der", type: "pkcs8" });
}

/** Derive the 32-byte Ed25519 public key from a 32-byte seed. */
export function ed25519PublicKey(seed32: Uint8Array): Uint8Array {
  const priv = privateKeyFromSeed(seed32);
  const spki = createPublicKey(priv).export({ format: "der", type: "spki" });
  return new Uint8Array(spki.subarray(spki.length - 32));
}

/** Sign `message` with the key derived from `seed32`; 64-byte signature. */
export function ed25519Sign(seed32: Uint8Array, message: Uint8Array): Uint8Array {
  const priv = privateKeyFromSeed(seed32);
  return new Uint8Array(cryptoSign(null, message, priv));
}

/** Verify a 64-byte signature against a 32-byte public key. */
export function ed25519Verify(
  publicKey32: Uint8Array,
  message: Uint8Array,
  signature64: Uint8Array,
): boolean {
  if (publicKey32.length !== 32 || signature64.length !== 64) return false;
  const der = Buffer.concat([SPKI_PREFIX, publicKey32]);
  const pub = createPublicKey({ key: der, format: "der", type: "spki" });
  return cryptoVerify(null, message, pub, signature64);
}
