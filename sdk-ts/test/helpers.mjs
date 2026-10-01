// Shared test helpers: load the repo's own dregg-wasm build as the
// differential ORACLE (the exact Rust dregg-turn/dregg-sdk code compiled to
// wasm), so the TS wire implementation drift-fails against the source of
// truth without running cargo.
//
// ⚠ ORACLE INTEGRITY (M30): the oracle MUST be the REAL, FRESHLY-BUILT wasm
// artifact — never a stale, hand-frozen snapshot. `wasm/pkg-oracle` is gitignored
// (`.gitignore` = `*`), so on a fresh clone it does NOT exist. The npm
// `pretest` hook rebuilds it (`npm run build:oracle` → `wasm-pack build`)
// before every `npm test`, so the compared bytes are always current source.
// A differential whose oracle is untracked and never rebuilt proves nothing:
// it silently blesses whatever the frozen binary happened to encode. This
// loader therefore FAILS LOUD when the oracle is absent rather than skipping.

import { existsSync, readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);

const ORACLE_MISSING =
  "dregg-wasm ORACLE MISSING — the wire differential cannot run without the " +
  "REAL, freshly-built wasm artifact. `wasm/pkg-oracle` is gitignored, so it must be " +
  "built: run `npm run build:oracle` (or `npm test`, whose `pretest` hook " +
  "builds it). Refusing to pass silently against an absent oracle (M30).";

let cached = null;

/** Load + initialize dregg-wasm (file-linked from ../wasm/pkg-oracle). */
export async function loadWasmOracle() {
  if (cached) return cached;
  let pkgDir;
  try {
    pkgDir = dirname(require.resolve("dregg-wasm/package.json"));
  } catch {
    throw new Error(ORACLE_MISSING);
  }
  const glue = join(pkgDir, "dregg_wasm.js");
  const bin = join(pkgDir, "dregg_wasm_bg.wasm");
  if (!existsSync(glue) || !existsSync(bin)) throw new Error(ORACLE_MISSING);
  const mod = await import(glue);
  mod.initSync({ module: readFileSync(bin) });
  cached = mod;
  return mod;
}

export const hex = (bytes) => Buffer.from(bytes).toString("hex");

export const fromHex = (s) => Uint8Array.from(Buffer.from(s, "hex"));

export const distDir = join(here, "..", "dist");

export const sdk = () => import(join(distDir, "index.mjs"));
export const raw = () => import(join(distDir, "raw.mjs"));
export const pg = () => import(join(distDir, "pg.mjs"));

/** Bytes after a `SignedTurn` envelope's turn: Ed sig/key + ML-DSA sig/key, length-prefixed. */
export const SIGNED_TURN_SUFFIX_LEN = 1 + 64 + 1 + 32 + 2 + 3309 + 2 + 1952;

/**
 * Read a default-bundle postcard `Turn`'s per-agent coordinates for a mock node:
 * `nonce` (the varint after the 32-byte agent) and, from the END, `validUntil`
 * and `previousReceiptHash`. A default bundle ends in exactly ten zero bytes
 * (empty `depends_on`, then nine None/empty proof-bundle fields), preceded by
 * `previous_receipt_hash: Option<[u8; 32]>`, preceded by
 * `valid_until: Option<i64>` (zigzag varint).
 *
 * ⚠ A `Some` head is recognized by its last byte being non-zero, so mocks using
 * this must mint heads that do not end in `0x00` (asserted).
 */
export function decodeTurnCoordinates(turnBytes) {
  const t = turnBytes;
  let nonce = 0n;
  let shift = 0n;
  for (let k = 32; ; k++) {
    nonce |= BigInt(t[k] & 0x7f) << shift;
    if ((t[k] & 0x80) === 0) break;
    shift += 7n;
  }
  const tail = t.length - 10;
  if (!t.subarray(tail).every((b) => b === 0)) throw new Error("not a default-bundle turn tail");
  let previousReceiptHash;
  let vuEnd;
  if (t[tail - 1] === 0) {
    vuEnd = tail - 1;
  } else {
    if (t[tail - 33] !== 1) throw new Error("previous_receipt_hash: expected Some tag 0x01");
    previousReceiptHash = hex(t.subarray(tail - 32, tail));
    vuEnd = tail - 33;
  }
  let validUntil;
  if (t[vuEnd - 1] !== 0) {
    let start = vuEnd - 1;
    while (t[start - 1] & 0x80) start--;
    if (t[start - 1] !== 1) throw new Error("valid_until: expected Some tag 0x01");
    let z = 0n;
    for (let k = vuEnd - 1; k >= start; k--) z = (z << 7n) | BigInt(t[k] & 0x7f);
    validUntil = z & 1n ? -((z + 1n) >> 1n) : z >> 1n;
  }
  return { nonce, validUntil, previousReceiptHash };
}
