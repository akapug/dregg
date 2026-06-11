/**
 * Byte / hex / integer helpers shared by the wire and crypto internals.
 */

/** Lowercase hex encode (matches `dregg_types::hex_encode`). */
export function hexEncode(bytes: Uint8Array): string {
  let out = "";
  for (const b of bytes) out += b.toString(16).padStart(2, "0");
  return out;
}

/** Hex decode; throws on odd length or non-hex characters. */
export function hexDecode(hex: string): Uint8Array {
  const clean = hex.startsWith("0x") ? hex.slice(2) : hex;
  if (clean.length % 2 !== 0 || /[^0-9a-fA-F]/.test(clean)) {
    throw new Error(`invalid hex string (len ${clean.length})`);
  }
  const out = new Uint8Array(clean.length / 2);
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(clean.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

/** Decode hex that must be exactly `len` bytes. */
export function hexDecodeExact(hex: string, len: number): Uint8Array {
  const b = hexDecode(hex);
  if (b.length !== len) throw new Error(`expected ${len} bytes, got ${b.length}`);
  return b;
}

export function concatBytes(...parts: Uint8Array[]): Uint8Array {
  let total = 0;
  for (const p of parts) total += p.length;
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of parts) {
    out.set(p, off);
    off += p.length;
  }
  return out;
}

/** u64 little-endian, 8 bytes (accepts number or bigint). */
export function u64le(v: number | bigint): Uint8Array {
  const out = new Uint8Array(8);
  let n = BigInt(v);
  if (n < 0n) throw new Error("u64le: negative");
  for (let i = 0; i < 8; i++) {
    out[i] = Number(n & 0xffn);
    n >>= 8n;
  }
  return out;
}

/** i64 little-endian (two's complement), 8 bytes. */
export function i64le(v: number | bigint): Uint8Array {
  let n = BigInt(v);
  if (n < 0n) n += 1n << 64n;
  return u64le(n);
}

/** u32 little-endian, 4 bytes. */
export function u32le(v: number): Uint8Array {
  const out = new Uint8Array(4);
  out[0] = v & 0xff;
  out[1] = (v >>> 8) & 0xff;
  out[2] = (v >>> 16) & 0xff;
  out[3] = (v >>> 24) & 0xff;
  return out;
}

export function bytesEqual(a: Uint8Array, b: Uint8Array): boolean {
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}

/** Assert a value is a Uint8Array of exactly `len` bytes; returns a copy. */
export function exactBytes(v: Uint8Array, len: number, what: string): Uint8Array {
  if (!(v instanceof Uint8Array) || v.length !== len) {
    throw new Error(`${what} must be exactly ${len} bytes`);
  }
  return Uint8Array.from(v);
}

export const utf8 = {
  encode: (s: string): Uint8Array => new TextEncoder().encode(s),
};
