/**
 * BLAKE3 — portable TypeScript implementation (hash + derive_key modes).
 *
 * Full tree hashing: inputs larger than one 1024-byte chunk are split per the
 * BLAKE3 spec (left subtree = the largest power-of-two number of chunks that
 * leaves at least one byte on the right), so this implementation agrees with
 * the Rust `blake3` crate on inputs of ANY length — turn-hash preimages
 * routinely exceed one chunk.
 *
 * Shared lineage: the single-chunk core mirrors the independent JS
 * implementation pinned in `extension/test/derivation.test.mjs`; this module
 * extends it with the parent-node tree layer. Both are pinned by the same
 * golden derivation vector (seed 00..3f -> pubkey 335840a9…8b9a) as
 * `sdk/src/profiles.rs` and `cli/src/commands/id.rs`, and differentially
 * tested against the repo's own `dregg-wasm` build — if any implementation
 * drifts, the whole constellation fails together.
 */

const IV = [
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
] as const;

const MSG_PERMUTATION = [2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8] as const;

const CHUNK_LEN = 1024;
const BLOCK_LEN = 64;

const CHUNK_START = 1 << 0;
const CHUNK_END = 1 << 1;
const PARENT = 1 << 2;
const ROOT = 1 << 3;
const DERIVE_KEY_CONTEXT = 1 << 5;
const DERIVE_KEY_MATERIAL = 1 << 6;

const rotr = (x: number, n: number): number => ((x >>> n) | (x << (32 - n))) >>> 0;

function g(s: number[], a: number, b: number, c: number, d: number, mx: number, my: number): void {
  s[a] = (s[a] + s[b] + mx) >>> 0;
  s[d] = rotr(s[d] ^ s[a], 16);
  s[c] = (s[c] + s[d]) >>> 0;
  s[b] = rotr(s[b] ^ s[c], 12);
  s[a] = (s[a] + s[b] + my) >>> 0;
  s[d] = rotr(s[d] ^ s[a], 8);
  s[c] = (s[c] + s[d]) >>> 0;
  s[b] = rotr(s[b] ^ s[c], 7);
}

function roundFn(s: number[], m: number[]): void {
  g(s, 0, 4, 8, 12, m[0], m[1]);
  g(s, 1, 5, 9, 13, m[2], m[3]);
  g(s, 2, 6, 10, 14, m[4], m[5]);
  g(s, 3, 7, 11, 15, m[6], m[7]);
  g(s, 0, 5, 10, 15, m[8], m[9]);
  g(s, 1, 6, 11, 12, m[10], m[11]);
  g(s, 2, 7, 8, 13, m[12], m[13]);
  g(s, 3, 4, 9, 14, m[14], m[15]);
}

function compress(
  cv: number[],
  blockWords: number[],
  counterLo: number,
  counterHi: number,
  blockLen: number,
  flags: number,
): number[] {
  const s = [
    cv[0], cv[1], cv[2], cv[3], cv[4], cv[5], cv[6], cv[7],
    IV[0], IV[1], IV[2], IV[3],
    counterLo >>> 0, counterHi >>> 0, blockLen >>> 0, flags >>> 0,
  ];
  let m = blockWords.slice();
  for (let r = 0; r < 7; r++) {
    roundFn(s, m);
    if (r < 6) m = MSG_PERMUTATION.map((i) => m[i]);
  }
  const out = new Array<number>(16);
  for (let i = 0; i < 8; i++) {
    out[i] = (s[i] ^ s[i + 8]) >>> 0;
    out[i + 8] = (s[i + 8] ^ cv[i]) >>> 0;
  }
  return out;
}

const readLE32 = (bytes: Uint8Array, off: number): number =>
  (bytes[off] | (bytes[off + 1] << 8) | (bytes[off + 2] << 16) | (bytes[off + 3] << 24)) >>> 0;

function wordsToBytes(words: number[]): Uint8Array {
  const out = new Uint8Array(words.length * 4);
  words.forEach((w, i) => {
    out[i * 4] = w & 0xff;
    out[i * 4 + 1] = (w >>> 8) & 0xff;
    out[i * 4 + 2] = (w >>> 16) & 0xff;
    out[i * 4 + 3] = (w >>> 24) & 0xff;
  });
  return out;
}

function bytesToWords(bytes: Uint8Array): number[] {
  const out = new Array<number>(bytes.length / 4);
  for (let i = 0; i < out.length; i++) out[i] = readLE32(bytes, i * 4);
  return out;
}

/**
 * Compress one chunk (≤ 1024 bytes) at chunk index `counter`.
 * Returns the full 16-word output of the final block compression; callers
 * take the first 8 words as the chaining value (or all of it for the root).
 */
function chunkOutput(
  input: Uint8Array,
  counter: number,
  keyWords: number[],
  flags: number,
  isRoot: boolean,
): number[] {
  const counterLo = counter >>> 0;
  const counterHi = Math.floor(counter / 2 ** 32) >>> 0;
  let cv = keyWords.slice();
  const blockCount = input.length === 0 ? 1 : Math.ceil(input.length / BLOCK_LEN);
  let last: number[] = [];
  for (let i = 0; i < blockCount; i++) {
    const block = input.subarray(i * BLOCK_LEN, Math.min((i + 1) * BLOCK_LEN, input.length));
    let blockFlags = flags;
    if (i === 0) blockFlags |= CHUNK_START;
    if (i === blockCount - 1) {
      blockFlags |= CHUNK_END;
      if (isRoot) blockFlags |= ROOT;
    }
    const padded = new Uint8Array(BLOCK_LEN);
    padded.set(block);
    last = compress(cv, bytesToWords(padded), counterLo, counterHi, block.length, blockFlags);
    cv = last.slice(0, 8);
  }
  return last;
}

/** Largest power-of-two multiple of CHUNK_LEN strictly less than `len`. */
function leftLen(len: number): number {
  let full = Math.floor((len - 1) / CHUNK_LEN); // chunks that leave ≥1 byte on the right
  let p = 1;
  while (p * 2 <= full) p *= 2;
  return p * CHUNK_LEN;
}

/** Chaining value (8 words) of the subtree over `input` starting at chunk `counter`. */
function subtreeCv(input: Uint8Array, counter: number, keyWords: number[], flags: number): number[] {
  if (input.length <= CHUNK_LEN) {
    return chunkOutput(input, counter, keyWords, flags, false).slice(0, 8);
  }
  const split = leftLen(input.length);
  const left = subtreeCv(input.subarray(0, split), counter, keyWords, flags);
  const right = subtreeCv(input.subarray(split), counter + split / CHUNK_LEN, keyWords, flags);
  return compress(keyWords, left.concat(right), 0, 0, BLOCK_LEN, flags | PARENT).slice(0, 8);
}

/** Hash `input` with the given key words and mode flags, 32-byte output. */
function blake3Internal(input: Uint8Array, keyWords: number[], flags: number): Uint8Array {
  if (input.length <= CHUNK_LEN) {
    return wordsToBytes(chunkOutput(input, 0, keyWords, flags, true).slice(0, 8));
  }
  const split = leftLen(input.length);
  const left = subtreeCv(input.subarray(0, split), 0, keyWords, flags);
  const right = subtreeCv(input.subarray(split), split / CHUNK_LEN, keyWords, flags);
  const out = compress(keyWords, left.concat(right), 0, 0, BLOCK_LEN, flags | PARENT | ROOT);
  return wordsToBytes(out.slice(0, 8));
}

/** `blake3::hash(input)` — 32-byte digest. */
export function blake3(input: Uint8Array | string): Uint8Array {
  const bytes = typeof input === "string" ? new TextEncoder().encode(input) : input;
  return blake3Internal(bytes, IV.slice(), 0);
}

/** `blake3::derive_key(context, keyMaterial)` — 32-byte output. */
export function blake3DeriveKey(context: string, keyMaterial: Uint8Array): Uint8Array {
  const contextKey = blake3Internal(
    new TextEncoder().encode(context),
    IV.slice(),
    DERIVE_KEY_CONTEXT,
  );
  return blake3Internal(keyMaterial, bytesToWords(contextKey), DERIVE_KEY_MATERIAL);
}

/**
 * An incremental-update convenience mirroring `blake3::Hasher` call sites:
 * collects updates, hashes on finalize. (The Rust hasher is streaming; the
 * wire preimages here are small enough that buffering is fine.)
 */
export class Blake3Hasher {
  private parts: Uint8Array[] = [];
  private readonly context: string | null;

  constructor(context: string | null = null) {
    this.context = context;
  }

  static new(): Blake3Hasher {
    return new Blake3Hasher(null);
  }

  /** `blake3::Hasher::new_derive_key(context)`. */
  static newDeriveKey(context: string): Blake3Hasher {
    return new Blake3Hasher(context);
  }

  update(bytes: Uint8Array | string): this {
    this.parts.push(typeof bytes === "string" ? new TextEncoder().encode(bytes) : bytes);
    return this;
  }

  finalize(): Uint8Array {
    let total = 0;
    for (const p of this.parts) total += p.length;
    const all = new Uint8Array(total);
    let off = 0;
    for (const p of this.parts) {
      all.set(p, off);
      off += p.length;
    }
    return this.context === null ? blake3(all) : blake3DeriveKey(this.context, all);
  }
}
