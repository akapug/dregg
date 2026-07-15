/**
 * The `DreggLaunchpad` client — the BIDDER's leg of the verified launch loop.
 *
 * `chain/contracts/launchpad/DreggLaunchpad.sol` runs the loop create → gate →
 * launch → clear → lock on-chain. `./sealedbid` derives the seal that loop
 * expects. Neither of them is reachable from a browser: nothing built the
 * calldata, nothing kept the opening, nothing signed a transaction from the
 * bidder's address. That is this module.
 *
 * ## What is derived, not asserted
 *
 * `DREGG_LAUNCHPAD_ABI` is a verbatim subset of the contract's compiled ABI —
 * emitted by `forge inspect DreggLaunchpad abi --json` from
 * `chain/contracts/launchpad/DreggLaunchpad.sol`, with `internalType` dropped.
 * `test/launchpad.test.mjs` re-runs that command and asserts every entry here is
 * byte-identical to the contract's own, so a contract edit that changes a
 * signature turns the test red rather than silently producing calldata the
 * launchpad decodes into something else. Selectors are never written down: they
 * are `keccak256` of the signature the ABI itself yields (`selectorOf`), pinned
 * against `cast sig` vectors in the same test.
 *
 * The seal is NOT re-derived here — `./sealedbid`'s `launchpadSeal` is the one
 * derivation, cross-pinned to `sealOf` by a shared vector.
 *
 * ## The two named deploy-time dependencies (nothing here broadcasts)
 *
 * 1. READS need an `eth_call` transport (an RPC URL + a deployed address). The
 *    client takes one as an injected `EthCall`; with none, a read throws
 *    `RpcRequiredError` by name rather than inventing state. Every read is
 *    therefore exercisable offline against a transport stub.
 * 2. SENDING needs a nonce, a gas market, and an `eth_sendRawTransaction` — all
 *    RPC. So the client's writes stop at a `TxRequest` (`{to, data, value}`),
 *    which is complete and offline-checkable; handed the RPC-sourced fee fields
 *    (`TxGas`), `signTxRequest` produces the raw EIP-1559 transaction. It signs
 *    with `./evm`'s `signDigest` — the extension's ONE secp256k1 leg, over the
 *    same wallet seed. There is no second key and no new crypto here: RLP is an
 *    encoding, and the digest it produces goes to the existing signer.
 */
import {
  keccak256,
  fromHex0x,
  hex0x,
  toChecksumAddress,
  signDigest,
  recoverAddress,
} from "./evm";
import { launchpadSeal, checkLaunchpadReveal, type LaunchpadSeal } from "./sealedbid";

function utf8(s: string): Uint8Array {
  return new TextEncoder().encode(s);
}

function concatBytes(...parts: Uint8Array[]): Uint8Array {
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

// ─── The ABI (verbatim from `forge inspect DreggLaunchpad abi --json`) ─────────

export interface AbiParam {
  readonly name: string;
  readonly type: string;
  readonly indexed?: boolean;
  readonly components?: readonly AbiParam[];
}

export interface AbiEntry {
  readonly type: "function" | "error" | "event";
  readonly name: string;
  readonly inputs: readonly AbiParam[];
  readonly outputs?: readonly AbiParam[];
  readonly stateMutability?: string;
  readonly anonymous?: boolean;
}

/**
 * The bidder-facing surface of `DreggLaunchpad`. A SUBSET — the launchpad also
 * exposes the creator's `registerLaunch`/`withdrawProceeds`, the clearer's
 * `finalizeClearing`, and the graduation calls; a bidder drives none of them, so
 * this client does not encode them. Every entry present is exactly the
 * contract's (asserted entry-by-entry against `forge inspect` in
 * `test/launchpad.test.mjs`).
 */
export const DREGG_LAUNCHPAD_ABI: readonly AbiEntry[] = [
  // ── the two turns of the ceremony ──
  {
    type: "function",
    name: "commitBid",
    inputs: [
      { name: "launchId", type: "uint256" },
      { name: "sealedHash", type: "bytes32" },
      { name: "proof", type: "bytes" },
    ],
    outputs: [],
    stateMutability: "payable",
  },
  {
    type: "function",
    name: "revealBid",
    inputs: [
      { name: "launchId", type: "uint256" },
      { name: "price", type: "uint256" },
      { name: "qty", type: "uint256" },
      { name: "salt", type: "bytes32" },
    ],
    outputs: [],
    stateMutability: "nonpayable",
  },
  // ── the bidder's exits: the cleared settle, and the stuck-launch backstop ──
  {
    type: "function",
    name: "settleBid",
    inputs: [
      { name: "launchId", type: "uint256" },
      { name: "bidder", type: "address" },
    ],
    outputs: [],
    stateMutability: "nonpayable",
  },
  {
    type: "function",
    name: "reclaimEscrow",
    inputs: [{ name: "launchId", type: "uint256" }],
    outputs: [],
    stateMutability: "nonpayable",
  },
  // ── the reads a bidder needs ──
  {
    type: "function",
    name: "phaseOf",
    inputs: [{ name: "launchId", type: "uint256" }],
    outputs: [{ name: "", type: "uint8" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "getBid",
    inputs: [
      { name: "launchId", type: "uint256" },
      { name: "bidder", type: "address" },
    ],
    outputs: [
      { name: "committed", type: "bool" },
      { name: "revealed", type: "bool" },
      { name: "price", type: "uint256" },
      { name: "qty", type: "uint256" },
      { name: "filled", type: "uint256" },
      { name: "settled", type: "bool" },
      { name: "deposit", type: "uint256" },
    ],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "refundable",
    inputs: [{ name: "launchId", type: "uint256" }],
    outputs: [{ name: "", type: "bool" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "checkSchedule",
    inputs: [
      { name: "launchId", type: "uint256" },
      {
        name: "s",
        type: "tuple",
        components: [
          { name: "totalSupply", type: "uint256" },
          { name: "saleSupply", type: "uint256" },
          { name: "creatorAllocation", type: "uint256" },
          { name: "poolAllocation", type: "uint256" },
          { name: "creatorLockUntil", type: "uint64" },
          { name: "reservePrice", type: "uint256" },
          { name: "graduationBps", type: "uint16" },
        ],
      },
    ],
    outputs: [{ name: "", type: "bool" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "scheduleCommitOf",
    inputs: [{ name: "launchId", type: "uint256" }],
    outputs: [{ name: "", type: "bytes32" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "sealOf",
    inputs: [
      { name: "price", type: "uint256" },
      { name: "qty", type: "uint256" },
      { name: "salt", type: "bytes32" },
      { name: "bidder", type: "address" },
    ],
    outputs: [{ name: "", type: "bytes32" }],
    stateMutability: "pure",
  },
  {
    type: "function",
    name: "clearingPriceOf",
    inputs: [{ name: "launchId", type: "uint256" }],
    outputs: [{ name: "", type: "uint256" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "soldQtyOf",
    inputs: [{ name: "launchId", type: "uint256" }],
    outputs: [{ name: "", type: "uint256" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "tokenOf",
    inputs: [{ name: "launchId", type: "uint256" }],
    outputs: [{ name: "", type: "address" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "launchCount",
    inputs: [],
    outputs: [{ name: "", type: "uint256" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "REFUND_GRACE",
    inputs: [],
    outputs: [{ name: "", type: "uint64" }],
    stateMutability: "view",
  },
  {
    type: "function",
    name: "TOKEN_UNIT",
    inputs: [],
    outputs: [{ name: "", type: "uint256" }],
    stateMutability: "view",
  },
  // ── the events a bidder's own turns emit ──
  {
    type: "event",
    name: "BidCommitted",
    inputs: [
      { name: "launchId", type: "uint256", indexed: true },
      { name: "bidder", type: "address", indexed: true },
      { name: "sealedHash", type: "bytes32", indexed: false },
      { name: "deposit", type: "uint256", indexed: false },
    ],
    anonymous: false,
  },
  {
    type: "event",
    name: "BidRevealed",
    inputs: [
      { name: "launchId", type: "uint256", indexed: true },
      { name: "bidder", type: "address", indexed: true },
      { name: "price", type: "uint256", indexed: false },
      { name: "qty", type: "uint256", indexed: false },
    ],
    anonymous: false,
  },
  // ── every named refusal a bidder's turn can hit ──
  { type: "error", name: "NoSuchLaunch", inputs: [{ name: "launchId", type: "uint256" }] },
  { type: "error", name: "NotCommitPhase", inputs: [] },
  { type: "error", name: "NotRevealPhase", inputs: [] },
  { type: "error", name: "NotClearPhase", inputs: [] },
  { type: "error", name: "AlreadyCommitted", inputs: [] },
  { type: "error", name: "AlreadyRevealed", inputs: [] },
  { type: "error", name: "NoCommit", inputs: [] },
  { type: "error", name: "BidMismatch", inputs: [] },
  { type: "error", name: "NotEligible", inputs: [{ name: "bidder", type: "address" }] },
  {
    type: "error",
    name: "UnderCollateralized",
    inputs: [
      { name: "deposit", type: "uint256" },
      { name: "needed", type: "uint256" },
    ],
  },
  { type: "error", name: "NothingToSettle", inputs: [] },
  { type: "error", name: "LaunchAlreadyCleared", inputs: [] },
  {
    type: "error",
    name: "RefundNotYetAvailable",
    inputs: [{ name: "refundableAt", type: "uint64" }],
  },
  { type: "error", name: "NothingToRefund", inputs: [] },
  { type: "error", name: "AlreadyRefunded", inputs: [] },
  { type: "error", name: "TransferFailed", inputs: [] },
];

function findEntry(kind: AbiEntry["type"], name: string): AbiEntry {
  const e = DREGG_LAUNCHPAD_ABI.find(x => x.type === kind && x.name === name);
  if (!e) throw new Error(`DreggLaunchpad ABI: no ${kind} named ${name}`);
  return e;
}

/** The canonical ABI type of a param (`tuple` expands to its components). */
export function canonicalType(p: AbiParam): string {
  if (p.type.startsWith("tuple")) {
    const inner = (p.components ?? []).map(canonicalType).join(",");
    return `(${inner})${p.type.slice("tuple".length)}`;
  }
  return p.type;
}

/** The canonical signature of a function/error/event, e.g. `commitBid(uint256,bytes32,bytes)`. */
export function signatureOf(kind: AbiEntry["type"], name: string): string {
  const e = findEntry(kind, name);
  return `${e.name}(${e.inputs.map(canonicalType).join(",")})`;
}

/** The 4-byte selector `0x…` — keccak of the signature the ABI yields, never a literal. */
export function selectorOf(kind: AbiEntry["type"], name: string): string {
  return hex0x(keccak256(utf8(signatureOf(kind, name))).slice(0, 4));
}

/** The `topics[0]` of an event — keccak of its canonical signature. */
export function eventTopic(name: string): string {
  return hex0x(keccak256(utf8(signatureOf("event", name))));
}

// ─── ABI coding (only the types this surface uses; anything else fails loudly) ──

function word(value: bigint): Uint8Array {
  const out = new Uint8Array(32);
  let v = value;
  for (let i = 31; i >= 0 && v > 0n; i--) {
    out[i] = Number(v & 0xffn);
    v >>= 8n;
  }
  return out;
}

function toBigInt(v: unknown): bigint {
  if (typeof v === "bigint") return v;
  if (typeof v === "number") {
    if (!Number.isSafeInteger(v)) throw new Error(`ABI: ${v} is not a safe integer`);
    return BigInt(v);
  }
  if (typeof v === "string") return BigInt(v);
  throw new Error(`ABI: cannot read an integer from ${typeof v}`);
}

function toBytes(v: unknown): Uint8Array {
  if (v instanceof Uint8Array) return v;
  if (typeof v === "string") return fromHex0x(v);
  throw new Error(`ABI: cannot read bytes from ${typeof v}`);
}

function isDynamicType(p: AbiParam): boolean {
  const t = p.type;
  if (t === "bytes" || t === "string") return true;
  if (t.endsWith("[]")) return true;
  if (t.startsWith("tuple")) return (p.components ?? []).some(isDynamicType);
  return false;
}

/** How many 32-byte words a STATIC param occupies. */
function staticWords(p: AbiParam): number {
  if (p.type.startsWith("tuple")) {
    let n = 0;
    for (const c of p.components ?? []) n += staticWords(c);
    return n;
  }
  return 1;
}

function tupleValues(p: AbiParam, v: unknown): unknown[] {
  const comps = p.components ?? [];
  if (Array.isArray(v)) return v;
  if (v && typeof v === "object") {
    const rec = v as Record<string, unknown>;
    return comps.map(c => {
      if (!(c.name in rec)) throw new Error(`ABI: tuple is missing field ${c.name}`);
      return rec[c.name];
    });
  }
  throw new Error("ABI: a tuple takes an object or an array");
}

function encodeValue(p: AbiParam, v: unknown): Uint8Array {
  const t = p.type;

  if (t === "tuple") return encodeParams(p.components ?? [], tupleValues(p, v));

  if (t === "bytes" || t === "string") {
    const b = t === "string" ? utf8(String(v)) : toBytes(v);
    const padded = new Uint8Array(Math.ceil(b.length / 32) * 32);
    padded.set(b);
    return concatBytes(word(BigInt(b.length)), padded);
  }

  if (t === "bool") return word(v ? 1n : 0n);

  if (t === "address") {
    const a = toBytes(v);
    if (a.length !== 20) throw new Error("ABI: address must be 20 bytes");
    const out = new Uint8Array(32);
    out.set(a, 12);
    return out;
  }

  const fixedBytes = /^bytes(\d+)$/.exec(t);
  if (fixedBytes) {
    const n = Number(fixedBytes[1]);
    const b = toBytes(v);
    if (b.length !== n) throw new Error(`ABI: ${t} must be ${n} bytes, got ${b.length}`);
    const out = new Uint8Array(32);
    out.set(b); // bytesN is LEFT-aligned
    return out;
  }

  const uint = /^uint(\d+)$/.exec(t);
  if (uint) {
    const bits = BigInt(uint[1]);
    const x = toBigInt(v);
    if (x < 0n) throw new Error(`ABI: ${t} cannot encode a negative value`);
    if (x >= 1n << bits) throw new Error(`ABI: value exceeds ${t}`);
    return word(x);
  }

  throw new Error(`DreggLaunchpad ABI: unsupported type ${t}`);
}

/** Head/tail ABI encoding of a parameter list. */
function encodeParams(params: readonly AbiParam[], values: readonly unknown[]): Uint8Array {
  if (params.length !== values.length) {
    throw new Error(`ABI: expected ${params.length} argument(s), got ${values.length}`);
  }
  const encoded = params.map((p, i) => ({ dynamic: isDynamicType(p), bytes: encodeValue(p, values[i]) }));
  let headLen = 0;
  for (const e of encoded) headLen += e.dynamic ? 32 : e.bytes.length;

  const heads: Uint8Array[] = [];
  const tails: Uint8Array[] = [];
  let tailOffset = headLen;
  for (const e of encoded) {
    if (e.dynamic) {
      heads.push(word(BigInt(tailOffset)));
      tails.push(e.bytes);
      tailOffset += e.bytes.length;
    } else {
      heads.push(e.bytes);
    }
  }
  return concatBytes(...heads, ...tails);
}

function readWord(data: Uint8Array, at: number): Uint8Array {
  if (at + 32 > data.length) throw new Error("ABI: truncated data");
  return data.slice(at, at + 32);
}

function wordToBigInt(w: Uint8Array): bigint {
  let x = 0n;
  for (const b of w) x = (x << 8n) | BigInt(b);
  return x;
}

function decodeStatic(p: AbiParam, data: Uint8Array, at: number): unknown {
  const t = p.type;
  if (t === "tuple") {
    const out: Record<string, unknown> = {};
    let off = at;
    for (const c of p.components ?? []) {
      out[c.name] = decodeStatic(c, data, off);
      off += 32 * staticWords(c);
    }
    return out;
  }
  const w = readWord(data, at);
  if (t === "bool") return wordToBigInt(w) !== 0n;
  if (t === "address") return toChecksumAddress(hex0x(w.slice(12)).slice(2));
  const fixedBytes = /^bytes(\d+)$/.exec(t);
  if (fixedBytes) return hex0x(w.slice(0, Number(fixedBytes[1])));
  if (/^uint(\d+)$/.test(t)) return wordToBigInt(w);
  throw new Error(`DreggLaunchpad ABI: cannot decode type ${t}`);
}

function decodeDynamic(p: AbiParam, data: Uint8Array, at: number): unknown {
  const len = Number(wordToBigInt(readWord(data, at)));
  const body = data.slice(at + 32, at + 32 + len);
  if (body.length !== len) throw new Error("ABI: truncated dynamic data");
  return p.type === "string" ? new TextDecoder().decode(body) : hex0x(body);
}

function decodeParams(params: readonly AbiParam[], data: Uint8Array): unknown[] {
  const out: unknown[] = [];
  let head = 0;
  for (const p of params) {
    if (isDynamicType(p)) {
      if (p.type.startsWith("tuple") || p.type.endsWith("[]")) {
        throw new Error(`DreggLaunchpad ABI: cannot decode dynamic type ${p.type}`);
      }
      out.push(decodeDynamic(p, data, Number(wordToBigInt(readWord(data, head)))));
      head += 32;
    } else {
      out.push(decodeStatic(p, data, head));
      head += 32 * staticWords(p);
    }
  }
  return out;
}

/** `0x`-prefixed calldata for a launchpad function: selector ‖ encoded args. */
export function encodeFunctionData(name: string, args: readonly unknown[] = []): string {
  const e = findEntry("function", name);
  return hex0x(concatBytes(fromHex0x(selectorOf("function", name)), encodeParams(e.inputs, args)));
}

/** Decode an `eth_call` return into the function's positional outputs. */
export function decodeFunctionResult(name: string, data: string): unknown[] {
  const e = findEntry("function", name);
  return decodeParams(e.outputs ?? [], fromHex0x(data));
}

/**
 * Decode a launchpad call's ARGUMENTS back out of its calldata — the inverse of
 * `encodeFunctionData`. Lets a caller read back exactly what a built (or pending)
 * transaction will tell the launchpad, rather than trusting the intent that
 * produced it. Throws if the selector is not this function's.
 */
export function decodeFunctionArgs(name: string, calldata: string): unknown[] {
  const e = findEntry("function", name);
  const bytes = fromHex0x(calldata);
  const sel = hex0x(bytes.slice(0, 4));
  if (sel !== selectorOf("function", name)) {
    throw new Error(`DreggLaunchpad: calldata selector ${sel} is not ${name}'s`);
  }
  return decodeParams(e.inputs, bytes.slice(4));
}

export interface DecodedRevert {
  /** The error's name, e.g. `BidMismatch` — the contract's OWN reason. */
  name: string;
  signature: string;
  args: Record<string, unknown>;
}

/**
 * Decode a launchpad revert into the contract's named reason. Recognizes every
 * error a bidder's turn can hit (`DREGG_LAUNCHPAD_ABI`), plus the two builtins
 * `Error(string)` / `Panic(uint256)`. Returns `null` for revert data this ABI
 * does not know — a caller must NOT paper an unknown revert over as a known one.
 */
export function decodeLaunchpadRevert(data: string): DecodedRevert | null {
  let bytes: Uint8Array;
  try {
    bytes = fromHex0x(data);
  } catch {
    return null;
  }
  if (bytes.length < 4) return null;
  const sel = hex0x(bytes.slice(0, 4));
  const body = bytes.slice(4);

  if (sel === "0x08c379a0") {
    const [reason] = decodeParams([{ name: "reason", type: "string" }], body);
    return { name: "Error", signature: "Error(string)", args: { reason } };
  }
  if (sel === "0x4e487b71") {
    const [code] = decodeParams([{ name: "code", type: "uint256" }], body);
    return { name: "Panic", signature: "Panic(uint256)", args: { code } };
  }

  for (const e of DREGG_LAUNCHPAD_ABI) {
    if (e.type !== "error") continue;
    if (selectorOf("error", e.name) !== sel) continue;
    const values = decodeParams(e.inputs, body);
    const args: Record<string, unknown> = {};
    e.inputs.forEach((p, i) => { args[p.name] = values[i]; });
    return { name: e.name, signature: signatureOf("error", e.name), args };
  }
  return null;
}

// ─── The launch's disclosed schedule ──────────────────────────────────────────

/**
 * `DreggLaunchpad.Schedule` — the DISCLOSED supply/vesting terms. Field order is
 * the contract's; `abi.encode` is order-sensitive, so it is taken from the ABI
 * (`checkSchedule`'s tuple), never retyped here.
 */
export interface LaunchSchedule {
  totalSupply: bigint;
  saleSupply: bigint;
  creatorAllocation: bigint;
  poolAllocation: bigint;
  creatorLockUntil: bigint | number;
  reservePrice: bigint;
  graduationBps: number;
}

function scheduleParam(): AbiParam {
  const p = findEntry("function", "checkSchedule").inputs.find(x => x.name === "s");
  if (!p) throw new Error("DreggLaunchpad ABI: checkSchedule has no schedule param");
  return p;
}

/**
 * `keccak256(abi.encode(s))` — the launch's `scheduleCommit`. A bidder checks a
 * launch page's claimed schedule against `scheduleCommitOf(launchId)` with this
 * and NO RPC beyond the one read: the disclosure is publicly re-derivable, which
 * is the whole point of committing it (`registerLaunch`, `checkSchedule`).
 */
export function scheduleCommit(s: LaunchSchedule): string {
  return hex0x(keccak256(encodeParams([scheduleParam()], [s])));
}

export const LAUNCH_PHASES = ["None", "Commit", "Reveal", "Cleared", "Finalized"] as const;
export type LaunchPhase = (typeof LAUNCH_PHASES)[number];

export function phaseName(value: number | bigint): LaunchPhase {
  const i = Number(value);
  const p = LAUNCH_PHASES[i];
  if (!p) throw new Error(`DreggLaunchpad: unknown phase ${i}`);
  return p;
}

/**
 * The contract's `REFUND_GRACE` (`7 days`) mirrored for UI arithmetic — how long
 * after `revealEnd` a stuck launch's escrow becomes permissionlessly reclaimable.
 * A mirror, so `test/launchpad.test.mjs` pins it against the Solidity source; the
 * authoritative value is the `REFUND_GRACE()` read, which this ABI exposes.
 */
export const REFUND_GRACE_SECONDS = 7 * 24 * 60 * 60;

// ─── Transactions: the request (offline) and the raw signing (existing leg) ────

export interface TxRequest {
  /** The launchpad address. */
  to: string;
  /** The bidder — `msg.sender`, and the address sealed INTO the bid. */
  from?: string;
  /** `0x…` calldata. */
  data: string;
  /** `0x…` wei to attach (the escrow, for `commitBid`). */
  value: string;
  chainId: number;
}

/** The fee/nonce fields only an RPC can supply. See the module header. */
export interface TxGas {
  nonce: number | bigint;
  maxFeePerGas: bigint | string;
  maxPriorityFeePerGas: bigint | string;
  gasLimit: bigint | string;
}

/** Thrown by a read with no `eth_call` transport wired — the RPC dependency, by name. */
export class RpcRequiredError extends Error {
  constructor(what: string) {
    super(
      `DreggLaunchpad.${what}: reading on-chain state needs an eth_call transport ` +
      `(an RPC endpoint + the deployed launchpad address). Construct the client with ` +
      `{ ethCall } to enable reads; the commit/reveal transaction BUILDING path needs none.`,
    );
    this.name = "RpcRequiredError";
  }
}

function minimalBytes(x: bigint): Uint8Array {
  if (x < 0n) throw new Error("RLP: negative");
  if (x === 0n) return new Uint8Array(0); // RLP encodes 0 as the empty string
  const hex = x.toString(16);
  return fromHex0x(hex.length % 2 ? "0" + hex : hex);
}

type RlpItem = Uint8Array | RlpItem[];

function rlpLength(len: number, offset: number): Uint8Array {
  if (len < 56) return Uint8Array.of(offset + len);
  const lenBytes = minimalBytes(BigInt(len));
  return concatBytes(Uint8Array.of(offset + 55 + lenBytes.length), lenBytes);
}

function rlpEncode(item: RlpItem): Uint8Array {
  if (item instanceof Uint8Array) {
    if (item.length === 1 && item[0] < 0x80) return item;
    return concatBytes(rlpLength(item.length, 0x80), item);
  }
  const body = concatBytes(...item.map(rlpEncode));
  return concatBytes(rlpLength(body.length, 0xc0), body);
}

function txFields(req: TxRequest, gas: TxGas): RlpItem[] {
  const to = fromHex0x(req.to);
  if (to.length !== 20) throw new Error("signTxRequest: `to` must be a 20-byte address");
  return [
    minimalBytes(BigInt(req.chainId)),
    minimalBytes(toBigInt(gas.nonce)),
    minimalBytes(toBigInt(gas.maxPriorityFeePerGas)),
    minimalBytes(toBigInt(gas.maxFeePerGas)),
    minimalBytes(toBigInt(gas.gasLimit)),
    to,
    minimalBytes(toBigInt(req.value)),
    fromHex0x(req.data),
    [], // accessList — empty
  ];
}

/** The EIP-1559 signing digest: `keccak256(0x02 ‖ rlp([chainId, nonce, …]))`. */
export function eip1559SigningDigest(req: TxRequest, gas: TxGas): Uint8Array {
  return keccak256(concatBytes(Uint8Array.of(0x02), rlpEncode(txFields(req, gas))));
}

export interface SignedTx {
  /** `0x02…` — the raw EIP-1559 transaction, ready for `eth_sendRawTransaction`. */
  rawTransaction: string;
  /** The transaction hash it will have once mined. */
  transactionHash: string;
  /** The digest that was signed. */
  digest: string;
  /** The recovered sender — asserted to equal the signing key's own address. */
  from: string;
}

/**
 * Sign a launchpad `TxRequest` as a type-2 (EIP-1559) transaction with the
 * EXTENSION'S OWN secp256k1 key — `./evm`'s `signDigest`, the same leg that
 * serves `personal_sign` and EIP-712. No second signer, no second key: the
 * bidder address sealed into the bid is this key's address, so only this key can
 * produce the `msg.sender` the launchpad recomputes the seal against.
 *
 * Broadcasting the result is the caller's (RPC) business — see the module header.
 */
export function signTxRequest(privateKey: Uint8Array, req: TxRequest, gas: TxGas): SignedTx {
  const fields = txFields(req, gas);
  const digest = eip1559SigningDigest(req, gas);
  const sig = signDigest(privateKey, digest);
  // EIP-1559 carries yParity (0/1), not the EIP-155 v; `signDigest` reports 27/28.
  const yParity = sig.v - 27;
  const signed = concatBytes(
    Uint8Array.of(0x02),
    rlpEncode([
      ...fields,
      minimalBytes(BigInt(yParity)),
      minimalBytes(BigInt(sig.r)),
      minimalBytes(BigInt(sig.s)),
    ]),
  );
  const from = recoverAddress(digest, fromHex0x(sig.signature));
  if (req.from && from.toLowerCase() !== req.from.toLowerCase()) {
    throw new Error(
      `signTxRequest: the signing key recovers to ${from}, not the requested sender ${req.from} — ` +
      `the seal binds the bidder address, so a bid signed by the wrong key can never reveal`,
    );
  }
  return {
    rawTransaction: hex0x(signed),
    transactionHash: hex0x(keccak256(signed)),
    digest: hex0x(digest),
    from,
  };
}

// ─── The opening store — the thing a commit is worthless without ───────────────

/**
 * A stored OPENING: everything needed to reveal, and nothing that can be
 * recomputed from the chain. The launchpad publishes only `seal` during the
 * commit window; `revealBid` demands `(price, qty, salt)` back and recomputes
 * `keccak256(abi.encode(price, qty, salt, bidder))` against it.
 *
 * If this record is lost, the bid CANNOT be revealed — not by the bidder, not by
 * the operator, not by anyone: `salt` is 32 fresh random bytes and the seal is a
 * preimage-resistant hash of it. That is the design working (it is what makes the
 * bid hiding), not a bug to route around. The escrow is not lost with it: see
 * `OpeningLostError` and `reclaimEscrowTx`.
 */
export interface LaunchpadOpening {
  chainId: number;
  /** The launchpad contract this bid lives in. */
  launchpad: string;
  launchId: string;
  /** The bidder — sealed into the commitment. */
  bidder: string;
  /** wei per whole token. */
  price: string;
  /** whole tokens. */
  qty: string;
  /** The 32-byte hiding nonce. THE unrecoverable part. */
  salt: string;
  /** The commitment escrowed on-chain. */
  seal: string;
  /** The wei escrowed with the commit (`price * qty`). */
  deposit: string;
  createdAt: number;
}

/** Identifies one bid: a launch (chain + launchpad + id) and a bidder. */
export interface OpeningRef {
  chainId: number;
  launchpad: string;
  launchId: string | number | bigint;
  bidder: string;
}

/**
 * The store key. Keyed by LAUNCH **and** BIDDER — a wallet may hold several
 * identities and a launch id is only unique within one launchpad on one chain,
 * so a narrower key would let one bid's opening silently overwrite another's.
 */
export function openingKey(ref: OpeningRef): string {
  return [
    String(ref.chainId),
    ref.launchpad.toLowerCase(),
    String(ref.launchId),
    ref.bidder.toLowerCase(),
  ].join(":");
}

/** The persistence the store needs — `chrome.storage.local` in the extension. */
export interface OpeningKv {
  get(): Promise<Record<string, LaunchpadOpening>>;
  set(map: Record<string, LaunchpadOpening>): Promise<void>;
}

/**
 * The bidder committed, and the opening is gone. UNRECOVERABLE BY CONSTRUCTION —
 * there is no derivation, no support path, and no operator override that can
 * reveal this bid, because the salt was random and the chain only ever saw its
 * hash. The bid will not clear and the tokens will not be awarded.
 *
 * The ESCROW, however, is not gone. `DreggLaunchpad` has two exits and this bid
 * still reaches one of them:
 *  - the launch CLEARS → `settleBid(launchId, bidder)` refunds the whole deposit
 *    (an unrevealed committer has `filled == 0`, so `payment == 0`);
 *  - the launch STALLS → past `revealEnd + REFUND_GRACE` (7 days),
 *    `reclaimEscrow(launchId)` returns the whole deposit permissionlessly.
 * Both are permissionless. `recovery` carries the shape of that path so a UI can
 * offer it instead of pretending the bid is still alive.
 */
export class OpeningLostError extends Error {
  readonly name = "OpeningLostError";
  /** Not "try again later" — no future state of the world reveals this bid. */
  readonly unrecoverable = true;
  readonly ref: OpeningRef;
  readonly recovery = {
    bidCanBeRevealed: false,
    escrowIsRecoverable: true,
    ifLaunchClears: "settleBid(launchId, bidder) — an unrevealed committer is filled 0, so the whole deposit is refunded",
    ifLaunchStalls: `reclaimEscrow(launchId) — permissionless once revealEnd + REFUND_GRACE (${REFUND_GRACE_SECONDS}s) has passed`,
  } as const;

  constructor(ref: OpeningRef) {
    super(
      `No stored opening for launch ${String(ref.launchId)} on launchpad ${ref.launchpad} ` +
      `(chain ${ref.chainId}) as ${ref.bidder}. This bid CANNOT be revealed: the salt was 32 ` +
      `random bytes and the chain only ever saw keccak256(price,qty,salt,bidder) — losing the ` +
      `opening is unrecoverable by construction. The ESCROW is still recoverable: settleBid() ` +
      `refunds it in full if the launch clears, and reclaimEscrow() does so permissionlessly ` +
      `once the launch is past revealEnd + REFUND_GRACE (${REFUND_GRACE_SECONDS}s) without clearing.`,
    );
    this.ref = ref;
  }
}

/** The stored opening does not open its own seal — refuse rather than reveal garbage. */
export class OpeningTamperedError extends Error {
  readonly name = "OpeningTamperedError";
  readonly ref: OpeningRef;
  readonly recomputed: string;
  readonly expected: string;
  constructor(ref: OpeningRef, recomputed: string, expected: string) {
    super(
      `The stored opening for launch ${String(ref.launchId)} does not open its own seal ` +
      `(recomputed ${recomputed}, stored ${expected}). Revealing it would be refused on-chain ` +
      `with BidMismatch. The stored record is corrupt or was edited; the bid is treated as ` +
      `unrevealable — recover the escrow via settleBid()/reclaimEscrow().`,
    );
    this.ref = ref;
    this.recomputed = recomputed;
    this.expected = expected;
  }
}

/**
 * The openings a bidder MUST keep to reveal. Backed by the extension's existing
 * sealed `chrome.storage.local` (the same store the wallet's other secrets live
 * in) via an injected `OpeningKv`, so this class is exactly the code the
 * background runs and is drivable offline against a plain map.
 */
export class LaunchpadOpeningStore {
  constructor(private readonly kv: OpeningKv) {}

  /**
   * Persist an opening. REFUSES to overwrite an existing one: the launchpad
   * accepts one commitment per address (`AlreadyCommitted`), so a second local
   * write for the same (launch, bidder) could only destroy the opening of a bid
   * that is already escrowed on-chain — turning a live bid into an unrevealable
   * one. Pass `{ replace: true }` only when the first commit is known never to
   * have been sent.
   */
  async put(opening: LaunchpadOpening, opts: { replace?: boolean } = {}): Promise<void> {
    const key = openingKey(opening);
    const map = await this.kv.get();
    if (map[key] && !opts.replace) {
      throw new Error(
        `An opening is already stored for launch ${opening.launchId} as ${opening.bidder}. ` +
        `The launchpad takes ONE commitment per address (AlreadyCommitted), so overwriting it ` +
        `would strand the escrowed bid with no opening. Reveal the stored bid, or pass ` +
        `replace:true if the stored commit was never broadcast.`,
      );
    }
    map[key] = opening;
    await this.kv.set(map);
  }

  async get(ref: OpeningRef): Promise<LaunchpadOpening | null> {
    const map = await this.kv.get();
    return map[openingKey(ref)] ?? null;
  }

  async list(filter?: { chainId?: number; launchpad?: string; bidder?: string }): Promise<LaunchpadOpening[]> {
    const map = await this.kv.get();
    return Object.values(map).filter(o =>
      (filter?.chainId === undefined || o.chainId === filter.chainId)
      && (filter?.launchpad === undefined || o.launchpad.toLowerCase() === filter.launchpad.toLowerCase())
      && (filter?.bidder === undefined || o.bidder.toLowerCase() === filter.bidder.toLowerCase()));
  }

  async remove(ref: OpeningRef): Promise<boolean> {
    const map = await this.kv.get();
    const key = openingKey(ref);
    if (!(key in map)) return false;
    delete map[key];
    await this.kv.set(map);
    return true;
  }

  /**
   * Fetch the opening for a reveal, checking it still opens its own seal. The
   * ONLY way to a reveal: a missing opening throws `OpeningLostError` (naming the
   * refund backstop) and a corrupt one throws `OpeningTamperedError` — neither is
   * ever silently swallowed into an "empty" or "not yet" state.
   */
  async requireForReveal(ref: OpeningRef): Promise<LaunchpadOpening> {
    const opening = await this.get(ref);
    if (!opening) throw new OpeningLostError(ref);
    const check = checkLaunchpadReveal(
      BigInt(opening.price),
      BigInt(opening.qty),
      opening.salt,
      opening.bidder,
      opening.seal,
    );
    if (!check.ok) throw new OpeningTamperedError(ref, check.recomputed, check.expected);
    return opening;
  }
}

// ─── The client ───────────────────────────────────────────────────────────────

/** An `eth_call` transport: returns the `0x…` return data. The RPC dependency. */
export type EthCall = (request: { to: string; data: string }) => Promise<string>;

export interface BidState {
  committed: boolean;
  revealed: boolean;
  price: bigint;
  qty: bigint;
  filled: bigint;
  settled: boolean;
  deposit: bigint;
}

export interface LaunchpadClientOptions {
  /** The DEPLOYED launchpad address (a deploy-time input; nothing here assumes one). */
  address: string;
  chainId: number;
  /** Optional `eth_call` transport. Without it, reads throw `RpcRequiredError`. */
  ethCall?: EthCall;
}

/**
 * The bidder's client for a deployed `DreggLaunchpad`. Writes build a
 * `TxRequest` (offline, complete); reads go through the injected `EthCall`.
 */
export class DreggLaunchpadClient {
  readonly address: string;
  readonly chainId: number;
  private readonly ethCall?: EthCall;

  constructor(opts: LaunchpadClientOptions) {
    if (fromHex0x(opts.address).length !== 20) {
      throw new Error("DreggLaunchpadClient: address must be a 20-byte launchpad address");
    }
    this.address = toChecksumAddress(opts.address.replace(/^0x/, "").toLowerCase());
    this.chainId = opts.chainId;
    this.ethCall = opts.ethCall;
  }

  private tx(data: string, value: bigint, from?: string): TxRequest {
    return { to: this.address, from, data, value: "0x" + value.toString(16), chainId: this.chainId };
  }

  /**
   * Seal a bid and build its `commitBid` transaction. The seal comes from
   * `./sealedbid`'s `launchpadSeal` — the derivation cross-pinned to the
   * contract's `sealOf`; this client never re-derives it. The escrow attached is
   * the bidder's own maximum payment `price * qty` (a smaller one is refused at
   * reveal with `UnderCollateralized`; the excess over the UNIFORM clearing price
   * comes back at settlement).
   *
   * The returned `opening` is what MUST be persisted before this transaction is
   * broadcast — see `LaunchpadOpeningStore`.
   */
  commitBid(params: {
    launchId: string | number | bigint;
    price: bigint;
    qty: bigint;
    salt: string;
    bidder: string;
    /** Eligibility evidence for a gated launch (`ILaunchEligibility`); `0x` when open. */
    proof?: string;
  }): { tx: TxRequest; seal: LaunchpadSeal; opening: LaunchpadOpening } {
    const seal = launchpadSeal(params.price, params.qty, params.salt, params.bidder);
    const data = encodeFunctionData("commitBid", [
      toBigInt(params.launchId),
      seal.seal,
      params.proof ?? "0x",
    ]);
    const deposit = BigInt(seal.deposit);
    return {
      tx: this.tx(data, deposit, params.bidder),
      seal,
      opening: {
        chainId: this.chainId,
        launchpad: this.address,
        launchId: String(params.launchId),
        bidder: params.bidder,
        price: seal.price,
        qty: seal.qty,
        salt: seal.salt,
        seal: seal.seal,
        deposit: seal.deposit,
        createdAt: Date.now(),
      },
    };
  }

  /**
   * Build the `revealBid` transaction from a stored opening. The opening is
   * re-checked against its own seal first: a reveal that does not open the
   * commitment is refused on-chain (`BidMismatch`), so it is refused here rather
   * than spending gas to be told.
   */
  revealBid(opening: LaunchpadOpening): { tx: TxRequest; binds: boolean } {
    const check = checkLaunchpadReveal(
      BigInt(opening.price),
      BigInt(opening.qty),
      opening.salt,
      opening.bidder,
      opening.seal,
    );
    if (!check.ok) {
      throw new OpeningTamperedError(
        { chainId: opening.chainId, launchpad: opening.launchpad, launchId: opening.launchId, bidder: opening.bidder },
        check.recomputed,
        check.expected,
      );
    }
    const data = encodeFunctionData("revealBid", [
      toBigInt(opening.launchId),
      BigInt(opening.price),
      BigInt(opening.qty),
      opening.salt,
    ]);
    return { tx: this.tx(data, 0n, opening.bidder), binds: true };
  }

  /** `settleBid` — the cleared-launch exit: tokens for a winner, the deposit back for anyone else. */
  settleBidTx(params: { launchId: string | number | bigint; bidder: string; from?: string }): TxRequest {
    return this.tx(
      encodeFunctionData("settleBid", [toBigInt(params.launchId), params.bidder]),
      0n,
      params.from ?? params.bidder,
    );
  }

  /**
   * `reclaimEscrow` — the STUCK-launch exit, and the backstop a bidder who lost
   * their opening is pointed at. Permissionless once `revealEnd + REFUND_GRACE`
   * has passed with no clearing; before that the chain refuses it by name
   * (`RefundNotYetAvailable(refundableAt)`).
   */
  reclaimEscrowTx(params: { launchId: string | number | bigint; from?: string }): TxRequest {
    return this.tx(encodeFunctionData("reclaimEscrow", [toBigInt(params.launchId)]), 0n, params.from);
  }

  private async call(name: string, args: readonly unknown[]): Promise<unknown[]> {
    if (!this.ethCall) throw new RpcRequiredError(name);
    const data = await this.ethCall({ to: this.address, data: encodeFunctionData(name, args) });
    return decodeFunctionResult(name, data);
  }

  /** The launch's phase — `None` for a launch that does not exist. */
  async phaseOf(launchId: string | number | bigint): Promise<LaunchPhase> {
    const [v] = await this.call("phaseOf", [toBigInt(launchId)]);
    return phaseName(v as bigint);
  }

  /** The bidder's OWN commit state: committed / revealed / filled / the escrow held. */
  async bidOf(launchId: string | number | bigint, bidder: string): Promise<BidState> {
    const [committed, revealed, price, qty, filled, settled, deposit] =
      await this.call("getBid", [toBigInt(launchId), bidder]);
    return {
      committed: committed as boolean,
      revealed: revealed as boolean,
      price: price as bigint,
      qty: qty as bigint,
      filled: filled as bigint,
      settled: settled as boolean,
      deposit: deposit as bigint,
    };
  }

  /** Whether the launch is in its permissionless refund window (stuck, never cleared). */
  async refundable(launchId: string | number | bigint): Promise<boolean> {
    const [v] = await this.call("refundable", [toBigInt(launchId)]);
    return v as boolean;
  }

  /** The launch's committed schedule hash — compare against `scheduleCommit(s)`. */
  async scheduleCommitOf(launchId: string | number | bigint): Promise<string> {
    const [v] = await this.call("scheduleCommitOf", [toBigInt(launchId)]);
    return v as string;
  }

  /**
   * Check a claimed schedule against the launch's on-chain commitment — the
   * REPLAYABLE disclosure. Verified locally too (`scheduleCommit`), so a bidder
   * who has the schedule hash needs no second round-trip to trust the page.
   */
  async checkSchedule(launchId: string | number | bigint, s: LaunchSchedule): Promise<boolean> {
    const [v] = await this.call("checkSchedule", [toBigInt(launchId), s]);
    return v as boolean;
  }

  /** The contract's OWN seal derivation — a cross-check of `launchpadSeal` against the deployed code. */
  async sealOf(price: bigint, qty: bigint, salt: string, bidder: string): Promise<string> {
    const [v] = await this.call("sealOf", [price, qty, salt, bidder]);
    return v as string;
  }

  async clearingPriceOf(launchId: string | number | bigint): Promise<bigint> {
    const [v] = await this.call("clearingPriceOf", [toBigInt(launchId)]);
    return v as bigint;
  }

  async soldQtyOf(launchId: string | number | bigint): Promise<bigint> {
    const [v] = await this.call("soldQtyOf", [toBigInt(launchId)]);
    return v as bigint;
  }

  async tokenOf(launchId: string | number | bigint): Promise<string> {
    const [v] = await this.call("tokenOf", [toBigInt(launchId)]);
    return v as string;
  }

  async launchCount(): Promise<bigint> {
    const [v] = await this.call("launchCount", []);
    return v as bigint;
  }

  /** The contract's own `REFUND_GRACE` — the authority `REFUND_GRACE_SECONDS` mirrors. */
  async refundGrace(): Promise<bigint> {
    const [v] = await this.call("REFUND_GRACE", []);
    return v as bigint;
  }
}

// ─── The page-request adapters (what `window.dregg.launchpad` sends) ───────────

/**
 * Build the client for the launchpad a page request names. The address and chain
 * are the CALLER'S — a launchpad is a deployed contract and the extension pins no
 * address — so both are validated here rather than defaulted into fiction.
 */
export function launchpadFromRequest(request: Record<string, unknown>): DreggLaunchpadClient {
  const address = String(request.launchpad ?? "");
  const chainId = Number(request.chainId ?? 0);
  if (!address) throw new Error("launchpad: a launchpad address is required");
  if (!Number.isInteger(chainId) || chainId <= 0) {
    throw new Error("launchpad: a positive integer chainId is required");
  }
  return new DreggLaunchpadClient({ address, chainId });
}

/**
 * The RPC-sourced fee fields, iff the request carries a COMPLETE set. A nonce and
 * the fee market exist only on a live node, so a partial set is treated as none:
 * signing a transaction with a guessed nonce is worse than handing back the
 * request and naming the dependency.
 */
export function txGasFromRequest(request: Record<string, unknown>): TxGas | null {
  const tx = request.tx as Record<string, unknown> | undefined;
  if (!tx || typeof tx !== "object") return null;
  const fields = ["nonce", "maxFeePerGas", "maxPriorityFeePerGas", "gasLimit"];
  if (!fields.every(k => tx[k] !== undefined && tx[k] !== null && tx[k] !== "")) return null;
  return {
    nonce: BigInt(String(tx.nonce)),
    maxFeePerGas: BigInt(String(tx.maxFeePerGas)),
    maxPriorityFeePerGas: BigInt(String(tx.maxPriorityFeePerGas)),
    gasLimit: BigInt(String(tx.gasLimit)),
  };
}

/** The unsigned half of a launchpad result, with the RPC dependency spelled out. */
export const UNSIGNED_TX_REASON =
  "no nonce/gas supplied: a nonce and the current fee market can only come from an RPC. "
  + "Broadcast this request through a provider, or pass "
  + "tx:{nonce,maxFeePerGas,maxPriorityFeePerGas,gasLimit} to get a signed rawTransaction back.";

/**
 * Sign a built launchpad transaction when the caller supplied the fee fields;
 * otherwise return the unsigned request and SAY why. Signing goes through
 * `signTxRequest` → `./evm`'s `signDigest`: the extension's one secp256k1 key,
 * the same one the bid's seal binds.
 */
export function signedOrUnsignedTx(
  privateKey: Uint8Array,
  tx: TxRequest,
  gas: TxGas | null,
): Record<string, unknown> {
  if (!gas) return { tx, signed: false, unsignedReason: UNSIGNED_TX_REASON };
  const signed = signTxRequest(privateKey, tx, gas);
  return {
    tx,
    signed: true,
    rawTransaction: signed.rawTransaction,
    transactionHash: signed.transactionHash,
    from: signed.from,
  };
}
