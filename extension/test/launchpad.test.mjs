import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

import {
  DREGG_LAUNCHPAD_ABI,
  DreggLaunchpadClient,
  LaunchpadOpeningStore,
  OpeningLostError,
  OpeningTamperedError,
  RpcRequiredError,
  REFUND_GRACE_SECONDS,
  decodeFunctionArgs,
  decodeLaunchpadRevert,
  encodeFunctionData,
  eventTopic,
  openingKey,
  scheduleCommit,
  selectorOf,
  signatureOf,
  signTxRequest,
  launchpadFromRequest,
  txGasFromRequest,
  signedOrUnsignedTx,
} from './.build/launchpad.mjs';
import { deriveEvmIdentity } from './.build/evm.mjs';

const HERE = dirname(fileURLToPath(import.meta.url));
const CHAIN_DIR = resolve(HERE, '../../chain');
const LAUNCHPAD_SOL = resolve(CHAIN_DIR, 'contracts/launchpad/DreggLaunchpad.sol');

// ─── The fixtures ──────────────────────────────────────────────────────────────
//
// The bid is the SAME one `test/sealedbid.test.mjs` pins and
// `chain/test/P0ParityLaunchLoop.t.sol::test_SealVector_MatchesTheExtensionDerivation`
// asserts on the contract side. The client must carry exactly that seal into
// `commitBid` calldata: a client that seals differently produces bids the
// launchpad can never reveal (`BidMismatch`), which is the bug this vector exists
// to catch — so it is re-pinned HERE, through the calldata the client actually
// emits, not just through the seal function.
const BIDDER = '0x00000000000000000000000000000000000A11CE';
const PRICE = 5000000000n; // 5 gwei per whole token
const QTY = 400n;
const SALT = '0x000000000000000000000000000000000000000000000000000000000d1e55ed';
const SEAL_VECTOR = '0xc9b84c4f878aeb4b76a6ffa62d14611a5226a9d4015a9eb4818aa04db238c0bb';

// A launchpad address is a DEPLOY-TIME input. Nothing here needs a live one: the
// client builds calldata offline and reads go through an injected transport, so
// this is a placeholder address and every test below runs with no RPC and no
// deployed contract.
const PAD = '0x000000000000000000000000000000000000BEEF';
const CHAIN_ID = 46630; // Robinhood Chain (the launchpad's target), per DreggLaunchpad.sol
const LAUNCH_ID = 7;

function client(ethCall) {
  return new DreggLaunchpadClient({ address: PAD, chainId: CHAIN_ID, ethCall });
}

/**
 * A stand-in for `chrome.storage.local`, with its serialization: every write
 * round-trips through JSON, so an opening holding a bigint (or anything else the
 * real store cannot persist) fails here exactly as it would in the browser.
 */
function memoryKv() {
  let map = {};
  return {
    async get() { return JSON.parse(JSON.stringify(map)); },
    async set(next) { map = JSON.parse(JSON.stringify(next)); },
    raw: () => map,
  };
}

function ref(over = {}) {
  return { chainId: CHAIN_ID, launchpad: PAD, launchId: String(LAUNCH_ID), bidder: BIDDER, ...over };
}

// ══════════════════════════════════════════════════════════════════════════════
// 1 — THE HONEST POLE, FIRST: a sealed bid commits, is kept, and REVEALS.
// ══════════════════════════════════════════════════════════════════════════════

test('the honest pole: commit → keep the opening → reveal, end to end and offline', async () => {
  const pad = client();
  const store = new LaunchpadOpeningStore(memoryKv());

  // COMMIT: seal the bid, build the transaction, keep the opening.
  const { tx, seal, opening } = pad.commitBid({
    launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER,
  });
  await store.put(opening);

  // The seal that goes on-chain is the pinned cross-language one.
  assert.equal(seal.seal, SEAL_VECTOR);
  // The escrow is the bidder's own maximum payment (`UnderCollateralized` otherwise).
  assert.equal(tx.value, '0x' + (PRICE * QTY).toString(16));
  assert.equal(tx.to, '0x000000000000000000000000000000000000bEEF'); // EIP-55 of PAD
  assert.equal(tx.chainId, CHAIN_ID);

  // REVEAL: a different session, a fresh store handle over the same storage —
  // the opening is restored and the reveal binds.
  const restored = await store.requireForReveal(ref());
  assert.equal(restored.seal, SEAL_VECTOR);
  const { tx: revealTx, binds } = pad.revealBid(restored);
  assert.equal(binds, true);

  // The reveal calldata carries EXACTLY the committed opening back.
  const [id, price, qty, salt] = decodeFunctionArgs('revealBid', revealTx.data);
  assert.equal(id, BigInt(LAUNCH_ID));
  assert.equal(price, PRICE);
  assert.equal(qty, QTY);
  assert.equal(salt, SALT);
  assert.equal(revealTx.value, '0x0'); // revealBid is not payable
});

test('calldata decodes back to the call it encodes, and refuses the wrong selector', () => {
  const { tx } = client().commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER });
  assert.deepEqual(decodeFunctionArgs('commitBid', tx.data), [BigInt(LAUNCH_ID), SEAL_VECTOR, '0x']);
  assert.throws(() => decodeFunctionArgs('revealBid', tx.data), /is not revealBid's/);
});

// ══════════════════════════════════════════════════════════════════════════════
// 2 — THE ABI IS THE CONTRACT'S (derived, not asserted)
// ══════════════════════════════════════════════════════════════════════════════

function forgeAbi() {
  try {
    const out = execFileSync('forge', ['inspect', 'DreggLaunchpad', 'abi', '--json'], {
      cwd: CHAIN_DIR, encoding: 'utf8', timeout: 600_000, stdio: ['ignore', 'pipe', 'pipe'],
    });
    return JSON.parse(out);
  } catch (e) {
    return { unavailable: e.message };
  }
}

const normParam = (p) => ({
  name: p.name,
  type: p.type,
  ...(p.indexed !== undefined ? { indexed: p.indexed } : {}),
  ...(p.components ? { components: p.components.map(normParam) } : {}),
});

const normEntry = (e) => ({
  type: e.type,
  name: e.name,
  inputs: (e.inputs ?? []).map(normParam),
  ...(e.type === 'function' ? { outputs: (e.outputs ?? []).map(normParam), stateMutability: e.stateMutability } : {}),
  ...(e.type === 'event' ? { anonymous: !!e.anonymous } : {}),
});

test('every ABI entry is byte-identical to the compiled contract (forge inspect)', (t) => {
  // THE drift gate. `src/launchpad.ts` hand-copies a SUBSET of the contract's
  // compiled ABI; this re-derives the real one from
  // `chain/contracts/launchpad/DreggLaunchpad.sol` and compares entry by entry.
  // A signature change on either side turns this red instead of silently
  // producing calldata the launchpad decodes into something else.
  const real = forgeAbi();
  if (real.unavailable) {
    t.skip(`forge is not available, so the ABI cannot be re-derived from the contract: ${real.unavailable}`);
    return;
  }
  assert.ok(Array.isArray(real) && real.length > 0, 'forge returned an ABI');

  for (const ours of DREGG_LAUNCHPAD_ABI) {
    const theirs = real.find(e => e.type === ours.type && e.name === ours.name);
    assert.ok(theirs, `the contract declares ${ours.type} ${ours.name}`);
    assert.deepEqual(
      normEntry(ours),
      normEntry(theirs),
      `${ours.type} ${ours.name} matches the contract's compiled ABI exactly`,
    );
  }
});

test('selectors are keccak of the ABI signature and match cast sig', () => {
  // Vectors from `cast sig "<signature>"` (foundry), not from our own keccak —
  // an independent tool computing the same 4 bytes.
  const vectors = {
    commitBid: ['commitBid(uint256,bytes32,bytes)', '0x91749f23'],
    revealBid: ['revealBid(uint256,uint256,uint256,bytes32)', '0xa20e7816'],
    settleBid: ['settleBid(uint256,address)', '0xe55df556'],
    reclaimEscrow: ['reclaimEscrow(uint256)', '0x1f9cc9af'],
    phaseOf: ['phaseOf(uint256)', '0x9a243ebf'],
    getBid: ['getBid(uint256,address)', '0xeba1b60b'],
    refundable: ['refundable(uint256)', '0x90445a6c'],
    sealOf: ['sealOf(uint256,uint256,bytes32,address)', '0xd6f41b26'],
    scheduleCommitOf: ['scheduleCommitOf(uint256)', '0x68d3980e'],
    clearingPriceOf: ['clearingPriceOf(uint256)', '0x6657fb61'],
    soldQtyOf: ['soldQtyOf(uint256)', '0x6e4cad9f'],
    checkSchedule: ['checkSchedule(uint256,(uint256,uint256,uint256,uint256,uint64,uint256,uint16))', '0x8f07e483'],
  };
  for (const [name, [sig, selector]] of Object.entries(vectors)) {
    assert.equal(signatureOf('function', name), sig, `${name} signature`);
    assert.equal(selectorOf('function', name), selector, `${name} selector`);
  }
});

test('error selectors and event topics match cast', () => {
  const errors = {
    BidMismatch: '0x90d5a467',
    UnderCollateralized: '0x019a2247',
    NotCommitPhase: '0xdc816a87',
    NotRevealPhase: '0xd1088db6',
    AlreadyCommitted: '0xbfec5558',
    AlreadyRevealed: '0xa89ac151',
    NoCommit: '0xfbd0656a',
    NotEligible: '0x3a1c1545',
    NoSuchLaunch: '0x84385c76',
    RefundNotYetAvailable: '0x2f222a18',
    LaunchAlreadyCleared: '0xde0762c7',
    AlreadyRefunded: '0xa85e6f1a',
    NothingToRefund: '0xf76aef65',
  };
  for (const [name, selector] of Object.entries(errors)) {
    assert.equal(selectorOf('error', name), selector, `${name} selector`);
  }
  // `cast keccak "BidCommitted(uint256,address,bytes32,uint256)"` etc.
  assert.equal(eventTopic('BidCommitted'), '0xac0361642c7caf4d76d0e2dfbe38804253aedd43a560146470da108817ceb405');
  assert.equal(eventTopic('BidRevealed'), '0xcb6c2dec3ffcf2b41060c9d3c54fb8dc170a2df672e7d4de62dfb54d13a8cd32');
});

test('REFUND_GRACE_SECONDS mirrors the contract constant', () => {
  // The mirror is only for UI arithmetic; the authority is the `REFUND_GRACE()`
  // read. Pin it against the source so the "you can reclaim after N" a bidder is
  // told cannot drift from the chain that enforces it.
  const src = readFileSync(LAUNCHPAD_SOL, 'utf8');
  assert.match(src, /uint64 public constant REFUND_GRACE = 7 days;/);
  assert.equal(REFUND_GRACE_SECONDS, 7 * 24 * 60 * 60);
});

// ══════════════════════════════════════════════════════════════════════════════
// 3 — THE CALLDATA IS WHAT THE CHAIN EXPECTS (cast vectors)
// ══════════════════════════════════════════════════════════════════════════════

test('commit calldata is byte-identical to cast, and carries the pinned seal', () => {
  const { tx } = client().commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER });
  // `cast calldata "commitBid(uint256,bytes32,bytes)" 7 <SEAL_VECTOR> 0x`
  assert.equal(
    tx.data,
    '0x91749f23'
    + '0000000000000000000000000000000000000000000000000000000000000007'
    + 'c9b84c4f878aeb4b76a6ffa62d14611a5226a9d4015a9eb4818aa04db238c0bb'
    + '0000000000000000000000000000000000000000000000000000000000000060'
    + '0000000000000000000000000000000000000000000000000000000000000000',
  );
  // The seal inside the calldata IS the cross-language vector — the launchpad
  // recomputes exactly this at `revealBid`.
  assert.ok(tx.data.includes(SEAL_VECTOR.slice(2)));
});

test('a gated launch carries its eligibility proof as real dynamic bytes', () => {
  const { tx } = client().commitBid({
    launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER, proof: '0xdeadbeef',
  });
  // `cast calldata "commitBid(uint256,bytes32,bytes)" 7 <SEAL_VECTOR> 0xdeadbeef`
  assert.equal(
    tx.data,
    '0x91749f23'
    + '0000000000000000000000000000000000000000000000000000000000000007'
    + 'c9b84c4f878aeb4b76a6ffa62d14611a5226a9d4015a9eb4818aa04db238c0bb'
    + '0000000000000000000000000000000000000000000000000000000000000060'
    + '0000000000000000000000000000000000000000000000000000000000000004'
    + 'deadbeef00000000000000000000000000000000000000000000000000000000',
  );
});

test('reveal / settle / reclaim calldata are byte-identical to cast', async () => {
  const pad = client();
  const store = new LaunchpadOpeningStore(memoryKv());
  const { opening } = pad.commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER });
  await store.put(opening);

  // `cast calldata "revealBid(uint256,uint256,uint256,bytes32)" 7 5000000000 400 <SALT>`
  assert.equal(
    pad.revealBid(await store.requireForReveal(ref())).tx.data,
    '0xa20e7816'
    + '0000000000000000000000000000000000000000000000000000000000000007'
    + '000000000000000000000000000000000000000000000000000000012a05f200'
    + '0000000000000000000000000000000000000000000000000000000000000190'
    + '0000000000000000000000000000000000000000000000000000000d1e55ed'.padStart(64, '0'),
  );
  // `cast calldata "settleBid(uint256,address)" 7 0x…0A11CE`
  assert.equal(
    pad.settleBidTx({ launchId: LAUNCH_ID, bidder: BIDDER }).data,
    '0xe55df556'
    + '0000000000000000000000000000000000000000000000000000000000000007'
    + '00000000000000000000000000000000000000000000000000000000000a11ce',
  );
  // `cast calldata "reclaimEscrow(uint256)" 7`
  assert.equal(
    pad.reclaimEscrowTx({ launchId: LAUNCH_ID }).data,
    '0x1f9cc9af0000000000000000000000000000000000000000000000000000000000000007',
  );
});

test('the disclosed schedule hashes to the contract commitment', () => {
  const s = {
    totalSupply: 1_000_000_000n,
    saleSupply: 850_000_000n,
    creatorAllocation: 50_000_000n,
    poolAllocation: 100_000_000n,
    creatorLockUntil: 10_000n,
    reservePrice: 1_000_000_000n,
    graduationBps: 5000,
  };
  // `cast keccak $(cast abi-encode "f((uint256,uint256,uint256,uint256,uint64,uint256,uint16))" "(…)")`
  // — i.e. `keccak256(abi.encode(s))`, exactly what `registerLaunch` commits and
  // `checkSchedule` recomputes. A bidder verifies a launch page's claimed
  // disclosure against `scheduleCommitOf` with this and no trust in the page.
  assert.equal(scheduleCommit(s), '0x60b5bb9cd31a5931fc555c2b2b6e3508913d2365a27d5bf161344dadfe2411e2');

  // …and the same encoding drives the on-chain check.
  assert.equal(
    encodeFunctionData('checkSchedule', [7n, s]).slice(0, 10),
    '0x8f07e483',
  );
});

test('the encoder fails closed on values the chain could not carry', () => {
  const pad = client();
  assert.throws(() => pad.commitBid({ launchId: 1n << 256n, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER }), /uint256/);
  assert.throws(() => pad.commitBid({ launchId: 1, price: PRICE, qty: QTY, salt: '0xdead', bidder: BIDDER }), /32 bytes/);
  assert.throws(() => pad.commitBid({ launchId: 1, price: -1n, qty: QTY, salt: SALT, bidder: BIDDER }), /negative/);
  assert.throws(() => new DreggLaunchpadClient({ address: '0xdead', chainId: 1 }), /20-byte/);
});

// ══════════════════════════════════════════════════════════════════════════════
// 4 — THE OPENING STORE (a commit without its opening is a dead bid)
// ══════════════════════════════════════════════════════════════════════════════

test('the opening survives storage: it is JSON-persistable, keyed by launch AND bidder', async () => {
  const kv = memoryKv();
  const store = new LaunchpadOpeningStore(kv);
  const pad = client();

  const mine = pad.commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER });
  const bob = '0x00000000000000000000000000000000000B0B00';
  const theirs = pad.commitBid({ launchId: LAUNCH_ID, price: 4000000000n, qty: QTY, salt: SALT, bidder: bob });

  await store.put(mine.opening);
  await store.put(theirs.opening); // same launch, other bidder: MUST NOT collide

  assert.equal(Object.keys(kv.raw()).length, 2);
  assert.notEqual(openingKey(ref()), openingKey(ref({ bidder: bob })));
  assert.equal((await store.get(ref())).seal, SEAL_VECTOR);
  assert.equal((await store.get(ref({ bidder: bob }))).price, '4000000000');
  // Nor across launches, launchpads, or chains.
  assert.notEqual(openingKey(ref()), openingKey(ref({ launchId: '8' })));
  assert.notEqual(openingKey(ref()), openingKey(ref({ chainId: 1 })));
  assert.notEqual(openingKey(ref()), openingKey(ref({ launchpad: '0x0000000000000000000000000000000000001234' })));
  // Case never splits a key.
  assert.equal(openingKey(ref()), openingKey(ref({ bidder: BIDDER.toLowerCase() })));

  assert.equal((await store.list({ bidder: BIDDER })).length, 1);
  assert.equal((await store.list()).length, 2);
});

test('a lost opening is reported UNRECOVERABLE and points at the refund backstop', async () => {
  const store = new LaunchpadOpeningStore(memoryKv());

  // Nothing stored: the bidder committed on-chain and the opening is gone.
  await assert.rejects(() => store.requireForReveal(ref()), (err) => {
    assert.ok(err instanceof OpeningLostError);
    // NOT "empty", NOT "try later", NOT a null the caller might treat as "no bid".
    assert.equal(err.unrecoverable, true);
    assert.equal(err.recovery.bidCanBeRevealed, false);
    // The escrow is NOT lost with the bid — both permissionless exits are named.
    assert.equal(err.recovery.escrowIsRecoverable, true);
    assert.match(err.message, /CANNOT be revealed/);
    assert.match(err.message, /unrecoverable by construction/);
    assert.match(err.message, /reclaimEscrow/);
    assert.match(err.message, /REFUND_GRACE/);
    assert.match(err.recovery.ifLaunchClears, /settleBid/);
    assert.match(err.recovery.ifLaunchStalls, /reclaimEscrow/);
    return true;
  });

  // And the client can hand the bidder that exact backstop transaction.
  assert.equal(
    client().reclaimEscrowTx({ launchId: LAUNCH_ID, from: BIDDER }).data,
    '0x1f9cc9af0000000000000000000000000000000000000000000000000000000000000007',
  );
});

test('a tampered opening fails the reveal check instead of being revealed', async () => {
  const pad = client();

  for (const [what, mutate] of [
    ['salt', (o) => ({ ...o, salt: '0x' + '11'.repeat(32) })],
    ['price', (o) => ({ ...o, price: '9000000000' })],
    ['qty', (o) => ({ ...o, qty: '401' })],
    ['bidder', (o) => ({ ...o, bidder: '0x00000000000000000000000000000000000B0B00' })],
    ['seal', (o) => ({ ...o, seal: '0x' + 'ab'.repeat(32) })],
  ]) {
    const kv = memoryKv();
    const store = new LaunchpadOpeningStore(kv);
    const { opening } = pad.commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER });
    await store.put(opening);

    // Something edited the stored record between commit and reveal.
    const corrupt = mutate(opening);
    await kv.set({ [openingKey(corrupt)]: corrupt });

    await assert.rejects(
      () => store.requireForReveal(ref({ bidder: corrupt.bidder })),
      (err) => {
        assert.ok(err instanceof OpeningTamperedError, `${what}: reported as tampered`);
        assert.notEqual(err.recomputed, err.expected);
        assert.match(err.message, /BidMismatch/); // the on-chain refusal it would earn
        return true;
      },
      `a tampered ${what} must not reveal`,
    );

    // The direct path refuses too — the check is not only in the store.
    assert.throws(() => pad.revealBid(corrupt), OpeningTamperedError);
  }
});

test('storing a second opening for the same bid is refused (it would strand the escrow)', async () => {
  const store = new LaunchpadOpeningStore(memoryKv());
  const pad = client();
  const first = pad.commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER });
  await store.put(first.opening);

  const second = pad.commitBid({ launchId: LAUNCH_ID, price: 9000000000n, qty: QTY, salt: '0x' + '22'.repeat(32), bidder: BIDDER });
  // The launchpad takes ONE commitment per address (`AlreadyCommitted`); silently
  // overwriting would leave the ESCROWED bid with no opening — a dead bid.
  await assert.rejects(() => store.put(second.opening), /AlreadyCommitted|already stored/);
  assert.equal((await store.get(ref())).seal, SEAL_VECTOR, 'the first opening is intact');

  // An explicit replace is available for a commit that was never broadcast.
  await store.put(second.opening, { replace: true });
  assert.equal((await store.get(ref())).seal, second.seal.seal);

  assert.equal(await store.remove(ref()), true);
  assert.equal(await store.remove(ref()), false);
});

// ══════════════════════════════════════════════════════════════════════════════
// 5 — READS (offline against a transport stub; the RPC is a NAMED dependency)
// ══════════════════════════════════════════════════════════════════════════════

test('reads decode the contract return shapes', async () => {
  const seen = [];
  const stub = async ({ to, data }) => {
    seen.push({ to, data });
    if (data.startsWith(selectorOf('function', 'phaseOf'))) {
      return '0x' + (1).toString(16).padStart(64, '0'); // Phase.Commit
    }
    if (data.startsWith(selectorOf('function', 'getBid'))) {
      // `cast abi-encode "f(bool,bool,uint256,uint256,uint256,bool,uint256)" true true 5000000000 400 50 false 2000000000000`
      return '0x'
        + '0000000000000000000000000000000000000000000000000000000000000001'
        + '0000000000000000000000000000000000000000000000000000000000000001'
        + '000000000000000000000000000000000000000000000000000000012a05f200'
        + '0000000000000000000000000000000000000000000000000000000000000190'
        + '0000000000000000000000000000000000000000000000000000000000000032'
        + '0000000000000000000000000000000000000000000000000000000000000000'
        + '000000000000000000000000000000000000000000000000000001d1a94a2000';
    }
    if (data.startsWith(selectorOf('function', 'refundable'))) return '0x' + '0'.repeat(64);
    if (data.startsWith(selectorOf('function', 'tokenOf'))) {
      return '0x' + '000000000000000000000000' + 'cafe'.padStart(40, '0');
    }
    if (data.startsWith(selectorOf('function', 'REFUND_GRACE'))) {
      return '0x' + (7 * 24 * 60 * 60).toString(16).padStart(64, '0');
    }
    throw new Error(`unexpected call ${data.slice(0, 10)}`);
  };
  const pad = client(stub);

  assert.equal(await pad.phaseOf(LAUNCH_ID), 'Commit');
  assert.deepEqual(await pad.bidOf(LAUNCH_ID, BIDDER), {
    committed: true, revealed: true, price: 5000000000n, qty: 400n, filled: 50n, settled: false, deposit: 2000000000000n,
  });
  assert.equal(await pad.refundable(LAUNCH_ID), false);
  // The decoded address is EIP-55 checksummed — `cast to-check-sum-address 0x…cafe`.
  assert.equal(await pad.tokenOf(LAUNCH_ID), '0x000000000000000000000000000000000000cafE');
  // The mirror is the contract's real constant.
  assert.equal(Number(await pad.refundGrace()), REFUND_GRACE_SECONDS);

  // Every read went to the launchpad address with a selector-prefixed payload.
  assert.ok(seen.length >= 5);
  for (const call of seen) assert.equal(call.to.toLowerCase(), PAD.toLowerCase());
});

test('a read with no RPC transport names the dependency instead of inventing state', async () => {
  const pad = client(); // no ethCall — the offline construction
  await assert.rejects(() => pad.phaseOf(LAUNCH_ID), (err) => {
    assert.ok(err instanceof RpcRequiredError);
    assert.match(err.message, /eth_call transport/);
    assert.match(err.message, /RPC endpoint \+ the deployed launchpad address/);
    return true;
  });
  // …while the write path stays fully usable with no RPC at all.
  assert.ok(pad.commitBid({ launchId: 1, price: PRICE, qty: QTY, salt: SALT, bidder: BIDDER }).tx.data.startsWith('0x91749f23'));
});

// ══════════════════════════════════════════════════════════════════════════════
// 6 — REVERTS COME BACK BY THE CONTRACT'S OWN NAME
// ══════════════════════════════════════════════════════════════════════════════

test('a launchpad revert decodes to its named reason and arguments', () => {
  assert.deepEqual(decodeLaunchpadRevert('0x90d5a467'), {
    name: 'BidMismatch', signature: 'BidMismatch()', args: {},
  });

  // `cast calldata "UnderCollateralized(uint256,uint256)" 1000 2000`
  const under = decodeLaunchpadRevert(
    '0x019a2247'
    + '00000000000000000000000000000000000000000000000000000000000003e8'
    + '00000000000000000000000000000000000000000000000000000000000007d0',
  );
  assert.equal(under.name, 'UnderCollateralized');
  assert.deepEqual(under.args, { deposit: 1000n, needed: 2000n });

  // `cast calldata "RefundNotYetAvailable(uint64)" 1893456000`
  const early = decodeLaunchpadRevert('0x2f222a180000000000000000000000000000000000000000000000000000000070dbd880');
  assert.equal(early.name, 'RefundNotYetAvailable');
  assert.equal(early.args.refundableAt, 1893456000n);

  // `cast calldata "NotEligible(address)" 0x…0A11CE`
  const gated = decodeLaunchpadRevert('0x3a1c154500000000000000000000000000000000000000000000000000000000000a11ce');
  assert.equal(gated.name, 'NotEligible');
  // EIP-55 checksummed — `cast to-check-sum-address 0x…0A11CE`.
  assert.equal(gated.args.bidder, '0x00000000000000000000000000000000000A11cE');

  // The builtins, too.
  const str = decodeLaunchpadRevert(
    '0x08c379a0'
    + '0000000000000000000000000000000000000000000000000000000000000020'
    + '0000000000000000000000000000000000000000000000000000000000000004'
    + '6e6f706500000000000000000000000000000000000000000000000000000000',
  );
  assert.deepEqual(str, { name: 'Error', signature: 'Error(string)', args: { reason: 'nope' } });
});

test('an unknown revert is reported as unknown, never papered over', () => {
  assert.equal(decodeLaunchpadRevert('0xdeadbeef'), null); // not a launchpad error
  assert.equal(decodeLaunchpadRevert('0x'), null);
  assert.equal(decodeLaunchpadRevert('not hex at all'), null);
});

// ══════════════════════════════════════════════════════════════════════════════
// 7 — SIGNING GOES THROUGH THE EXTENSION'S ONE EVM LEG
// ══════════════════════════════════════════════════════════════════════════════

const TEST_SEED = new Uint8Array(32).fill(0x42); // a test seed; no live key is used anywhere here
const GAS = { nonce: 3, maxPriorityFeePerGas: 1_000_000_000n, maxFeePerGas: 30_000_000_000n, gasLimit: 200_000n };

test('the commit transaction is signed by the same key that the seal binds', () => {
  // The bidder address is DERIVED from the wallet seed by `src/evm.ts` — the one
  // secp256k1 leg. The launchpad recomputes the seal against `msg.sender`, so the
  // signer and the sealed bidder must be the same key; here they are, by
  // construction rather than by convention.
  const id = deriveEvmIdentity(TEST_SEED);
  const pad = client();
  const { tx, seal } = pad.commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: id.address });

  const signed = signTxRequest(id.privateKey, tx, GAS);
  assert.equal(signed.from, id.address); // recovered from the signature, not asserted
  assert.match(signed.rawTransaction, /^0x02[0-9a-f]+$/);
  assert.match(signed.transactionHash, /^0x[0-9a-f]{64}$/);
  assert.notEqual(seal.seal, SEAL_VECTOR); // a different bidder ⇒ a different seal
});

test('a transaction signed by the wrong key is refused, not sent to fail on-chain', () => {
  const mine = deriveEvmIdentity(TEST_SEED);
  const other = deriveEvmIdentity(new Uint8Array(32).fill(0x43));
  const { tx } = client().commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: mine.address });
  assert.throws(
    () => signTxRequest(other.privateKey, tx, GAS),
    /the seal binds the bidder address/,
  );
});

// ══════════════════════════════════════════════════════════════════════════════
// 8 — THE PAGE-REQUEST ADAPTERS (the exact code the background worker runs)
// ══════════════════════════════════════════════════════════════════════════════

test('a request names its own deployed launchpad, or is refused', () => {
  const pad = launchpadFromRequest({ launchpad: PAD, chainId: CHAIN_ID });
  assert.equal(pad.chainId, CHAIN_ID);
  assert.equal(pad.address.toLowerCase(), PAD.toLowerCase());
  // The extension pins NO launchpad address and NO chain: a request that omits
  // them is refused rather than defaulted to somewhere real.
  assert.throws(() => launchpadFromRequest({ chainId: CHAIN_ID }), /launchpad address is required/);
  assert.throws(() => launchpadFromRequest({ launchpad: PAD }), /chainId is required/);
  assert.throws(() => launchpadFromRequest({ launchpad: PAD, chainId: 0 }), /chainId is required/);
  assert.throws(() => launchpadFromRequest({ launchpad: PAD, chainId: 1.5 }), /chainId is required/);
});

test('gas is taken only as a COMPLETE RPC-sourced set', () => {
  const full = { nonce: 3, maxFeePerGas: '30000000000', maxPriorityFeePerGas: '1000000000', gasLimit: 200000 };
  assert.deepEqual(txGasFromRequest({ tx: full }), {
    nonce: 3n, maxFeePerGas: 30_000_000_000n, maxPriorityFeePerGas: 1_000_000_000n, gasLimit: 200_000n,
  });
  // Nonce 0 is a REAL nonce (a first-ever transaction) — it must not read as absent.
  assert.equal(txGasFromRequest({ tx: { ...full, nonce: 0 } }).nonce, 0n);

  assert.equal(txGasFromRequest({}), null);
  // A partial set never becomes a guessed nonce.
  for (const drop of ['nonce', 'maxFeePerGas', 'maxPriorityFeePerGas', 'gasLimit']) {
    const partial = { ...full };
    delete partial[drop];
    assert.equal(txGasFromRequest({ tx: partial }), null, `missing ${drop} ⇒ no signing`);
  }
});

test('no gas ⇒ the unsigned request plus the named RPC reason; gas ⇒ a raw transaction', () => {
  const id = deriveEvmIdentity(TEST_SEED);
  const { tx } = client().commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: id.address });

  const unsigned = signedOrUnsignedTx(id.privateKey, tx, null);
  assert.equal(unsigned.signed, false);
  assert.equal(unsigned.rawTransaction, undefined); // nothing half-signed escapes
  assert.deepEqual(unsigned.tx, tx); // …but the call itself is complete and offline
  assert.match(unsigned.unsignedReason, /can only come from an RPC/);

  const signed = signedOrUnsignedTx(id.privateKey, tx, GAS);
  assert.equal(signed.signed, true);
  assert.equal(signed.from, id.address);
  assert.match(signed.rawTransaction, /^0x02[0-9a-f]+$/);
  assert.equal(signed.unsignedReason, undefined);
});

test('foundry decodes our raw transaction back to the fields we built', (t) => {
  // A cross-tool pin on the RLP/EIP-1559 serialization: `cast decode-transaction`
  // parses the raw bytes independently and must recover the same call, value,
  // chain, nonce — and the same sender, from the signature alone.
  const id = deriveEvmIdentity(TEST_SEED);
  const pad = client();
  const { tx } = pad.commitBid({ launchId: LAUNCH_ID, price: PRICE, qty: QTY, salt: SALT, bidder: id.address });
  const signed = signTxRequest(id.privateKey, tx, GAS);

  let decoded;
  try {
    let out = JSON.parse(execFileSync('cast', ['decode-transaction', signed.rawTransaction], {
      encoding: 'utf8', timeout: 60_000, stdio: ['ignore', 'pipe', 'pipe'],
    }));
    if (typeof out === 'string') out = JSON.parse(out); // cast emits the JSON as a string
    decoded = out;
  } catch (e) {
    t.skip(`cast is not available to independently decode the raw transaction: ${e.message}`);
    return;
  }

  assert.equal(decoded.type, '0x2', 'an EIP-1559 transaction');
  assert.equal(decoded.to.toLowerCase(), PAD.toLowerCase());
  // Foundry recovers the sender from the SIGNATURE — the seal's bidder is the signer.
  assert.equal(decoded.signer.toLowerCase(), id.address.toLowerCase());
  assert.equal(decoded.input.toLowerCase(), tx.data.toLowerCase());
  assert.equal(BigInt(decoded.value), PRICE * QTY);
  assert.equal(BigInt(decoded.chainId), BigInt(CHAIN_ID));
  assert.equal(BigInt(decoded.nonce), 3n);
  assert.equal(BigInt(decoded.gas), 200_000n);
  assert.equal(BigInt(decoded.maxFeePerGas), 30_000_000_000n);
  assert.equal(BigInt(decoded.maxPriorityFeePerGas), 1_000_000_000n);
  assert.deepEqual(decoded.accessList, []);
  assert.equal(decoded.hash.toLowerCase(), signed.transactionHash.toLowerCase());
});
