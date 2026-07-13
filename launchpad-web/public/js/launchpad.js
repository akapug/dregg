// launchpad.js — the launch flow, driving the REAL DreggLaunchpad contract.
// Every function here is a real on-chain call (or a real read); there is no mirror
// of the clearing mechanism — the contract computes and verifies it.

/* global ethers */
import { state } from './app.js';

// ── (a) register a launch with a DISCLOSED schedule (no hidden supply) ──
// The schedule MUST close: saleSupply + creatorAllocation == totalSupply, or the
// contract reverts (SupplyDoesNotClose). Returns { launchId, token }.
export async function register({ name, symbol, totalSupply, saleSupply, creatorAllocation,
  creatorLockUntil, reservePriceWei, commitDuration, revealDuration }) {
  const s = [BigInt(totalSupply), BigInt(saleSupply), BigInt(creatorAllocation),
    BigInt(creatorLockUntil), BigInt(reservePriceWei)];
  const tx = await state.pad.registerLaunch(name, symbol, s, commitDuration, revealDuration,
    ethers.ZeroAddress, ethers.ZeroAddress);
  const rc = await tx.wait();
  // pull the LaunchRegistered event for the id + token
  let launchId = null, token = null;
  for (const log of rc.logs) {
    try { const p = state.pad.interface.parseLog(log);
      if (p && p.name === 'LaunchRegistered') { launchId = p.args.launchId.toString(); token = p.args.token; } }
    catch (_e) {}
  }
  return { launchId, token, txHash: rc.hash, schedule: {
    totalSupply: String(totalSupply), saleSupply: String(saleSupply),
    creatorAllocation: String(creatorAllocation), creatorLockUntil: String(creatorLockUntil),
    reservePrice: String(reservePriceWei) } };
}

// ── (b) sealed commit ──
// The seal is computed by the ON-CHAIN `sealOf` view — the exact preimage encoding
// the contract will re-check in revealBid (no JS re-derivation, no drift). The salt
// is generated + kept locally; losing it means you cannot reveal (fail-closed UX).
export function freshSalt() { return ethers.hexlify(ethers.randomBytes(32)); }

export async function seal(priceWei, qty, salt, bidder) {
  return state.pad.sealOf(BigInt(priceWei), BigInt(qty), salt, bidder);
}

export async function commit({ launchId, priceWei, qty, salt }) {
  const sealedHash = await seal(priceWei, qty, salt, state.account);
  const deposit = BigInt(priceWei) * BigInt(qty); // escrow the max payment
  const tx = await state.pad.commitBid(launchId, sealedHash, '0x', { value: deposit });
  const rc = await tx.wait();
  return { sealedHash, deposit: deposit.toString(), txHash: rc.hash };
}

// ── (b) reveal ──
export async function reveal({ launchId, priceWei, qty, salt }) {
  const tx = await state.pad.revealBid(launchId, BigInt(priceWei), BigInt(qty), salt);
  const rc = await tx.wait();
  return { txHash: rc.hash };
}

// ── (c) build the clearing order (untrusted search the contract VERIFIES) ──
// Sort the revealed bidders descending by price; the contract re-checks this is a
// permutation (no-drop/no-insert) and non-increasing before it walks the fill.
// `bids` = the /api/launches/:id detail's bids array (revealed subset).
export function clearingOrder(bids) {
  const revealed = bids.filter((b) => b.revealed);
  // the on-chain _revealedBidders order is push-order of reveals; we return the
  // permutation of THAT array's indices, sorted by descending price.
  const idx = revealed.map((_, i) => i);
  idx.sort((a, b) => {
    const pa = BigInt(revealed[a].price), pb = BigInt(revealed[b].price);
    return pb > pa ? 1 : pb < pa ? -1 : 0;
  });
  return { order: idx, revealed };
}

export async function finalize({ launchId, order }) {
  const tx = await state.pad.finalizeClearing(launchId, order.map((i) => BigInt(i)), '0x');
  const rc = await tx.wait();
  return { txHash: rc.hash };
}

// ── (d) settle a bidder (permissionless; every winner pays the uniform price) ──
export async function settle({ launchId, bidder }) {
  const tx = await state.pad.settleBid(launchId, bidder);
  const rc = await tx.wait();
  return { txHash: rc.hash };
}

// ── read helpers over the backend API ──
export async function fetchLaunches() { return (await (await fetch('/api/launches')).json()).launches; }
export async function fetchLaunch(id) { const r = await fetch('/api/launches/' + id); return r.ok ? r.json() : null; }
export async function submitDisclosure(id, schedule, meta) {
  const r = await fetch(`/api/launches/${id}/disclose`, { method: 'POST',
    headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ schedule, meta }) });
  return r.json();
}
