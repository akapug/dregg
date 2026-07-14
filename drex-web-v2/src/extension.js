// extension.js — the frontend ↔ ./extension handshake. The installed Dragon's
// Egg Cipherclerk (window.dregg) is the IDENTITY + WALLET + SIGNER; this app is
// the ORCHESTRATOR. Every signing action routes through the extension's real
// page API (extension/src/page.ts): the EVM leg (dregg.evm), the sealed-bid
// commit→reveal ceremony (dregg.sealedBid), and the dregg-native order-turn
// (dregg.drex.placeOrder). NOTHING is signed in-page; the extension holds keys.
//
// Detection is the real one page.ts uses: window.dregg is defined by the
// injected page script, which fires a `dregg:ready` event on install. If no
// extension is present, `detect()` resolves { installed:false } and the UI shows
// the honest install prompt — it never fakes a wallet.

// Resolve the installed extension (or report absent). Handles both orders:
// window.dregg already injected, or the `dregg:ready` event still to fire.
export function detect(timeoutMs = 1200) {
  return new Promise((resolve) => {
    if (typeof window !== 'undefined' && window.dregg) return resolve({ installed: true, api: window.dregg });
    let done = false;
    const onReady = () => {
      if (done) return; done = true;
      window.removeEventListener('dregg:ready', onReady);
      resolve(window.dregg ? { installed: true, api: window.dregg } : { installed: false });
    };
    if (typeof window !== 'undefined') window.addEventListener('dregg:ready', onReady);
    setTimeout(() => {
      if (done) return; done = true;
      if (typeof window !== 'undefined') window.removeEventListener('dregg:ready', onReady);
      resolve(window && window.dregg ? { installed: true, api: window.dregg } : { installed: false });
    }, timeoutMs);
  });
}

function api() {
  if (typeof window === 'undefined' || !window.dregg) {
    throw new Error('the Dragon\'s Egg Cipherclerk is not installed — no window.dregg');
  }
  return window.dregg;
}

// ── connect / authorize — the consent handshake (dregg.authorize) ──
// Requests permission to place DrEX orders; the extension renders its
// authorization-first confirm popup. Also pulls the EVM address so the UI can
// show the one identity that does both the dregg-native order + the on-chain
// escrow leg.
export async function connect() {
  const d = api();
  const auth = await d.authorize({ action: 'drex.trade', resource: 'drex', mode: 'selective' });
  let evmAddress = null;
  try { evmAddress = (await d.evm.getAddress()).address; } catch (_e) { /* EVM leg optional */ }
  let connected = true;
  try { connected = await d.isConnected(); } catch (_e) { /* older builds */ }
  return { auth, evmAddress, connected };
}

// ── sealed-bid commit (dregg.sealedBid.commit) ──
// Hides the order behind keccak256, escrows it via an EIP-712 `SealedBid`
// signature (the extension's EVM key signs), stores the opening in the
// extension. Returns the commitment + the signed escrow envelope — the exact
// shape an on-chain `SealedAuction` verifies.
export function sealedCommit({ auctionId, order, chainId, verifyingContract, deadline }) {
  return api().sealedBid.commit({ auctionId, order, chainId, verifyingContract, deadline });
}

// ── sealed-bid reveal (dregg.sealedBid.reveal) ──
// Returns the opening (order, salt) + a `RevealBid` signature and confirms it
// binds to the commitment. `bindsCommitment` is the extension's own re-hash
// check — the same recomputation the on-chain revealBid runs.
export function sealedReveal({ auctionId }) {
  return api().sealedBid.reveal({ auctionId });
}

// ── dregg-native order-turn (dregg.drex.placeOrder) ──
// Signs the order as a real dregg Turn with the sealed key, and (given holdings)
// attaches a REAL Bulletproof solvency proof bound to the order-turn id and a
// blinded ring-membership eligibility proof.
export function placeOrder(order, opts) {
  return api().drex.placeOrder(order, opts);
}

// ── EVM address (dregg.evm.getAddress) ──
export function evmAddress() {
  return api().evm.getAddress();
}
