// api.js — the DrEX v2 API client. Thin wrappers over the REAL endpoints the
// dev server (serve.mjs) exposes. Every call here hits real Rust behind the
// server; nothing is mocked. The endpoint set mirrors the surfaces the protocol
// actually has today (open-tier clear + live-node settle + node status); the
// shielded / sealed-bid / composition endpoints are NAMED in `endpoints` with
// `live:false` so the UI can render them honestly (a control that is present but
// not-yet-wired), never as if they were live.

async function postJson(path, body) {
  const r = await fetch(path, {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(body),
  });
  const j = await r.json();
  return j;
}

// ── Tier 2 OPEN — the real multilateral ring/TTC clear (drex_clear). LIVE. ──
// Posts the revealed order book; the server shells to the `drex_clear` binary
// (solver.rs ring match → verified_settle.rs kernel fold). Returns the real
// cleared batch: the ring, per-trader allocations off the verified post-ledger,
// per-asset conservation, and the over-debit reject-polarity check.
export function clearOpen(orders) {
  return postJson('/clear', orders);
}

// ── Live-node settle — lands the cleared batch as one real turn. LIVE (solo). ──
export function settle(cleared) {
  return postJson('/settle', cleared);
}

// ── Node status probe — is a live dregg node reachable for settlement? ──
export async function nodeStatus() {
  try {
    const r = await fetch('/node/status');
    return r.json();
  } catch (e) {
    return { up: false, error: String(e && e.message || e) };
  }
}

// The endpoint map the UI reads to decide what is a live control vs. a
// deploy-gated one. `live` reflects what serve.mjs actually serves TODAY; the
// rest are named surfaces the phased build wires in (Phase 2 / Phase 3). This is
// the single source of truth for "don't render a not-yet-live flow as live".
export const endpoints = {
  clearOpen:      { path: '/clear',           live: true,  tier: 'open',     phase: 1, mechanism: 'ring' },
  settle:         { path: '/settle',          live: true,  tier: 'open',     phase: 1, note: 'solo dev node; no on-chain settle yet' },
  clearShielded:  { path: '/clear-shielded',  live: false, tier: 'shielded', phase: 2, note: 'fhEgg solver — plaintext Cert-F; wired in the v1 server (:8781), NOT yet served by v2 serve.mjs' },
  proveShielded:  { path: '/prove-shielded',  live: false, tier: 'shielded', phase: 2, note: 'real Cert-F STARK, reveal-nothing (seconds); wired in the v1 server (:8781), NOT yet served by v2 serve.mjs' },
  commitBid:      { path: '/bid',             live: false, tier: 'shielded', phase: 2, note: 'sealed-bid commit → on-chain commitBid — DESIGNED, not built (needs the public signed-data RPC)' },
  revealBid:      { path: '/reveal',          live: false, tier: 'shielded', phase: 2, note: 'sealed-bid reveal — DESIGNED, not built' },
  deposit:        { path: '/deposit',         live: false, tier: 'dark',     phase: 3, note: 'escrow-contract lock → LC attest → shield — escrow contract ember-gated' },
  clearDark:      { path: '/clear-dark',      live: false, tier: 'dark',     phase: 3, note: 'output-boundary MPC no-viewer clear — needs the persistent n-party federation' },
};
