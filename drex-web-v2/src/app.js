// app.js — the DrEX v2 product frontend (Preact + htm + signals).
//
// Rich Phase-1 seed (Open-first, extension-central). The extension (window.dregg)
// is the identity + wallet + signer; this app is the orchestrator. What is wired
// REAL end-to-end here:
//   • the app SHELL (header, wallet handshake, node probe);
//   • the TIER-DIAL as a first-class control — Open/Shielded/Dark, with the
//     "what each viewer sees" honest display, reusing the session's viz
//     (drex-web/drex-viz.js ringGraph) to redact the REAL cleared ring per tier;
//   • the OPEN-tier multilateral ring order-entry wired to the REAL /clear
//     (drex_clear: solver.rs + verified_settle.rs), built by REAL entry;
//   • the SEALED-BID commit→reveal two-phase ceremony routed through the REAL
//     extension (dregg.sealedBid.commit/reveal → real keccak256 + EIP-712 +
//     secp256k1), with the on-chain escrow post labelled deploy-gated;
//   • dregg-native order signing through dregg.drex.placeOrder.
// Shielded/Dark tiers and the other seven mechanisms are PRESENT as honestly-
// labelled controls; nothing not-yet-live is shown as live.
import { h, render } from 'preact';
import { signal, computed } from '@preact/signals';
import htm from 'htm';
import { clearOpen, settle, nodeStatus } from './api.js';
import * as ext from './extension.js';
import { TIERS, MECHANISMS, COMPOSITION, ASSETS } from './model.js';
import { ringGraph } from '../../drex-web/drex-viz.js';

const html = htm.bind(h);
const SHOW = (s) => ({ dangerouslySetInnerHTML: { __html: s } });

// ── app state ──
const activeTier = signal('open');
const activeMech = signal('ring');
const entryMode  = signal('direct');   // 'direct' | 'sealed'
const book = signal([
  { id: 1, trader: 'Ada',  offerAsset: 'GOLD', offerAmount: 100, wantAsset: 'ART',  wantMin: 10, priority: 3 },
  { id: 2, trader: 'Bram', offerAsset: 'ART',  offerAmount: 50,  wantAsset: 'WINE', wantMin: 20, priority: 1 },
  { id: 3, trader: 'Cyl',  offerAsset: 'WINE', offerAmount: 80,  wantAsset: 'GOLD', wantMin: 40, priority: 2 },
]);
const draft = signal({ trader: '', offerAsset: 'SILVER', offerAmount: 30, wantAsset: 'PEARL', wantMin: 5, priority: 4 });
const clearing = signal(null);
const clearBusy = signal(false);
const settleState = signal(null);
const node = signal({ up: null });
const wallet = signal({ status: 'unknown' });     // unknown|absent|detected|connected|error
const sealed = signal({ phase: 'idle' });          // idle|committed|revealed|error
const yourOrder = signal({ trader: 'You', offerAsset: 'SILVER', offerAmount: 30, wantAsset: 'PEARL', wantMin: 5, priority: 4 });

const tierById = (id) => TIERS.find(t => t.id === id);
const mechById = (id) => MECHANISMS.find(m => m.id === id);
const activeMechObj = computed(() => mechById(activeMech.value));

// Convert a REAL drex_clear result into the shape drex-viz.ringGraph expects
// (assets=nodes, orders parallel to solverCert edges/flows/caps). Faithful — it
// reads the cleared allocations, it does not synthesize a book.
function toVizRing(res) {
  const allocs = (res.allocations || []).filter(a => !a.rested);
  if (!allocs.length) return null;
  const assets = [...new Set(allocs.flatMap(a => [a.sentAsset, a.recvAsset]))];
  const idx = (a) => assets.indexOf(a);
  return {
    assets,
    orders: allocs.map(a => ({ trader: a.trader, offerAsset: a.sentAsset, wantAsset: a.recvAsset, offerAmount: a.offer, wantMin: a.wantMin })),
    solverCert: { edges: allocs.map(a => [idx(a.sentAsset), idx(a.recvAsset)]), f: allocs.map(a => Number(a.sent)), c: allocs.map(a => Number(a.offer)) },
  };
}
const vizRing = computed(() => (clearing.value && clearing.value.ring ? toVizRing(clearing.value) : null));

// ── header ──
function Header() {
  const n = node.value, w = wallet.value;
  const wlabel = w.status === 'connected' ? 'wallet: cipherclerk · connected' + (w.evmAddress ? ' · ' + w.evmAddress.slice(0, 6) + '…' : '')
    : w.status === 'detected' ? 'wallet: cipherclerk · detected'
    : w.status === 'absent' ? 'wallet: extension not installed'
    : 'wallet: detecting…';
  return html`
    <header class="hdr">
      <div class="brand">
        <span class="logo">◇</span>
        <div><div class="title">DrEX</div><div class="sub">one exchange · a privacy dial · one verified kernel</div></div>
      </div>
      <div class="pills">
        <span class=${'pill ' + (n.up === true ? 'live' : n.up === false ? 'warn' : '')}>
          ${n.up === true ? 'node: live @ ' + (n.node || '').replace(/^https?:\/\//, '') : n.up === false ? 'node: offline · local clear only' : 'node: probing…'}</span>
        <span class=${'pill ' + (w.status === 'connected' ? 'live' : w.status === 'absent' || w.status === 'error' ? 'warn' : '')}>${wlabel}</span>
      </div>
    </header>`;
}

// ── wallet handshake — connect to the installed extension ──
function WalletPanel() {
  const w = wallet.value;
  if (w.status === 'connected') {
    return html`<section class="card wallet ok">
      <div class="card-h">Wallet — Dragon's Egg Cipherclerk <span class="badge live">connected</span></div>
      <div class="wrow">dregg identity authorized for <span class="mono">drex.trade</span>${w.evmAddress ? html` · EVM leg <span class="mono">${w.evmAddress}</span>` : ''}</div>
      <div class="hint">one identity does both the dregg-native order-turn and the on-chain escrow leg. Every signature is gated by the extension's confirm-intent popup.</div>
    </section>`;
  }
  if (w.status === 'absent') {
    return html`<section class="card wallet warn">
      <div class="card-h">Wallet — extension required</div>
      <p>The Dragon's Egg Cipherclerk (<span class="mono">./extension</span>) is not installed in this browser, so there is no <span class="mono">window.dregg</span> to sign with.</p>
      <p class="honest">The seed refuses to fake a wallet. Sealed-bid signing and dregg-native order-turns route through the installed extension; without it those actions are unavailable. The Open-tier clear below still runs (the matcher does not need your key).</p>
      <button class="ghost" onClick=${detectWallet}>Re-check for the extension</button>
    </section>`;
  }
  // unknown / detected / error
  return html`<section class="card wallet">
    <div class="card-h">Wallet — Dragon's Egg Cipherclerk</div>
    <p>${w.status === 'detected' ? 'Extension detected. Connect to authorize DrEX trading and pull your identity.' : w.status === 'error' ? ('Connect failed: ' + (w.error || 'unknown')) : 'Detecting the installed extension…'}</p>
    <button class="primary" disabled=${w.status === 'unknown'} onClick=${connectWallet}>Connect the cipherclerk</button>
  </section>`;
}

async function detectWallet() {
  wallet.value = { status: 'unknown' };
  const d = await ext.detect();
  wallet.value = d.installed ? { status: 'detected' } : { status: 'absent' };
}
async function connectWallet() {
  try {
    const r = await ext.connect();
    wallet.value = { status: 'connected', evmAddress: r.evmAddress, auth: r.auth };
  } catch (e) {
    wallet.value = { status: 'error', error: String(e && e.message || e) };
  }
}

// ── the tier dial — first-class; live viewer-lens over the REAL cleared ring ──
function TierDial() {
  const t = tierById(activeTier.value);
  const vr = vizRing.value;
  return html`
    <section class="card dial">
      <div class="card-h">Privacy tier <span class="hint">— the dial over one kernel; the guarantee never moves, only what the world sees</span></div>
      <div class="dial-row">
        ${TIERS.slice().sort((a, b) => a.order - b.order).map(tier => html`
          <button class=${'tierbtn ' + (activeTier.value === tier.id ? 'on ' : '') + (tier.live ? '' : 'preview')}
            onClick=${() => (activeTier.value = tier.id)}
            title=${tier.live ? tier.tagline : 'preview — ' + (tier.deployDeps || []).join('; ')}>
            <span class="tname">${tier.name}</span>
            <span class=${'grade g-' + tier.grade.toLowerCase()}>${tier.grade}</span>
          </button>`)}
      </div>
      <div class="dial-body">
        <div class="lens">
          ${vr ? html`<div class="lenssvg" ...${SHOW(ringGraph(vr, activeTier.value))}></div>`
               : html`<div class="lens-empty">Clear a batch below to see the same ring through each viewer's eyes — Open shows every flow, Shielded blurs the amounts, Dark seals the orders.</div>`}
          ${!t.live && html`<div class="preview-tag">PREVIEW — not live with real money. ${t.grade}.</div>`}
        </div>
        <div class="tier-detail">
          <div class="tagline">${t.tagline}</div>
          <div class="posture">${t.posture}</div>
          <div class="whosees">
            <div><b>world sees</b><span>${t.whoSees.world}</span></div>
            <div><b>solver sees</b><span>${t.whoSees.solver}</span></div>
            <div><b>you see</b><span>${t.whoSees.you}</span></div>
          </div>
          ${!t.live && html`<div class="deploydeps">Deploy-gated: ${(t.deployDeps || []).join(' · ')}</div>`}
        </div>
      </div>
    </section>`;
}

// ── mechanism rail ──
function MechanismRail() {
  return html`
    <section class="card rail">
      <div class="card-h">Mechanism <span class="hint">— the 8-mechanism family; each has its own order shape</span></div>
      <div class="mech-list">
        ${MECHANISMS.map(m => {
          const runnable = m.live && m.tier === activeTier.value;
          return html`<button class=${'mechbtn ' + (activeMech.value === m.id ? 'on ' : '') + (runnable ? '' : 'muted')}
            onClick=${() => (activeMech.value = m.id)} title=${m.blurb}>
            <span class="mname">${m.name}</span>
            <span class=${'mtier tier-' + m.tier}>${m.tier}</span>
            ${!m.live && html`<span class="soon">${m.endpoint ? 'engine live · other tier' : 'not wired'}</span>`}
          </button>`;
        })}
      </div>
    </section>`;
}

// ── order entry — dispatch on the active mechanism ──
function OrderEntry() {
  const m = activeMechObj.value;
  if (!m) return null;
  if (m.id === 'ring') return html`<${RingEntry} />`;
  return html`
    <section class="card entry">
      <div class="card-h">Order entry — ${m.name}</div>
      <div class="notlive">
        <p><b>${m.name}</b> takes a <b>${m.orderShape}</b>-shaped order.</p>
        <p class="blurb">${m.blurb}</p>
        <p class="honest">Its order-entry form is part of the phased architecture (see the overhaul plan).
          ${m.endpoint ? html`A real engine serves it at <span class="mono">${m.endpoint}</span>, but at the <b>${m.tier}</b> tier — not the live Open path.` : 'It is not wired to a live endpoint yet.'}
          The live end-to-end flow today is the Open-tier multilateral ring clear.</p>
        <button class="ghost" onClick=${() => { activeTier.value = 'open'; activeMech.value = 'ring'; }}>→ Go to the live Open ring clear</button>
      </div>
    </section>`;
}

// ── the ring entry: a mode toggle between the direct open clear and the ──
// ── sealed-bid two-phase ceremony (routed through the extension) ──
function RingEntry() {
  return html`
    <section class="card entry">
      <div class="card-h">Order entry — Open multilateral ring <span class="badge live">LIVE · /clear</span></div>
      <div class="modetog">
        <button class=${'mtog ' + (entryMode.value === 'direct' ? 'on' : '')} onClick=${() => (entryMode.value = 'direct')}>Direct clear</button>
        <button class=${'mtog ' + (entryMode.value === 'sealed' ? 'on' : '')} onClick=${() => (entryMode.value = 'sealed')}>Sealed-bid (commit → reveal)</button>
      </div>
      ${entryMode.value === 'direct' ? html`<${DirectBook} />` : html`<${SealedBidFlow} />`}
    </section>`;
}

function DirectBook() {
  const d = draft.value;
  const setD = (k, v) => (draft.value = { ...draft.value, [k]: v });
  const addOrder = () => {
    const t = (d.trader || '').trim(); if (!t) return;
    const id = Math.max(0, ...book.value.map(o => o.id)) + 1;
    book.value = [...book.value, { id, ...d, trader: t, offerAmount: +d.offerAmount, wantMin: +d.wantMin, priority: +d.priority }];
    draft.value = { ...draft.value, trader: '' };
  };
  const rm = (id) => (book.value = book.value.filter(o => o.id !== id));
  return html`
    <div>
      <p class="entry-lead">Build the batch with real orders. Each is an intent: <i>offer</i> an asset, <i>want</i> ≥ a minimum of another. The real
        matcher (Johnson circuits + Shapley–Scarf TTC) finds the multilateral ring no pairwise swap can close; the verified kernel settles it conserving + all-or-nothing.</p>
      <div class="book">
        ${book.value.map(o => html`<div class="ord" key=${o.id}>
          <span class="who">${o.trader}</span>
          <span class="leg">offer <b>${o.offerAmount} ${o.offerAsset}</b> · want ≥ <b>${o.wantMin} ${o.wantAsset}</b></span>
          <span class="prio">p${o.priority}</span>
          <button class="x" onClick=${() => rm(o.id)}>✕</button></div>`)}
        ${book.value.length === 0 && html`<div class="empty">no orders — add one below</div>`}
      </div>
      <div class="draft">
        <input class="in trader" placeholder="trader" value=${d.trader} onInput=${e => setD('trader', e.target.value)} onKeyDown=${e => e.key === 'Enter' && addOrder()} />
        <label>offer<input class="in num" type="number" min="1" value=${d.offerAmount} onInput=${e => setD('offerAmount', e.target.value)} /></label>
        <${AssetSel} value=${d.offerAsset} onChange=${v => setD('offerAsset', v)} />
        <span class="arrow">→</span>
        <label>want ≥<input class="in num" type="number" min="0" value=${d.wantMin} onInput=${e => setD('wantMin', e.target.value)} /></label>
        <${AssetSel} value=${d.wantAsset} onChange=${v => setD('wantAsset', v)} />
        <label>prio<input class="in num sm" type="number" min="1" value=${d.priority} onInput=${e => setD('priority', e.target.value)} /></label>
        <button class="add" onClick=${addOrder}>+ add</button>
      </div>
      <div class="actions">
        <button class="primary" disabled=${clearBusy.value || book.value.length < 2} onClick=${runClear}>${clearBusy.value ? 'clearing…' : 'Clear the batch →'}</button>
        <span class="hint">real POST /clear · ${book.value.length} order(s)</span>
      </div>
      ${clearing.value && html`<${ClearingResult} res=${clearing.value} />`}
    </div>`;
}

// ── the sealed-bid two-phase ceremony, routed through the extension ──
function SealedBidFlow() {
  const w = wallet.value, o = yourOrder.value, s = sealed.value;
  const setO = (k, v) => (yourOrder.value = { ...yourOrder.value, [k]: v });
  if (w.status !== 'connected') {
    return html`<div class="notlive">
      <p class="honest">The sealed-bid commit→reveal ceremony signs through the installed extension (keccak256 commitment + EIP-712 <span class="mono">SealedBid</span>/<span class="mono">RevealBid</span> + secp256k1). Connect the cipherclerk first.</p>
      <button class="primary" disabled=${w.status === 'absent'} onClick=${connectWallet}>Connect the cipherclerk</button>
      ${w.status === 'absent' && html`<p class="hint">extension not installed — sealed-bid is unavailable in this browser (honest fallback; no faked signature).</p>`}
    </div>`;
  }
  return html`
    <div>
      <p class="entry-lead">A sealed bid hides your order until a reveal window. <b>Commit</b>: publish a binding-but-hiding keccak256 commitment, escrow-signed by the extension. <b>Reveal</b>: publish the opening; anyone re-hashes to check it binds. Both phases are separate, extension-signed actions.</p>
      <div class="yourorder">
        <span>your order:</span>
        <label>offer<input class="in num" type="number" min="1" value=${o.offerAmount} onInput=${e => setO('offerAmount', +e.target.value)} /></label>
        <${AssetSel} value=${o.offerAsset} onChange=${v => setO('offerAsset', v)} />
        <span class="arrow">→</span>
        <label>want ≥<input class="in num" type="number" min="0" value=${o.wantMin} onInput=${e => setO('wantMin', +e.target.value)} /></label>
        <${AssetSel} value=${o.wantAsset} onChange=${v => setO('wantAsset', v)} />
      </div>
      <div class="phases">
        <div class=${'phase ' + (s.phase !== 'idle' ? 'done' : 'active')}>
          <div class="ph-h"><span class="ph-n">1</span> Commit — hide the order</div>
          <button class="primary sm" disabled=${s.busy} onClick=${doCommit}>${s.busy && s.phase === 'idle' ? 'signing…' : 'Commit (extension signs)'}</button>
          ${s.commit && html`<div class="sealbox">
            <div class="srow"><b>commitment</b> <span class="mono">${s.commit.commitment.slice(0, 34)}…</span></div>
            <div class="srow"><b>escrow sig</b> <span class="mono">${(s.commit.signature || '').slice(0, 34)}…</span> <span class="chip">EIP-712 SealedBid</span></div>
            <div class="srow hint">the order is hidden — only H(bidder‖order‖salt) is public. Posting to an on-chain SealedAuction escrow is deploy-gated (no contract deployed).</div>
          </div>`}
        </div>
        <div class=${'phase ' + (s.phase === 'revealed' ? 'done' : s.phase === 'committed' ? 'active' : '')}>
          <div class="ph-h"><span class="ph-n">2</span> Reveal — open + check it binds</div>
          <button class="primary sm" disabled=${s.phase !== 'committed' || s.busy} onClick=${doReveal}>${s.busy && s.phase === 'committed' ? 'signing…' : 'Reveal (extension signs)'}</button>
          ${s.reveal && html`<div class="sealbox">
            <div class="srow"><b>opening</b> offer ${s.reveal.order.offerAmount} ${s.reveal.order.offerAsset} → want ≥ ${s.reveal.order.wantMin} ${s.reveal.order.wantAsset}</div>
            <div class="srow"><b>binds commitment</b> <span class=${s.reveal.bindsCommitment ? 'ok' : 'no'}>${s.reveal.bindsCommitment ? '✔ verified (re-hash matches)' : '✗'}</span></div>
            <div class="srow hint">the extension re-hashed the opening — the same check an on-chain revealBid runs. The revealed order can now join the open batch and clear.</div>
            <button class="ghost sm" onClick=${addRevealedToBook}>Add revealed order to the batch →</button>
          </div>`}
        </div>
      </div>
      ${s.error && html`<div class="result err">Sealed-bid error: ${s.error}</div>`}
    </div>`;
}

const AUCTION_ID = 1;
async function doCommit() {
  sealed.value = { phase: 'idle', busy: true };
  try {
    const order = { ...yourOrder.value };
    const commit = await ext.sealedCommit({ auctionId: AUCTION_ID, order });
    sealed.value = { phase: 'committed', commit, order };
  } catch (e) {
    sealed.value = { phase: 'error', error: String(e && e.message || e) };
  }
}
async function doReveal() {
  const prev = sealed.value;
  sealed.value = { ...prev, busy: true };
  try {
    const reveal = await ext.sealedReveal({ auctionId: AUCTION_ID });
    sealed.value = { ...prev, phase: 'revealed', reveal, busy: false };
  } catch (e) {
    sealed.value = { ...prev, phase: 'error', error: String(e && e.message || e), busy: false };
  }
}
function addRevealedToBook() {
  const o = (sealed.value.reveal && sealed.value.reveal.order) || yourOrder.value;
  const id = Math.max(0, ...book.value.map(x => x.id)) + 1;
  book.value = [...book.value, { id, trader: 'You', offerAsset: o.offerAsset, offerAmount: +o.offerAmount, wantAsset: o.wantAsset, wantMin: +o.wantMin, priority: +o.priority || 3 }];
  entryMode.value = 'direct';
}

function AssetSel({ value, onChange }) {
  return html`<select class="in sel" value=${value} onChange=${e => onChange(e.target.value)}>${ASSETS.map(a => html`<option value=${a}>${a}</option>`)}</select>`;
}

// ── run the real clear / settle ──
async function runClear() {
  clearBusy.value = true; clearing.value = null; settleState.value = null;
  const orders = book.value.map(({ trader, offerAsset, offerAmount, wantAsset, wantMin, priority }) =>
    ({ trader, offerAsset, offerAmount: +offerAmount, wantAsset, wantMin: +wantMin, priority: +priority }));
  try { clearing.value = await clearOpen(orders); }
  catch (e) { clearing.value = { error: String(e && e.message || e) }; }
  finally { clearBusy.value = false; }
}
async function runSettle() {
  if (!clearing.value || !clearing.value.ring) return;
  settleState.value = { busy: true };
  try { settleState.value = await settle(clearing.value); }
  catch (e) { settleState.value = { nodeUp: false, error: String(e && e.message || e) }; }
}

function ClearingResult({ res }) {
  if (res.error) return html`<div class="result err">Matcher error: ${res.error}<div class="hint">run the app via serve.mjs (it shells to the real drex_clear binary)</div></div>`;
  const ring = res.ring, cleared = res.allocations || [];
  const live = cleared.filter(a => !a.rested), rested = cleared.filter(a => a.rested);
  const color = { GOLD: '#f0c14b', ART: '#bc8cff', WINE: '#f85149', SILVER: '#8b949e', PEARL: '#58a6ff' };
  return html`<div class="result">
    ${!ring ? html`<div class="noring">No clearing ring over this book — every order rests. <span class="hint">${res.provenance || ''}</span></div>` : html`
      <div class="res-h">Cleared · real solver <span class=${'chip ' + (res.ok ? 'ok' : 'warn')}>${res.ok ? 'fair · conserving · no-mint' : 'partial'}</span></div>
      <div class="ring"><span class="rlabel">ring (${ring.participants.length}-party${res.twoCycles === 0 ? ', genuinely multilateral' : ''}):</span>
        ${ring.legs.map(l => html`<span class="rleg">${l.fromTrader}→${l.toTrader} ${l.amount} ${l.asset}</span>`)}</div>
      <div class="allocs">
        ${live.map(a => html`<div class="alloc"><span class="who">${a.trader}</span><span class="leg">sent ${a.sent} ${a.sentAsset} · got <b>${a.received} ${a.recvAsset}</b> (≥${a.wantMin})</span><span class=${a.ir && a.budget ? 'ok' : 'no'}>${a.ir && a.budget ? '✔' : '✗'}</span></div>`)}
        ${rested.map(a => html`<div class="alloc rest"><span class="who">${a.trader}</span><span class="leg">rests — no match this batch</span><span>·</span></div>`)}
      </div>
      ${res.conservation && res.conservation.length > 0 && html`<div class="cons"><div class="hint">per-asset conservation (in = out) — from the verified settle:</div>
        ${res.conservation.map(c => html`<div class="consrow"><span>${c.asset}: ${c.in} in = ${c.out} out</span><span class=${c.ok ? 'ok' : 'no'}>${c.ok ? '✔' : '✗'}</span><div class="bar"><span style=${'width:100%;background:' + (color[c.asset] || '#58a6ff')}></span></div></div>`)}</div>`}
      ${res.reject && html`<div class="reject">reject-polarity: drain a sender one short → leg ${res.reject.refusedAt} REFUSED by the verified kernel; whole ring aborts. <span class="hint">over-debit is provably impossible, not merely avoided.</span></div>`}
      <div class="settle-line">
        <button class="ghost" disabled=${settleState.value && settleState.value.busy} onClick=${runSettle}>${settleState.value && settleState.value.busy ? 'settling…' : 'Settle on the live node →'}</button>
        <span class="hint">lands the ring as one real turn (solo dev node; no on-chain settle yet)</span>
      </div>
      ${settleState.value && !settleState.value.busy && html`<${SettleResult} s=${settleState.value} />`}`}
  </div>`;
}

function SettleResult({ s }) {
  if (!s.nodeUp) return html`<div class="settle warn">No live node reachable (${s.error || 'offline'}). The clearing above is the real verified solver, but it did not land on a node this run. <span class="hint">start one: dregg-node run --port 8420 --enable-faucet --prove-turns</span></div>`;
  if (!s.accepted) return html`<div class="settle warn">Node rejected the settlement turn: ${s.error || 'unknown'}</div>`;
  const proven = !!(s.proof && s.proof.present);
  return html`<div class=${'settle ' + (proven ? 'ok' : 'warn')}>
    <div class="sh">${proven ? 'Settled · proven' : 'Committed · proof pending'}</div>
    <div class="srow">turn <span class="mono">${(s.turnHash || '').slice(0, 24)}…</span> on ${s.node}</div>
    ${proven && html`<div class="srow">${s.proof.mode === 'stark_full_turn' ? `full-turn STARK proof · ${s.proof.len} bytes` : 'witnessed receipt (prove_pool)'} — re-checkable at /api/turn/${(s.turnHash || '').slice(0, 10)}…/proof</div>`}
    ${!proven && html`<div class="srow hint">${s.proofNote || ''}</div>`}
  </div>`;
}

function CompositionStrip() {
  return html`<section class="card comp">
    <div class="card-h">Composition journey <span class="hint">— deposit → shield → clear → settle (Phase 3; each stage's honest grade)</span></div>
    <div class="comp-row">
      ${COMPOSITION.map((c, i) => html`<div class="comp-stage"><div class="cstage-h">${i + 1}. ${c.name}</div><div class="cverb">${c.verb}</div><div class=${'cgrade ' + (c.live ? 'live' : 'gated')}>${c.grade}</div></div>${i < COMPOSITION.length - 1 ? html`<span class="comp-arrow">→</span>` : ''}`)}
    </div>
  </section>`;
}

function App() {
  return html`<div class="app">
    <${Header} />
    <${WalletPanel} />
    <${TierDial} />
    <div class="grid"><${MechanismRail} /><${OrderEntry} /></div>
    <${CompositionStrip} />
    <footer class="foot">Seed · Phase 1 (Open-first). The Open-tier ring clear is real end-to-end (solver.rs + verified_settle.rs + solo-node settle); the sealed-bid ceremony is real extension-signed crypto. Shielded / Dark tiers and the other seven mechanisms are present as honestly-labelled previews — not live with real money — and wire in per the phased plan (docs/deos/DREX-FRONTEND-OVERHAUL.md).</footer>
  </div>`;
}

render(html`<${App} />`, document.getElementById('root'));

nodeStatus().then(s => (node.value = s)).catch(() => (node.value = { up: false }));
detectWallet();
