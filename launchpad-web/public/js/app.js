// app.js — shared launchpad frontend runtime. Loads /api/config, wires the REAL
// wallet, builds the on-chain contract, and exposes formatting + trust chips.
//
// Wallet, the drex-web way (reuse the real wallet, no mock): if the page has an
// injected EVM wallet (window.ethereum — MetaMask / the browser extension), we
// drive the contract through it (BrowserProvider + the user's signer). Against a
// LOCAL anvil with no injected wallet, we fall back to an anvil dev key so the
// product is clickable end-to-end locally — the SAME contract calls, just a local
// signer instead of the extension.

/* global ethers */
export const state = { cfg: null, provider: null, signer: null, pad: null, account: null, dev: false };

// anvil's canonical dev accounts (LOCAL fallback only; never used off localhost).
const ANVIL_KEYS = [
  '0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80',
  '0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d',
  '0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a',
  '0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6',
  '0x47e179ec197488593b187f80a00eb0da91f1b9d0b13f8733639f19c30a34926a',
];

export async function loadConfig() {
  if (state.cfg) return state.cfg;
  state.cfg = await (await fetch('/api/config')).json();
  return state.cfg;
}

function isLocal(rpc) { return /127\.0\.0\.1|localhost/.test(rpc); }

// Connect the wallet + build the contract. `devIndex` picks an anvil dev account
// for the local fallback (0=creator, 1..=bidders) so the demo has distinct actors.
export async function connect(devIndex = 0) {
  const cfg = await loadConfig();
  if (window.ethereum) {
    state.provider = new ethers.BrowserProvider(window.ethereum);
    await state.provider.send('eth_requestAccounts', []);
    state.signer = await state.provider.getSigner();
    state.dev = false;
  } else if (isLocal(cfg.rpc)) {
    state.provider = new ethers.JsonRpcProvider(cfg.rpc);
    state.signer = new ethers.Wallet(ANVIL_KEYS[devIndex % ANVIL_KEYS.length], state.provider);
    state.dev = true;
  } else {
    throw new Error('no injected wallet found (install MetaMask / the extension)');
  }
  state.account = await state.signer.getAddress();
  state.pad = new ethers.Contract(cfg.address, cfg.abi, state.signer);
  return state;
}

// read-only contract (no wallet needed) for pages that only display.
export async function readonlyPad() {
  const cfg = await loadConfig();
  const provider = new ethers.JsonRpcProvider(cfg.rpc);
  return new ethers.Contract(cfg.address, cfg.abi, provider);
}

// ── formatting ──
export const fmtEth = (wei) => ethers.formatEther(BigInt(wei || 0));
export const fmtGwei = (wei) => ethers.formatUnits(BigInt(wei || 0), 'gwei');
export const short = (a) => a ? a.slice(0, 6) + '…' + a.slice(-4) : '';
export const fmtWhole = (base) => (BigInt(base || 0) / 10n ** 18n).toString(); // token base→whole
export const nowSec = () => Math.floor(Date.now() / 1000);

export function chip(grade) {
  return `<span class="chip ${grade}">${grade}</span>`;
}
export function phaseBadge(phase) {
  const cls = { Commit: 'commit', Reveal: 'reveal', ClearReady: 'reveal', Cleared: 'cleared', Finalized: 'cleared' }[phase] || '';
  return `<span class="badge ${cls}">${phase}</span>`;
}

// header wallet pill wiring (optional, pages call this)
export async function mountWalletPill(id = 'walletPill', devIndex = 0) {
  const el = document.getElementById(id);
  if (!el) return;
  el.onclick = async () => {
    try { await connect(devIndex); el.textContent = (state.dev ? 'dev ' : '') + short(state.account); el.className = 'pill live'; }
    catch (e) { el.textContent = 'wallet: ' + e.message; el.className = 'pill warn'; }
  };
  el.textContent = 'connect wallet';
}
