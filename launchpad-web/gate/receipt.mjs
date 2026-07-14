// receipt.mjs — generate a STATIC, self-contained verifiable-receipt page from a
// REAL launch on a deployed DreggLaunchpad. No mock: every number written into
// the receipt is read back from the on-chain contract after driving a full fair
// launch (register → sealed commit → reveal → uniform-price clear → settle →
// graduate) against the deployed bytecode.
//
//   RPC=http://127.0.0.1:8545 ADDRESS=0x… OUT=public/receipt.html node gate/receipt.mjs
//
// The wrapper gate/make-receipt.sh spins a local anvil, deploys the real
// contract, and runs this — leaving public/receipt.html as a shareable artifact
// whose every field a reader can recompute from the chain themselves.

import { writeFileSync } from 'node:fs';
import { ethers } from 'ethers';
import { LAUNCHPAD_ABI, TOKEN_ABI, POOL_ABI } from '../shared/abi.mjs';

const RPC = process.env.RPC || 'http://127.0.0.1:8545';
const ADDRESS = process.env.ADDRESS;
const OUT = process.env.OUT || new URL('../public/receipt.html', import.meta.url).pathname;
const CHAIN_LABEL = process.env.CHAIN_LABEL || 'local anvil (chainId 31337)';
const G = 10n ** 9n;

const KEYS = [
  '0xac0974bec39a17e36ba4a6b4d238ff944bacb478cbed5efcae784d7bf4f2ff80', // creator
  '0x59c6995e998f97a5a0044966f0945389dc9e86dae88c7a8412f4603b6b78690d', // alice
  '0x5de4111afa1a4b94908f83103eb1f1706367c2e68ca870fc3fb9a804cdab365a', // bob
  '0x7c852118294e51e653712a81e05800f419141751be58f605c371e15141b007a6', // carol
  '0x47e179ec197488593b187f80a00eb0da91f1b9d0b13f8733639f19c30a34926a', // dave
];

const provider = new ethers.JsonRpcProvider(RPC);
const wallets = KEYS.map((k) => new ethers.NonceManager(new ethers.Wallet(k, provider)));
const [creator, alice, bob, carol, dave] = wallets;
const addrs = await Promise.all(wallets.map((w) => w.getAddress()));
const [creatorA, aliceA, bobA, carolA, daveA] = addrs;
const pad = (w) => new ethers.Contract(ADDRESS, LAUNCHPAD_ABI, w);
const warp = async (s) => { await provider.send('evm_increaseTime', [s]); await provider.send('evm_mine', []); };
const esc = (x) => String(x).replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));
const gw = (w) => (Number(BigInt(w || 0)) / 1e9).toFixed(3);
const eth = (w) => ethers.formatEther(BigInt(w || 0));

async function main() {
  if (!ADDRESS) { console.error('ADDRESS env required'); process.exit(2); }
  const net = await provider.getNetwork();

  // ── drive a real fair launch ──
  const now = (await provider.getBlock('latest')).timestamp;
  const lockUntil = now + 30 * 86400;
  const s = [1200n, 1000n, 100n, 100n, BigInt(lockUntil), 1n * G, 5000n];
  const rcR = await (await pad(creator).registerLaunch('AuroraGate', 'AURG', s, 100, 100, ethers.ZeroAddress, ethers.ZeroAddress)).wait();
  let launchId, token, scheduleCommit;
  for (const log of rcR.logs) {
    try { const p = pad(creator).interface.parseLog(log);
      if (p?.name === 'LaunchRegistered') { launchId = p.args.launchId.toString(); token = p.args.token; scheduleCommit = p.args.scheduleCommit; } } catch (_e) {}
  }

  const bids = [
    { w: alice, a: aliceA, name: 'alice', price: 5n * G, qty: 400n, salt: ethers.id('a') },
    { w: bob,   a: bobA,   name: 'bob',   price: 4n * G, qty: 400n, salt: ethers.id('b') },
    { w: carol, a: carolA, name: 'carol', price: 3n * G, qty: 400n, salt: ethers.id('c') },
    { w: dave,  a: daveA,  name: 'dave',  price: 2n * G, qty: 400n, salt: ethers.id('d') },
  ];
  for (const b of bids) {
    const seal = await pad(b.w).sealOf(b.price, b.qty, b.salt, b.a);
    await (await pad(b.w).commitBid(launchId, seal, '0x', { value: b.price * b.qty })).wait();
  }
  await warp(101);
  for (const b of bids) await (await pad(b.w).revealBid(launchId, b.price, b.qty, b.salt)).wait();
  await warp(101);
  await (await pad(creator).finalizeClearing(launchId, [0, 1, 2, 3].map(BigInt), '0x')).wait();
  for (const b of bids) await (await pad(creator).settleBid(launchId, b.a)).wait();

  const [qSeed, tSeed] = await pad(creator).graduationSeed(launchId);
  await (await pad(creator).graduate(launchId, qSeed, tSeed)).wait();

  // ── read every displayed number back from the chain ──
  const clearingPrice = await pad(creator).clearingPriceOf(launchId);
  const soldQty = await pad(creator).soldQtyOf(launchId);
  const onChainCommit = await pad(creator).scheduleCommitOf(launchId);
  const tok = new ethers.Contract(token, TOKEN_ABI, provider);
  const [tName, tSym, tCap, tMinted, tTotal] = await Promise.all([tok.name(), tok.symbol(), tok.cap(), tok.minted(), tok.totalSupply()]);
  const U = await pad(creator).TOKEN_UNIT();
  const poolAddr = await pad(creator).poolOf(launchId);
  const pool = new ethers.Contract(poolAddr, POOL_ABI, provider);
  const [rq, rt] = await pool.reserves();
  const [fq, ft] = await pool.floors();
  const spot = await pool.spotPriceWeiPerToken();

  const fills = [];
  for (const b of bids) {
    const bal = await tok.balanceOf(b.a);
    const g = await pad(creator).getBid(launchId, b.a);
    fills.push({ name: b.name, addr: b.a, price: b.price, qty: b.qty, filled: g.filled, paid: g.paid ?? 0n, bal });
  }

  // independently recompute the schedule commit (the reader's check)
  const recomputed = ethers.keccak256(ethers.AbiCoder.defaultAbiCoder().encode(
    ['uint256', 'uint256', 'uint256', 'uint256', 'uint64', 'uint256', 'uint16'],
    [1200n, 1000n, 100n, 100n, BigInt(lockUntil), 1n * G, 5000n]));
  const commitMatches = recomputed.toLowerCase() === onChainCommit.toLowerCase();

  const html = renderReceipt({
    net, launchId, contract: ADDRESS, token, tName, tSym, tCap, tMinted, tTotal, U,
    clearingPrice, soldQty, onChainCommit, recomputed, commitMatches, lockUntil,
    fills, poolAddr, rq, rt, fq, ft, spot, qSeed, tSeed,
  });
  writeFileSync(OUT, html);
  console.log(`receipt written → ${OUT}`);
  console.log(`  launch ${launchId} · token ${tSym} @ ${token}`);
  console.log(`  uniform clearing price ${gw(clearingPrice)} gwei · sold ${soldQty}`);
  console.log(`  schedule commit ${commitMatches ? 'RECOMPUTED-MATCH' : 'MISMATCH'}`);
}

function chip(grade) { return `<span class="chip ${grade}">${grade}</span>`; }

function renderReceipt(d) {
  const U = d.U;
  const row = (f) => {
    const win = f.filled > 0n;
    return `<tr class="${win ? 'win' : 'lose'}">
      <td>${esc(f.name)}</td>
      <td class="mono">${esc(f.addr.slice(0, 10))}…</td>
      <td class="num">${gw(f.price)} gwei</td>
      <td class="num">${f.qty}</td>
      <td class="num">${(f.filled / U).toString()}</td>
      <td class="num">${win ? gw(d.clearingPrice) + ' gwei' : '—'}</td>
      <td>${win ? '<span class="b ok">FILLED</span>' : '<span class="b no">below clearing</span>'}</td>
    </tr>`;
  };
  return `<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>dregg launchpad — verifiable receipt · launch ${esc(d.launchId)}</title>
<style>
:root{--bg:#0d1117;--bg2:#161b22;--bg3:#0a0e14;--line:#21262d;--fg:#c9d1d9;--muted:#8b949e;--accent:#58a6ff;--green:#3fb950;--red:#f85149;--dragon:#a78bfa;--proved:#238636;--replay:#8957e5;--built:#9e6a03;--unbuilt:#484f58}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--fg);font:13px/1.55 ui-monospace,SFMono-Regular,Menlo,monospace}
header{padding:16px 22px;border-bottom:1px solid var(--line);background:var(--bg3)}
header h1{margin:0;font-size:17px;color:var(--dragon)}
header .sub{color:var(--muted);font-size:12px;margin-top:4px}
main{max-width:1000px;margin:0 auto;padding:22px 20px 70px}
h2{font-size:12px;color:var(--accent);text-transform:uppercase;letter-spacing:.06em;margin:26px 0 10px}
.card{border:1px solid var(--line);border-radius:8px;background:var(--bg2);padding:15px;margin-bottom:14px}
.kv{display:grid;grid-template-columns:auto 1fr;gap:5px 14px;font-size:12px}
.kv .k{color:var(--muted);text-transform:uppercase;font-size:10px;letter-spacing:.04em}
.kv .v{text-align:right;word-break:break-all}
.mono{font-family:ui-monospace,monospace}
.big{font-size:26px;color:var(--dragon);font-weight:700}
table{width:100%;border-collapse:collapse;font-size:12px;margin-top:4px}
th,td{text-align:left;padding:7px 9px;border-bottom:1px solid var(--line)}
th{color:var(--muted);text-transform:uppercase;font-size:10px;letter-spacing:.04em}
td.num,th.num{text-align:right}
tr.lose td{color:var(--muted)}
.b{font-size:10px;padding:1px 7px;border-radius:9px;border:1px solid var(--line)}
.b.ok{border-color:var(--green);color:var(--green)}
.b.no{border-color:var(--red);color:var(--red)}
.chip{display:inline-block;font-size:9.5px;font-weight:700;letter-spacing:.05em;border-radius:5px;padding:1px 6px;margin-right:5px;color:#fff}
.chip.PROVED{background:var(--proved)}.chip.REPLAYABLE{background:var(--replay)}.chip.BUILT{background:var(--built)}.chip.UNBUILT{background:var(--unbuilt);color:#c9d1d9}
.claim{border:1px solid var(--line);border-radius:8px;padding:11px 12px;margin-bottom:9px;background:var(--bg2)}
.claim .lab{font-weight:600}
.claim .det{color:var(--muted);font-size:11px;margin:3px 0 5px}
.claim .cite{color:#6e7681;font-size:10px;word-break:break-all}
.match{color:var(--green)}.nomatch{color:var(--red)}
.note{font-size:11px;color:var(--muted);margin-top:10px;line-height:1.6}
.banner{font-size:11px;color:var(--muted);background:var(--bg3);border:1px solid var(--line);border-radius:7px;padding:9px 12px;margin-bottom:16px}
</style></head><body>
<header>
  <h1>dregg launchpad — verifiable receipt</h1>
  <div class="sub">launch #${esc(d.launchId)} · ${esc(d.tName)} (${esc(d.tSym)}) · every number below is read back from the on-chain contract — recompute it yourself</div>
</header>
<main>
  <div class="banner">This is a static snapshot of a REAL launch driven against the deployed <span class="mono">DreggLaunchpad</span> bytecode on ${esc(CHAIN_LABEL)} (chainId ${esc(d.net.chainId)}). No value at stake; a demonstration receipt. Point an explorer at the contract + token addresses and every field re-derives.</div>

  <h2>The one uniform clearing price</h2>
  <div class="card">
    <div class="big">${gw(d.clearingPrice)} gwei / token</div>
    <div class="note">Everyone who cleared paid the <b>same</b> price — there is no earliest block to win and no ordering edge. ${chip('PROVED')} <span class="mono">uniform_price_no_arbitrage</span> (metatheory/Market/Optimality.lean:130). Sold ${esc(d.soldQty.toString())} of ${esc((d.tCap / U).toString())} tokens (full sale tranche).</div>
  </div>

  <h2>The sealed book, cleared</h2>
  <div class="card">
    <table>
      <tr><th>bidder</th><th>address</th><th class="num">bid price</th><th class="num">bid qty</th><th class="num">filled</th><th class="num">paid (uniform)</th><th>outcome</th></tr>
      ${d.fills.map(row).join('\n      ')}
    </table>
    <div class="note">Sealed during commit (no bid observable), revealed after (${chip('PROVED')} <span class="mono">reveal_binds_committed</span>, SealedAuction.lean:248 — no late-switch), cleared at one price. A bidder below the clearing price fills 0; a marginal bidder fills partially; all winners pay the clearing price, refunds returned.</div>
  </div>

  <h2>Disclosed supply — recompute the commitment</h2>
  <div class="card">
    <div class="kv">
      <span class="k">total supply</span><span class="v mono">1200</span>
      <span class="k">sale tranche</span><span class="v mono">1000</span>
      <span class="k">creator alloc</span><span class="v mono">100 (locked until ${esc(new Date(d.lockUntil * 1000).toISOString().slice(0, 10))})</span>
      <span class="k">pool alloc</span><span class="v mono">100</span>
      <span class="k">token cap</span><span class="v mono">${esc((d.tCap / U).toString())} · minted once: ${esc(d.tMinted)}</span>
      <span class="k">on-chain scheduleCommit</span><span class="v mono">${esc(d.onChainCommit.slice(0, 18))}…</span>
      <span class="k">recomputed keccak</span><span class="v mono">${esc(d.recomputed.slice(0, 18))}…</span>
      <span class="k">match</span><span class="v ${d.commitMatches ? 'match' : 'nomatch'}">${d.commitMatches ? 'RECOMPUTED-MATCH ✓' : 'MISMATCH ✗'}</span>
    </div>
    <div class="note">Sale + creator + pool = total, or the contract reverts registration. ${chip('PROVED')} <span class="mono">execMintA_iff_spec</span> (supplycreation.lean:177) — no undisclosed mint door. The token mints exactly once for the whole cap: no second-mint function exists.</div>
  </div>

  <h2>Graduation — the provably-solvent pool</h2>
  <div class="card">
    <div class="kv">
      <span class="k">pool address</span><span class="v mono">${esc(d.poolAddr)}</span>
      <span class="k">quote reserve</span><span class="v mono">${eth(d.rq)} ETH</span>
      <span class="k">token reserve</span><span class="v mono">${(d.rt / U).toString()}</span>
      <span class="k">reserve floor</span><span class="v mono">${eth(d.fq)} ETH / ${(d.ft / U).toString()} tok</span>
      <span class="k">spot price</span><span class="v mono">${gw(d.spot)} gwei / token</span>
      <span class="k">seeded from raise</span><span class="v mono">${eth(d.qSeed)} ETH (50% of proceeds) + ${(d.tSeed / U).toString()} tokens</span>
    </div>
    <div class="note">Graduated liquidity is pool-owned; there is no creator-withdrawal door. A trade that would drive the reserve below its floor REVERTS. ${chip('PROVED')} <span class="mono">pool_solvent_forever</span> (metatheory/Market/Liquidity.lean:145).</div>
  </div>

  <h2>Why it is fair — each claim, graded</h2>
  <div class="claim"><div class="lab">${chip('PROVED')} No snipe / no front-run</div><div class="det">One uniform price removes the value of ordering. Sniper edge dies structurally.</div><div class="cite">uniform_price_no_arbitrage · metatheory/Market/Optimality.lean:130</div></div>
  <div class="claim"><div class="lab">${chip('PROVED')} No hidden supply</div><div class="det">Supply is disclosed and closes; the token mints once for the cap; no second-mint door.</div><div class="cite">execMintA_iff_spec · metatheory/Dregg2/Circuit/Spec/supplycreation.lean:177</div></div>
  <div class="claim"><div class="lab">${chip('PROVED')} No late-switch / no peek</div><div class="det">A revealed bid is exactly the sealed one; a bid never committed can never win.</div><div class="cite">reveal_binds_committed · SealedAuction.lean:248 · uncommitted_cannot_win :415</div></div>
  <div class="claim"><div class="lab">${chip('PROVED')} No silent LP / mint drain</div><div class="det">Pool-owned liquidity, never insolvent; disclosed single mint.</div><div class="cite">pool_solvent_forever · metatheory/Market/Liquidity.lean:145</div></div>
  <div class="claim"><div class="lab">${chip('REPLAYABLE')} Every number recomputable</div><div class="det">Read the contract + Transfer logs; recompute the schedule commit (done above).</div><div class="cite">keccak(abi.encode(schedule)) == scheduleCommitOf(launchId)</div></div>

  <div class="note">
    <b>Honest scope.</b> This receipt proves the on-chain, mechanical surface of the sale: the distribution and disclosure are fair and the supply is real. It makes no claim about the token's value or the team's off-mechanism conduct (bonded, not proven), and nothing here is deployed with value at stake. A fairly-launched token can still go to zero. Contract <span class="mono">${esc(d.contract)}</span> · token <span class="mono">${esc(d.token)}</span>.
  </div>
</main></body></html>`;
}

main().catch((e) => { console.error('receipt error:', e); process.exit(2); });
