// serve.mjs — the DrEX v2 dev server. A SEPARATE file + port (8782) from the
// current demo's serve.mjs (:8781) and offerings.mjs (:8790), so it never
// clobbers the live drex-web lanes. It serves the v2 static app (index.html,
// styles.css, dist/) and exposes the SAME REAL endpoints the app calls:
//
//   POST /clear        → the REAL matcher (drex_clear: solver.rs ring match →
//                        verified_settle.rs kernel fold). Local binary first,
//                        else ssh the prebuilt matcher on the build host.
//   GET  /node/status  → probe a live dregg node (for the settle path).
//   POST /settle       → land the cleared batch as ONE real turn on the live
//                        node (per-trader Transfer + batch EmitEvent), read the
//                        proof + receipt back. If no node, { nodeUp:false } and
//                        the UI keeps the labelled local-clear result.
//
// The wallet is NOT mounted here — v2 routes all signing through the INSTALLED
// extension (window.dregg), not a standalone wasm. Binds 127.0.0.1 by default
// (same all-interfaces guard shape as the existing servers).

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import crypto from 'node:crypto';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(HERE, '..');
const PORT = process.env.PORT || 8782;
const HOST = process.env.DREX_BIND || '127.0.0.1';
const WILDCARD = HOST === '0.0.0.0' || HOST === '::' || HOST === '*';
if (WILDCARD && process.env.DREX_ALLOW_WILDCARD !== '1') {
  console.error(`refusing to bind ${HOST} (all-interfaces = public unless a host firewall gates :${PORT}).`);
  console.error(`  set DREX_BIND=127.0.0.1 (default) or the LAN IP; wildcard needs DREX_ALLOW_WILDCARD=1 behind a firewall.`);
  process.exit(1);
}

const NODE = (process.env.DREGG_NODE || 'http://127.0.0.1:8420').replace(/\/$/, '');
const NODE_PASSPHRASE = process.env.DREGG_NODE_PASSPHRASE || 'drex-dev-node';
const REMOTE_HOST = process.env.DREX_REMOTE || 'persvati';
const REMOTE_DIR = process.env.DREX_REMOTE_DIR || 'dregg-build/drex-matcher';
let nodeBearer = null;

// ── the REAL matcher: locate drex_clear (local target first, else remote) ──
function drexClearCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'target', prof, 'drex_clear');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local target/' + prof };
  }
  return { cmd: 'ssh', args: [REMOTE_HOST, `cd ${REMOTE_DIR} && ./target/debug/drex_clear`], where: REMOTE_HOST + ':' + REMOTE_DIR };
}
function runClear(ordersJson) {
  return new Promise((resolve) => {
    const { cmd, args } = drexClearCmd();
    const child = spawn(cmd, args, { cwd: REPO });
    let out = '', err = '';
    child.stdout.on('data', d => (out += d));
    child.stderr.on('data', d => (err += d));
    child.on('error', e => resolve({ error: 'spawn failed: ' + e.message }));
    child.on('close', (code) => {
      const line = out.trim().split('\n').filter(Boolean).pop() || '';
      try { resolve(JSON.parse(line)); }
      catch (_e) { resolve({ error: 'drex_clear produced no JSON (exit ' + code + ')', stderr: err.slice(-400) }); }
    });
    child.stdin.end(ordersJson);
  });
}

// ── the live-node settle (ported, compact) ──
const traderCell = (t) => crypto.createHash('sha256').update('drex-trader-v1:' + String(t)).digest('hex');
const SETTLE_CELL = 'de55e771' + '0'.repeat(56);
const felt = (n) => String(Math.max(0, Math.min(Number.MAX_SAFE_INTEGER, Math.floor(Number(n) || 0))));
async function nodeUnlock() {
  if (nodeBearer) return nodeBearer;
  const r = await fetch(NODE + '/cipherclerk/unlock', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ passphrase: NODE_PASSPHRASE }) });
  const j = await r.json();
  if (!j.success || !j.bearer_token) throw new Error('node unlock failed: ' + (j.error || r.status));
  nodeBearer = j.bearer_token; return nodeBearer;
}
async function nodeGet(p) {
  const r = await fetch(NODE + p, { headers: nodeBearer ? { Authorization: 'Bearer ' + nodeBearer } : {} });
  if (!r.ok) return { __status: r.status };
  return r.json();
}
async function nodeFaucet(cell, amount) {
  try { await fetch(NODE + '/api/faucet', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ recipient: cell, amount }) }); } catch (_e) {}
}
async function settleOnNode(cleared) {
  const bearer = await nodeUnlock();
  const ident = await nodeGet('/api/node/identity');
  const operator = ident && ident.agent_cell;
  if (!operator) throw new Error('node identity has no agent cell');
  const conserved = (cleared.conservation || []).reduce((s, c) => s + (Number(c.in) || 0), 0);
  const fills = (cleared.allocations || []).filter(a => !a.rested && Number(a.received) > 0)
    .map(a => ({ trader: String(a.trader), cell: traderCell(a.trader), recvAsset: a.recvAsset, received: Math.floor(Number(a.received)), amount: Math.max(1, Math.floor(Number(a.received))) }));
  const FUND_CEILING = 9000;
  const rawTotal = fills.reduce((s, f) => s + f.amount, 0);
  let scale = 1;
  if (rawTotal > FUND_CEILING) { scale = FUND_CEILING / rawTotal; for (const f of fills) f.amount = Math.max(1, Math.floor(f.amount * scale)); }
  const settledTotal = fills.reduce((s, f) => s + f.amount, 0);
  const dests = fills.length ? fills.map(f => f.cell) : [SETTLE_CELL];
  await Promise.all(dests.map(c => nodeFaucet(c, 0)));
  const effects = fills.length ? fills.map(f => ({ kind: 'transfer', to: f.cell, amount: f.amount })) : [{ kind: 'transfer', to: SETTLE_CELL, amount: 1 }];
  effects.push({ kind: 'emit_event', topic: 'drex_clear_batch', data: [felt(fills.length), felt(conserved)] });
  const fee = 800 + 350 * effects.length;
  const need = fee + settledTotal + (fills.length ? 0 : 1);
  if ((ident.agent_balance || 0) < need) {
    await nodeFaucet(operator, 10000);
    const re = await nodeGet('/api/node/identity');
    if (re && (re.agent_balance || 0) < need) throw new Error(`operator underfunded (have ${re.agent_balance}, need ${need}); faucet rate-limited — retry ~1 min`);
  }
  const submit = await fetch(NODE + '/turn/submit', { method: 'POST', headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + bearer }, body: JSON.stringify({ agent: operator, nonce: 0, fee, memo: 'drex_clear', actions: [{ effects }] }) }).then(r => r.json());
  if (!submit.accepted || !submit.turn_hash) return { nodeUp: true, accepted: false, operator, error: submit.error || 'turn not accepted' };
  const turnHash = submit.turn_hash;
  let proof = null, r = null;
  for (let i = 0; i < 40; i++) {
    if (!proof) { const p = await nodeGet('/api/turn/' + turnHash + '/proof'); if (p && !p.__status && p.proof_len) proof = { present: true, len: p.proof_len, mode: 'stark_full_turn' }; }
    const recs = await nodeGet('/api/starbridge/receipts?turn_hash=' + turnHash);
    if (Array.isArray(recs) && recs.length) r = recs[0].receipt || recs[0];
    if (proof || (r && (r.witness_count > 0 || r.has_proof))) break;
    await new Promise(x => setTimeout(x, 600));
  }
  if (!proof && r && (r.witness_count > 0 || r.has_proof)) proof = { present: true, len: null, mode: 'witnessed_receipt', witnessCount: r.witness_count };
  const proofNote = proof ? null : 'prove_pool enqueued the async STARK job; no proof attached yet (committed-but-unattested)';
  return {
    nodeUp: true, accepted: true, node: NODE, operator, turnHash,
    proof: proof || { present: false }, proofNote,
    settle: { mode: 'per_trader_transfer', traders: fills.length, settledTotal, scaled: scale < 1, scale: Number(scale.toFixed(6)) },
    receipt: r && { finality: r.finality, preState: r.pre_state, postState: r.post_state, computronsUsed: r.computrons_used, actionCount: r.action_count, hasProof: r.has_proof, witnessCount: r.witness_count, executorSigned: r.executor_signed },
  };
}

// ── static + routing ──
const MIME = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.mjs': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8', '.json': 'application/json', '.map': 'application/json', '.svg': 'image/svg+xml' };
function send(res, code, body, type) { res.writeHead(code, { 'Content-Type': type || 'text/plain', 'Cache-Control': 'no-cache' }); res.end(body); }
function readBody(req) { return new Promise((resolve) => { let b = ''; req.on('data', c => { b += c; if (b.length > 1 << 20) req.destroy(); }); req.on('end', () => resolve(b)); }); }

http.createServer(async (req, res) => {
  let url = decodeURIComponent(req.url.split('?')[0]);
  if (url === '/') url = '/index.html';

  if (req.method === 'POST' && url === '/clear') {
    const result = await runClear(await readBody(req));
    return send(res, result.error ? 502 : 200, JSON.stringify(result), MIME['.json']);
  }
  if (req.method === 'GET' && url === '/node/status') {
    try { const r = await fetch(NODE + '/status'); return send(res, 200, JSON.stringify({ up: true, node: NODE, status: await r.json() }), MIME['.json']); }
    catch (e) { return send(res, 200, JSON.stringify({ up: false, node: NODE, error: e.message }), MIME['.json']); }
  }
  if (req.method === 'POST' && url === '/settle') {
    let cleared; try { cleared = JSON.parse(await readBody(req)); } catch (_e) { return send(res, 400, JSON.stringify({ error: 'bad json' }), MIME['.json']); }
    try { return send(res, 200, JSON.stringify(await settleOnNode(cleared)), MIME['.json']); }
    catch (e) { return send(res, 200, JSON.stringify({ nodeUp: false, node: NODE, error: e.message }), MIME['.json']); }
  }

  // static — v2 dir only, plus the reused drex-viz from the sibling drex-web/
  // (the bundle inlines it, but allow direct source serving for the no-build
  // dev path). No path escape outside the repo.
  const file = path.join(HERE, url);
  if (!path.resolve(file).startsWith(REPO)) return send(res, 403, 'forbidden');
  fs.readFile(file, (err, buf) => {
    if (err) return send(res, 404, 'not found: ' + url);
    send(res, 200, buf, MIME[path.extname(file)] || 'application/octet-stream');
  });
}).listen(PORT, HOST, () => {
  console.log('DrEX v2 dev server → http://' + HOST + ':' + PORT);
  console.log('  REAL matcher   POST /clear  → drex_clear @ ' + drexClearCmd().where);
  console.log('  LIVE node      POST /settle → ' + NODE + '   (GET /node/status probes it)');
  console.log('  build the app first:  npm run build   (esbuild → dist/app.js)');
});
