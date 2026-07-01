// A hermetic local stub of the dregg node + the cap-auth webauth control plane,
// for driving the cipherclerk extension on camera WITHOUT the public devnet.
//
// HONEST: this is a STUB. The node status it reports is canned. But the login
// leg is the REAL challenge/sign flow: the extension signs the server's nonce
// with the profile's real Ed25519 key, and this stub VERIFIES that signature
// with node:crypto before minting a session — a forged signature is rejected
// (see /auth/login). The subject is derived here as a stub (dregg:<pubkey-16>),
// not the substrate account-identity cell a real deployment computes.

import express from 'express';
import crypto from 'node:crypto';

const PORT = parseInt(process.argv[2] || '8420', 10);
const app = express();
app.use(express.json());
app.use(express.raw({ type: 'application/octet-stream', limit: '4mb' }));

const nodeStatus = {
  ok: true,
  version: '0.1.0-local-stub',
  public_key: '11'.repeat(32),
  federation_mode: 'single',
  latest_height: 42,
  merkle_root: 'abcdef0123456789'.repeat(4),
  height: 42,
  peer_count: 3,
};
const status = (_req, res) => res.json(nodeStatus);
app.get('/status', status);
app.get('/api/node/status', status);
app.get('/api/node/health', status);
app.get('/api/node/identity', (_req, res) =>
  res.json({ public_key: '11'.repeat(32), agent_cell: '22'.repeat(32), unlocked: true,
    agent_balance: 1_000_000, agent_nonce: 7 }));

// ── cap-account login: challenge → sign → session (the REAL handshake) ────────
const challenges = new Map(); // pubkey -> { challenge, expiresAt }

app.post('/auth/challenge', (req, res) => {
  const pk = String(req.body?.public_key || '');
  const nonce = crypto.randomBytes(16).toString('hex');
  const expiresAt = Math.floor(Date.now() / 1000) + 300;
  const challenge = `dregg-login:v1:${pk.slice(0, 16)}:${nonce}:${expiresAt}`;
  challenges.set(pk, { challenge, expiresAt });
  res.json({ challenge, expires_at: expiresAt });
});

// Build an Ed25519 public KeyObject from a raw 32-byte hex key (SPKI DER wrap).
function ed25519FromRaw(hex) {
  const raw = Buffer.from(hex, 'hex');
  if (raw.length !== 32) return null;
  const der = Buffer.concat([Buffer.from('302a300506032b6570032100', 'hex'), raw]);
  try { return crypto.createPublicKey({ key: der, format: 'der', type: 'spki' }); }
  catch { return null; }
}

app.post('/auth/login', (req, res) => {
  const pk = String(req.body?.public_key || '');
  const challenge = String(req.body?.challenge || '');
  const sigHex = String(req.body?.signature || '');
  const key = ed25519FromRaw(pk);
  if (!key) return res.status(400).json({ error: 'bad public key' });
  let ok = false;
  try { ok = crypto.verify(null, Buffer.from(challenge, 'utf8'), key, Buffer.from(sigHex, 'hex')); }
  catch { ok = false; }
  if (!ok) return res.status(401).json({ error: 'signature did not verify against the challenge' });
  // Genuine possession proven. Mint a session. (subject is a STUB derivation.)
  const subject = `dregg:${pk.slice(0, 16)}`;
  res.json({
    session_token: 'sess_' + crypto.randomBytes(18).toString('hex'),
    subject,
    account_id: pk.slice(0, 16),
    expires_at: Math.floor(Date.now() / 1000) + 3600,
  });
});

app.post('/auth/logout', (_req, res) => res.json({ ok: true }));

// Permissive fallbacks so an unrelated popup probe never errors on camera.
app.get('*', (_req, res) => res.json({ ok: true }));
app.post('*', (_req, res) => res.json({ ok: true }));

app.listen(PORT, '127.0.0.1', () => console.error(`mock-node: http://127.0.0.1:${PORT}`));
