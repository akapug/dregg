// Local static+fixture server for the portal.dregg.studio capture.
//
// Serves the committed static portal (`portal/dist`) AND a small SAMPLE cell
// set on the node read API the portal fetches (`/api/cells`, `/api/cell/{id}`,
// `/observability/stream`). The shapes match the REAL edge node
// (`discord-bot/src/http_server.rs::BotCellView` + the SSE hello/ping frames),
// so the portal renders exactly as it does against a live node.
//
// HONESTY: the in-tab STARK verify (the marquee) is the REAL wasm light client
// and needs no server — it re-witnesses a finalized history in the tab. This
// server ONLY supplies the network-graph DATA, which here is a labelled SAMPLE
// set, not a live devnet. See demo/SURFACES.md.
//
// Usage: node demo/surfaces/serve.mjs [port]   (default 8787)
import { createServer } from "node:http";
import { readFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { extname, join, normalize } from "node:path";
import { fileURLToPath } from "node:url";
import { dirname } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const ROOT = join(here, "..", "..");
const DIST = join(ROOT, "portal", "dist");
// The committed portal/dist/pkg is missing the wasm-bindgen `snippets/` dir the
// in-tab verifier needs, so serve the COMPLETE freshly-built bundle from
// wasm/pkg for /pkg/* (same exports: produce_external_history_envelope,
// verify_devnet_history, genesis_vk_anchor, verify_slot_opening).
const WASM_PKG = join(ROOT, "wasm", "pkg");
const PORT = Number(process.argv[2] || 8787);

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".wasm": "application/wasm",
  ".json": "application/json; charset=utf-8",
  ".map": "application/json; charset=utf-8",
  ".svg": "image/svg+xml",
};

// A small SAMPLE cell set (shape == BotCellView). Index 0 is the custodial hub.
const CELLS = [
  { id: "b3a1f0c2d4e6a8b0c2d4e6f80a1c3e5f7092b4d6a8c0e2f406182a3c4e6f8091", found: true, balance: 41500, nonce: 128, capability_count: 9, has_program: false, program_vk: null, created_by_factory: null, nullifier_known: false },
  { id: "1c9e7d5b3a1f0e8c6a4b2d0f8e6c4a2b1093f7d5b3a1e9c7f5d3b1a9e7c5d3f1", found: true, balance: 8800, nonce: 42, capability_count: 4, has_program: true, program_vk: "9f2c7a4e1b8d5c3a0f6e2d9b4c7a1e8f", created_by_factory: "aa11bb22cc33dd44ee55ff6600778899", nullifier_known: false },
  { id: "77aa55cc33ee11ff9988776655443322110fedcba9876543210abcdef0123456", found: true, balance: 3200, nonce: 17, capability_count: 3, has_program: false, program_vk: null, created_by_factory: null, nullifier_known: true },
  { id: "2f4e6a8c0d2b4f6a8c0e2d4b6f8a0c2e4d6b8f0a2c4e6d8b0f2a4c6e8d0b2f4a", found: true, balance: 15600, nonce: 73, capability_count: 6, has_program: true, program_vk: "3d1a9f7c5e2b8d4a0c6f3e1b9d7a5c2f", created_by_factory: "aa11bb22cc33dd44ee55ff6600778899", nullifier_known: false },
  { id: "8e6c4a2f0d8b6e4c2a0f8d6b4e2c0a8f6d4b2e0c8a6f4d2b0e8c6a4f2d0b8e6c", found: true, balance: 990, nonce: 8, capability_count: 2, has_program: false, program_vk: null, created_by_factory: null, nullifier_known: false },
  { id: "5b3d1f9e7c5a3b1d9f7e5c3a1b9d7f5e3c1a9b7d5f3e1c9a7b5d3f1e9c7a5b3d", found: true, balance: 6100, nonce: 31, capability_count: 5, has_program: false, program_vk: null, created_by_factory: null, nullifier_known: false },
  { id: "0a2c4e6d8b0f2a4c6e8d0b2f4a6c8e0d2b4f6a8c0e2d4b6f8a0c2e4d6b8f0a2c", found: true, balance: 2450, nonce: 12, capability_count: 3, has_program: true, program_vk: "7c4a1f9e6d3b8c5a2f0e7d4b1a9c6f3e", created_by_factory: null, nullifier_known: false },
];
const BY_ID = Object.fromEntries(CELLS.map((c) => [c.id, c]));

let seq = 100;

const server = createServer(async (req, res) => {
  const url = new URL(req.url, "http://localhost");
  const path = url.pathname;

  if (path === "/api/cells") {
    return json(res, 200, CELLS);
  }
  if (path.startsWith("/api/cell/")) {
    const id = decodeURIComponent(path.slice("/api/cell/".length));
    const c = BY_ID[id] || { id, found: false, balance: 0, nonce: 0, capability_count: 0, has_program: false, program_vk: null, created_by_factory: null, nullifier_known: false };
    return json(res, 200, c);
  }
  if (path === "/observability/stream") {
    res.writeHead(200, {
      "content-type": "text/event-stream",
      "cache-control": "no-cache",
      connection: "keep-alive",
    });
    res.write(`event: hello\ndata: ${JSON.stringify({ apps: 8, nullifiers: 3 })}\n\n`);
    const t = setInterval(() => {
      seq += 1;
      res.write(`event: ping\ndata: ${JSON.stringify({ seq, nullifiers: 3 })}\n\n`);
    }, 2000);
    req.on("close", () => clearInterval(t));
    return;
  }

  // static file: /pkg/* → the complete wasm bundle; everything else → portal/dist
  let rel = normalize(path === "/" ? "/index.html" : path).replace(/^(\.\.[/\\])+/, "");
  let file;
  if (rel.startsWith("/pkg/")) {
    const sub = rel.slice("/pkg/".length);
    // Prefer the committed portal build; fall back to wasm/pkg for the
    // wasm-bindgen snippets/ dir the committed dist omits.
    const primary = process.env.PORTAL_PKG === "committed"
      ? join(DIST, "pkg", sub)
      : join(WASM_PKG, sub);
    const fallback = process.env.PORTAL_PKG === "committed"
      ? join(WASM_PKG, sub)
      : join(DIST, "pkg", sub);
    file = existsSync(primary) ? primary : fallback;
  } else {
    file = join(DIST, rel);
  }
  try {
    const body = await readFile(file);
    res.writeHead(200, { "content-type": MIME[extname(file)] || "application/octet-stream" });
    res.end(body);
  } catch {
    res.writeHead(404, { "content-type": "text/plain" });
    res.end("not found: " + rel);
  }
});

function json(res, code, obj) {
  res.writeHead(code, { "content-type": "application/json; charset=utf-8" });
  res.end(JSON.stringify(obj));
}

server.listen(PORT, () => {
  console.log(`portal capture server: http://localhost:${PORT}  (dist=${DIST})`);
});
