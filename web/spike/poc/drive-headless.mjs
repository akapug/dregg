// drive-headless.mjs — load the POC page in REAL headless Chrome (no puppeteer/npm),
// drive it over the DevTools Protocol with node's built-in WebSocket, and report the
// in-browser verdict. This closes the "Node-ESM proxy" gap: the real Lean executor
// wasm runs in an actual browser engine here, not just Node.
//
// Usage: node drive-headless.mjs            (serves web/spike on :8011, drives Chrome)
import { spawn } from "node:child_process";
import http from "node:http";
import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const SPIKE = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const PORT = 8011;
const CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome";
const CDP_PORT = 9222;

const MIME = { ".html":"text/html", ".js":"text/javascript", ".mjs":"text/javascript",
  ".wasm":"application/wasm", ".json":"application/json", ".css":"text/css" };

// --- tiny static server (cross-origin-isolation headers in case threads ever needed) ---
const server = http.createServer((req, res) => {
  let p = decodeURIComponent(req.url.split("?")[0]);
  if (p === "/") p = "/poc/index.html";
  const fp = path.join(SPIKE, p);
  if (!fp.startsWith(SPIKE) || !fs.existsSync(fp) || fs.statSync(fp).isDirectory()) {
    res.writeHead(404); res.end("404"); return;
  }
  res.setHeader("Cross-Origin-Opener-Policy", "same-origin");
  res.setHeader("Cross-Origin-Embedder-Policy", "require-corp");
  res.setHeader("Content-Type", MIME[path.extname(fp)] || "application/octet-stream");
  fs.createReadStream(fp).pipe(res);
});

async function cdp() {
  // discover the page target's websocket
  const list = await fetch(`http://127.0.0.1:${CDP_PORT}/json`).then(r => r.json());
  const page = list.find(t => t.type === "page") || list[0];
  return page.webSocketDebuggerUrl;
}

async function main() {
  await new Promise(r => server.listen(PORT, r));
  console.log(`[poc] serving ${SPIKE} on http://127.0.0.1:${PORT}`);

  const userDir = fs.mkdtempSync("/tmp/poc-chrome-");
  const chrome = spawn(CHROME, [
    "--headless=new", `--remote-debugging-port=${CDP_PORT}`,
    `--user-data-dir=${userDir}`, "--no-first-run", "--no-default-browser-check",
    "--disable-gpu", `http://127.0.0.1:${PORT}/poc/index.html`,
  ], { stdio: ["ignore", "ignore", "pipe"] });

  // wait for CDP endpoint
  let wsUrl;
  for (let i = 0; i < 100; i++) {
    try { wsUrl = await cdp(); break; } catch { await new Promise(r => setTimeout(r, 100)); }
  }
  if (!wsUrl) { console.error("[poc] CDP never came up"); chrome.kill(); server.close(); process.exit(2); }

  const ws = new WebSocket(wsUrl);
  let id = 0; const pend = new Map();
  const send = (method, params={}) => new Promise(res => { const i = ++id; pend.set(i, res); ws.send(JSON.stringify({ id:i, method, params })); });
  await new Promise(r => ws.addEventListener("open", r, { once:true }));
  ws.addEventListener("message", ev => {
    const m = JSON.parse(ev.data);
    if (m.id && pend.has(m.id)) { pend.get(m.id)(m.result); pend.delete(m.id); }
  });

  await send("Runtime.enable");
  await send("Page.enable");

  // poll window.__POC_RESULT__ until set (the page boots wasm + runs turns async)
  let result = null;
  for (let i = 0; i < 200; i++) {   // up to ~20s
    const r = await send("Runtime.evaluate", {
      expression: "JSON.stringify(window.__POC_RESULT__ || null)", returnByValue: true });
    const v = r?.result?.value;
    if (v && v !== "null") { result = JSON.parse(v); break; }
    await new Promise(r => setTimeout(r, 100));
  }

  // grab the rendered post-state for evidence
  const dom = await send("Runtime.evaluate", {
    expression: "JSON.stringify({title:document.title,"+
      "out1:document.getElementById('out1').textContent,"+
      "out2:document.getElementById('out2').textContent,"+
      "status:document.getElementById('status').textContent})", returnByValue: true });
  const ev = JSON.parse(dom.result.value);

  console.log("\n[poc] === in-browser (headless Chrome) result ===");
  console.log("[poc] status:", ev.status);
  console.log("[poc] turn ① post-state:", ev.out1);
  console.log("[poc] turn ② post-state:", ev.out2);
  console.log("[poc] document.title:", ev.title);
  console.log("[poc] verdict:", result ? (result.pass ? "PASS" : "FAIL: "+result.detail) : "TIMEOUT");

  ws.close(); chrome.kill(); server.close();
  process.exit(result && result.pass ? 0 : 1);
}
main().catch(e => { console.error(e); process.exit(3); });
