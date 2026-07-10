// The Commons demo — a tiny self-contained static server.
//
// Why a server (not a bare file:// open): the page loads an ES-bundled module and a
// wasm binary, and the wasm-bindgen glue instantiates the module via
// `instantiateStreaming`, which needs a real HTTP origin + `application/wasm` MIME.
// So we serve, rather than double-click.
//
// It bundles `app.ts` (the element + engine wiring) on startup with esbuild, and
// serves it alongside the page, the wasm glue + binary (from ../extension), and the
// scene. `run.mjs` reuses `buildApp` + `makeServer` to drive the same page headless.
//
//   node demo/serve.mjs        → serves at http://127.0.0.1:8787 (open it)
//   node demo/serve.mjs 9000   → serves on a chosen port

import http from "node:http";
import { readFile } from "node:fs/promises";
import { createReadStream } from "node:fs";
import { fileURLToPath } from "node:url";
import { createRequire } from "node:module";
import path from "node:path";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const REPO = path.resolve(__dirname, "..");
const EXT = path.join(REPO, "extension");

// esbuild lives under extension/node_modules; resolve it from there.
const extRequire = createRequire(path.join(EXT, "package.json"));
const esbuild = extRequire("esbuild");

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".mjs": "text/javascript; charset=utf-8",
  ".wasm": "application/wasm",
  ".scene": "text/plain; charset=utf-8",
  ".txt": "text/plain; charset=utf-8",
};

/** Bundle the page-side app (imports the shipping element + engine from ../extension/src). */
export async function buildApp() {
  const out = await esbuild.build({
    entryPoints: [path.join(__dirname, "app.ts")],
    bundle: true,
    format: "iife",
    platform: "browser",
    target: ["es2022"],
    sourcemap: "inline",
    write: false,
    logLevel: "silent",
  });
  return out.outputFiles[0].text;
}

/** Serve the demo. Returns { server, base }. */
export async function makeServer(port = 0) {
  const appJs = await buildApp();
  const index = await readFile(path.join(__dirname, "index.html"), "utf8");
  const scene = await readFile(path.join(__dirname, "stories", "the-commons.scene"), "utf8");

  const server = http.createServer(async (req, res) => {
    try {
      const url = (req.url || "/").split("?")[0];
      if (url === "/" || url === "/index.html") return send(res, index, MIME[".html"]);
      if (url === "/app.js") return send(res, appJs, MIME[".js"]);
      if (url === "/stories/the-commons.scene") return send(res, scene, MIME[".scene"]);
      if (url === "/dregg_wasm.js") {
        const js = await readFile(path.join(EXT, "dregg_wasm.js"), "utf8");
        return send(res, js, MIME[".js"]);
      }
      if (url === "/dregg_wasm_bg.wasm") {
        res.writeHead(200, { "content-type": MIME[".wasm"] });
        return createReadStream(path.join(EXT, "dregg_wasm_bg.wasm")).pipe(res);
      }
      res.writeHead(404, { "content-type": "text/plain" });
      res.end("not found");
    } catch (e) {
      res.writeHead(500, { "content-type": "text/plain" });
      res.end(String(e?.message ?? e));
    }
  });
  await new Promise((r) => server.listen(port, "127.0.0.1", r));
  const { port: p } = server.address();
  return { server, base: `http://127.0.0.1:${p}` };
}

function send(res, body, type) {
  res.writeHead(200, { "content-type": type });
  res.end(body);
}

// Run standalone: `node demo/serve.mjs [port]`
if (import.meta.url === `file://${process.argv[1]}`) {
  const port = Number(process.argv[2] || 8787);
  const { base } = await makeServer(port);
  console.log(`\n  The Commons — verifiable story demo`);
  console.log(`  open:  ${base}\n`);
  console.log(`  (Ctrl-C to stop)\n`);
}
