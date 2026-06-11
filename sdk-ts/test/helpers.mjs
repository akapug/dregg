// Shared test helpers: load the repo's own dregg-wasm build as the
// differential ORACLE (the exact Rust dregg-turn/dregg-sdk code compiled to
// wasm), so the TS wire implementation drift-fails against the source of
// truth without running cargo.

import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);

let cached = null;

/** Load + initialize dregg-wasm (file-linked from ../wasm/pkg). */
export async function loadWasmOracle() {
  if (cached) return cached;
  const pkgDir = dirname(require.resolve("dregg-wasm/package.json"));
  const mod = await import(join(pkgDir, "dregg_wasm.js"));
  mod.initSync({ module: readFileSync(join(pkgDir, "dregg_wasm_bg.wasm")) });
  cached = mod;
  return mod;
}

export const hex = (bytes) => Buffer.from(bytes).toString("hex");

export const fromHex = (s) => Uint8Array.from(Buffer.from(s, "hex"));

export const distDir = join(here, "..", "dist");

export const sdk = () => import(join(distDir, "index.mjs"));
export const raw = () => import(join(distDir, "raw.mjs"));
