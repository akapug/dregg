// Build the dregg front-door extension with esbuild.
//
// Bundling notes:
//  - `@dregg/sdk/browser` is ALIASED to the sdk-ts SOURCE (`../src/browser.ts`),
//    so esbuild compiles it and INLINES `@noble/ed25519` + `@noble/hashes` into
//    one self-contained file (the published `dist/browser.mjs` externalizes
//    noble, which an extension bundle cannot do). The signing path is therefore
//    byte-identical to the SDK and needs no node_modules at runtime.
//  - background + popup are ESM (MV3 module worker / module popup);
//    content + page are IIFE (MV3 content scripts cannot be modules).
import * as esbuild from "esbuild";
import { fileURLToPath } from "node:url";
import { dirname, resolve } from "node:path";

const here = dirname(fileURLToPath(import.meta.url));
const watch = process.argv.includes("--watch");
const dev = watch || process.argv.includes("--dev");
const tests = process.argv.includes("--tests");

// Resolve `@dregg/sdk` and its subpaths to the local sdk-ts SOURCE.
const sdkSrc = resolve(here, "..", "src");
const alias = {
  "@dregg/sdk/browser": resolve(sdkSrc, "browser.ts"),
  "@dregg/sdk/raw": resolve(sdkSrc, "raw.ts"),
  "@dregg/sdk": resolve(sdkSrc, "index.ts"),
};

const common = {
  bundle: true,
  target: ["es2022"],
  sourcemap: dev,
  alias,
  logLevel: "info",
};

/** The extension bundles (manifest entry points). */
const moduleBundles = {
  ...common,
  entryPoints: [resolve(here, "src/background.ts"), resolve(here, "src/popup.ts")],
  outdir: resolve(here, "dist"),
  format: "esm",
};
const iifeBundles = {
  ...common,
  entryPoints: [resolve(here, "src/content.ts"), resolve(here, "src/page.ts")],
  outdir: resolve(here, "dist"),
  format: "iife",
};

async function buildAll() {
  await esbuild.build(moduleBundles);
  await esbuild.build(iifeBundles);
  console.log("extension built → dist/");
}

async function buildTests() {
  // The trusted-path core + the SDK classes, bundled to ONE ESM file so
  // `node --test` can drive the flow headlessly (mediator and test share a
  // single copy of the SDK — no cross-bundle class-identity mismatch).
  await esbuild.build({
    ...common,
    entryPoints: [resolve(here, "test/harness.ts")],
    outdir: resolve(here, "test/.build"),
    format: "esm",
    outExtension: { ".js": ".mjs" },
  });
  console.log("test harness built → test/.build/harness.mjs");
}

if (watch) {
  const m = await esbuild.context(moduleBundles);
  const i = await esbuild.context(iifeBundles);
  await Promise.all([m.watch(), i.watch()]);
  console.log("watching…");
} else {
  if (!tests) await buildAll();
  if (tests || process.argv.includes("--all")) await buildTests();
}
