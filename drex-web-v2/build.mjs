// build.mjs — the esbuild bundle step. Bundles src/app.js (Preact + htm +
// @preact/signals + the reused drex-web/drex-viz.js) into one self-contained,
// minified dist/app.js. esbuild is a single Go binary — the whole build toolchain
// is one dependency, not a 300-package tree. At runtime the page makes ZERO
// external requests: everything is inlined. Pass --watch to rebuild on change.
import { build, context } from 'esbuild';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const watch = process.argv.includes('--watch');

const opts = {
  entryPoints: [path.join(HERE, 'src', 'app.js')],
  outfile: path.join(HERE, 'dist', 'app.js'),
  bundle: true,
  format: 'esm',
  target: 'es2020',
  minify: !watch,
  sourcemap: true,
  logLevel: 'info',
  // htm + preact use h() as the pragma; we import { h } explicitly so no JSX
  // transform is needed — plain tagged-template rendering, no compiler.
};

if (watch) {
  const ctx = await context(opts);
  await ctx.watch();
  console.log('esbuild: watching src/ …');
} else {
  await build(opts);
  console.log('esbuild: built dist/app.js');
}
