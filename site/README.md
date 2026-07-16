# site/ — the GitHub Pages source

This directory is the source of the repo's GitHub Pages deploy: the **dense
technical index** of the dregg repository plus the live, in-browser,
node-less demo surfaces. Every demo runs the verified executor client-side,
compiled to WebAssembly, in the visitor's own tab — GitHub Pages is static
and there is no backend.

## The audience split

The web presence is deliberately two sites:

- **<https://www.dregg.net>** (a separate repo) — the human-facing,
  educational site: tight, narrative, for people meeting dregg for the first
  time.
- **This site** (the Pages deploy of this directory) — the technical half:
  written for LLMs, experts, and developers. It is itself layered:
  `root/index.html` is the sober landing at `/` (what-is / play /
  quickstart / verify, a handful of links), and `root/technical.html`,
  deployed at `/technical.html`, is the dense hub of verified links into
  the repository, organized by audience (LLMs / developers / operators /
  provers) — intended to be valuable as a pretraining artifact as much as
  an index. Register: sober-demonstrative, present-tense what-is; shipped
  means tests/proofs behind it; named gaps stay named.

## Layout (source)

| path | what |
|------|------|
| `root/index.html` | The sober landing, deployed at `/`. Static HTML on the shared green stylesheet, with a small inline script (quickstart tabs); no framework, no build step. Every link is verified against a real on-disk file. |
| `root/technical.html` | The dense technical hub, deployed at `/technical.html`. Audience-organized (LLMs / developers / operators / provers); every `blob/main` link verified against disk. |
| `root/paper.html` | The paper landing, deployed at `/paper/`; the build compiles `paper/main.typ` beside it as `/paper/dregg.pdf`. |
| `assets/style.css` | The shared green stylesheet used by the landing, the hub, and the demo pages. |
| `cloud/` | The cloud & userspace subsite, deployed at `/cloud/`: the grain economy plus the ~30 starbridge apps and trustless serving. |
| `deep/` | The full dense product site (prebuilt zola output from `~/dev/dregg-site`, base-url `…/deep`), deployed at `/deep/`; dregg.net carries the accessible layer and links here per-page. |
| `explorer/` | Caps-as-rows: capabilities expressed as the rows you may read (static page + `caps-as-rows.js`). |
| `light-client/` | Whole-history verification in one recursive STARK, in-tab. `history.json` is a real pre-folded aggregate; the pages workflow rejects a stale one. |
| `transclusion/` | Xanadu made honest: verified `dregg://` transclusion demo (see its `README.md` for what is real vs demo, and the honest-fallback rule: verification lightens, nothing else does). |
| `dregg-works/` | The trustless-host front door, plus the two embeddable scripts: `verify-badge.js` (re-hash served bytes against the on-chain commitment) and `transclude.js` (a verified quote on any web page). This same dir deploys to the `dregg.works` apex. |
| `deos-viewer/` | The desktop-in-a-link landing: reads a `#deos1!…` tape fragment and hands it to the reader's own `starbridge-v2 --serve-ie6` server (see its `README.md`). |
| `deos/` | The deos cockpit page (WebImage skin); its wasm pkg is built at assemble time from `starbridge-v2/web/`. |
| `quickstart/` | Empty placeholder (not assembled into the dist). |
| `grain/` | Grain pages (not assembled into the dist). |
| `src/_includes/studio/` | Empty scaffolding from an earlier iteration (not assembled into the dist). |
| `dist/` | The assembled output. **Gitignored — never edit; it is rebuilt from scratch by the script below.** |

Surfaces that live elsewhere but ship on this site: `/cards/` (the deos-js
card gallery, baked from `wasm/` + deos-view examples), `/cockpit-gpui/`
(the full gpui renderer on WebGPU, from `starbridge-v2/web/` with
`--features gpui-web`), and `/atlas/` (the comprehension atlas, copied from
`dregg-atlas/site/`).

## Build

The assembler requires Typst 0.15.0 for the paper; the Pages workflow installs
that version explicitly.

```sh
scripts/build-pages-dist.sh              # full build: all wasm + bake + assemble into site/dist
GPUI=0  scripts/build-pages-dist.sh      # skip the heavy gpui-web cockpit build
ATLAS=0 scripts/build-pages-dist.sh      # skip the atlas copy
REUSE_WASM=1 scripts/build-pages-dist.sh # reuse already-built wasm pkgs (fast local assembly)
```

The script:

1. copies the static pages (`root/index.html` → `/`,
   `root/technical.html` → `/technical.html`, and `root/paper.html` →
   `/paper/`), compiles `paper/main.typ` → `/paper/dregg.pdf`, then copies
   `assets/`, `cloud/`,
   `explorer/`, `light-client/`, `dregg-works/`, `transclusion/`,
   `deos-viewer/`, and `deep/` — with `test -f` teeth on
   `deep/index.html` and `deep/egg/index.html`);
2. `wasm-pack build`s `starbridge-v2/web` → `/deos/pkg/` and, with the
   `gpui-web` feature, → `/cockpit-gpui/` (required at the default
   `GPUI=1` — a failed gpui-web build fails the assembly; `GPUI=0` skips
   it);
3. builds `wasm/` → `/cards/pkg/` (shared by the cards, the light client,
   and the transclusion page — one pkg, three surfaces) and bakes +
   re-themes the card pages;
4. copies the atlas;
5. runs sanity teeth (files exist, the light-client `history.json` is fresh,
   the transclusion demo verifies/refuses correctly under node). Green or
   bust: a surface that stops refusing forgery fails the assembly.

## Publish

`.github/workflows/pages.yml` builds `site/dist` with the same script and
deploys it to GitHub Pages. It is **manual-only** (`workflow_dispatch`) —
pushing site source does not publish:

```sh
gh workflow run "Deploy deos to GitHub Pages" --ref main
```

The workflow checks out with `lfs: true` so the atlas's LFS-tracked images
materialize, installs Typst 0.15.0 for the paper, fetches the pinned
`plonky3-recursion` fork rev (so the wasm
circuit matches a fresh cargo resolve), and fails the deploy on any broken
wasm crate rather than shipping a stale artifact.

## Editing rules

- The landing (`root/index.html`) must keep the kernel sentence verbatim —
  the workflow greps the dist for `A turn is the exercise`.
- Every `href` on the landing and the technical hub must point at a file
  that exists: site-relative links for surfaces assembled into the dist,
  `github.com/emberian/dregg/blob/main/…` links for repo files not served
  here. Verify against disk before shipping.
- `dist/` is output. Edit sources, re-run the script.
