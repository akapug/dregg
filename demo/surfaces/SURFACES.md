# The wonder surfaces — portal.dregg.studio + the deos-desktop

Two visual beats the terminal/cockpit film (the browser lane, `dregg-agent/demo/`)
doesn't carry: the **public web portal** and the **deos-desktop**. These are the
prettiest, most-striking surfaces in the project. This lane captures them and
builds two companion clips plus a full-tour stitch.

> Coordination: the browser lane owns `dregg-agent/demo/` (the terminal agent film
> `film.mp4`, the 2-min single cut `film-full.mp4`, the browser companion
> `film-browser.mp4` = cockpit + extension + panes, and `dregg-agent/demo/capture/`).
> **This lane owns `demo/surfaces/`** — portal + desktop only. Nothing here writes
> the browser lane's media; `build-full-tour.sh` reads it read-only.

All media is **gitignored** (`demo/surfaces/.gitignore`) — only the capture
scripts + this doc are committed. Regenerate any clip with the commands below.

## Deliverables (all local, regenerate any time)

| file | what | dur | honesty |
|------|------|-----|---------|
| `out/portal.mp4`    | portal.dregg.studio — hero verify · living network · cell inspector | ~0:18 | **live-render** (real served portal) + a labelled sandbox caveat, see below |
| `out/desktop.mp4`   | the deos-desktop — showcase · moldable workbench · a verified turn | ~0:22 | **live-render** (real gpui offscreen bake, this machine) |
| `out/full-tour.mp4` | the whole breadth — browser main cut → portal → desktop | ~2:40 | composite (browser cut is the browser lane's; portal/desktop as above) |
| `out/shots/*.png`   | the portal stills (hero/network/cell) | — | live-render |
| `out/desktop/*.png` | the desktop bakes (showcase/desktop + before/after turn) | — | live-render |

---

## SURFACE 1 — portal.dregg.studio (the public "trust nothing" face)

The static portal (`portal/dist/`) is a recursive-STARK **light client in a browser
tab**: the hero says *"Don't trust the server. Verify it yourself."*, and the
in-tab `dregg_wasm` verifier re-witnesses a finalized history. `cell.html` folds a
cell's whole committed history to one root; `index.html` shows the living network
(cells read live from the edge node's `/api/cells` + `/observability/stream` SSE).

### Beats / shot-list

| # | shot | on screen |
|---|------|-----------|
| P1 | **hero** (`shots/01-hero.png`) | "Don't trust the server / **Verify it yourself**" · "RECURSIVE-STARK LIGHT CLIENT · IN THIS TAB" · the `dregg_wasm · recursive-STARK verifier` panel ("Proof engine idle — a verifier, not a viewer") |
| P2 | **living network** (`shots/02-network.png`) | "Sovereign cells, proving themselves" · the hub-and-spoke cell graph · the live SSE chip (`live · seq N · 3 nullifiers`) · the cell grid (balance/nonce/caps) |
| P3 | **cell inspector** (`shots/03-cell-fold.png`) | "RECURSIVE FOLD · WHOLE COMMITTED HISTORY → ONE ROOT" (t0 t1 t2 → root) · the field table "CELL FIELDS · READ LIVE FROM THE EDGE / the server's claim" (found-on-chain, balance, nonce, caps, program vk, minted-by-factory) |

### HONESTY (read before posting)

- **The portal UI is the REAL served portal** (`portal/dist/`), driven in headless
  chromium via Playwright — the hero copy, the verifier panel, the living-network
  graph over the cell set, and the cell fold-theatre + field table are all genuine
  painted surfaces.
- **The network-graph data is a labelled SAMPLE set**, not a live devnet. `serve.mjs`
  serves a small cell set whose shape matches the real edge node
  (`discord-bot/src/http_server.rs::BotCellView` + the SSE `hello`/`ping` frames),
  so the portal renders exactly as against a live node — but no live-network / live-n=5
  claim is made.
- **The in-tab STARK verify is REAL wasm, but does NOT complete in this sandbox.**
  The verifier's proof-**generation** step (`produce_external_history_envelope`)
  traps with a wasm `unreachable` under this box's cached headless-chromium
  (Playwright build 1223) — a wasm limit here. It completes in a **full desktop
  browser**. So the captured shots show the portal's trust-first UI + the verifier
  **engaging** (the "Proof engine idle / press run" panel, the fold theatre), **not**
  a green "Verified ✓" end-state — we do not fabricate one. For the network + cell
  shots the capture aborts `/pkg/**` so the (blocking) verifier can't stall the page;
  the cell shot removes the resulting "couldn't run here" banner to frame the
  inspector's structure honestly.
- Marketing line, kept truthful: *"a recursive-STARK light client that verifies in
  your browser — trusting no server (runs in a full desktop browser)."*

### Re-capture — exact commands

```sh
# 0. deps once (kept out of git): playwright + a cached chromium
cd demo/surfaces && npm i playwright && cd ../..
export CHROME_PATH="$HOME/Library/Caches/ms-playwright/chromium-1223/chrome-mac-arm64/Google Chrome for Testing.app/Contents/MacOS/Google Chrome for Testing"
#   (any Playwright chromium works; point CHROME_PATH at it, or drop CHROME_PATH
#    and run `npx playwright install chromium` to fetch the matching build.)

# 1. serve the portal + the sample read-API (static portal/dist + wasm from wasm/pkg)
node demo/surfaces/serve.mjs 8787 &     # http://localhost:8787

# 2. drive it in Playwright → shots/*.png + video/*.webm
node demo/surfaces/capture.mjs
kill %1

# 3. build the clip (needs an ffmpeg with drawtext; brew install ffmpeg@6)
bash demo/surfaces/build-portal-clip.sh   # → out/portal.mp4
```

Notes: `serve.mjs` serves `/pkg/*` from `wasm/pkg` (the committed `portal/dist/pkg`
omits the wasm-bindgen `snippets/` dir the verifier needs). `PORTAL_PKG=committed`
serves the committed 15 MB build instead (both behave identically here).

---

## SURFACE 2 — the deos-desktop (the WONDER surface)

`starbridge-v2` bakes the live gpui desktop **offscreen via wgpu/Metal** — no
display needed. The prebuilt binary at `target/debug/starbridge-v2` (built with the
`headless-render` feature) renders 26 surface modes to PNG in ~15-20s each. This is
a **genuine live render on this machine**, not a pre-baked atlas.

### Beats / shot-list

| # | shot | on screen |
|---|------|-----------|
| D1 | **showcase** (`desktop/showcase.png`, 5120×3200) | the polished dark deos desktop: cap-bounded **membrane** fork · **deos-matrix** chat · **deos-zed** editor (the `commit_turn` seam) · recorded **terminal** (`312 passed; 0 failed`) · confined **Hermes** agent with live tool budgets · `Σ balance = 5000 conserved` + seL4 / verified / height chips |
| D2 | **moldable workbench** (`desktop/desktop.png`, 3200×2000) | the NT/Pharo workbench over the live verified World: 4 sovereign cell-icons · **Inspector** (state-slots + balance gauge) · **Spotter** (13 matches) · **World Explorer** (Ledger/Chronicle/Conservation, Σ=5000) · right-click context menu · **Workflow Composer** · the floating **Pharo Halo** · 12-window taskbar |
| D3 | **a verified turn re-paints the world** (`desktop/desktop.world-board-{before,after}.png`) | the confined agent **composes a live World Board from scratch**; height 5 → 8; per-cell balance breakdown, **Σ balance = 5000 invariant under transfers** |

### HONESTY

- **Live-render, this machine.** All three PNGs are fresh gpui offscreen bakes from
  `target/debug/starbridge-v2` — real `deos_view::ViewNode` scenes over a real cell
  World (`BALANCE_SUM = 5000`, conserved). The `--render-desktop` mode also drives
  **real verified turns** (height 5 → 8) and drops the before/after companions.
- Not seL4-on-hardware and not the live QEMU image viewer (`make run-image` needs
  the seL4 image build + QEMU — out of scope here); this is the same live-cell
  content via the far cheaper gpui offscreen path. No live-cloud / live-n=5 claim.
- Fallback (unused — the live bake works): a full pre-baked atlas exists at
  `dregg-atlas/` (40 surface PNGs + an HTML viewer at `dregg-atlas/site/index.html`);
  label it **pre-baked-atlas** if ever used instead of the live bake.

### Re-capture — exact commands

```sh
# the binary already exists (built with headless-render); no rebuild needed.
# NB: it APPENDS .png — pass a basename without extension.
./target/debug/starbridge-v2 --render-showcase demo/surfaces/out/desktop/showcase
./target/debug/starbridge-v2 --render-desktop  demo/surfaces/out/desktop/desktop
#   → desktop.png + desktop.world-board-{before,after}.png + desktop.viewnode-{before,after}.png
# (rebuild if absent: cargo build -p starbridge-v2 --features headless-render)

# build the clip (needs ffmpeg@6 for drawtext + imagemagick for prescale)
bash demo/surfaces/build-desktop-clip.sh   # → out/desktop.mp4
```

Other striking modes (all live, headless PNG): `--render-cockpit`,
`--render-agent-attach`, `--render-unified-boot`, `--render-client-signed-turn`,
`--render-self-hosting[-full]`, `--render-apps-showcase`, `--render-service-economy`,
`--render-webshell-live`, `--render-live-brain`. Add `--render-size W H` to override.

---

## Composition — the two films

### A. The tight ~2-min SUBMISSION cut (the highlight)

The browser lane's `dregg-agent/demo/film-full.mp4` (~1:59) is the highlight —
terminal agent (2× recap) → cockpit verify + tamper. Give the two wonder surfaces
a **flash each** near the "prove / trust-nothing" beat:

```
0:00  COLD OPEN + SETUP + OPERATE + SPEND + CLIMAX   (terminal agent — browser lane)
1:05  PROVE + TEETH                                   (cockpit verify + BadSignature — browser lane)
1:30  ► FLASH: portal.dregg.studio — "verify it yourself, in your browser"   (~4s, out/portal.mp4 P1)
1:34  ► FLASH: the deos-desktop — sovereign cells, inspectors, a verified turn (~5s, out/desktop.mp4 D1/D2)
1:40  CLOUD + CLOSE                                    (browser lane)
```

Two ~4-5s inserts keep the 2-min length while adding the prettiest surfaces. Cut
the portal flash to P1 (the "Verify it yourself" hero) and the desktop flash to the
showcase D1 + a beat of the D2 workbench.

### B. The full-tour companion (~2:40, the whole breadth)

`build-full-tour.sh` concatenates (normalized to 1280×800): the browser main cut →
`portal.mp4` → `desktop.mp4`.

```sh
bash demo/surfaces/build-full-tour.sh    # → out/full-tour.mp4  (~2:40)
```

```
0:00–1:59  browser main cut     terminal agent + cockpit verify + tamper   (film-full.mp4)
1:59–2:17  portal.dregg.studio  verify-it-yourself · living network · cell fold-to-one-root
2:17–2:40  the deos-desktop     showcase · moldable workbench · a verified turn re-paints Σ=5000
```

For the explicit extension + panes breadth, the browser lane's
`dregg-agent/demo/film-browser.mp4` (~1:08) can be spliced in before the portal beat
— add its path to the `CANDIDATES` list in `build-full-tour.sh` to reach ~3:45.
```
