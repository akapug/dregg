# THE DREGG ATLAS

A self-built, offline-explorable interactive map of dregg — the formally verified
distributed object-capability OS. It was authored by an AI agent *crawling the
live verified image* through the `dregg-mcp` harness: every state, cell, turn,
and refusal here was read or fired against the real embedded executor. Nothing is
mocked.

## Open it

Open **`site/index.html`** in any browser (it is fully offline — JS is vendored,
data is inlined). Seven views:

- **Game Tree** — the reachable PROTOCOL state-space as a radial starburst
  (genesis at the centre, depth as colour-graded rings). Each node is a
  world-state (keyed by its post-state Merkle root); each edge a turn fired
  through the verified executor. Click a state for its cell snapshot and its
  committed/refused turns; click to highlight its reachable subtree.
- **UI Tree** — the UI INTERACTION state-space: exploring inside and through the
  cockpit surfaces. A radial DAG (HOME → the 28 surfaces → each surface's internal
  navigations: cycling focus chips, picking lenses, toggling, scrubbing). Each
  node is a distinct *rendered* UI state (screenshot); each edge the interaction
  that reaches it. Click a state for its screenshot + the interactions out of it.
  (Driving the real cockpit headlessly this way also shakes out render bugs —
  260 states rendered with zero panics; four live-animated tabs are excluded, see
  the Anomalies page.)
- **Ocap Web** — cells + the capability grants between them; click a cell for its
  seven presentation faces.
- **Surfaces** — every cockpit surface screenshotted (the `Tab` enum's 30 surfaces
  plus the dock dev panes), each with a first-principles, code-grounded explainer
  and the components it is built from (click a card → its full page). The surfaces
  now render inside the **coherent five-mode frame** (`cockpit/frame.rs`,
  `docs/deos/COCKPIT-UX.md`): a persistent top bar (identity cell + cap-badge · live
  ledger clock · ⌘K palette · ⌘J dock), a left rail of the five modes — **Inhabit ·
  Author · Dev · Inspect · Operate** — a mode sub-nav, and a collapsible dev dock.
  The gallery groups the surfaces by their mode; the Inspect mode's main surface is
  the **reflective inspector card** (the inspector reborn as a live deos-js card,
  itself an object the image renders).
- **Components** — the gpui-component widget pillar: the visual building blocks the
  cockpit is built from. Each widget names what it is, its variants, and the
  surfaces that render it; the catalog marks which are *used live in the cockpit
  today* (a live grep of the cockpit tree) vs *available* in the palette.
- **Protocol** — the deep reference: the thesis, the eight verbs, the four
  substances + conservation, the AuthRequired lattice, the refusal taxonomy, the
  receipt structure.
- **About** — what this is and how it was built.

The four pillars — Game Tree, Ocap Web, Surfaces, Components — plus the Atlas Web,
the cross-linked hypermedia map over every object (cell · surface · component ·
effect · verb · state) with a ⌘K spotter. Every object carries a stable id and
typed edges, so anything cross-links to anything.

## Regenerate it from the live system

```
cd dregg-atlas

# 0. build the dregg-mcp harness + the headless-render binary (once). The
#    workspace is UNIFIED (one root `target/`); mcp_client.py finds the binaries
#    in `<repo>/target/release/` (falling back to the old per-crate path).
( cd ../starbridge-v2 && cargo build --release --features native-full \
                       --bin dregg-mcp --bin starbridge-v2 )

python3 crawl.py    # walk the protocol state-space + emit the hypermap (MCP `map`
                    # tool merged in) + the components pillar (a source grep)
python3 shoot.py    # screenshot every cockpit surface (the surfaces.py census;
                    # --no-mcp emits the manifest only, for a later screenshot pass)
# the UI tree: BFS-walk the cockpit's UI state-space, screenshot each state
( cd ../starbridge-v2 && ZED_OFFSCREEN_PREFER_CPU=1 \
  ATLAS_UI_NODES=260 target/release/starbridge-v2 --explore-ui ../dregg-atlas/ui-explore )
python3 verify.py   # ORACLE: assert conservation + well-formedness across the crawled state-space
python3 build.py    # assemble the site
open site/index.html
```

Tunables (env): `ATLAS_DEPTH` (game-tree depth, default 4), `ATLAS_NODES` /
`ATLAS_EDGES` (caps), `ATLAS_XFER` (transfer amount the crawl fires).

## How it works

- `mcp_client.py` — a JSON-RPC stdio client for `dregg-mcp` (the verified-executor
  driving harness; see `../docs/deos/DREGG-MCP.md`).
- `crawl.py` — DFS over the reachable state-space. Backtracking uses the MCP's
  fork-based `snapshot`/`restore` (instant), not a 3-second world reboot. The
  move set at each state is every self-affordance on every cell (peek/touch/write/
  grant) PLUS a cross-cell transfer between every ordered pair (value flow +
  conservation). Bounded by depth + node/edge caps; every bound is logged so a
  truncation is never mistaken for completeness.
- `surfaces.py` — the canonical SURFACE CENSUS (the single source of truth): the
  cockpit's 30 `Tab`s + the dock dev panes, each with its MCP screenshot tab name,
  bake path (`tab` vs `showcase`), explainer-section slug, and blurb. Imported by
  both `shoot.py` and `build.py`.
- `shoot.py` — drives the MCP `screenshot` tool (the real gpui Cockpit bake) over
  every surface in the census. Reuses a prior PNG when a re-bake isn't possible, so
  a new MCP only needs to fill the new surfaces.
- `components.py` — the COMPONENTS pillar emitter: a curated catalog of the
  gpui-component widget set (name · what-it-is · variants · module) joined with a
  LIVE grep of `starbridge-v2/src/cockpit/` so the "used in deos / on which surface"
  edges are never stale. Emits `data/components.json` with stable ids + typed edges.
- `crawl.py`'s hypermap — synthesizes a cross-linked typed graph (cell → face →
  affordance → effect → ocap-edge) AND merges the MCP `map` tool's authoritative
  backbone when present → `data/hypermap.json`.
- `build.py` + `tmpl/` — the site-builder: cytoscape.js + dagre for the graphs,
  the explainers parsed from `explainers/*.md`, the static pages cross-linked to
  the SPA (including a static `pages/components.html`).

The honest scope: the game tree is exhaustive *over the crawled move set* (the
self-affordance vocabulary + cross-cell transfers) up to the depth bound — not
over every possible effect/argument combination, which is unbounded. The move set
and bounds are stated in `data/gametree.json`'s `meta`.
