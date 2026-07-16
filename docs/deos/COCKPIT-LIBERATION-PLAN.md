# Cockpit Liberation Plan — surfaces as portable deos-view cards

The architectural goal: **starbridge-v2 is a thin gpui renderer, not the home of the
surfaces.** Every cockpit surface that today is a hardcoded gpui element tree becomes a
portable **deos-view card** — declarative `deos.ui.*` view-tree data, renderer-independent
(gpui today, web/HTML tomorrow), agent-rewritable, and reusable. The card is the source of
truth; gpui merely paints it; a button click fires the same cap-gated verified turn it
would today.

This document is the census + gap analysis + the surface→card pattern + the ranked
migration ladder + where progressive-disclosure lives + the apps-launcher-as-card plan. It
is read-only on code; the ladder's remaining rungs are sequenced below.

## The one-paragraph verdict

**The pattern is built and proven end-to-end, and the mode-card IS the deployed surface
for 19 of the cockpit's 32 tabs.** `starbridge-v2/src/dock/card_surface.rs` is the keystone:
it mounts a card over the cockpit's *live* `World`, generating the view-tree in Rust from the
live ledger, bridging it to a `deos_view::ViewNode`, hosting it in a `CardPane`, firing real
turns through `World::commit_turn`, AND routing edit-from-within (`ModeCardSurface::edit_view`,
a receipted `ViewPatch` with blame). `card-pane` rides the DEFAULT build (`default =
["desktop"]` folds it in — `starbridge-v2/Cargo.toml`), and for every carded tab the `Tab`
dispatch (`cockpit/panels_workspace.rs:193+`) renders the mode-card as the surface, with the
gpui panel demoted to the fail-soft fallback + the card-pane-off home. The
progressive-disclosure (simple-vs-adept) layer is built and wired: `ViewNode::Adept` +
`Disclosure` + the `disclose` pre-walk (`deos-view/src/tree.rs`), authored as `props.adept`
(`card_editor`), applied at every card mount (`card_pane.rs` mounts the `Simple`
projection; the web pipeline threads `req.disclosure`). What is NOT done:
(1) no surface has had its gpui tree DELETED — the card is the default *projection*, not yet
the sole *definition*, so every carded surface still carries a duplicate gpui render;
(2) the rich-interactive nodes (tab-strips, scrubbers, right-click menus, halo handles)
are IN the deos-view *renderer* (`tree.rs`'s
`Tabs`/`Slider`/`Menu`/`Halo`/`Grid`/`Gauge`/`Section`, plus `Pill`/`Icon` and the
coordinate-board `CoordGrid`), so the remaining gap is the deos-js authoring *mirror*
(`card_editor::ViewTree`) catching each up node-by-node as a surface needs to emit one;
(3) the apps-launcher is mounted, but only as gpui chrome (the Powerbox panel's
`apps_launcher_section`), not as a card — no `launcher_card.rs` exists. **Recommended first move: delete the gpui trees of the
self-contained carded read-only surfaces (`Objects`, then `Proofs`), completing the
thin-renderer flip — card as the ONLY render — on two surfaces the deos-view vocabulary
already covers without extension.**

---

## 1. Census — the cockpit's gpui-only surfaces

The cockpit is `starbridge-v2/src/cockpit/` (a `Tab` enum of 32 surfaces, `mod.rs:227+`).
The panel renderers are split across `panels_*.rs`. Almost every surface is a hand-built
gpui element tree: `div()` / `v_flex()` / `h_flex()` / `.child()`, button factories
(`verb_button`, `cycle_chip`, `nav_button`, `pill`), `cx.listener()` / `on_click` closures,
and `theme::*()` colors inline. The model objects (e.g. `WonderRoom`, `TrustPanel`,
`TimeCockpitModel`, `OcapGraph`) are mostly gpui-free and do the data work; the gpui coupling
is in the *render* function that walks that data into elements.

### The 32 surfaces, by coupling and complexity

Coupling = how much the render is raw gpui element-tree construction vs. a data/card path.
Complexity = read-only display vs. rich interaction (input state, drag, menus, scrubbers).
"Card today?" = the tab renders its mode-card as the surface in the default (card-pane)
build, gpui panel as fail-soft fallback.

| Surface | File:function (approx) | Coupling | Complexity | Card today? |
|---|---|---|---|---|
| Home | panels_workspace.rs:1175 | high | static prose + pills | **carded** (`ModeCard::Home`) |
| Shell | panels_workspace.rs:1273 | high | layout picker + ops | no |
| Agent | panels_workspace.rs:1640 | high | activity list | **carded** (`ModeCard::Agent`) |
| Buffer | panels_web.rs:1387 | high | text-buffer + commit | no |
| Terminal | panels_web.rs:1540 | high | command rows + run | no |
| Composer | panels_main.rs:346 | high | 7 verb buttons | **carded** (`ModeCard::Composer`) |
| Simulate | panels_main.rs:405 | high | pickers + predicted receipt | no |
| Objects | panels_workspace.rs:2741 | high | pure iteration | **carded** (`ModeCard::Objects`) |
| Debugger | panels_workspace.rs:2663 | high | step list + breakpoints | **carded** (`ModeCard::Debugger`) |
| Replay | panels_workspace.rs:2762 | med (delegates) | scrub history | **carded** (`ModeCard::Replay`) |
| Cipherclerk | panels_workspace.rs:2776 | high | macaroon lifecycle buttons | **carded** (`ModeCard::Cipherclerk`) |
| Editor | panels_web.rs:1678 | high (delegates) | monospace text | no |
| Swarm | panels_workspace.rs:2150 | high | member roster + pills | **carded** (`ModeCard::Swarm`) |
| Organs | panels_workspace.rs:2940 | high | sectioned read-only | **carded** (`ModeCard::Organs`) |
| Graph | panels_workspace.rs:2814 | high | edge-list iteration | **carded** (`ModeCard::Graph`) |
| Proofs | panels_web.rs:10 | high | verification-tier board | **carded** (`ModeCard::Proofs`) |
| WebOfCells | panels_web.rs:98 | high | tier toggle + affordances | **carded** (`ModeCard::WebCells`) |
| WebShell | panels_webshell.rs:619 | high | URL bar + Servo tile | no |
| LinksHere | panels_web.rs:719 | high | backlink list + depth | **carded** (`ModeCard::Links`) |
| Powerbox | panels_web.rs:983 | high | app picker + grant | **carded** (`ModeCard::Powerbox`) |
| Moldable | panels_moldable.rs:227 | med-high | tab-strip + Halo + Spotter | no |
| InspectAct | panels_moldable.rs:697 | high | state rows + affordance buttons | **carded** (`ModeCard::Inspector`) |
| ServiceExplorer | panels_moldable.rs:2187 | high | method list + arg inputs | **carded** (`ModeCard::ServiceExplorer`) |
| ServiceDirectory | panels_service_directory.rs:19 | high | service roster + announce | **carded** (`ModeCard::ServiceDirectory`) |
| Workspace | panels_moldable.rs:840 | high | cycle chips + predict/commit | no |
| Wonder | panels_moldable.rs:1104 | high | glowing-cell grid + hover halos | **carded** (`ModeCard::Wonder`) |
| Lanes | panels_moldable.rs:1108 | high | 4-lane tab-strip + gadgets | no |
| Time | time.rs:147 | high | scrubber drag + suspend/resume | no |
| Share | panels_moldable.rs:1478 | high | frustum cull + attenuation dial | no |
| Docs | docs.rs:123 | high | conflict editor + transclusion | no |
| Trust | panels_moldable.rs:761 | med (model render) | guardian/device list | **carded** (`ModeCard::Trust`) |
| Devtools | panels_devtools.rs:124 | high | sub-tabs + drill-downs | no |

A second desktop shell exists beside the cockpit: `starbridge-v2/src/deos_desktop/`
(the Windows-NT / Pharo workbench). Its `viewnode_pane.rs` is the reflective World-Status
pane — a `deos_view::ViewNode` body painted by deos-view's native renderer and rewritten
live by a confined agent. It is the cleanest existing demonstration of "a desktop window
body IS portable card data." The Halo (`deos_desktop/halo.rs`), right-click menus, and the
Spotter (`deos_desktop/spotter.rs`) live here as gpui chrome — the renderer carries
`Menu`/`Halo` nodes for these actuation surfaces, but no card emits them yet (the
authoring-mirror gap, §2).

### The clean-five vs. the hard-five

**Cleanest (read-mostly, self-contained, expressible in today's vocabulary):**
`Objects`, `Graph`, `Proofs`, `Organs`, `Home`. Pure iteration / badges / sectioned text,
few or zero event handlers, the model is already gpui-free.

**Hardest (rich state, custom interaction the vocabulary cannot express):**
`WebShell` (gpui `InputState` entity + Servo render tile), `Time` (drag scrubber +
suspend/resume lifecycle), `Docs` (conflict inline editor + hypermedia cross-index),
`Lanes` (four intricate gadgets in a tab-strip), `Wonder` (spatial glowing-cell grid +
direct-manipulation halos). `Moldable` is rich but *partly* data-driven already (it dispatches
`render_presentation_body()` generically — adding a Presentable needs no new gpui code).

---

## 2. The portable layer that already exists, and its gap

### What deos-view is

`deos-view/` is the renderer-extraction crate. `deos-js` stays gpui-free and produces a
*serializable* `deos.ui.*` element-tree; `deos-view` holds the two renderers that turn that
DATA into a surface — `native` (gpui-component pixels, `src/render.rs`'s `AppletView`) and
`web` (HTML string, `src/web.rs`). One view-tree, two backends.

The view-tree model (`deos-view/src/tree.rs`, the `ViewNode` enum, always compiled) is the
whole vocabulary:

| node | meaning | native | web |
|---|---|---|---|
| `vstack(...)` | vertical column | `v_flex` | `<div class=deos-vstack>` |
| `row(...)` | horizontal row | `h_flex` | `<div class=deos-row>` |
| `text(s)` | a label | `Label` | `<span class=deos-text>` |
| `bind{slot,label}` | live signal read off the ledger | bold `Label`, re-read | `<span data-slot>` |
| `button{label,turn,arg}` | fires a cap-gated verified turn | `Button` → `applet.fire` | `<button data-turn data-arg>` |
| `input{bind_view}` | ephemeral view-state field (no turn) | bordered field | `deos-input` |
| `list(...)` | vertical list | `v_flex` of children | `deos-list` |
| `table(...)` | table of row-nodes | `v_flex` of children | `deos-table` |

The nodes are mirrored in deos-js's `card_editor::ViewTree` (the gpui-free authoring
mirror — nine variants: `VStack/Row/Text/Bind/Button` plus the richness nodes
`Section`/`Pill`/`Grid`/`Icon`) and produced by the JS prelude
(`deos-js/src/js.rs:430`'s `deos.ui.*`). The wire format is `{kind, props, children}`;
an unknown kind renders as a visible `‹unmapped node: …›` placeholder (honest fallback).
The renderer (`deos-view`'s `ViewNode`) carries the full richness vocabulary already; the
authoring mirror catches up node-by-node as a surface needs to *emit* one (a card builds a
`ViewTree`, so a richer card needs the richer mirror, not just the richer renderer).

**Two load-bearing serialization facts:** a `bind`'s closure is dropped by
`JSON.stringify`, so the author tags the node with `props.slot` (the model slot to re-read);
and a button's `onClick` survives as `{turn, arg}` (camelCase `onClick`, snake alias). The
fine-grained re-render (`deos-view/src/render.rs`'s `BindingRegistry` weld) re-reads ONLY the
binds a committed turn dirtied — the SolidJS-shaped incremental update.

### What it ALREADY expresses well

The 8-node vocabulary cleanly covers any surface that is **a titled column of labeled rows,
some bound to live state, with buttons that fire turns**. That is precisely the clean-five
(`Objects`, `Graph`, `Proofs`, `Organs`, `Home`) and the bulk of the carded set (19 tabs at
HEAD, the census column above). The `inspector_card`
proves the richest read-case: RawFields → live `Bind` rows, Affordances → cap-gated `Button`s.
`props.tag` is already used as a styling escape hatch (e.g. `first-room`'s `tag:"genuine"` /
`tag:"refusal"` rows render with distinct CSS).

### The richer nodes (now IN the renderer; the mirror catches up)

The richness vocabulary below is BUILT into the deos-view *renderer*
(`deos-view/src/tree.rs`: `Section`, `Tabs`, `Gauge`, `Grid`, `Menu`, `Halo`, `Slider`, plus
`Pill`, `Icon`, and the coordinate-board `CoordGrid` — each with a native gpui walker and a
web HTML walker). The gap is not "the renderer can't
express these"; it is "the deos-js authoring *mirror* (`card_editor::ViewTree`) emits each one
node-by-node as a surface needs it." The list documents each node's shape and which surfaces
consume it:

1. **Tab-strip / sub-tabs** — `Lanes` (4 lanes), `Devtools` (3 sub-tabs), `Moldable`
   (one sub-tab per Presentation). Needs a `tabs{selected_slot}` container whose visible
   child is bound to a model slot, the tab buttons firing a `select` turn.
2. **The right-click actuation menu** — the `deos_desktop` context menu. Needs a
   `menu{items:[{label, turn, arg, enabled}]}` node (a list of affordances, lit/dim by the
   cap tooth — `enabled` is `is_attenuation(held, required)`).
3. **The Pharo Halo** — direct-manipulation handles floating on a selected object
   (`deos_desktop/halo.rs`). Needs a `halo{handles:[{glyph, turn}]}` overlay node anchored to
   a target; each handle fires the same actuation the menu would.
4. **Scrubber / slider** — `Time`'s rewind scrubber, `Replay`. Needs a `slider{slot, min,
   max, turn}` whose drag fires a `seek` turn (re-derive at a past height).
5. **Spatial grid** — `Wonder`'s glowing-cell grid, the desktop icon field. The mirror
   carries `Grid{cols}` + `Icon` (`card_editor::ViewTree`), and the Wonder card emits both
   today (`wonder_view` builds a 4-column grid of icon tiles) — this leg of the mirror is
   closed. A freeform `canvas` with per-child `x,y` (persisted positions) remains absent.
6. **Gauge / progress / pill** — a styled status indicator (glow = activity, a balance bar).
   `props.tag` covers simple cases; a first-class `gauge{slot, max}` is cleaner.
7. **Input with a live model binding** — `input` today binds only *ephemeral* view-state.
   `ServiceExplorer` arg rows, `WebShell` URL bar, the predicate composer want a text input
   whose value feeds a turn `arg`. Needs `input` to optionally carry the arg into a button's
   fire (`{bind_view}` → a button reads it as its arg).
8. **Styled section** — a titled, bordered container with a header. Cheap to fake with
   `vstack(text(title), …)`; a `section{title}` node makes disclosure + theming uniform.

These nodes each already ship BOTH a native (gpui) and a web (HTML) walker in `tree.rs`,
exactly as the original 8 do — renderer-independent by construction. None required a
kernel/circuit change — a card is *data*, the affordances are the same turns. What remains is
the authoring-mirror side: a card *builds* a `card_editor::ViewTree`, so a surface that needs
to EMIT (say) a `tabs` node needs the mirror to grow that constructor, not the renderer. The
first migrations (clean-five) need NONE of these; the mirror extension is staged behind the
surfaces that need it.

---

## 3. The reflective-cockpit prior art (RUNG 1+) — extend, don't reinvent

The "reflective cockpit" thread is already three rungs deep. Do not rebuild it.

- **RUNG 1** (`0c3e567b5`) — a confined agent reflects on a REAL cockpit surface and
  rewrites it live. `deos.editor.view()` reads the live surface's own view-tree;
  `deos.editor.editView(card, patch)` applies one structural patch as a *receipted turn with
  blame*; the re-folded tree paints through the SAME native renderer (and the IDENTICAL tree
  renders to HTML — renderer-independence). Proof:
  `deos-view/tests/agent_reflects_and_rewrites_a_surface_live.rs`.
- **RUNG 2** (`b18447aa7`) — lifts the loop into the shipped desktop window
  (`starbridge-v2/src/deos_desktop/viewnode_pane.rs`): the World-Status pane IS a
  `deos_view::ViewNode` body, and the agent's rewrite swaps the re-folded tree into the SAME
  live `AppletView` entity (`AppletView::set_tree`), so the real window repaints the rewrite.
- **RUNG 3** (`layout_card`) — the cockpit's *structure itself* (its mode→surface
  arrangement, formerly hardcoded `CockpitMode::surfaces()`) becomes editable card data
  (`deos-js/src/layout_card.rs`), mounted via `ensure_layout_card` (`cockpit/frame.rs:196`).
  The cockpit reads this layout cell to render the rail instead of compiled Rust.
- **The mode-card mount** (`dock/card_surface.rs`) — twenty `ModeCard` arms at HEAD
  (`composer / objects / graph / dynamics / agent / links / proofs / organs / home /
  inspector / service-directory / web-cells / trust / wonder / cipherclerk / debugger /
  replay / swarm / service-explorer / powerbox`) and a live-World bridge that hosts them as
  cockpit surfaces; 19 of them ARE a tab's default render (`Dynamics` mounts in the dock).

The pattern RUNG 1 established and the mode-card mount generalized: **a cockpit surface is a
card cell whose view is a `ViewTree` document, generated from live reflective state, painted
by deos-view, editable from within as receipted patches.** The view-builders live in two
homes: twelve in `deos-js/src/*_card.rs` (agent / coauthored / composer / dynamics / graph /
home / inspector / layout / links / objects / organs / proofs) and the rest directly in
`starbridge-v2/src/dock/card_surface.rs` (`wonder_view`, `trust_view`, and the
service-directory / web-cells / cipherclerk / debugger / replay / swarm builders in its
dispatch); a new surface adds one view-builder and one `ModeCard` arm.

---

## 4. The surface → card pattern (the source of truth flips)

### Two flavors of card, one renderer

1. **Static authored card** (the AX4 apps, `starbridge-apps/*/src/card.rs`). A pure
   `serde_json::Value` `{kind, props, children}` tree built once — a fixed layout of
   `text` / `bind(slot)` / `button(turn, arg)`. No gpui dependency at all. This is the
   proven *portable* pattern: e.g. `bounty-board` is a vstack of a title, a state `bind`, and
   four affordance buttons (`post/claim/submit/payout`).
2. **Reflective generated card** (the cockpit cards — view-builders in
   `deos-js/src/*_card.rs` and in `dock/card_surface.rs` itself, §3). A Rust *view-builder*
   reads the live ledger and emits the `ViewTree` (e.g. `objects_card::objects_view(ledger)`
   = one row per cell + an `inspect` button). The view is held as an editable
   `ProgramSource` document so an edit-from-within is a receipted patch. One carded surface
   is not live-backed: the Trust card's substance is `TrustPanel::demo()` — a fixture
   (a representative identity until an on-ledger identity cell is wired), not the ledger.

Both produce the SAME `{kind, props, children}` data the SAME renderer paints. The cockpit
surfaces are flavor 2 (they reflect live state); the launchable apps are flavor 1.

### The live mount — already built

`dock/card_surface.rs::build_mode_card_surface` is the keystone weld:

1. **Generate** the view-tree in Rust from the live `World` (`ModeCard::view_tree`).
2. **Attach** an applet to the live cockpit `World` (`WorldSinkAdapter::live`) focused on a
   cell — the card's substance is the operator's REAL cell, bounded by `held`.
3. **Bridge** the `ViewTree` JSON → `deos_view::ViewNode` (`parse_view_tree`).
4. **Host** it in a `CardPane` gpui entity — a `bind` re-reads the operator's real cell each
   frame, a button's `on_click` fires ONE cap-gated verified turn through
   `World::commit_turn` (inheriting light-client unfoolability).
5. **Adopt** the view as a `CardEditor` document so `ModeCardSurface::edit_view(patch, cx)`
   re-folds the view + `set_tree`s the `CardPane` — reshape-from-within, a receipted patch
   with blame, not a recompile.

This is the keystone, and it is deployed: `card-pane` is folded into the default `desktop`
feature, and the `Tab` dispatch renders the mode-card as the surface for every carded tab.
The button-click → real-turn routing is solved: the affordance name IS the turn method; the
cap tooth (`is_attenuation(held, required)`) runs in-band before the executor.

### The flip: card-as-sole-definition

The card is the **default render** for the 19 carded tabs; what is NOT done is making it the
sole **definition**. Every carded surface still keeps its gpui render function as the
fail-soft fallback + the card-pane-off home, so the render logic is duplicated. The
liberation is: for a migrated surface, **delete the gpui render function and make the card
the only render.** The surface's "definition" becomes its `*_card.rs` view-builder; gpui
`AppletView`/`CardPane` is the dumb painter. This is the concrete meaning of "starbridge-v2
is a thin renderer."

Sequencing note: `card-pane` pulls multi-GB mozjs and the lean/headless builds keep it off —
which is exactly why the gpui fallbacks still exist. Deleting a surface's gpui tree therefore
needs a minimal gpui-free static fallback (the AX4 flavor, a serde_json card with no live
bind) for the card-pane-off build. The reflective generated cards do not need mozjs to
*render* (the view-builder is pure Rust + `parse_view_tree`); only agent *rewrite* reaches
SpiderMonkey.

---

## 5. The migration ladder (cleanest first)

The pattern is proven and 19 tabs render card-as-default; the ladder is about (a) deleting
the duplicate gpui trees so the card is the sole definition and (b) extending card coverage
to the remaining gpui-only surfaces, easiest vocabulary-fit first.

**Rung A — delete one carded surface's gpui tree (the thin-renderer completion).**
- **`Objects`** is the cleanest first move. `ModeCard::Objects` + `objects_card.rs` (live
  roster → rows + `inspect` buttons) + edit-from-within render as the surface today. The
  move: delete its gpui tree in `panels_workspace.rs:2741` (and give the card-pane-off build
  a static fallback). Self-contained (no input state, no menus), and it proves the
  load-bearing claim — *the surface is defined by its card, gpui only paints* — on a real
  surface end-to-end. **Recommended FIRST.**

**Rung B — delete the remaining read-only surfaces' trees (their cards render today).**
- **`Proofs`** (`panels_web.rs:10`) — a verification-tier board, pure read-only badges +
  receipt rows; `deos-js/src/proofs_card.rs` is the default render. **Recommended companion
  to Rung A.**
- **`Organs`** (`panels_workspace.rs:2940`) — sectioned read-only organ cell-state;
  `deos-js/src/organs_card.rs` uses the renderer's `Section`.
- **`Home`** (`panels_workspace.rs:1175`) — static prose + liveness pills; `LandingPortal`
  is gpui-free and `deos-js/src/home_card.rs` is the default render.

**Rung C — card the moderate-interaction gpui-only surfaces.**
- **`Simulate` / `Workspace`** — pickers (cycle chips) + a predicted-receipt readout; need
  the `tabs`/`select` node for the effect-palette cycle and `input` carrying a turn arg.
- **`Shell`** — layout picker + ops; `section` + buttons.
- The carded rosters (`Swarm`, `Trust`, `Cipherclerk`, `ServiceExplorer`) sit here for
  tree-deletion once their write-affordances (the genuine crypto / announce / invoke turns
  that today live only in the gpui fallback) are expressed as card buttons — `input`→arg
  binding for `ServiceExplorer`.

**Rung D — the rich surfaces (drive the authoring-mirror extension §2).**
- **`Lanes`**, **`Devtools`**, **`Moldable`** — need the mirror to emit `tabs`.
- **`Time`** — needs `slider`/scrubber (the `Replay` card exists; its scrub affordance wants
  the same node).
- The desktop icon field — freeform `canvas` + `halo` (the `Wonder` card emits the
  mirror's `Grid`/`Icon` today; its drag-value grab/drop turn stays in the gpui room).
- **`Buffer` / `Terminal` / `Editor`** — text-input surfaces; need `input` carrying turn args.
- **`WebShell`** — needs an embedded native render tile (Servo) the card references by handle;
  the URL bar is an `input`. This is the genuine ceiling — a card referencing an opaque
  native paint region. Park until the rest lands.
- **`Docs`** — the conflict editor is a load-bearing dregg-doc seam; migrate last, with care.

The right-click actuation menu and the Halo (Rung D's `menu` + `halo` nodes) are the
highest-leverage extensions because they are the cross-surface *actuation* primitive — once
expressed as card nodes, every carded surface gets uniform direct-manipulation for free.

---

## 6. Progressive disclosure and delight — where it lives

The delight requirement (a 1999-AOL 4-year-old clicks around with wonder; an adept inspects
and molds it live) lives in the **card layer**, specifically two mechanisms, neither of
which forks the source of truth:

1. **A disclosure level per render, not per card — built and wired.** A node authored with
   `props.adept: true` (`card_editor`'s section flag) lifts into `ViewNode::Adept`, and
   `deos_view::disclose` (`deos-view/src/tree.rs`) is a pure pre-walk run BEFORE any
   renderer walk: `Disclosure::Simple` DROPS adept-marked subtrees — raw hex cell ids,
   slot/field indices, receipt hashes — showing the friendly label + the live value + the
   buttons; `Disclosure::Adept` UNWRAPS them (the Pharo "see the bones" mode). One card,
   two projections — and because the pre-walk runs before `bind_plan`'s cursor walk, both
   projections keep self-consistent bind cursors in every renderer identically. The card
   mount applies `disclose(&tree, Disclosure::Simple)` on every build
   (`starbridge-v2/src/card_pane.rs`), and the web pipeline threads `req.disclosure`
   (`deos-view/src/pipeline.rs`).
2. **Friendly-by-default labels.** The view-builders already prefer `short_hex` + a human
   label over raw bytes (`objects_card` rows are `"{short} · bal {n}"`, not a 32-byte id).
   Make this a convention: a `bind`/`text` carries a human `label`; the hex/slot is an
   `adept`-tagged sibling, hidden at the simple level. Progressive disclosure is then "show
   the adept siblings," not a different card.

Because disclosure is a pre-walk projection over one card, it is renderer-independent (web
and gpui paint the same disclosed tree), it survives agent rewrite (a patch adds an `adept` node; both
levels stay coherent), and it keeps the card the single source of truth. Delight is the
*default projection*; moldability is the *adept projection*; both are the same object.

---

## 7. The apps-launcher as a card

`RegistryLauncher` (`starbridge-v2/src/powerbox.rs:471`) is built, tested, and mounted as
gpui chrome: the Powerbox panel renders its `rows()` as launch buttons
(`cockpit/panels_app_launcher.rs::apps_launcher_section`, mounted from the Powerbox render
in `panels_web.rs`), and a launch drives `RegistryLauncher::launch_on_world` — seeding the
app's cell + committing a verified turn on the cockpit's live `World`. It wraps the
`AppRegistry` of wired starbridge-apps (`bounty-board`, `gallery`, `kvstore`, `identity`,
`nameservice`, `first-room`, `polis`, …), exposing `rows()` (one `AppLaunchRow` per app)
and `launch(id)`, and the launcher data itself is gpui-free. What it is NOT is a card (no
`launcher_card.rs` exists) — the mount is a hand-built gpui section, exactly the coupling
this plan removes. It should surface as a **launcher card**, tying the apps-in-desktop
milestone to the liberation:

1. **A launcher card** — a new `launcher_card.rs` (reflective flavor): a vstack with a title
   and one `button` per `RegistryLauncher::rows()` entry, the button's affordance
   `launch:<app-id>` (arg unused). Pure today-vocabulary; trivial.
2. **The launch router** — the cockpit's actuation dispatch (where button turns route)
   intercepts a `launch:<app-id>` turn: instead of firing on a cell, it mounts that app's
   card as a new `ModeCardSurface`/`CardPane` window. Each app already ships its AX4
   `card.rs` (the static flavor) — so opening an app mounts ITS card, painted by the SAME
   renderer.
3. **The uniform payoff** — the launcher is a card, every app IS a card, the cockpit shell is
   the renderer that paints whichever card is mounted. The desktop becomes "a launcher card
   that opens app cards," not a fixed set of compiled tabs. This is the same source-of-truth
   flip as §4, applied to the app boundary: `RegistryLauncher::launch(id)` (which mints the
   confined app-cell + a standing `CapabilityRequest`) stays the trusted designation flow;
   the powerbox grant is itself a card surface.

The launcher card is the natural next brand-new card: it is read-only + buttons (no
vocabulary gap), and it lights up the apps-in-desktop milestone directly.

---

## 8. Summary — what to build, in order

1. **Delete the `Objects` gpui tree** (Rung A): `objects_card` renders the surface today;
   make it the ONLY render. Proves "starbridge-v2 is a thin renderer" on one self-contained
   surface, end-to-end (card defines it, gpui paints it, buttons fire real turns,
   edit-from-within reshapes it).
2. **Delete the `Proofs` tree** (Rung B) + **stand up the launcher card** (§7, still
   greenfield — no `launcher_card.rs` exists): complete a second flip and light the
   apps-in-desktop milestone — both fit today's vocabulary.
3. **Grow the authoring mirror** to emit the richer nodes (§2) as the surfaces that need them
   arrive — the renderer has `section`/`tabs`/`menu`/`halo`/`slider`/`grid`, and the mirror
   already carries `section`/`pill`/`grid`/`icon`; the remaining `card_editor::ViewTree`
   constructors: `tabs`/`menu`/`halo` (the actuation primitives, highest leverage) →
   `slider`.
4. **Walk the ladder** (Rungs C, D): card the remaining gpui-only surfaces, then the rich
   ones, `WebShell` and `Docs` last.

The liberation is not greenfield: the mount bridge, the renderer, the disclosure layer, the
edit-from-within loop, and twenty mode-cards exist, and 19 tabs render card-as-default. The
work is (a) deleting the duplicate gpui trees so the card is the sole definition, surface by
surface, (b) the authoring-mirror extensions the rich surfaces need, and (c) the
launcher-as-card that makes the desktop a renderer of cards.
