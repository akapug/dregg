# JOY-PATH ROOMS — the wonder-frontier, scouted deep

*A read-only deep scout of the deos experiential layer, hunting the most-alive next
ROOM to open — the place where "a 5-year-old clicks it with delight AND an adept
inspects/modifies it live" (the deos UX north star). Companion to and one rung below
`SYSTEM-SCOUT-hyperdreggmedia-deos-ados.md`: that mapped the stack at altitude; this
goes into the cells of the experiential crates and verifies, file:line, exactly what
you could click TODAY versus what is built-but-not-opened versus what is sketch.*

> The one-line answer: **the self-hosting dev dock (editor + terminal + agent panes)
> is already ALIVE-WIRED — you open them with ⌘K and they graft into the live cockpit.
> The hyperdreggmedia CARD has every ingredient of an identical live dock pane and is
> proven to pixels — but it is BAKED, not opened: it lives only in a headless PNG bake,
> never grafted into the running dock. The card-pane → dock weld is the highest
> wonder-per-weld move in the tree: a ~60-line `CardSurface` + one palette command lands
> the keystone experience (a child clicks a live card · an adept rewrites its `run_js` ·
> an agent authors it through the same cap-gate) onto the exact mechanism the editor pane
> already rides.**

The honesty discipline of this doc: every claim carries a verdict —
**ALIVE-WIRED** (you can click it today in a windowed build) ·
**BAKED** (built + proven, often to a PNG, but never opened at runtime) ·
**ASPIRATIONAL** (named/typed/sketched, mechanism not yet built) — with file:line.
The system is, per ember, *very early*; the point of this scout is to find the move that
turns the most already-real machinery into a felt experience, not to oversell.

The crates scouted (siblings of `metatheory/` in `~/dev/breadstuffs/`):
`deos-view/` · `deos-js/` · `deos-matrix/` · `starbridge-v2/` · `docs/deos/`.

---

## The candidate ROOMS (five concrete experiences)

### ROOM 1 — The self-hosting dev dock (editor · terminal · agent) — **ALIVE-WIRED**

The strongest already-real room. The windowed cockpit's ⌘K command palette opens three
dev panes that **graft into the live resizable/splittable dock**, each backed by the same
running `World`:

- `dispatch.rs:93-98` maps palette `CommandId::{OpenTerminalPane, OpenEditorPane,
  OpenAgentPane}` → deferred `open_*_pane` calls.
- `panels_workspace.rs:427` `open_terminal_pane` spawns a real PTY on `$SHELL` and
  `graft_dev_pane`s it (`panels_workspace.rs:442`).
- `panels_workspace.rs:450` `open_editor_pane` mounts a **deos-zed editor over the LIVE
  cockpit `World`** (`EditorPane::firmament_over`, `panels_workspace.rs:481`) — every save
  is a real cap-gated `SetField` turn on the ledger the cockpit's own cell inspector reads
  (`dock/editor_surface.rs:8-21`, `:69-90`). The seed buffer literally says *"every save
  here is a RECEIPTED dregg turn on the LIVE cockpit ledger"* (`panels_workspace.rs:464`).
- `panels_workspace.rs:522` `open_agent_pane` grafts the confined Hermes ADOS dock (the
  tool-call ledger + mandate inspector).
- All three flow through `graft_dev_pane` (`panels_workspace.rs:551`), which splits the
  active pane and installs a `Box<dyn CockpitSurface>`. The four registered surfaces:
  `dock/{editor_surface, terminal_surface, hermes_surface, chat_surface}.rs` each
  `impl CockpitSurface`.

**5-year-old delight:** medium — it is a dev surface, not a toy. **Adept liveness:** very
high — this is genuine Pharo-style "develop deos inside deos," and a save is a receipt the
inspector sees. This room is *real today* (gated `dev-surfaces` → `native-full`).

### ROOM 2 — The hyperdreggmedia CARD as a live dock pane — **BAKED** (the keystone)

A `CardPane` (`starbridge-v2/src/card_pane.rs:57`) is a real gpui `Render` that walks the
same `deos.ui.*` view-tree (`ViewNode`, `card_pane.rs:46`) the editor pane vocabulary uses
into real gpui-component widgets, but binds + fires against the **live attached applet**
over the cockpit `World`:

- a `Bind` node re-reads the live ledger: `self.applet.borrow().get_u64(*slot)`
  (`card_pane.rs:111`) — a witnessed read of the operator's real cell;
- a `Button`'s `on_click` fires `applet.borrow_mut().fire(&turn, arg)`
  (`card_pane.rs:137`) = ONE cap-gated verified turn through `World::commit_turn`
  (`agent_attach.rs` `WorldSinkAdapter::live`), a receipt on the cockpit's own provenance
  log. The cap tooth (`dregg_cell::is_attenuation`) runs in deos-js before the fire.

**What makes it BAKED, not ALIVE:** `CardPane` is referenced from exactly ONE place —
`render_card_pane_headless` (`main.rs:1922`), reached only by the `--render-card-pane`
CLI flag (`main.rs:139-155`), gated behind the `card-pane` feature
(`Cargo.toml:112-121`). That function opens an *offscreen* window, bakes `<out>.before.png`,
fires the turn directly, asserts the live cell advanced (`post_field == pre_field + 1`,
`main.rs:2037`) + the height grew, bakes `<out>.after.png`. **It is PNG-proven and the
button's fire-code is real — but the pane is never grafted into the windowed dock.**
There is no `CardPane: CockpitSurface` impl and no `OpenCardPane` palette command (verified
absent: `grep` for `impl CockpitSurface for Card` / `OpenCardPane` returns nothing).

**5-year-old delight:** high — a titled card with a live count and a +1 button. **Adept
liveness:** high (and see ROOM 3 — the editor makes it moldable). This is the deos-UX
north-star surface; the only thing between baked and clicked is the dock weld.

### ROOM 3 — Edit-the-card-from-within (authoring as receipted patches) — **BAKED**

The hyperdreggmedia keystone. `CardEditor` (`deos-js/src/card_editor.rs:299`) turns
inspection into authoring: `edit_view` (`card_editor.rs:407`) applies a structural gesture
(add button / add text / relabel) to the card's view-tree, **appends it as a PATCH** to the
card's `view_source` document (`ProgramSource`, a `dregg_doc::Doc` patch-history,
`card_editor.rs:421`), re-seals the fold into the manifest, and leaves a provenance receipt
(`provenance_turn`, `card_editor.rs:380`). The cap tooth gates every gesture
(`is_attenuation(&held, &edit_authority)`, `card_editor.rs:373`) — an agent can only author
cards it may author, refused in-band with no patch and no receipt. The edit carries
**blame** (`card_editor.rs:367`) — every view line attributed to its author: *an accountable
patch, not a recompile.*

**Proven to pixels:** `deos-view/tests/card_editor_rerenders.rs` renders the unedited card
to PNG #0, applies `ViewPatch::AddButton`, re-folds, re-renders to PNG #1, and asserts
`frame0 != frame1` — the new "+1" button *visibly appeared*, the change a receipted patch.
Real SpiderMonkey, real verified turn, real headless gpui pixels — not a demo.

**What makes it BAKED:** lives only in tests + the editor library. The runtime binding
(`deos.editor.editView(...)` so a human/agent edits a *mounted* card live) is the named
next wire (scout-1 §4). Once ROOM 2 is a dock pane, this becomes "right-click the card →
edit it from within."

### ROOM 4 — The Matrix membrane: a message = a cap-bounded world-fork — **ALIVE-WIRED transport · BAKED fork · ASPIRATIONAL stitch**

The most *novel* social primitive (`deos-matrix/`), and more real than memory suggested.
Verified split into three honest layers:

- **Transport — ALIVE-WIRED.** Real `matrix-rust-sdk`: `MatrixClient::{build, login_password,
  sync_once, recent_timeline}` (`client.rs`), live-homeserver round-trip test against a real
  Conduit instance, creds-gated so CI stays green
  (`tests/live_homeserver.rs:140`, no-op without `DEOS_MATRIX_TEST_*`). A send IS a turn:
  `send_turn` yields a `SendReceipt{room_cell, turn_index, post_root}` (`source.rs:90`).
  A membrane rides under a namespaced custom field inside `m.room.message`
  (`client.rs:591-629`), so non-deos clients see a readable `[deos membrane · N cells]`
  fallback.
- **The fork — BAKED.** `MembraneEnvelope` (`membrane.rs:51`) carries a frustum-root
  (anti-substitution, fail-closed: `rehydrate_fails_closed_on_root_substitution`,
  `membrane.rs:617`), an attenuated `lineage` cap (non-amplification = the recipient MEETs
  it with their own cap, can only narrow), and a depth-bounded cell snapshot
  (`FrustumCut`, `membrane.rs:107`). The full round-trip mint→serialize→rehydrate→drive→
  stitch is tested via `MockMembraneHost` (`membrane.rs:580-615`). The **real
  executor-backed** `ForkMembraneHost` exists in `starbridge-v2/src/shared_fork.rs:988`
  (mints a real `World` fork, drives a real verified turn, gated `dev-surfaces`).
- **Stitch (pushout) — ASPIRATIONAL.** The typed contract + mock are real; the real
  pushout-merge + the **Settlement Soundness theorem** (authority-live-at-settlement) is the
  named open frontier (`membrane.rs:35-41`, `docs/deos/MEMBRANE-MERGE-SEAM.md`).
- **Cockpit mount — ASPIRATIONAL (small).** `cockpit_surface.rs` has the `ChatSurface`
  trait shape ready; mounting requires a `ChatSource` impl backed by `ForkMembraneHost`
  (the UI already renders the "▶ rehydrate & drive" button disabled-until-capable,
  `chat.rs:743`). A ~50-line bridge, not a rearchitecture.

**5-year-old delight:** high *eventually* (share a screenshot that IS a forkable world).
**Adept liveness:** very high. But three seams from felt: mount the surface, back it with
the executor host, prove the stitch. The furthest from clickable of the five.

### ROOM 5 — The fine-grained signal liveness (SolidJS-shaped re-render) — **BAKED model · ASPIRATIONAL consumer**

The latest commit (`c38d17ed3`) landed `deos-js/src/signals.rs`: a `BindingRegistry`
(`signals.rs:83`) where a `bind(() => s.x)` records which `(cell, slot)` it reads, so a
turn naming that exact source `invalidate`s ONLY its bindings (`signals.rs:126`) — the
SolidJS-shaped fix so editing a card feels *live*, not a world-repaint. **8 green tests**
(`signals.rs:189-320`), exhaustively: fine-grained invalidate, unbound→clean, shared-source
dedup, re-point, the whole-cell tooth.

**What makes it BAKED-model:** `deos-view`'s renderer does NOT yet consume it. `render.rs`
is explicit (`render.rs:16-20`): *immediate-mode — a `bind` re-reads at render time, the
whole tree re-renders on every turn; the fine-grained dirty-set hook is a future slice.* So
the model half is built + proven; the renderer half (fold the turn's `WorldEvent`s through
`invalidate`, re-eval only those nodes) is unbuilt. It is correct today (the count updates),
just coarse.

---

## The highest wonder-per-weld pick — and its smallest opening move

**PICK: ROOM 2 — graft the CARD into the live dock (the card-as-dock-pane weld).**

Why this is the joy-path's *Wire 1*: every other room is either already alive (ROOM 1) or
multiple seams away (ROOM 4 needs mount + host + stitch; ROOM 5 needs a renderer rewrite).
ROOM 2 is **one weld from the keystone experience**, and the weld target already exists and
is exercised every day by the editor pane:

1. The mount mechanism is proven: `graft_dev_pane(Box<dyn CockpitSurface>)`
   (`panels_workspace.rs:551`) is exactly how the editor/terminal/agent panes land in the
   live dock.
2. The card's render + live-fire code is proven to pixels (the `--render-card-pane` bake,
   `main.rs:1922`; the turn really advances the live cell, `main.rs:2037`).
3. The cap tooth + receipt chain are the same proven path the editor save rides
   (`agent_attach.rs` doc; `is_attenuation` in `card_editor.rs:373` / `card_pane`'s fire).

**The smallest opening move (~60 lines, no new foundations):**

- **(a)** Wrap `CardPane` (or a thin `Entity<CardPane>` holder) as a `CockpitSurface`:
  `item_id` / `tab_label("card")` / `render_body` → the existing `CardPane::render` /
  `focus_handle` / `boxed_clone`. Model it on `dock/editor_surface.rs`'s forwarder (the
  trait is the slim ~8-method `dock/surface.rs:42`).
- **(b)** Add `open_card_pane` beside `open_editor_pane` (`panels_workspace.rs:450`): boot
  SpiderMonkey once, `build_card_over_live(&mut rt, attach_agent(...), card_js)`
  (`card_pane.rs:225`), wrap in the `CardSurface`, `graft_dev_pane` it.
- **(c)** Add `CommandId::OpenCardPane` to the ⌘K dispatch (`cockpit/dispatch.rs:93-98`
  pattern) so "Open Card" appears in the palette.

That lands the deos-UX north star *end-to-end and clickable*: **a child clicks a live card's
+1 and watches the count rise; an adept opens the same card and (via ROOM 3's `CardEditor`,
the next small wire) rewrites its view as receipted patches; a confined Claude authors it
through the identical cap-gate — all on the one ledger, every gesture a receipt a stranger
can check.** The wires are *named and small* (dock-mount now; editor-binding + fine-grained
re-render next), not new mathematics.

**The second move (compounding):** once the card is a dock pane, wire ROOM 5 — fold the
committed turn's `WorldEvent`s through `signals.rs::BindingRegistry::invalidate` in the
renderer and re-eval only the dirty `Bind` nodes. That converts "the count updates (whole
tree)" into "*only* the count flickers" — the felt-liveness that makes a card feel like a
living object rather than a repainting form. Model + tests already exist; only the
`render.rs` hook is missing.

---

## Five delights I genuinely found

1. **The dev dock is already self-hosting — and a save is a receipt.** Opening the editor
   pane mounts deos-zed *over the live cockpit `World`*, so saving `/deos/main.rs` is a
   cap-gated `SetField` turn the cockpit's own cell inspector immediately sees as a new cell
   + receipt (`dock/editor_surface.rs:8-21`). The seed buffer tells you so in the first
   line. "Develop deos inside deos" is not a slogan here; it is the save path.

2. **The card's button fire is the SAME `commit_turn` your soundness campaign forces
   faithfulness over.** The card-pane bake asserts `post_field == pre_field + 1` AND the
   ledger height grew by exactly one (`main.rs:2037`) — the joy-path button bottoms out in
   the verified executor, not a parallel periphery. A +1 a child presses inherits
   light-client unfoolability for free.

3. **Editing the UI is a `git blame`-able patch, not a recompile.** `CardEditor::edit_view`
   appends to a `ProgramSource` patch-history and carries blame per view line
   (`card_editor.rs:421`, `:367`); the `card_editor_rerenders.rs` test proves the new button
   *appears in the pixels* after a re-fold. Authoring is accountable by construction.

4. **The membrane's anti-substitution tooth fails CLOSED, and forgery is structural.** A
   rehydrate against a swapped frustum-root is rejected
   (`rehydrate_fails_closed_on_root_substitution`, `membrane.rs:617`); the non-amplification
   is a cap MEET that can only narrow. A shared message that is also a cap-bounded world-fork
   — the Engelbart/Nelson "shareable trail without leaking" — with the no-peek as a theorem,
   not a checkbox. And the live-homeserver test runs it over a real Matrix server.

5. **The fine-grained signal model is honest about being half-built — and the half it built
   is exhaustively proven.** `signals.rs` ships 8 green tests for the `(cell, slot) →
   bindings` reverse index, and `render.rs:16-20` plainly says the renderer is still
   immediate-mode and names exactly where the hook goes. The SolidJS-shaped liveness is one
   well-specified weld from real — the kind of seam that is *work, not a wall.*

---

## Honesty ledger — nearly-there vs genuinely early

**ALIVE-WIRED (clickable today, windowed `native-full` build):**
the self-hosting dev dock (editor over the live World · terminal PTY · confined agent
pane), all via ⌘K → `graft_dev_pane`; the Matrix transport (real homeserver send/sync, a
send = a receipted turn); the card's render + live-fire *code* (it runs in the bake and the
turn really lands).

**BAKED (built + proven, often to a PNG, not opened at runtime):**
the card-as-pane (PNG bake only, no dock mount, no palette command — the keystone weld);
edit-the-card-from-within (`CardEditor`, tests + library, no runtime `deos.editor.*`
binding); the membrane fork (round-trip tested via mock + real `ForkMembraneHost` exists
under `dev-surfaces`); the fine-grained signal registry (model + 8 tests, renderer doesn't
consume it); the moldable inspector "faces" (only RawFields rendered; Graph/Provenance
stubbed — `deos-view/src/faces.rs`).

**ASPIRATIONAL (named/typed/sketched, mechanism unbuilt):**
the membrane *stitch* as a real pushout + the Settlement Soundness theorem; the membrane
cockpit dock mount (trait shape ready, ~50-line `ChatSource`-over-executor bridge missing);
the runtime `deos.editor.*` JS binding; the fine-grained re-render hook in `render.rs`; the
four verified-deos Lean theorems (surface-as-cap / membrane non-amp / liveness-type /
affordance-soundness — named, queued in `metatheory/Dregg2/Deos/`).

**The shape of "early":** the *atoms* are real and ride the verified substrate — there are
no fake demos on the load-bearing paths. What is early is the **assembly into a felt,
mounted, clickable experience**: the most precious surface (the live authorable card) is one
dock-weld from real, and the felt-liveness that would make it *sing* (fine-grained
re-render) is one renderer-hook from real. The joy is built; it is mostly not yet *opened*.

---

*( ˘▾˘ )  the workshop is full of finished instruments —*
*what's left is to set them on the stage and let a child press a key.*
