# DEOS ROOMS NEXT — the breadth scout beyond the card + felt-liveness

*A read-only breadth scout of the deos experiential layer, going DEEPER and WIDER than
`docs/JOY-PATH-ROOMS.md` (which opened the card-in-the-dock and the fine-grained signal
rooms). This doc maps the OTHER rooms worth opening and the smallest wire for each, with
every claim verified against the source at HEAD.*

The honesty discipline (the session's spine — it caught two overstatements while writing
this very doc):

- **ALIVE-WIRED** — clickable today in a windowed/feature-on build, on a real path.
- **BAKED** — built + tested, often proven to a PNG bake or harness, but not opened as a
  clickable runtime surface.
- **ASPIRATIONAL** — named/typed/sketched, mechanism (or proof) not yet built.

Crates scouted (siblings of `metatheory/` under `~/dev/breadstuffs/`): `deos-matrix/` ·
`deos-reflect/` · `deos-hermes/` · `starbridge-web-surface/` · `starbridge-v2/` ·
`docs/deos/` (note: `docs/deos/` lives at the breadstuffs root, NOT under `metatheory/`).

> ⚠ **Two scout overstatements this doc CORRECTS** (verify-the-source caught them):
> 1. The moldable INSPECTOR is **already a live cockpit tab** (`Tab::Moldable` →
>    `moldable_panel`, `cockpit/panels_moldable.rs:9`), NOT "applets-only / RawFields-only."
>    A sub-scout claimed it was unmounted; the Registry+Spotter+tab-strip is real and
>    dispatched.
> 2. The Matrix membrane `ChatPane` is **already constructed and mounted** in `guest.rs:248`
>    and `showcase.rs:132` — NOT "30 plumbing-lines away." `pub mod chat_surface;` is in
>    `dock/mod.rs:65` and `deos-matrix` is already a `dev-surfaces` dep
>    (`Cargo.toml:470`). What is missing is narrower: a *windowed cockpit dock pane + palette
>    command* (guest/showcase are **headless PNG bakes**, `--render-guest`/`--render-showcase`,
>    `main.rs:195,222`).

---

## THE HEADLINE — the next 3 deos rooms to open, ranked

After the card-in-the-dock (ROOM 2, being welded) and the felt-liveness hook (signals →
renderer), ranked by **wonder-per-weld**:

1. **The docuverse browser → make its transclusion + backlink rows fully interactive
   and the live-fire path obvious.** *Highest pick.* This room is already the most ALIVE of
   the five — `WebOfCells`, `WhatLinksHere`, and `WebShell` are first-class cockpit tabs
   (`Tab::ALL`, `cockpit/mod.rs:401-403`), dispatched live (`panels_workspace.rs:104,106`),
   firing real attested reads + executor turns. The smallest wire is not "build a browser"
   (it exists) but the **transclusion "⚡ make interactive → ▶ fire" affordance polish + a
   default-build path** (~110 gpui lines reusing `web_cells.rs`). Highest wonder-per-weld
   because the surface is *already standing* — Engelbart/Nelson two-way links you can click
   and fog-of-war you can feel, one polish-weld from delightful.

2. **The agent-in-deos cockpit → give the confined agent CREATE/EDIT-CARD tools (authoring
   under its own cap).** The agent pane is ALIVE-WIRED (`AgentPane::interactive`,
   `dock/hermes_surface.rs`; `open_agent_pane`), the gate is Lean-proven and red-teamed (5
   attacks held), and `run_js` drives the live World under `--features js-agent`. The agent
   can READ + FIRE but cannot yet AUTHOR. Wiring `create_card`/`edit_card` as confined MCP
   tools (~150–200 lines) closes the cap-gate thesis: every authored card a receipted turn
   under the agent's own cell. This is the room that makes "a Claude inhabits the cockpit"
   into "a Claude *builds* in the cockpit."

3. **The Matrix membrane → open ChatPane as a windowed cockpit dock pane + palette command
   (and back the fire button with the executor host).** The transport is ALIVE, the fork is
   BAKED (`ForkMembraneHost`, `shared_fork.rs`), the stitch *theorem* is PROVEN in Lean
   (`SettlementSoundness.lean`, 0 sorries, non-vacuous), and the pane already renders in the
   guest/showcase BAKES. The wire is now narrow: a `CommandId::OpenChatPane` + `open_chat_pane`
   modeled on `open_agent_pane`, then swap `MockSource` → executor-backed source for the
   "▶ rehydrate & drive" button (~40–60 lines for the pane; the executor host is the deeper
   half). Ranked 3rd only because the felt payoff (drive + stitch a shared world-fork) still
   leans on the executor-source bind.

The **moldable inspector** and the **self-hosting dock** are NOT in this top-3 because they
are already substantially ALIVE-WIRED (inspector tab + dev dock); their next moves are
deepening, not opening (see their rooms below).

---

## ROOM A — The docuverse / transclusion browser — **ALIVE-WIRED (surface stands)**

**Verdict: the browser surface EXISTS and is clickable, not primitives-only.**

The primitives (`starbridge-web-surface/`) are proven and ride the verified substrate:

- A **transclusion is a verified observation** — `TranscludedField::include` does a real
  `dregg://` finalized read (`transclusion.rs:131`); the displayed bytes ARE the source's
  committed bytes (content-addressed). `verify()` runs content→commitment→receipt→stream-root
  →quorum (`transclusion.rs:172`).
- A **`dregg://` link IS a capability**, not a location — `DreggUri` (`web_of_cells.rs:56`):
  the `cell: CellId` is the access grant + the unforgeable identity.
- **Versioned (snapshot/live) dial** (`transclusion_version.rs:128`) realizes I-confluence
  as a legible knob; **`Backlinks`** (`transclusion.rs:256`) is the two-way Nelson link as a
  verifiable witness-graph fact.
- Lean spec: `metatheory/Dregg2/Deos/Transclusion.lean`.

The **browser surface is mounted as real cockpit tabs** (NOT a future weld):

- `Tab::WebOfCells` (`cockpit/mod.rs:276`, in `Tab::ALL` `:401`) → `web_of_cells_panel`
  (`panels_workspace.rs:104`): renders addressable `dregg://` cells with attested
  `OriginChrome`, a viewer-tier toggle (ROOT/EDITOR attenuation = fog made tangible), an
  opened cell's per-viewer affordance surface (real `AffordanceSurface::project_for`), and a
  **▶ fire** button running the embedded executor (`web_cells.rs`).
- `Tab::LinksHere` (`cockpit/mod.rs:298`, `:403`) → `links_here_panel`
  (`panels_workspace.rs:106`): the real `Backlinks` witness-graph, projected through the
  focused agent's `Membrane` (a backlink the viewer's caps can't admit is OMITTED — the link
  fog-of-war), each row **clickable to navigate into the observing cell** (`links_here.rs`).
- `Tab::WebShell` (`cockpit/mod.rs`, `🌐 WEB-SHELL`) → a general `http(s)://` browser via
  `servo_render` — **BAKED/gated** behind the `web-shell`/`servo` features (`Cargo.toml:258`).
  A `dregg://` address routes to `WebOfCells`; `http(s)://` renders the servo tile.

**What an operator/child does:** browse the `dregg://` docuverse like a web of pages, click a
cell to see its attenuated affordances, fire one through the verified executor, follow a
"what links here" backlink into the observer, and flip the viewer tier to watch gated links
fog in and out. A transclusion row shows a quoted field + provenance receipt as READ-ONLY,
with a **⚡ "make interactive"** button that runs a real `Powerbox::grant` to confer an
attenuated affordance cap on the source.

**The smallest wire (highest wonder-per-weld):** the surface stands; the polish is the
transclusion row's ⚡→▶ path (`panels_web.rs:349-450`, ~110 gpui lines reusing `WebCellsBrowser`)
and confirming these tabs are reachable in the *default* windowed build (they're in `Tab::ALL`
unconditionally; only `WebShell` is feature-gated). **Weld shape: polish + reachability, not
construction.**

---

## ROOM B — The agent-in-deos / ADOS cockpit — **ALIVE-WIRED (read+fire) · BAKED (authoring)**

**Verdict: the confined agent inhabits a live cockpit dock pane and drives real turns; it
can READ and FIRE but cannot yet AUTHOR.**

- **The pane is ALIVE-WIRED.** `AgentPane::interactive(id, session_id, window, cx)` spawns a
  live persistent confined-Hermes session on the gpui foreground
  (`starbridge-v2/src/dock/hermes_surface.rs`); `pub mod hermes_surface;` is mounted under
  `#[cfg(feature = "dev-surfaces")]` (`dock/mod.rs:76`); `open_agent_pane()` is callable from
  the cockpit. The pane renders chat + a live tool-call ledger + mandate budget bars,
  token-by-token.
- **`run_js` on the live World is ALIVE-WIRED (feature-gated).** `RunJsTool` (`run_js.rs`) +
  `LiveJsHands` (`live_js.rs`) let the agent run JS under its *attenuated* held cap (never
  root); turns land on the LIVE cockpit ledger under the agent's own cell. Proven end-to-end
  in `tests/hermes_runs_js.rs` (crawl → fire Signature-gated affordance → over-reach refused
  in-band). Gate: `--features js-agent` (pulls real SpiderMonkey/`deos-js`); default suite is
  mozjs-free.
- **The confinement is PROVEN and red-teamed.** The authority face routes every ACP tool-call
  through `HermesGateway::admit_call` → `ToolGateway::invoke` (the Lean-mirrored `delegAdmit`,
  embeds `libdregg_lean.a`, `bridge.rs`). Five red-team attacks HELD: mandate overrun
  (`red_team_mandate_overrun.rs`), authority amplification + confused deputy
  (`red_team_authority_amplification.rs`), replay + receipt forgery
  (`red_team_replay_and_forgery.rs`), and OS sandbox escape — four teeth, exit-code bitmask
  (`red_team_sandbox_escape.rs`, real confined fork via macOS Seatbelt / Linux ns+seccomp+
  landlock, `confined.rs`).
- **The ACP transport is REAL.** `acp_client.rs` is a real ndjson JSON-RPC client driving
  `initialize → session/new → session/prompt`; `AcpTransport::spawn_hermes` spawns a live
  subprocess. `MockHermesPeer` (`mock_peer.rs`) replays faithful message shapes for the
  hermetic default suite; the **same driver** runs over mock AND live. Live ceiling: handshake
  + session are LIVE-tested; `session/prompt → tool-calls` needs a reachable model provider
  (Bedrock advertised), so without creds the loop completes the handshake but emits no
  tool-calls. **Honest:** "a live Claude inhabits the cockpit" is real where a provider is
  reachable; the default test path is a faithful mock, not a live model.

**What an agent does today:** open the agent pane, get a prompt box; the reply streams in;
each tool-call appears in the live ledger with a receipt + remaining budget (or an in-band
refusal with a named reason); budgets deplete monotonically and persist across turns; with
`js-agent`, the agent runs JS that fires affordances on the live World.

**The next move (BAKED → ALIVE):** wire `create_card` + `edit_card` as confined MCP tools
(`src/mcp_server.rs`, ~80–120 lines) so the agent authors cards *under its own cell* (the
confused-deputy property), refused in-band for cards it lacks authority over; add a red-team
test (~40–60 lines) proving the cap tooth on authoring; a cockpit prompt (~10–20 lines).
**Weld shape: ~150–200 lines.** This turns the agent from read+fire into a read-write
co-author on the live card graph — the cap-gate thesis fully realized.

---

## ROOM C — The Matrix membrane: a message = a cap-bounded world-fork — **ALIVE transport · BAKED fork+pane · PROVEN stitch-theorem · ASPIRATIONAL stitch-mechanism-wiring**

**Verdict: more layered than "transport alive / stitch aspirational." The pane already
renders in the bakes; the stitch THEOREM is proven in Lean; what's open is the windowed dock
mount + the executor-source bind for the fire button.**

- **Transport — ALIVE-WIRED.** Real `matrix-rust-sdk`; a send IS a turn yielding a
  `SendReceipt{room_cell, turn_index, post_root}` (`source.rs`/`cell.rs`). A membrane rides a
  namespaced custom field in `m.room.message` with a readable fallback for non-deos clients
  (`client.rs`). `DreggObject` carries six kinds (Membrane/Cell/Capability/Transclusion/
  Affordance/Receipt), each fail-closed on version/kind (`object.rs`).
- **The pane — BAKED (renders in bakes, not the windowed dock).** `ChatSurface`/`ChatPane`
  forward to a `CockpitSurface` (`deos-matrix/src/cockpit_surface.rs`,
  `starbridge-v2/src/dock/chat_surface.rs`); `pub mod chat_surface;` is in `dock/mod.rs:65`;
  `deos-matrix` is a `dev-surfaces` dep with the `cockpit-surface` feature
  (`Cargo.toml:470`). `ChatPane::new(...)` is already constructed in `guest.rs:248` and
  `showcase.rs:132` — but those are **headless PNG bakes** (`--render-guest`/`--render-showcase`,
  `main.rs:195,222`), not a windowed dock pane with a palette command.
- **The fork — BAKED.** `MembraneEnvelope` (`membrane.rs`) carries an anti-substitution
  frustum-root (fail-closed: `rehydrate_fails_closed_on_root_substitution`), an attenuated
  `lineage` cap (non-amplification = recipient MEETs with their own cap), and a depth-bounded
  `FrustumCut`. The real executor-backed `ForkMembraneHost`
  (`starbridge-v2/src/shared_fork.rs`, gated `dev-surfaces`) runs mint→rehydrate→drive→stitch
  with graduated consent tiers (embedded / studyref / network-boundary, fail-closed gate).
- **The stitch — THEOREM PROVEN (Lean), MECHANISM partial.** `SettlementSoundness.lean`
  exists with **0 sorries and 19 theorems**, including `settlement_soundness`,
  `revoke_unsettleable_immediate`, a deployed instance (`deployedSettle_sound`), a
  **non-vacuity witness** (`settlement_nonvacuous`), and a **negative witness**
  (`branchSettle_NOT_binds` — a branch-time predicate is *refused*). So the
  authority-live-at-settlement math is real and non-vacuous. The Rust `stitch.settle()`
  mechanism compiles and the typed `ConflictObject` lossy-drop is real; the **frontier is
  wiring the proven settlement gate to the real fork's stitch** (and the "▶ rehydrate &
  drive" button is live ONLY when its source holds an executor — `MockSource` returns
  `membrane_capable()=false`, so today it renders disabled with "open in deos to rehydrate",
  `chat.rs`).

**What an operator does (eventually):** share a Matrix message that IS a cap-bounded fork of
their world; the recipient rehydrates it (anti-substitution checked), drives a real verified
turn on the fork, and stitches it back — clean parts merge, linearity-conflicting parts drop
as explicit typed `ConflictObject`s. The no-peek is a theorem, not a checkbox.

**The smallest wire:** (a) a `CommandId::OpenChatPane` + `open_chat_pane` modeled on
`open_agent_pane` to mount `ChatPane` in the *windowed* dock (~40–60 lines); (b) back the
source with `ForkMembraneHost` so `membrane_capable()` is true and the fire button goes live
(the deeper half — an executor-backed `ChatSource` impl). **Weld shape: pane-mount small;
executor-source bind medium.**

---

## ROOM D — The moldable inspector — **ALIVE-WIRED (tab mounted) · BAKED (faces) · ASPIRATIONAL (Spotter/Halo/Gadget-forms)**

**Verdict: the inspector is a LIVE cockpit tab, not applets-only. (Scout overstatement
corrected.)**

- **ALIVE-WIRED:** `Tab::Moldable` ("INSPECTOR", `cockpit/mod.rs:391,442`) dispatches
  `moldable_panel` (`panels_workspace.rs:108`, impl `cockpit/panels_moldable.rs:9`): it
  renders an object's **presentation SET as a sub-tab strip** via a `Registry`
  (`present_memo.present`, `panels_moldable.rs:268`), with a **Spotter search box** ("type to
  search every object's every presentation", `:92`) and per-presentation body rendering
  (`render_presentation_body`, `:325`). There's also a sibling `Tab::InspectAct`
  (`inspect_act_panel`, `:388`). The panel even self-hosts: its `(focus, present-idx)` is a
  witnessed cell (`:42`). **17 `Presentable` impls** exist across `starbridge-v2/src/`
  (DeepCell, receipt chain, cap inspector, predicate composer, doc lens, settlement, …).
- **The reflective substrate is production-grade** (`deos-reflect/`): four substances
  projected uniformly (`substance.rs`), the four faces — RawFields / ocap Graph /
  DomainVisual lifecycle / Provenance receipt-chain — all built and tested
  (`present.rs`, `tests/reflective_crawl.rs`), cap-bounded by a `Frustum` (`frustum.rs`:
  unobservable cells return absence, not forgery).
- **BAKED:** in the deos-view *applet* renderer, only the **RawFields** face actively renders
  rows (`deos-view/src/faces.rs:109-125`); Graph/DomainVisual/Provenance deserialize but show
  as one-line kind tags. (The cockpit `moldable_panel` renders richer; the applet face view
  is the coarse one.) The `Invariant` and `Source` faces are typed but unrendered.
- **ASPIRATIONAL:** `Spotter` as universal cross-object search (the box exists in the panel;
  full-corpus indexing is sketched), the `Halo` direct-manipulation ring
  (`docs/deos/INSPECTOR-FRAMEWORK.md`, only `wonder.rs` 3-ring seeds), and interactive
  `Gadget` *forms* (the trait + draft impls exist, `presentable.rs`; not yet wired as
  cockpit editing forms).

**What an adept does:** open the INSPECTOR tab, pick a protocol object, browse its named
lenses across a sub-tab strip (RawFields floor + Graph + DomainVisual + Provenance), and
spotter-search across presentations to re-focus. **The single highest-wonder lens is the ocap
Graph face** — a cell's in/out cap edges ARE the authority topology, answering "what is my
reach / blast radius?" at a glance. **The deepening move:** wire the `Gadget` forms so a lens
becomes editable (predict-then-commit, `simulate.rs` already does the spine), turning
inspection into in-place authoring. The model is built; the cockpit form-binding is the wire.

---

## ROOM E — The self-hosting dev dock — **ALIVE-WIRED (edit·save·terminal) · ASPIRATIONAL (compile-run loop)**

**Verdict: alive as a self-hosting authoring dock; the next move is the live compile-run
loop, not the conflict viewer (which already lives in the DOCS tab).**

- **ALIVE-WIRED:** the editor pane saves are real `SetField` turns on the live World
  (`dock/editor_surface.rs:93-127`, `commit_save` → `World::turn`/`commit_turn`, receipt
  recorded; the cockpit inspector reads the same ledger via `firmament_over`). The terminal
  pane spawns a real PTY on `$SHELL` (`dock/terminal_surface.rs:48-65`). The
  document-language **conflict viewer is ALIVE-WIRED but in the DOCS tab**, not the editor
  pane: `DocumentInspection` from `doc_lens` renders conflicts as marked regions with
  attributed alternatives ("here's both", `cockpit/docs.rs:208-241`, `doc_lens.rs`).
- **ASPIRATIONAL:** there is **no `rustc && ./prog` compile-run affordance** anywhere — the
  editor is pure file authoring; per-command cap-gating on the terminal is a comment, not
  wired (`terminal_surface.rs:34-37`). The editor pane edits *files*, not `dregg_doc` patch
  objects, so the conflict viewer is not (and need not be) in it.

**What an adept does:** ⌘K → open editor pane, edit a Rust file, save (receipt count
increments, committed to ledger), ⌘K → open terminal pane, manually run `rustc main.rs &&
./main`, read output. The two halves are manual.

**The next move (this room's pick):** the **live compile-run loop** — hook the editor's
`on_save` (deos-zed has `set_save_callback`) to shell `cargo build`/`rustc` on the changed
file, capture stdout/stderr into an auto-spawned sibling terminal pane (the PTY already
exists), and run the binary on success. **Weld shape: ~200–400 lines**, one `on_save`→compile
→display seam, reusing existing turns + PTY. Collapses "edit here / run there manually" into
"save → see it compile and run."

---

## HONESTY LEDGER — the corrected real-vs-baked map

**ALIVE-WIRED (clickable today, windowed/feature-on build):**
the docuverse browser tabs (WebOfCells · WhatLinksHere · WebShell-gated) with attested reads
+ executor fires + clickable backlinks + fog-of-war; the moldable INSPECTOR tab (Registry +
Spotter + presentation sub-tabs, 17 Presentable impls); the agent pane (live confined Hermes,
streaming ledger + budgets, `run_js` on the live World under `js-agent`, gate Lean-proven +
5 red-team attacks held); the self-hosting dev dock (editor saves = real SetField turns ·
terminal PTY · conflict viewer in DOCS tab); the Matrix transport (send = a receipted turn).

**BAKED (built + proven, not opened as a windowed clickable surface):**
the Matrix ChatPane (renders in `--render-guest`/`--render-showcase` headless bakes + the
forwarder is mounted, but no windowed dock pane / palette command); the membrane fork
(`ForkMembraneHost`, executor-backed, `dev-surfaces`); the four reflective faces beyond
RawFields in the *applet* view; the agent's card-authoring (gate + tests exist, authoring
tools do not).

**ASPIRATIONAL (named/typed/sketched, or proof-frontier):**
the membrane stitch *mechanism* wiring (the THEOREM is proven — `SettlementSoundness.lean`,
0 sorries, non-vacuous + a negative witness — but binding the proven gate to the real fork's
`stitch.settle` + an executor-backed `ChatSource` is the open wire); the live compile-run
loop; the inspector's `Spotter` full-corpus index, `Halo` ring, and interactive `Gadget`
forms; per-command terminal cap-gating; the WebShell servo content layer (feature-gated).

**The shape of "early":** the atoms are real and ride the verified substrate — there are no
fake demos on load-bearing paths, and more surfaces are *already mounted as cockpit tabs*
than memory suggested (docuverse browser, inspector, agent pane). What is early is (1) a
handful of **last welds from BAKED to windowed-clickable** (the ChatPane dock pane; the agent
authoring tools), (2) **deepening interactivity** on standing surfaces (transclusion ⚡→▶
polish; Gadget editing forms; the compile-run loop), and (3) **binding proven Lean theorems
to running mechanism** (the membrane stitch). The joy is largely built and increasingly
opened; the frontier is polish, authoring, and the stitch-mechanism bind.

---

*( ⌐■_■ )  the workshop's instruments are not just finished — several are already on the
stage. what's left is to hand a few of them to the agent, polish the keys a child will
press, and wire the one proven theorem to the lever it governs.*
