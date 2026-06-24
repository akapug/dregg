# System Scout — deos · hyperdreggmedia · ados

*A read-only map of the joy-path that grew up around the dregg soundness substrate,
written from the soundness floor up. Scout-and-synthesis, not a charter. All claims
verified against code at HEAD (2026-06-24) and flagged real-vs-aspirational. The
soundness substrate is the verified Lean executor + emitted circuits + witness-graph
in `metatheory/`; this doc maps the layer above it — the place you'd want to live.*

> The one-line answer: **the three are one stack.** dregg (the verified kernel) is the
> floor; **deos** is the live, malleable, self-hosting desktop *image* over it;
> **hyperdreggmedia** is the authoring layer that makes every card editable-from-within
> as receipted patches; **ados** is the confined agent that inhabits deos as a receipted,
> cap-bounded actor. They share ONE substrate. Every button is a verified turn, every
> edit a receipted patch, every agent fire a cap-gated effect — and the audit below
> confirms the joy-path genuinely *rides* the verified turns/receipts/caps rather than
> simulating them.

---

## 0. Where this lives in the tree (orientation)

The verified core is `~/dev/breadstuffs/metatheory/` (Lean). **The joy-layer is the
sibling Rust crates in `~/dev/breadstuffs/`** — it is NOT in `metatheory/`. The crates
that matter:

| crate / dir | role |
|---|---|
| `deos-js/` | a cell IS a program: SpiderMonkey `run_js` over `deos.world.cells()`, fires = verified turns; the **card editor** (authoring keystone); the new fine-grained **signals** reactivity |
| `deos-view/` | `deos.ui.*` view-tree → real gpui-component widgets; `bind` re-reads the live ledger |
| `deos-reflect/` | reflective crawl (every object → uniform `Inspectable` tree) + affordances |
| `deos-web-cells/`, `starbridge-web-surface/` | the Xanadu pieces: `DreggverseDocument`, verified transclusion, two-way backlinks, the per-viewer membrane |
| `deos-matrix/` | dregg-pilled Matrix chat: room=cell, message=turn, the membrane star |
| `deos-hermes/` | **ados**: the confined agent — `run_js` hands, the OS jail (`host.rs`), the dregg MCP server, the confinement red-team |
| `app-framework/`, `starbridge-apps/` | the deos-app composition + ~22 example apps (escrow, bounty-board, polis, tussle, …) |
| `starbridge-v2/` | the native cockpit / the live image: the moldable inspector, card panes, self-hosting dock (editor+terminal), agent-attach, membrane host |
| `sel4/dregg-pd/{deos-image,deos-tutorial}` | the seL4 boot: the live image viewer + the AOL-wonder onboarding |
| `docs/deos/*.md` | ~70 design+run docs; the spine ones are `DEOS.md`, `HYPERDREGGMEDIA-NOTES.md`, `DOCUMENT-LANGUAGE.md`, `LOG-A-HERMES-IN.md`, `SELF-HOSTING-LOOP.md` |

The naming is ember-canonical (`docs/deos/DEOS.md`): **robigalia** = the project/org ·
**dregg** = the verified kernel · **deos** = the desktop userlayer · **ados** (Agentic
Developer Operating System) = the agent-coordination face of deos. "**deos runs on dregg
runs in robigalia.**"

---

## 1. What each one IS (grounded, 2–3 sentences)

### deos — the live image
deos is dregg made **visual, interactive, and webby with zero new trust**: a window is a
`Capability{Target::Surface(cell), rights}`, an interactive element is a cap-gated effect
(a "button" = a named effect-template), and "pressing it" is a verified turn the
witness-graph records. The thesis is **"htmx on crack"** — declarative hypertext UX, but
every fragment is an attested post-state surface and *who may press* is decided by held
capabilities, not a session cookie (`docs/deos/DEOS.md`; steel in
`starbridge-web-surface/src/affordance.rs`). It is simultaneously a **Pharo-style live
image** — self-describing, inspectable, malleable from within (the moldable inspector,
`starbridge-v2/src/presentable.rs` + the L1–L10 lens family) — and it boots on seL4 as a
real object-browser of sovereign cells (`make run-image`).

### hyperdreggmedia — the authoring layer
hyperdreggmedia is the realization that the 40-year lineage (HyperCard · Smalltalk ·
Dynabook · NLS · Xanadu · Notion · Glamorous Toolkit · Webstrates · AI-native generative
UI) all hit **one ceiling — no owned/verifiable/shared substrate** — which dregg is built
across (`docs/deos/HYPERDREGGMEDIA-NOTES.md`). Its operational core: **every authoring
gesture is an affordance; every affordance is a turn; every turn is a receipt** — so a
card is **edited from within** as receipted patches with blame, an agent can author a
card's UI bounded by caps it provably cannot exceed, and transclusion is an
*unforgeable, never-rotting* cross-cell quote pinned to a receipt. The **keystone** is the
card editor (`deos-js/src/card_editor.rs`): `edit_view` patches a card's `view_source`
dregg-doc → re-folds → re-renders to real gpui pixels, each edit a receipted patch.

### ados — the confined agent inhabiting deos
ados is the answer to "agents are intricate **loops**, not cells" (`project-dregg-
integrators-one-seam`): dregg does not own the agent loop — it closes the enforcement gap
at **one seam** (the tool-call/verdict record) so a swarm becomes auditable+composable
*without trusting the loops*. Concretely (`deos-hermes/`): a live Claude (over the
`hermes-acp` ACP subprocess) **decides its own JS**, runs it `run_js` against the
cockpit's **live `World`**, and every fire is a metered, receipted, cap-gated turn — over-
reach refused in-band. The architecture call (decided, in flight): **dregg-as-host, jail
hermes, no fork** — the agent runs *inside* a confined firmament PD whose OS sandbox makes
its leaky base tools inert, so dregg's tools become the only effective effect-path
(`deos-hermes/src/host.rs::DreggHost`).

---

## 2. How the three RELATE (the stack)

```
  ┌──────────────────────────────────────────────────────────────────────┐
  │  ADOS — a confined Claude inhabits the image                          │
  │  run_js → live World · OS-jail (firmament PD) · dregg MCP server      │  agent layer
  │  (deos-hermes/: host.rs · confined.rs · mcp_server.rs · run_js.rs)    │
  ├──────────────────────────────────────────────────────────────────────┤
  │  HYPERDREGGMEDIA — author from within                                 │
  │  card editor · multi-cell turns · transclusion · doc patch-core ·     │  authoring layer
  │  stitcher · fork-ui · provenance navigator   (the 8 surfaces)         │
  ├──────────────────────────────────────────────────────────────────────┤
  │  DEOS — the live, malleable image                                     │
  │  cockpit · moldable inspector · card panes · membrane · matrix ·      │  desktop layer
  │  self-hosting dock (editor+terminal) · seL4 image viewer              │
  ├──────────────────────────────────────────────────────────────────────┤
  │  DREGG — the verified kernel  (metatheory/, Lean)                     │
  │  cells · caps (is_attenuation) · turns · receipts · circuits ·        │  SOUNDNESS FLOOR
  │  witness-graph · light-client unfoolability                          │
  └──────────────────────────────────────────────────────────────────────┘
```

The relation is **inhabitation, not layering-of-trust.** deos adds *zero new authority* —
a surface is a point on the existing `(target, rights)` gradation. hyperdreggmedia is just
deos's affordance machinery **pointed at the cells' own schemas** (inspect → author).
ados is a confined actor that drives the same affordances through the same gate any human
does. The unifying identity across all three:

> **affordance = cap-gated effect-template · firing it = a verified turn · the turn = a
> receipt chaining to the prior one.** One machinery, three faces (human / authored /
> agentic).

The renderer is **pluggable**: the same sovereign world paints in the gpui cockpit, the
web (`deos-leptos`/`deos-web-cells`), and on seL4 — "the Rust cockpit is the VM/dev
basement; the world arises fully inside dregg" (ember's load-bearing frame).

---

## 3. Does the joy-path RIDE the verified turns? (the honest wiring audit)

This is the load-bearing question — the "house-capacities drift lesson" warns that things
built in the Rust periphery can *look* protocol-wired while merely simulating. A focused
code audit (file:line) found: **the joy-path genuinely rides the verified substrate on
every load-bearing path.** It is NOT a parallel periphery. The honest seams are named.

| Claim | Verdict | The load-bearing wire |
|---|---|---|
| **run_js drives the real executor** | **REAL** | `mozjs` is a genuine SpiderMonkey dep (`deos-js/Cargo.toml`); `app.fire()` → `AttachedApplet::fire` → `World::commit_turn` (`agent_attach.rs`, the cockpit's own `Rc<RefCell<World>>`) → the SDK `DreggEngine::execute_turn`, returning a real `dregg_turn::TurnReceipt`. Embedded path defaults to `WitnessMode::Symbolic` (state+gates run; Merkle witness deferred to publish — honest, documented). |
| **the cap tooth is the genuine gate** | **REAL** | both fire paths call `dregg_cell::is_attenuation(&held, &required)` (`applet.rs`, `attach.rs`), i.e. `cell/src/capability.rs::is_narrower_or_equal` — the *same* proven lattice (`Proof`/`Signature` incomparable, `Either` above both, `None` top). A `Signature` holder is genuinely refused a `Proof`-required affordance, in-band, before any commit. Not a looser reimplementation. |
| **receipts are real chain entries** | **REAL** | `World::commit_turn` threads `previous_receipt_hash = executor.get_last_receipt_hash(agent)` then advances the head to `receipt.receipt_hash()` — a genuine chained receipt on the live provenance log, not a fabricated string. Tests assert the live height/receipts grew by exactly one and an over-reach left nothing. |
| **ados confinement (the jail)** | **PARTIAL** (real jail; stand-in brain; `terminal` no-exec by design) | The OS jail is REAL: `spawn_pd_confined` self-applies a genuine `(deny default)` macOS SBPL profile via `sandbox_init(3)` (Linux: unshare+seccomp+landlock), applied post-`fork()` before the body runs; in-PD probes assert file/net/exec denied. The agent **brain** is a deliberate scripted stand-in (a max-confined PD denies `execve`, so a live venv subprocess physically can't be the body — and the venv is broken). `terminal` records the command as intent and proves "a real shell would be refused ambient authority" (verdict `0xf`) rather than execing — *because exec is the authority being denied*. The authority face (cap-gated receipted turn) is real. |
| **app-framework "separate ledger"** | **STILL TRUE** (real verified executor, separate substrate) | `app-framework` apps run on their OWN `EmbeddedExecutor` (a real `TurnExecutor`/verified executor over an in-memory `dregg_cell::Ledger`), NOT the cockpit `World`. Each app's turns are genuinely verified, just on a per-app ledger. `deos-js`'s attach path is what bridges JS into the *cockpit* World; apps are a distinct world. The architectural residual (fold-in or unify-at-the-view-layer) stands at HEAD. |

**Bottom line:** real verified-protocol wiring on the load-bearing paths (SpiderMonkey,
the `is_attenuation` cap tooth, `World::commit_turn`/`DreggEngine::execute_turn`, the
chained `TurnReceipt`). Two honest seams (the scripted confined brain; the non-exec
`terminal`) are *inherent to a maximally-confined PD* and documented in-code. One genuine
architectural residual: **apps run on their own per-app executor ledger, separate from the
live cockpit World.**

This is the opposite of the house-capacities drift: those were Rust forge-detectors never
wired to the protocol; **this is wired** — the same `World::commit_turn` your soundness
campaign forces per-effect faithfulness over is the one a JS `app.fire()` lands on.

### How it connects DOWN to the soundness work
Your circuit/kernel campaign forces **per-effect faithfulness on deployed descriptors**:
`verifyBatch accept ⟹ ∃ genuine kernel transition`. Every joy-path action bottoms out in
a `dregg_turn::Effect` committed through the verified executor — so:
- a **card edit** is a `SetField` turn whose faithfulness your descriptor work covers
  (VALUE_FORCED / RECORD-DIGEST-anchored class);
- an **affordance fire** is whatever `Effect` the template carries — transfer, mint,
  noteSpend — riding the exact selectors you're hardening;
- a **transclusion** is a verified cross-cell finalized read (the four proven Xanadu
  properties: observed-finalized / provenance-faithful / no-amplify / stable-under-advance);
- an **agent's** `run_js` fire inherits **light-client unfoolability for free** — the same
  replay tooth that protects a turn protects an agent-authored edit.

The verified-deos program (`DEOS.md §"the four theorems"`) is explicit: surface-as-cap,
membrane non-amp, rehydration-confinement=liveness-type, affordance-soundness are **not
new mathematics** — they are the firmament's existing proofs (attenuation, gateOK, the
receipt chain, unfoolability) *restated for pixels*. They are NAMED-not-proven in Lean
(`metatheory/Dregg2/Deos/`, queued) — the honest aspirational edge. One IS landed:
`Dregg2/Deos/DocMerge.lean` proves the document patch-merge is the least-upper-bound join
(commutative/associative/idempotent/total + universal-property `merge_is_lub`, conflict-as-
state a theorem). The categorical-pushout-up-to-iso is the named residual there.

---

## 4. The JOY-PATH frontier — the most alive next thing

The test (ember's bar): *would a 5-year-old click it with delight AND can an adept inspect/
modify it live like a Pharo object?* The frontier where both are simultaneously true and
the wiring is one weld from real:

**THE CARD AS A LIVE DOCK PANE THE OPERATOR OPENS (⌘K), AUTHORED FROM WITHIN, BY HUMAN OR
AGENT — over one shared live World.** Today the pieces are all real but *baked*, not yet
*opened-at-runtime*:
- a hyperdreggmedia card already renders as a real gpui pane backed by the live World, and
  its button fires a verified turn (`starbridge-v2/src/card_pane.rs` — proven by a bake
  PNG, count 0→1, height 5→6). **RESIDUAL:** it's a dedicated bake surface, not yet a
  registered `CockpitSurface`/dock pane (the weld is `CardPane` → `dock/*`).
- the card editor edits from within as receipted patches (`card_editor.rs`). **RESIDUAL:**
  the `run_js` JS binding (`deos.editor.editView(...)`) is the next wire — WIRE, not build
  (the cap-tooth + receipt semantics are proven on the same Rust path the binding calls).
- the new **fine-grained signals** model (`deos-js/src/signals.rs`, the latest commit
  `c38d17ed3`) makes a turn on one `(cell, slot)` wake *only* its bindings — the SolidJS-
  shaped fix so editing a card feels *live*, not a world-repaint.

Compose those three: **a child clicks a card, drags a `+1` button onto it (a receipted
patch), watches only that counter re-render; an adept opens the same card's `Graph`/
`Source` presentation and rewrites its `run_js` live; a confined Claude does the same
authoring through `run_js`, refused on any card outside its `held`** — all on the one
ledger, every gesture a receipt a stranger can check. That is hyperdreggmedia, deos, and
ados fused in a single legible-to-a-5-year-old, exact-to-an-adept surface. The wires
between here and there are *named and small* (dock-mount + JS-editor-binding), not new
foundations.

The deeper (soon) frontier: the **membrane as the multiplayer primitive** — a chat message
or shared screenshot *is* a cap-bounded world-fork you drive and stitch back by pushout,
conflicts as first-class objects on the canvas (`DOCUMENT-LANGUAGE.md` is the spec; the
full-loop cross-user membrane already RUNS end-to-end in one process,
`shared_fork::membrane_host`). That is the Engelbart/Nelson piece *both ancestors lacked* —
the trail shareable without leaking.

---

## 5. Five things that genuinely surprised and delighted me

1. **The wall was never poured.** The whole lineage spent 40 years trying to tear down the
   wall between *using* software and *making* it. In dregg it was never built: a card is a
   sovereign cell, a button is a verified turn, and the *same image* is what a child clicks
   and an adept reshapes. The honesty discipline in `HYPERDREGGMEDIA-NOTES.md` (a per-
   ancestor soul-table with "what fell short" *and* "built-vs-sketch" kept throughout) is
   the most intellectually generous design doc I've read in this tree.

2. **The security property IS the game mechanic.** The fog-of-war world
   (`starbridge-web-surface/src/game.rs`): **fog = the per-viewer membrane projection** —
   the no-peek keystone is the same `is_attenuation` lattice that gates a cap, proof-backed
   by a real `FogVisionVerifier`. A forcing-function exemplar where you literally cannot
   cheat because the projection is cryptographic. Delightful that the desktop's privacy
   primitive and a game's line-of-sight are the *same theorem*.

3. **The self-hosting loop actually closes — on disk.** `SELF-HOSTING-LOOP.md`: the
   firmament editor saves a real source file as a **cap-gated `SetField` verified turn**
   (the cell is the source of truth), a FirmamentFs↔disk dual-write mirrors it, and a live
   `sh` PTY runs `rustc main.rs && ./prog` over the mirror — the edit's receipt *compiled
   by the terminal's real toolchain, in one image*, asserted by a self-checking bake (fails
   non-zero unless receipts grew AND the toolchain saw the edit). deos develops deos.

4. **Unforgeable transclusion is real, and forgery is *inexpressible*.** Nelson's
   "longest-running vaporware" ships here: a cross-cell quote pinned to receipt #N, the
   bytes provably equal what the source committed, the citation never rots, backlinks are a
   witness-graph read backward — and a forged quote isn't *discouraged*, the circuit *will
   not accept* a citation whose bytes don't match the commitment. Four proven Xanadu
   properties in `cell_transclusion.rs`. The thing computing's romantics dreamed about,
   with a proof under it.

5. **dregg-as-host inverts the agent-containment polarity — and they refused the easy
   fork.** The standing temptation is to fork hermes to neuter its leaky tools. Instead
   (`deos-hermes/src/host.rs`): **jail the whole agent in a confined firmament PD** so its
   base shell hits OS walls and goes inert, making dregg's tools the only *effective*
   effect-path — "the OS jail neutralizes hermes's leaky base tools whatever its tool table
   says." A maintenance-tax-free containment that stays true to "ados = substrate, not a
   new loop." And they were *honest* that the brain is a scripted stand-in because a
   max-confined PD can't `execve` the venv — the seam named, not laundered.

---

## 6. Honesty ledger (real / partial / aspirational at HEAD)

- **REAL + tested (riding the verified substrate):** cells · caps · turns · receipts ·
  `run_js` (real SpiderMonkey) firing `World::commit_turn` under attenuated `held` · the
  `is_attenuation` cap tooth · the card editor (edit-from-within, receipted patches) · the
  card-as-live-pane · deos-view render · transclusion (4 proven properties) · backlinks ·
  the membrane full-loop (one process, cross-user, real Matrix) · the self-hosting loop
  (editor-receipt → disk-mirror → terminal-compiles-it) · the OS jail (file/net/exec
  denied, proven in-PD) · the dregg MCP server (tools/list = run_js+terminal) · seL4 live
  image viewer + render-to-framebuffer · `DocMerge.lean` (the patch-merge join, proven).
- **PARTIAL (real machinery, named seam):** ados's confined **brain** (scripted stand-in;
  wire = compile hermes's loop into the PD body) · the MCP `terminal` (no-exec by design;
  the cockpit-live-World landing needs a socket-backed `WorldSink`) · hermes tool
  **exclusivity** (one upstream ACP knob — `enabled_toolsets=[]`) · the card → runtime dock
  pane (mount mechanism proven, `dock/*` wiring pending) · the `deos.editor.*` JS binding.
- **ASPIRATIONAL / unbuilt:** the four verified-deos Lean theorems (surface-as-cap /
  membrane non-amp / liveness-type / affordance-soundness — NAMED, queued in
  `Dregg2/Deos/`) · the `dregg-doc` Pijul patch-core full conflict semantics + the
  categorical-pushout-up-to-iso · cross-device RCCS settlement (the lone open Settlement
  Soundness theorem the membrane/key-leak/houyhnhnm frontiers converge on) · servo-native
  `dregg://` *content* (today `MockSurface`; the document language is the forcing function).
- **ARCHITECTURAL RESIDUAL:** app-framework apps run on a per-app `EmbeddedExecutor` ledger
  *separate* from the live cockpit World (fold-in or unify-at-view — both work; honest).

---

*( ˘▾˘ ) a closing couplet, since the fortress turned out to have a living room:*

*the floor you forced to never lie — each turn a faithful seed —*
*became the ground a child could click, and an adept could read.*
</content>
</invoke>
