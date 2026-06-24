# APPS RE-CENSUS — the DEOS-ERA bar (harsh)

The first census (`docs/APPS-CENSUS.md`) was **too kind**, and it owes a
correction. It judged each app by *surface-realness* — "does it sign real
Ed25519, ride the real `EmbeddedExecutor`, ship refusal-teeth?" — and called
every app that passed "REAL / ALIVE-RUNS." But "ALIVE-RUNS" there meant **the
test passes**. That is the floor (not-bullshit-on-the-surface), not the bar.

The actual bar in the deos / hyperdreggmedia era is different and harder:

> **DEOS-ERA-REAL** = a person can **open and use it in the live image today**.
> It mounts as a deos-js **card** / a **cockpit surface** / a reflective object
> a human can click, inspect, and drive — the way ROOM 2's cards, the
> inspector-card, the card-editor, and the membrane chat pane do. Its UI is a
> **view-tree** (`{kind, props, children}`) the renderer paints and the agent
> can rewrite from within, bound to the **live `World`** ledger.

By that bar almost the entire app corpus is **pre-deos**. A standalone Rust
crate that signs real turns headlessly but has **no card, no cockpit pane, no
view-tree, no openable surface, and runs on a separate substrate ledger** is
NOT a deos-era app — it is a **pre-deos artifact** that needs substantial work
to live in the current world.

Captured at HEAD `db701771c5`. Read-only; verified against source + git dates.

---

## The deos-era boundary (dated, from git)

The card / cockpit-surface epoch is **2026-06-23 onward**:

- `card_pane.rs` — first card-as-cockpit-pane — **2026-06-23**.
- `inspector_card.rs` + the six ROOM 2 cards — **2026-06-24**.
- The DeosApp **web surface** (app-framework `deos_app.rs`, axum HTTP
  `<dregg-affordance-surface>`) — **2026-06-14/15**. This is a *web-surface*
  generation, NOT a cockpit card and NOT openable in the live image. It
  **predates** the reflective cockpit. "Composed as a `DeosApp`" ≠ deos-era.
- **Every** `starbridge-apps/*` crate was last *meaningfully* touched
  **2026-06-15**. The later (06-21/22/23) touches are **tree-wide kernel
  sweeps** (`reject self-transfer`, threshold-QC test hardening) — NOT
  deos-surface work. **Zero** starbridge-apps produce a `ViewTree` / `deos_view`
  / `deos_js` / `CardPane`. (`grep -rln "ViewTree|deos_view|deos_js" starbridge-apps/`
  → empty.)

So: the apps were built **before** the world they now have to live in.

---

## What "deos-real" actually requires (the machinery, so the bar is concrete)

A genuinely deos-real surface (verified in source):

1. **A view-tree** — `deos_js::card_editor::ViewTree` (`{kind, props, children}`),
   rendered by `deos-view` to native gpui OR web DOM. `Bind` nodes re-read live
   ledger slots; `Button` nodes fire cap-gated verified turns.
2. **A cockpit mount** — hosted as a `CockpitSurface` / `CardPane` (e.g.
   `cockpit/panels_moldable.rs` mounts the inspector card + the six mode cards
   lazily as their mode's main-pane surface) over the cockpit's **live `World`**
   (`dregg_sdk::embed::DreggEngine`, ledger by value).
3. **Edit-from-within** — `edit_view` / `ViewPatch`: the view is *data*, so a
   user/agent reshapes the card's own view-source as a **receipted patch with
   blame**, no recompile.
4. **The cap tooth in-band** — fires checked against `held` via the proven
   `dregg_cell::is_attenuation` gate.

The **genuinely deos-real objects** in the tree today (the reference set):
`inspector_card`, the ROOM 2 cards (`dynamics_card`, `agent_card`, `links_card`,
`composer_card`, `objects_card`, `graph_card`), `card_editor`, `card_pane`
(counter), `coauthored_card`, and the **membrane chat pane** (deos-matrix,
⌘K → "Open Membrane"). These are deos-js cards / cockpit surfaces, not apps in
`starbridge-apps/`.

### The trap the first census fell into: the AppRegistry

`starbridge-v2/src/app_registry.rs` **does** wire 19 of the 22 starbridge-apps
into the cockpit. It is tempting to call that "deos-real." **It is not, by this
bar**, and the registry's own honest doc comment says why:

- A launched registry app runs on its **own app-substrate ledger** (the app
  framework's `EmbeddedExecutor`, `Arc<Mutex<Ledger>>`) — **NOT** the cockpit
  `World`'s engine ledger. They are *distinct physical ledgers*. The registry
  doc: *"folding an app's cells into `World`'s engine ledger would need a
  `World`/`DreggEngine` refactor out of this lane's scope."*
- A registry app surfaces as a **gadget-rolodex card** in the guest launcher
  (`guest.rs`: one glyph + label + tagline per `AppEntry`, read off
  `AppRegistry::standard`). That is a **launcher icon**, not an openable app UI.
  It has **no view-tree of its own**, no bespoke surface, no edit-from-within.
  Clicking it fires a canned demo turn on the side-ledger and the inspector can
  read the result — a "fire + inspect" seam, not "open and use the app."

So registry-wired ≠ deos-real. It is a real **integration seam** (a launcher +
a shared substrate ledger between fire and inspector), and it is the *closest*
the apps get — but a person cannot *open and drive the app's own interface* in
the live image. The app has no interface in the image.

---

## Headline

- **DEOS-ERA-REAL apps in `starbridge-apps/`: 0 of 22.** None mounts as a card
  or cockpit surface; none produces a view-tree; none runs on the live `World`
  ledger. They are pre-deos Rust libraries.
- **Registry-launchable (gadget-rolodex + side-ledger fire): 19 of 22.** Real
  integration, but a launcher entry + a fire-and-inspect seam — **not** an
  openable in-image app surface.
- **Not even registry-wired: 3** — `first-room`, `escrow-market` (wired as a
  framework entry actually — see table), and the standalone organ welds; the
  not-wired ones are `first-room`, plus apps whose ctor isn't a `DeosApp`.
  (Precisely: 19 framework/program entries are registered; `first-room` is NOT
  in the registry at all.)
- **The genuinely deos-era-real surfaces all live in `deos-js/` +
  `starbridge-v2/`, not in `starbridge-apps/`:** the inspector card, the six
  ROOM 2 cards, the card-editor, the card-pane, and the membrane chat pane.
- **The single best concept to port to a real deos card FIRST: `first-room`.**
  It is the "this is what dregg is *for*" app (mandate → conserving escrow → pay,
  with a 5-cheat battery each refused in-band with the receipt-why), it already
  has a gpui-free `Room`/`InhabitantView`, and it is *not even registry-wired*.
  Porting its room view to a deos-js card over the live `World` is the highest
  concept-value × tractability move — its "view" is already nearly a view-tree.
- **demo-agent/examples, sdk/examples, app-framework/examples, demo/**: all
  **headless** — zero deos presence (`grep` for `deos_view`/`deos_js`/`CardPane`
  → empty across all of them). The 11 placeholder demo-agent examples flagged by
  the first census remain TOY-STUB **and** pre-deos. Retire or fold into cards.

### The honest verdict

**The apps are mostly pre-deos artifacts and here is the real work.** The first
census's "all 22 are real" was true only at the surface-honesty floor; in the
deos era the apps are libraries that predate the image they must now inhabit.
Making one *deos-era-real* is not "add a README" (the first census's #1 move) —
it is **port the app's interface to a deos-js card view-tree, mount it as a
cockpit surface, and run it on the live `World` ledger (or fold the app's cells
into `World`'s engine ledger)**. That is the substantial work, per app, below.

---

## Per-app table (judged by the DEOS-ERA bar)

State legend:
- **PRE-DEOS-ARTIFACT** — headless lib/tests, no card, no view-tree, no
  cockpit surface of its own. (May be registry-launchable as a gadget icon — a
  fire-and-inspect seam — but that is not an openable in-image app surface.)
- **RETIRE** — stale concept, better told by another surface.
- (No app is DEOS-REAL.)

| App | deos-era state | Registry? | Concrete substantial work to be deos-real | Concept worth porting? |
|---|---|---|---|---|
| **first-room** | PRE-DEOS-ARTIFACT (richest) | **NO** | Port `Room`/`InhabitantView` → a deos-js **card** view-tree (it is *already* a gpui-free room view — closest to a view-tree of any app); mount as a cockpit surface; run the mandate/escrow/pay cycle + the 5-cheat battery on the live `World`. The cheat-refusals become live `Button` fires that show the receipt-why in-card. | **YES — #1.** The "this is what dregg is for" room. |
| **tussle** | PRE-DEOS-ARTIFACT | YES | Build a deos-js **card** with a board view-tree (figure poses as `Bind` rows, commit/reveal/resolve as `Button`s); the joint-state enum is forced by `SymMemberOf`. A verified *game* you can actually play in the image is the most demoable card. | **YES — #2 (fun).** |
| **polis** | PRE-DEOS-ARTIFACT (47 tests) | YES (program-backed, World path) | A governance **card**: council roster + proposals as `Bind` rows, propose/vote/commit as `Button` fires; ties to polisware-constitution. Substantial: multi-inhabitant turns need multiple `held` caps in one card. | YES — high concept, more work (multi-actor). |
| **nameservice** | PRE-DEOS-ARTIFACT (the exemplar) | YES | A register→resolve→renew→transfer→revoke **card**; the WriteOnce/Monotonic caveats become disabled/enabled affordance buttons (the cap tooth made visible). The pattern others copy → port it and the copies follow. | YES — the template. |
| **identity** | PRE-DEOS-ARTIFACT | YES | A credential **card**: issue→present(selective-disclosure)→verify→revoke; disclosure choices as card view-state, present as a fire. | YES — selective disclosure is legible. |
| **sealed-auction** | PRE-DEOS-ARTIFACT (Lean-mirrored) | YES | A sealed-bid **card**: commit (sealed) / reveal / settle buttons; settlement folds through `verified_settle`. Lean-tied = high integrity once carded. | YES — coordination demo. |
| **gallery** | PRE-DEOS-ARTIFACT | YES | Commit-reveal juried-gallery **card**: submissions as `Bind` rows, WriteOnce anti-swap board visible; phase lifecycle as a one-way set of buttons. | YES — visual, legible. |
| **bounty-board** | PRE-DEOS-ARTIFACT | YES | A bounty **card**: StrictMonotonic state machine as a stepper; WriteOnce first-claimer-wins → the claim button disables after first claim (cap tooth shown). | YES — small, clean. |
| **escrow-market** | PRE-DEOS-ARTIFACT (richest README) | YES | An escrowed-delivery **card**: fund→deliver→settle with the conserving settle shown live. Overlaps first-room's escrow organ — port via first-room. | Partial — fold into first-room. |
| **compute-exchange** | PRE-DEOS-ARTIFACT | YES | Near-twin of escrow-market. Don't card separately. | **RETIRE / MERGE** into escrow-market once carded. |
| **subscription** | PRE-DEOS-ARTIFACT | YES | A `CapInbox` publisher/consumer **card**: queue depth as `Bind`, publish/consume as fires. Storage-as-cell-programs is a strong dregg point. | YES — distinctive. |
| **agent-orchestration** | PRE-DEOS-ARTIFACT (+python) | YES (deos:: ctor) | Already has a `deos::orchestration_app` (web-surface flavor). A **card** showing the attenuated-mandate receipt chain (tools∧budget∧task) growing live; the python/hermes weld stays headless. | YES — the agent-substrate story. |
| **agent-provenance** | PRE-DEOS-ARTIFACT | YES | A proof-carrying-memory **card**: the blake3 hash-chain as an append-only `Bind` list, anyone re-verifies in-card. Conceptually overlaps "the dreggon's ledger" card (already deos-real). | Partial — the ledger card may already cover it. |
| **swarm-orchestration** | PRE-DEOS-ARTIFACT | YES | A swarm-dispatch **card**: conserved budget + epoch no-replay + async NOTIFY as live rows. | YES — but overlaps agent-orchestration. |
| **tool-access-delegation** | PRE-DEOS-ARTIFACT (Lean-diff) | YES | An ocap-for-AI-tools **card**: the rate-limited/time-bounded/revocable mandate cell with per-invocation caveats as live affordances; revoke is a fire. Best-documented + Lean-pinned. | **YES — high.** The "ocap for agents" thesis, clickable. |
| **governed-namespace** | PRE-DEOS-ARTIFACT (threshold-sig) | YES | A propose→vote→commit route-table-swap **card** under threshold-sig `Authorization::Custom`. Heavier than nameservice (threshold sig in a card). | YES — but after nameservice. |
| **supply-chain-provenance** | PRE-DEOS-ARTIFACT (hidden, 1468 LOC) | YES | A custody-chain **card**: each handoff a cap-attenuated transfer, single-custodianship a conservation law shown live. | YES — legible conservation story. |
| **compartment-workflow-mandate** | PRE-DEOS-ARTIFACT (Lean-diff, scaffold) | YES | A charter-DAG **card** (review→redact→sign): DAG step-order + clearance + budget teeth as a stepper. first-room already welds its `colonist_job`. | Partial — port via first-room. |
| **storage-gateway-mandate** | PRE-DEOS-ARTIFACT (thinnest) | YES | A gateway **card** (GET/PUT/LIST) with op-allowlist + prefix-auth + monotone volume budget. Thinnest substrate — lowest concept-priority. | Low. |
| **privacy-voting** | PRE-DEOS-ARTIFACT (composed **DeosApp** = HTTP web surface, NOT a card) | (web-mounted) | The first census called this "ahead of the curve" because it's a composed `DeosApp` — but `DeosApp` is an **axum web surface** (06-14 era), NOT a cockpit card. Real work = re-express the poll+ballot as a deos-js **card** (one-vote-per-ballot WriteOnce ballot as a disabling vote button). | YES — voting is legible; the WriteOnce tooth is a great teaching moment. |

### demo-agent / sdk / demo / app-framework (all headless, all pre-deos)

| Corpus | deos-era state | Disposition |
|---|---|---|
| `demo-agent/examples/` (41) | PRE-DEOS-ARTIFACT — headless ZK-pipeline walkthroughs; **11 still TOY-STUB** (`Authorization::Unchecked` + `[0u8;64]`/`vec![0x01]` proofs: `delegation_demo`, `atomic_swap_demo`, `agent_network`, `orchestration_demo`, `pipeline_demo`, `cross_fed_atomic`, `cross_federation_nft_swap`, `private_orderbook`, `delegation_swarm`, `unified_harness`, …). | **RETIRE the 11 placeholders** (worst misrepresentation; their stories are told by carded starbridge-apps). The 30 clean ones stay as headless feature-walkthroughs (CLI teaching), NOT deos surfaces. |
| `sdk/examples/` (`hello_receipt_chain`, `polis_ceremony`, `polis_sealed_vote`, `agent_demo`) | PRE-DEOS-ARTIFACT — headless one-binary walkthroughs over the real `AgentRuntime`. | KEEP as **CLI onboarding** (smallest "what is a receipt" primitive). Not deos surfaces; don't pretend they are. |
| `demo/` (`two-ai-handoff`, `multi-node-devnet`, `cross-app-e2e`, …) | PRE-DEOS-ARTIFACT — cross-process e2e harnesses + `expected.json` oracles. `two-ai-handoff` is the production receipt-chain reference. | KEEP as **test infra**. Not openable surfaces. (Devnet: no live server — local only.) |
| `app-framework/examples/` (`deos_app_in_an_afternoon`, `deos_council_board`, `stark_frustum_cull`, `stark_rehydrate`) | PRE-DEOS-ARTIFACT — these teach the **web-surface** `DeosApp` composition (06-14 era), not the card. | KEEP as the **web-surface** framework's teaching examples, but rename the mental model: this is the *older HTTP affordance-surface* generation, distinct from deos-js cards. The genuine modern composition exemplar is the card stack in `deos-js/`. |

---

## The ranked porting plan (concept-value × tractability)

The substantial work, ranked. Each item = "port the app's interface to a
deos-js card view-tree + mount as a cockpit surface + run on the live `World`."

1. **`first-room` → a deos-js card.** Highest concept-value (the for-what app),
   highest tractability (it already has a gpui-free `Room`/`InhabitantView` that
   is nearly a view-tree). Not even registry-wired — porting it *is* its first
   real presence. Do this first.
2. **`tussle` → a board card.** A *playable verified game* in the image is the
   most demoable single object; the joint-state safety is already forced by
   `SymMemberOf`.
3. **`tool-access-delegation` → an ocap-for-agents card.** The clearest "ocap
   for AI" thesis, Lean-pinned; revoke-as-a-fire is a strong moment.
4. **`nameservice` → the register/resolve/renew/transfer/revoke card.** The
   *template*: once carded, every WriteOnce/Monotonic-caveat app follows the
   pattern (gallery, bounty-board, identity, privacy-voting).
5. **`privacy-voting` → a real card** (NOT its existing HTTP DeosApp). The
   WriteOnce ballot's disabling vote button is the most legible cap tooth.
6. **`polis` → a governance card** (more work: multi-actor `held`).

The deepest structural lever sits under all of these: the **`World` /
`DreggEngine` ledger unification** the registry doc names as out-of-scope. Until
the app substrate ledger and the cockpit `World` engine ledger are one, even a
carded app fires on a side-ledger. Folding app cells into `World`'s engine
ledger (or vice-versa) is the load-bearing refactor that turns "fire + inspect"
into "open and drive the app in the one live image."

---

## Correcting the prior census, explicitly

- ❌ *"`starbridge-apps/` is the real face — all 22 apps are real / ALIVE-RUNS"*
  → **Correction:** "real" there meant *the test passes on real substrate*.
  Zero of the 22 are **deos-era-real** (openable/usable in the live image). They
  are **pre-deos libraries** that predate the cockpit/card/reflective epoch.
- ❌ *"The single highest-value move: add a README to `first-room`."*
  → **Correction:** the highest-value move is to **port `first-room` to a deos-js
  card on the live `World`** — a README finds the *test*, not an *app you can
  open*. Discoverability was the wrong frame; *inhabitability* is the bar.
- ❌ *"`privacy-voting` is ahead of the curve — a composed `DeosApp`."*
  → **Correction:** `DeosApp` is the **HTTP web-surface** generation (06-14),
  *not* a cockpit card. It is still pre-deos by the live-image bar.
- ❌ *Treating the AppRegistry as making apps "wired into the live cockpit."*
  → **Correction:** the registry is a real integration seam (a gadget launcher +
  a shared fire/inspect substrate ledger), but it surfaces apps as **rolodex
  icons firing canned demo turns on a side-ledger**, with **no openable app
  interface in the image**. Registry-wired ≠ deos-real.
