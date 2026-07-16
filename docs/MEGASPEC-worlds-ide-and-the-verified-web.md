# MEGASPEC — The Verified Substrate for Multiplayer Engineering Worlds + The Best IDE

*For Alif. Framed against your two north stars — "grinding out feature enablement for
multiplayer engineering world servers" and "eventually offering the best IDE that ever
existed." This is the map of the substrate underneath both, and the clean seams where
your work plugs in. It is written to REDUCE your surface area, not expand it: most of
what your two goals need is already load-bearing in-tree; this spec says what exists,
what it guarantees, and exactly where you attach.*

---

## 0. The one seam (TL;DR)

Your two goals are, in dregg terms, **the same object seen twice**:

> A **multiplayer engineering world server** is a federation of cells where every action is
> a verified turn and multiplayer is *sound-merge over shared state*.
> **An IDE** is that same world where the shared state is *code* — a patch-theoretic document
> whose every edit is a proven patch and whose merges cannot corrupt.

What the rest of us have been building is the two layers that make both real:

1. **The assurance floor** — every circuit emitted from Lean, byte-pinned, proven; a
   light-client/aggregator can verify world-state or an edit **without trusting the server**.
   (This is the property multiplayer and collaborative editing *both* need, and it's done.)
2. **The delivery layer** — a `<dregg-*>` **capability-resolving Web-Component SDK** that makes
   any world or editor reach **any browser** with honest, progressive trust. Drop a tag in a
   page; it renders + verifies + proves + (with custody) writes.

You own the **world-server domain logic** and the **IDE experience**. We own the **floor** and
the **delivery**. The contract between them is small and named in §7.

---

## 1. The assurance floor — why it matters for worlds + an IDE

The proof stack is not academic garnish; it's the thing that makes a multiplayer world or a
collaborative IDE trustworthy without a trusted server.

- **Everything is emitted from Lean and proven.** Every circuit is a byte-pinned
  `EffectVmDescriptor2` on the p3 descriptor prover; each is proven Rung 0 (the deployed bytes
  ARE the Lean object) → Rung 1 (accept ⟺ the genuine relation) → Rung 2 (no-forgery: the
  adversary is *proven* to fail, with a concrete cheat-witness that's UNSAT) → Rung 3 (the
  binding rides the aggregation fold to the root).
- **Light-client + aggregation soundness (the "Golden Lift").** A client that verifies only the
  aggregated root *sees the binding* — it does not trust the executor. **This is the exact
  property multiplayer needs:** a player verifies "what happened in the world" and a collaborator
  verifies "this edit / this merge was sound" from the proof alone, not from the server's word.
- **The one-sentence spine:** *nothing is trusted at runtime that isn't bound in a proof a
  stranger can check alone.* For your worlds: no player trusts the server about world-state. For
  your IDE: no collaborator trusts that a merge didn't corrupt — it's proven by construction.
- **It's fast.** The old O(n²) single-threaded hand engine is deleted; everything runs on the
  batched descriptor prover. (That whole engine-removal is done and committed.)

**Net for you:** you can build a multiplayer world / an IDE where *the server is not trusted* —
players and collaborators carry proofs, not faith. That is the differentiator no other world
server or IDE has.

---

## 2. The multiplayer world-server substrate (what already RUNS)

A "world server" in dregg is a **federation of world-cells**: shared state, every action one
cap-bounded verified turn, multiplayer via sound merge. The primitives are built and tested:

| crate | what it is | state |
|---|---|---|
| **`WorldCell`** (spween-dregg) | shared world state as a cell; one action = one verified turn admitted iff its gate passes | RUNS |
| **`mud-dregg`** | rooms-as-cells, commands-as-turns; **multiplayer = branch-stitch over the config lattice**; genuine conflicts REFUSED (Settlement Soundness) | RUNS |
| **branch-stitch-multiplayer** (in mud-dregg) | divergent player timelines **merged soundly**; disjoint merges succeed, real conflicts are first-class | RUNS |
| **`collective-choice`** | quorum-gated, one-vote-per-ballot, monotone-tally verified voting; light-client-recomputable tally | RUNS |
| **`spween-dregg`** | verifiable narrative worlds (CYOA / MUD); playthrough is an **un-retconnable receipt chain**; re-verifies by replay | RUNS |
| **`attested-dm`** | un-jailbreakable AI narration — each narration a receipted attested turn; prompt-injection is *refused*, provably (LLM live behind a feature; deterministic in tests) | RUNS |
| **federation seam** (`NodeTarget::Federation`) | flip a world-cell to submit its turns to a real `DREGG_NODE_URL` → **uncensorable shared world** | wired, live-run is the frontier |

**This is your multiplayer engineering world server, minus the engineering-world domain.** The
hard parts — verified turns, sound-merge multiplayer, conflict-as-first-class-state, quorum
decisions, federation — exist. What's missing is *your* domain: the engineering-world objects,
rules, and simulation, expressed as **cell-programs (gates) + turns**. See §7.1 for the seam.

The key merge property is worth stating plainly, because it's what makes a *multiplayer*
engineering world sound: **concurrent edits to shared world-state merge by categorical pushout;
a genuine conflict is a carried STATE, never a corruption or a lost write.** (Same math as the
IDE — §3 — because worlds and code are the same object.)

---

## 3. The IDE substrate — deos-zed + the Dregg Document Language

"The best IDE that ever existed" has a concrete floor in-tree:

- **`deos-zed`** — a *real* Zed / gpui-component code editor rendered as a deos surface. Its `Fs`
  seam is `RealFs` today; the documented next step is **`FirmamentFs`: a file IS a cell, a save
  IS a receipted turn.** (State: PARTIAL — real editor, the cell-backed FS is the wiring.)
- **`dregg-doc` — the Dregg Document Language (DDL)** — this is the crown jewel for collaborative
  editing, and it's **built and tested**. It's Pijul patch-theory realized:
  - a document is a **graph of alive/dead content atoms**, each carrying **provenance** (who
    authored it, in which proven turn);
  - an edit is a **patch** (`Add` / `Delete`-tombstone / `Connect` / `SetField`);
  - concurrent edits are reconciled by **merge = the categorical pushout** (a total graph union)
    — **sound by construction, cannot corrupt**;
  - a **conflict** (two live, mutually-unordered alternatives at one position) is a **first-class
    STATE the document carries** until a later patch resolves it — *never a merge failure.*
  - (This is Mimram–Di Giusto's *A Categorical Theory of Patches* in Pijul's graph-of-atoms
    model. Spec: `docs/deos/DOCUMENT-LANGUAGE.md`. There is a working
    `DocCollabWorld` executor — the in-tab collaborative-document world.)

**Why this is "the best IDE ever," concretely:**
- collaborative editing where **merges provably cannot corrupt** (pushout) and **conflicts are
  carried and renderable, not lost** — the failure mode of every existing collab editor is gone;
- **every edit is a proven patch with provenance** — you can verify *who* wrote a line and *that*
  the edit was sound, without trusting the server or the other collaborators;
- **transclusion of code across projects with authenticated provenance** (§5) — pull a function
  from another repo and its provenance + liveness travel with it (Ted Nelson with physics);
- **AI as a first-class author** whose every edit is a checkable patch — the thing that finally
  makes AI-in-the-loop editing *trustworthy* rather than a diff you squint at;
- and it all runs on the same verified substrate, so an IDE session *is* a multiplayer world.

**Your IDE = `deos-zed` (surface) + `dregg-doc` (collaborative patch-theory core) + the
delivery layer (§4).** The floor is real; the experience is yours to design.

---

## 4. The delivery layer — the `<dregg-*>` capability-resolving Web-Component SDK (the new architecture)

This is the layer that makes your worlds and your IDE **reach anyone, in any browser, with honest
trust**. Its element substrate exists and ships in the extension (state inventory in §6); this
section is its architecture.

### 4.1 What exists to build on
- **`@dregg/sdk`** (`sdk-ts/`, published npm) — a TypeScript SDK; it does *not* bundle wasm.
- **The extension** ("Dragon's Egg Cipherclerk", `extension/`) already injects a `window.dregg`
  provider into pages (MetaMask-shaped) and carries the **whole prover in wasm** (`prove_turn`,
  `verify`, membership/range/conservation proofs) plus a genuinely good **consent UX**
  (`confirm-intent`: a human-readable "faithful reading" of a turn bound to `[turn <hash>]`).
- **`deos-view`** already renders a renderer-agnostic `ViewNode` tree to HTML with
  `data-turn`/`data-slot`, and a proven in-tab loop (click → `deos-affordance` → a real verified
  turn in a wasm world → repaint) exists (`site/dist/cards/tally.html`).

### 4.2 The reframe: from an imperative provider to a declarative element runtime
The imperative provider (`window.dregg.request(...)`) remains for scripts; the element model is
**declarative**: a page drops
`<dregg-world src="…">` / `<dregg-editor doc="…">` / `<dregg-poll src="…">`, and a runtime
**resolves each capability from whatever is present**, degrading honestly.

### 4.3 The core insight — four capabilities, only ONE irreducible
| capability | what it is | polyfillable? |
|---|---|---|
| **RENDER** | cell → shadow-DOM view | ✅ extension-injected **or** page-bundled **or** server-SSR |
| **VERIFY** | re-check a receipt / proof / tally | ✅ anywhere with the wasm verifier — **trustless when client-side** |
| **PROVE** | produce the ZK proof for a turn | ✅ but degrades on *privacy* (extension: witness stays local → page wasm → server: witness leaks). Correctness is fine everywhere. |
| **CUSTODY / SIGN** | authorize a turn with the person's key | ❌ **irreducible** — only the extension **or a passkey/WebAuthn** can hold the key. A page can't sign for the person; a server has no custody. |

So the extension's real job is **custody + private proving + un-forgeable render**; everything
else falls back gracefully.

### 4.4 Shadow DOM = a trust boundary *inside* an untrusted page
Each `<dregg-*>` element renders into an encapsulated **Shadow DOM the host page cannot reach into
to forge**. So the element is the person's *sovereign verified surface embedded in a hostile
browser* — the page can host `<dregg-poll>` but can't lie about what's inside it. Trust scales
with the host: shadow-DOM-encapsulated in Chrome → digest-gated by the verified compositor on
starbridge/sel4 (where the *pixels themselves* are admitted by proof via `servo-render`).

### 4.5 The provider chain + honest trust labeling (the dreggic part)
```
  <dregg-poll> needs { render, verify, prove, custody }, resolved best-available:
    ├─ extension present   → render(injected, un-forgeable) · verify(local) · prove(witness-local) · custody(cipherclerk consent)   — FULL
    ├─ @dregg/sdk bundled  → render(page shadow-DOM) · verify(local wasm) · prove(page wasm) · custody → passkey/WebAuthn, else read-only
    └─ per-origin server   → render(SSR) · verify(server badge) · prove(server; witness leaks) · custody → read-only
```
The element **never hides its tier**: a reflected `trust="extension|sdk|server"` + a visible badge
("✓ verified by your cipherclerk" vs "✓ verified by this site's server (trust the origin)" vs
"⚠ render unverified"). The semantic web's failure was that a claim looked identical whether true
or merely asserted; here the **provenance of the verification itself is surfaced.**

Two settled design calls: **(1) ONE element implementation, capabilities resolved at runtime**
(the extension is a *provider* the uniform element upgrades to — not a separate privileged
element; avoids the custom-element define-once conflict). **(2) custody is a pluggable provider**
with **passkey/WebAuthn as the extension-less floor** — so *writes don't require our extension*;
sovereignty without lock-in.

### 4.6 What "server-mediated per origin" is for (and isn't)
The origin's dregg gateway is the **floor, not custody**: it can *serve the element runtime* (so a
page needn't bundle it) and *serve the receipt chain + a light-client verifier* (so a bare browser
can still SEE and check the verified state). It is **not** for signing (no server custody), and
server-side *proving* carries the honest caveat that the witness leaves the person's machine.
"View + verify anywhere; write + privacy is what the person's agent buys."

**Net for you:** a `<dregg-world>` / `<dregg-editor>` reaches *any* browser. Read + verify works
everywhere (even with no extension); write (custody) + privacy (local proving) + un-forgeable
render come with the person's agent. Same tag, honest trust, no lock-in.

---

## 5. The convergence: the semantic web, finally given physics

The old semantic web had *meaning* but no *physics* — `<claim about="…">` was inert, a `<link>`
was a dead reference, a `<vote>` was just a tag. dregg supplies the physics:
- **`<dregg-atom>`** carries *verifiable provenance* — a claim you can check, not just read.
- **`<dregg-transclude src="dregg://…">`** is Nelson's dream *authenticated and live* — pull a
  fragment (a doc atom, a world object, a code function) and its provenance/liveness/verifiability
  travel with it. A reference with *forces*.
- **`<dregg-poll>`** actually tallies (quorum, one-vote-per-ballot). The tag *does* something.
- an **edit is a proven patch**, concurrent edits **merge by pushout**, a **`<dregg-conflict>`**
  renders both live alternatives because conflict is first-class.
- and **AI can author and traverse the whole mesh**, with every atom it writes checkable.

Web Components are the native browser primitive for exactly this — encapsulated, composable,
transcludable DOM fragments with their own verified behavior. For your IDE this is the deep prize:
**code as a transcludable, provenance-carrying, soundly-merging hypermedia**, editable
collaboratively, verifiable by strangers, and authorable by AI — in a browser or on the OS.

---

## 6. Honest state inventory (RUNS / PARTIAL / FRONTIER)

**Assurance floor — DONE:** hand STARK engine deleted; all circuits on the descriptor
prover; Golden Lift (light-client + aggregation soundness) proven and wired; 7 emitted-descriptor
forgery bugs found *by proving* and fixed; predicate-comparison descriptors emitted. Axiom-clean.

**World / IDE substrate — RUNS:** `spween-dregg`, `collective-choice`, `mud-dregg`,
`dregg-governance` (governance = community = story, modulo two-vote-engines-not-yet-one-crate),
`attested-dm`, `dregg-doc` (the DDL), `deos-view`, `deos-web-cells` (transclusion/provenance
library), `deos-reflect`, `deos-js-runtime`. **PARTIAL:** `deos-zed` (real editor; FirmamentFs is
the wiring), `deos-leptos`, `deos-matrix`, `deos-terminal`.

**Delivery layer — RUNS the element substrate; FRONTIER the specializations (§8):** the
`<dregg-*>` Custom Elements exist and ship in the extension — `dregg-poll`, `dregg-doc`,
`dregg-embed`/`dregg-transclude`, `dregg-story`, `dregg-descent`, `dregg-sprite`
(`extension/src/elements/*.ts`), each a **closed**-shadow-root view with a reflected `trust=…`
tier + visible badge, fail-closed on an unresolved port; the engine (background) owns
wasm/keys/caps, the element only marshals port requests. The passkey/WebAuthn custody floor is
implemented (`extension/src/passkey.ts` — PRF-wraps the dregg mnemonic; fail-closed, never a
weak-KDF fallback). The wasm prover rides the deployed descriptor path: `wasm/src/lib.rs` routes
proofs through `prove_vm_descriptor2` / `verify_vm_descriptor2` with fail-closed
`descriptor_by_name` dispatch, and the extension ships built artifacts
(`extension/dist/dregg-cipherclerk-{chrome.zip,firefox.xpi}`, `extension/dregg_wasm_bg.wasm`).
**FRONTIER:** `<dregg-world>` / `<dregg-editor>` (no such elements yet), and the extension-less
provider tiers of §4.5 (page-bundled `@dregg/sdk` render/verify, per-origin SSR) — today's
elements resolve through the extension port.

---

## 7. The seams — where YOUR work plugs in (the small contract)

### 7.1 Multiplayer engineering world server
- **You build:** the engineering-world domain — objects, rules, simulation — as **cell-programs
  (gates) + turns** over `WorldCell`s, and the multiplayer topology as **branch-stitch** sessions.
- **You get for free:** verified turns, sound-merge multiplayer (pushout), conflict-as-state
  (Settlement Soundness), quorum decisions (`collective-choice`), federation
  (`NodeTarget::Federation`), and light-client verifiability (a player checks the world without
  trusting the server).
- **The seam:** a world is a set of cells + a gate program per action; an action is a turn; the
  merge is the config-lattice pushout. You express engineering-world *semantics*; the substrate
  enforces *soundness*.

### 7.2 The IDE
- **You build:** the editor experience on `deos-zed`, and the code-document model on the DDL.
- **You get for free:** patch-theoretic collaborative editing (sound merge, conflict-as-state,
  provenance per atom), file-as-cell / save-as-turn (`FirmamentFs`), transclusion, verifiability,
  AI-authored-and-checkable edits.
- **The seam:** `FirmamentFs` (file ↔ cell), the DDL `Patch` API (edit ↔ patch), and a
  `<dregg-editor>` element for the web/embedded surface.

### 7.3 The delivery
- **We build + own:** the `<dregg-*>` capability-resolving Web-Component SDK, the extension's
  custody/consent/prove providers, the passkey floor, honest trust labeling, and the
  servo/compositor path for the verified-pixel surface.
- **You consume:** drop a `<dregg-world>` / `<dregg-editor>` into any page (or the OS surface) and
  it renders + verifies + proves + writes, progressively trusted.

---

## 8. Immediate frontier (focused — the next moves, in order)

Standing under this list: the extension wasm rides the descriptor prover, the element substrate
(closed Shadow DOM + trust badge + fail-closed lifecycle, shared via `DreggElement`) exists, the
poll/doc/transclude/story/descent/sprite specializations exist, and the passkey custody floor is
implemented (§6). What remains:

1. **`<dregg-world>`** — the engineering-world surface as an element. The specialization pattern
   is established (`extension/src/elements/`); the world element does not exist yet.
2. **`<dregg-editor>`** — the DDL *editing* surface. `<dregg-doc>` renders (transclusion +
   conflict-as-state); the collaborative editor affordance surface is the gap.
3. **The extension-less provider tiers** (§4.5): page-bundled `@dregg/sdk` render/verify and the
   per-origin SSR floor, resolved best-available by the same elements — so read + verify reach a
   bare browser. (Custody already has its extension-less floor: the passkey provider.)

---

## Appendix — the load-bearing files (for grounding, not reading in full)

- Assurance: `metatheory/Dregg2/Circuit/Emit/*` (emitted descriptors + Rung 0/1/2),
  `*BindingFromFold.lean` (the fold carriers), `circuit/src/descriptor_ir2.rs`,
  `circuit/src/descriptor_by_name.rs`.
- Worlds: `spween-dregg/src/world.rs`, `mud-dregg/`, `collective-choice/src/lib.rs`,
  `dregg-governance/src/lib.rs`, `docs/deos/SPWEEN-ON-DREGG.md`.
- IDE: `deos-zed/`, `dregg-doc/src/lib.rs`, `docs/deos/DOCUMENT-LANGUAGE.md`.
- Delivery: `deos-view/src/web.rs`, `deos-web-cells/src/lib.rs`, `sdk-ts/` (`@dregg/sdk`),
  `extension/` (`src/page.ts` = `window.dregg`, `confirm-intent-script.js`, `dregg_wasm.js`),
  `wasm/` (the in-tab worlds + prover), `servo-render/` (verified-pixel compositor path).

*The floor is proven and fast. The worlds and the document language run. The delivery elements
run in the extension; the remaining delivery frontier is the world/editor specializations and
the extension-less provider tiers. Your two north stars stand on this; the seams are small and
named.*

---

## 9. Netlayer, same-origin, devtools, frameworks (the delivery details)

Four dimensions that shape how `<dregg-*>` reaches real browsers. The headline: **content-
addressing + proofs make the transport untrusted, which dissolves most same-origin anxiety.**

### 9.1 The netlayer — a FIFTH capability, and the transport is UNTRUSTED
Fetching a `dregg://` object is upstream of render/verify. But `dregg://` objects are
content-addressed (blake3) and proof-verified, so **you don't trust *where* you got the object —
you verify the hash + its receipt/proof.** A hostile CDN/gateway/peer cannot forge (a bad byte
fails the hash; a bad state fails the proof). FETCH resolves through the provider chain:
`extension netlayer (attested, cached, cross-origin) → @dregg/sdk direct-to-gateway → per-origin
server`. The extension netlayer's superpower is not more trust (you verify regardless) but
**reach**: a background service worker with cross-origin privileges does **cross-federation reads
a page's own `fetch()` can't** (CORS-blocked), caches across origins, and multiplexes node
connections. `window.dregg.fetch("dregg://…")` routes there.

### 9.2 Same-origin / CORS — mostly dissolved
Because content is self-verifying, **CORS is a plumbing boundary, not a security one.** SDK-only
(no extension) is limited to CORS-enabled/per-origin gateways — a plumbing limit, still safe.
Extension present → cross-origin privileges unlock **cross-federation transclusion**
(`<dregg-transclude src="dregg://otherfed/…">`) that raw page `fetch` can't reach. "Verify the
content, don't trust the source" is the whole resolution.

### 9.3 Devtools — the verified-substrate inspector (and the IDE debugger)
A **Dregg devtools panel** (`devtools_page` + `devtools.panels.create`, both Firefox + Chromium):
the cells on the page, each `<dregg-*>` element's committed slots + **turn/receipt history** + live
re-verification + its **trust tier** (extension/sdk/server); plus an Elements-inspector sidebar
pane so selecting a `<dregg-poll>` shows its cell URI + receipt chain + `[verified]` state. This is
the browser cousin of `deos-reflect` / the moldable inspectors, and it is **the debugger for the
worlds and the IDE**. Build early — it makes everything legible.

### 9.4 Browsers — Firefox-first WebExtensions (which *strengthens* the netlayer)
Target WebExtensions, **Firefox-first, Vivaldi/Chromium-compatible, no Chrome-only APIs**
(`extension/manifest-firefox.json` exists). Firefox keeps the **full `webRequest`** (real
interception/redirect) that Chromium MV3 gutted, plus richer `protocol_handlers` — so the deep
`dregg://` netlayer is *more capable on the primary browsers*. Vivaldi rides the reduced MV3 path;
a Chrome-only nicety only "if we had to."

### 9.5 Frameworks — htmx is home, React is free (via the standard)
**Web Components are framework-agnostic by standard**, so a `<dregg-poll>` works in plain HTML
*and* React 19 (props + events now clean) *and* Vue/Svelte/Solid — consuming custom elements is a
web standard, not a favor. So: **don't build a React-first SDK**; build *well-behaved custom
elements* (attribute/property reflection, real events); a thin optional `@dregg/react` wrapper is a
courtesy, not the architecture. The **htmx timeline is the native home**, two ways: (1) custom
elements = declarative hypermedia components; (2) the **`data-turn`/`data-slot` attribute API** is
literally htmx-flavored progressive enhancement — put `<button data-turn="vote" data-arg="0">` on
*any* element and it's a verified affordance (htmx has `hx-*`; dregg has `data-turn`, plus physics).
HTML + custom elements + the attribute API is the primary dreggic surface; frameworks are welcome
tourists on the same standard.
