# DREGG-WEB — working spec for the `<dregg-*>` delivery layer

*Our driver (not the Alif-facing megaspec — that's `MEGASPEC-worlds-ide-and-the-verified-web.md`).
This is the consolidated architecture + the decisions we've locked + the build roadmap for the
dreggic collectivity web: a capability-resolving Web-Component substrate that puts verified cells,
worlds, votes, and documents into any browser, honestly trusted, no lock-in.*

## The thesis (one paragraph)

Every dregg surface is a **Web Component** whose Shadow DOM is an encapsulated, self-verifying
render of a **cell**, holding its own in-tab verified executor, firing proven turns the person's
cipherclerk signs. The *same* element renders in a plain page (shadow-DOM trust boundary), in the
extension (custody + private proving + un-forgeable render), and — via `servo-render` — on
starbridge/sel4 (pixels digest-gated by the verified compositor). It is the **semantic web given
physics**: `dregg://` objects are content-addressed + proof-verified, so the transport is untrusted
and the content self-certifies; transclusion becomes an *authenticated, live* reference; a `<vote>`
actually tallies; an edit is a proven patch; a conflict is first-class. htmx is home; React is free
via the standard; AI can author the whole mesh with every atom checkable.

---

## Pillar 1 — The capability model (the crux)

A `<dregg-*>` element needs FIVE capabilities. **Only CUSTODY is irreducible**; the rest degrade
gracefully. The element resolves each from the best-available provider and **labels its trust tier
honestly**.

| capability | what | provider chain (best → floor) |
|---|---|---|
| **FETCH** | get a `dregg://` object + its proof/receipt | extension netlayer (attested, cached, cross-origin) → `@dregg/sdk` direct-to-gateway → per-origin server |
| **RENDER** | cell → Shadow-DOM view | extension-injected (un-forgeable) → page-bundled SDK (shadow-encapsulated) → server-SSR |
| **VERIFY** | re-check receipt / proof / tally | client wasm (trustless) anywhere → server "verified" badge (trust origin) |
| **PROVE** | produce the ZK proof for a turn | extension (witness stays local) → page wasm (witness in page) → server (witness leaks). Correctness fine everywhere; *privacy* degrades. |
| **CUSTODY / SIGN** | authorize a turn with the person's key | **irreducible**: extension cipherclerk → passkey/WebAuthn → read-only |

**Trust labeling** is the dreggic differentiator: a reflected `trust="extension\|sdk\|server"` +
a visible badge ("✓ verified by your cipherclerk" vs "✓ verified by this site's server (trust the
origin)" vs "⚠ render unverified"). The semantic web's failure was a claim looking identical
whether true or asserted; here **the provenance of the verification itself is surfaced.**

**Custody is a pluggable provider** — extension → passkey → read-only — so *writes don't require
our extension*. Sovereignty without lock-in.

## Pillar 2 — Content-addressed → the transport is UNTRUSTED

`dregg://` objects are blake3-content-addressed and proof-verified. **You never trust *where* you
got an object — you verify the hash + its receipt.** A forged byte fails the hash; a forged state
fails the proof. Consequences:
- **CORS is plumbing, not security.** Fetch from anywhere; the content self-certifies.
- **SDK-only** is limited to CORS-enabled/per-origin gateways (a plumbing limit, still safe).
- **Extension netlayer's superpower is REACH, not trust** — cross-origin privileges do
  **cross-federation reads** (`<dregg-transclude src="dregg://otherfed/…">`) a page's `fetch()`
  can't; caches across origins; multiplexes node connections. `window.dregg.fetch("dregg://…")`.

## Pillar 3 — Shadow DOM = a trust boundary inside a hostile page

Each element renders into an encapsulated Shadow DOM **the host page cannot reach in to forge.** A
page can host `<dregg-poll>` but can't lie about what's inside it. Trust scales with the host:
shadow-DOM-encapsulated in Firefox/Chromium → **digest-gated pixels** on servo-render + the verified
compositor (T1/T2/T3 Lean scene teeth) on starbridge/sel4, where the *render itself is in the proof*.

## Pillar 4 — The element catalog + one substrate

**One base element** (`class DreggElement extends HTMLElement`): `attachShadow({mode:open})` →
mint its OWN per-instance wasm world (from `src`/attrs, NOT a global) → render the world's
`view_tree` into the shadow root → wire clicks **scoped to the shadow** (page can't inject
affordances) → fire verified turn → repaint → re-run the light-client check → reflect
`[verified]` + `trust`. Specializations differ only by which world + renderer:

| element | world | what it is |
|---|---|---|
| `<dregg-card>` | generic (CardWorld) | the substrate proof — any cell as a card |
| `<dregg-poll>` | `collective-choice` | verifiable, quorum-gated, one-vote-per-ballot vote — droppable |
| `<dregg-doc>` / `<dregg-editor>` | `dregg-doc` (DDL) | patch-theoretic doc: transclusion, provenance, conflict-as-state |
| `<dregg-world>` | `WorldCell` / mud-dregg | a multiplayer world surface (Alif's domain plugs in) |
| `<dregg-transclude src="…">` | — | authenticated, live transclusion (nested custom element + provenance) |

**Plus the attribute API** (htmx-flavored progressive enhancement, *already the current pattern*):
`<button data-turn="vote" data-arg="0">` on *any* element → a verified affordance; `data-slot`
binds re-read the ledger. htmx has `hx-*`; dregg has `data-turn`/`data-slot`, plus physics.

## Pillar 5 — The DDL + transclusion = the semantic web with physics

`dregg-doc` (Pijul patch-theory, built): document = graph of provenance-carrying atoms; edit =
patch; merge = categorical **pushout** (cannot corrupt); **conflict = first-class carried STATE**.
Realized at the DOM:
- `<dregg-atom>` — verifiable provenance (who authored it, in which proven turn).
- `<dregg-transclude>` — Nelson authenticated + live: pull a fragment (doc atom / world object /
  code function) and its provenance/liveness/verifiability travel with it.
- `<dregg-conflict>` — renders both live alternatives (conflict isn't corruption).
- AI authors and traverses the mesh; every atom it writes is a checkable patch.

## Pillar 6 — Frameworks: htmx home, React free

Web Components are framework-agnostic by standard → `<dregg-poll>` works in plain HTML *and* React
19 (props+events clean) *and* Vue/Svelte/Solid. **Don't build a React-first SDK** — build
well-behaved custom elements (attribute/property reflection, real events); a thin optional
`@dregg/react` wrapper is a courtesy. HTML + custom elements + the `data-turn` API is the primary
dreggic surface.

## Pillar 7 — Devtools (build early — it makes everything legible)

A **Dregg devtools panel** (`devtools_page` + `devtools.panels.create`, Firefox + Chromium): cells
on the page, each element's committed slots + **turn/receipt history** + live re-verification + its
**trust tier**; + an Elements sidebar pane (select `<dregg-poll>` → cell URI + receipt chain +
`[verified]`). The browser cousin of `deos-reflect` — and **the debugger for the worlds and the IDE.**

---

## The seam (grounded in the real code)

- **`deos-view`'s `web` feature is gpui-free/serde-only and a wasm dep** (`wasm/Cargo.toml:73`:
  `deos-view = { …, default-features = false, features = ["web"] }`). ViewNode→HTML runs in wasm.
- **Worlds render in-wasm**: each world exposes `render_html()` (`CardWorld` at
  `wasm/src/bindings_card.rs:260`; the shared walk `render_world_html` at `:106` goes through
  `deos_view::render_html`), alongside `fire(turn,arg)` + `read`. The document worlds
  (`DocCollabWorld`, `DocTextWorld` — `wasm/src/bindings_doc.rs`) render through the same renderer.
- **`PollWorld` exists** (`wasm/src/bindings_card.rs:1238`) — the real `collective-choice`
  engine's shape as an in-tab world over the wasm `DreggRuntime` executor (re-implemented there
  rather than depending on the axum-bound crate).
- **The loop lives in per-instance, shadow-scoped elements** (`extension/src/elements/`):
  closed-shadow thin views in the page, engines in the background (the split is
  `DREGG-QUIET-UPGRADE.md` §3). `site/dist/cards/tally.html` remains the server-baked page shape.
- **Providers that exist**: extension injects `window.dregg` (`extension/src/page.ts`); `@dregg/sdk`
  (`sdk-ts/`, npm, no bundled wasm); `confirm-intent` faithful-reading consent UX; the extension
  netlayer (`extension/src/netlayer.ts`) resolves `dregg://` behind fail-closed content-addr +
  attestation gates.

---

## Build roadmap — status

0. **✅ wasm on the current descriptor prover** — the client-side prover is current +
   soundness-fixed.
1. **✅ `render_html()` in-wasm + `PollWorld`** — every world renders its own `view_tree` through
   `deos-view`'s web renderer inside wasm; `PollWorld` mirrors `CardWorld`.
2. **✅ The substrate element** — realized as per-kind thin-view elements sharing the port
   plumbing (`extension/src/elements/`, `cell-port.ts`) rather than a single `<dregg-card>` tag:
   the element is a VIEW (closed shadow, scoped affordance wire, honest badge, `trust` attr); the
   world/keys live in the background engine. There is no `<dregg-card>` element; `CardWorld` is
   the substrate world.
3. **✅ `<dregg-poll>`** — a plaintext `dregg://poll/…` on an opted-in origin upgrades to a live,
   votable, fail-closed thin view (`elements/dregg-poll.ts` + the `detect.ts` scanner).
4. **✅ Capability providers + FETCH netlayer** — extension `window.dregg` (`page.ts`),
   `@dregg/sdk` (`sdk-ts/`), passkey custody (`extension/src/passkey.ts`), and the
   content-addr-gated netlayer (`netlayer.ts`, wired in the background when a node URL is
   configured).
5. **✅ `<dregg-doc>` / `<dregg-transclude>`** — the DDL + authenticated transclusion
   (`elements/dregg-doc.ts`; `elements/dregg-embed.ts` + `dregg-transclude.ts` over
   `cell-port.ts`).
6. **Devtools panel** — not built (no `devtools_page` in either manifest).
7. **`@dregg/react`** courtesy wrapper (typed props + a hook) — not built.
8. **`<dregg-world>` / `<dregg-editor>`** — not built (the surfaces Alif's domain plugs into).

## Decisions locked

- **ONE element implementation, capabilities resolved at runtime** (not a privileged/fallback
  element split — avoids the custom-element define-once conflict; the extension is a *provider* the
  uniform element upgrades to).
- **Custody pluggable** with **passkey/WebAuthn as the extension-less floor** — writes without our
  extension.
- **Content-addressed → untrusted transport** — verify content, don't trust source; the same-origin
  resolution.
- **Firefox-first WebExtensions**, Vivaldi/Chromium-compatible, no Chrome-only APIs (Firefox's full
  `webRequest` + `protocol_handlers` *strengthen* the netlayer).
- **htmx-primary, React-free-via-standard** — well-behaved custom elements, not a framework SDK.

## Open questions

- **Where does the SDK live** — the extension-delivered elements live in `extension/src/elements/`;
  the page-bundled (`sdk`) tier has no element runtime yet. Evolve `@dregg/sdk` (`sdk-ts/`) into
  it, or a new package (`@dregg/elements`)? (Lean: evolve `sdk-ts`, add an `elements` entry.)
- **Devtools vs closed shadow** — the closed roots are deliberately unreachable from the page; the
  panel likely needs a privileged inspection channel through the background.

(Settled by the code: `collective-choice` runs in-tab as `PollWorld` — a re-implementation of the
engine's shape over the wasm executor, not a compile of the axum-bound crate; render is
`render_html()` in-wasm, one artifact; the poll shipped first, with no separate `<dregg-card>`.)

---

*Underneath: the assurance floor is proven + fast (engine deleted, descriptor prover, Golden Lift,
light-client-sound). The substrate, the collective vote, and the document each run as proven,
encapsulated, self-verifying elements; the remaining rungs are the devtools panel, the React
courtesy wrapper, and the world/editor surfaces.*
