# The Visitor-Side Verification Weld

*Grounded 2026-07-08 (two scouts, file:line receipts). Goal: make this sentence deployed fact,
not design goal: "a visitor's browser independently checks that bytes served from `*.dregg.works`
match the site's on-ledger commitment; a tampering host cannot strip the check."*

## Ground truth (verified live, 2026-07-08)

- `hello.dregg.works` serves **plain HTML, no verifier** — byte-verbatim from the DreggNet
  gateway's `SiteRegistry` (`~/dev/DreggNet/webapp/src/hosting.rs:221-240`; live-probed).
- Its commitment is the gateway's **off-ledger** ed25519 receipt chain over a Poseidon2
  content-root (`webapp/src/hosting.rs:1036-1096`, `SiteRegistry::signed` :746-767). The
  `/.well-known/dregg-receipt.json` trustless-read exists only in the portable binaries — the
  deployed gateway never dispatches it (live probe: 404).
- The **on-ledger** publish path is real and live in breadstuffs — `publishMinisite`
  (`portal/src/drive-actions.mjs:65-83`): a cap-gated signed turn writing
  `SITE_CONTENT_SLOT(0) = blake3(bytes)` per `starbridge-web-surface/src/web_of_cells.rs:10-21`
  — **but nothing currently served on `*.dregg.works` was published through it.**
- `site/dregg-works/verify-badge.js` has the whole check (verified standalone blake3 →
  `GET /api/cell/{id}` → compare `fields[0]`, refuse-on-mismatch) but is **page-delivered and
  page-configured** — strippable AND cell-swappable. Its default node is the dead devnet.

## The two-sided architecture — one core, two skins

A page cannot verify itself: a tamperer strips (or re-points) anything the host serves. The
checker must live in something the **visitor** installed:

1. **Their browser → the extension** (`extension/` — the MV3 cipherclerk; builds clean, TS
   green, wasm bundle already exports `blake3_hash`; rot is *endpoint defaults only*).
2. **Our browser → the starbridge servo pane** — verification as a property of *loading*:
   bytes hashed at the net-cap choke point, verdict chip in-band, fail-closed option.
   (Servo scout in flight; section below to be grounded when it reports.)

Both consume one verification core: `fetch bytes → blake3 → read committed slot 0 → compare →
verdict`, with the same refusal discipline (a failed check is never a pass).

## The load-bearing security decision: hostname → cell binding

Page-supplied cell ids (`data-cell`, meta tags) are not merely strippable — they are
**swappable**: a tamperer points the check at their own cell whose slot 0 matches the tampered
bytes. verify-badge.js is defeated this way *even when present*. The binding must be
out-of-band: an extension-held mapping seeded from **one pinned registry cell id** shipped in
extension defaults (genesis-anchor pattern), whose slots/events carry `name → site-cell-id`.
The on-ledger vocabulary exists (`starbridge-apps/nameservice`, `starbridge-apps/domains`);
the name→cell *read endpoint* does not yet.

## What already works (don't rebuild)

- Node `GET /api/cell/{id}` is public and returns `fields[]` (`node/src/api.rs:1594`, :4035);
  CORS **always admits `chrome-extension://` / `moz-extension://` origins** (`api.rs:1484-1488`)
  — zero manifest/server changes needed for the extension's commitment read.
- Extension chassis: content script on `<all_urls>` at `document_start`, background node-fetch
  plumbing, settings-page endpoint override (`extension/src/endpoints.ts:19-23`).
- Tab-side LC scaffolding: `verify_slot_opening` (`wasm/src/bindings_lightclient.rs:726-775`)
  reproduces the heap-path fold; the portal cell page already consumes openings gracefully
  (`portal/dist/cell.html:126-141`). Missing half = the node serving per-slot openings.

## The plan, effort-ranked

1. **Endpoint-default sweep (hours).** Kill dead `devnet.dregg.fg-goose.online` defaults:
   `extension/src/endpoints.ts:17`, `extension/manifest.json:19-20`,
   `site/dregg-works/verify-badge.js:142`, `transclude.js:158`, `sdk/src/endpoints.rs:53`.
   Point at the live read surface (portal.dregg.studio/api or a dedicated node host).
2. **The extension verifier module (a day).** On `*.dregg.works`: content script re-fetches
   `location.href` (`cache: "no-store"`, same-origin, no new permissions) → background blake3
   (bundled wasm) → `GET <node>/api/cell/<cell>` (node base from settings, never the page) →
   compare → per-tab action badge ✓/✕ + mismatch overlay. Lift verify-badge.js's check logic
   verbatim; its trust anchoring is exactly what moving into the extension fixes.
3. **Hostname→cell binding (days — the real design work).** Pinned registry cell + name-lookup
   read (node endpoint or client-side registry-event scan). Without this the weld is spoofable.
4. **Publish/serve unification (days).** A breadstuffs-native site-serving path (DreggNet is
   abandoned-as-product; no `SiteRegistry` port exists yet) so the flagship `*.dregg.works`
   sites are the SAME bytes committed by the on-ledger blake3 slot-0 turn. Serve is already
   byte-verbatim, so this is publish-plumbing, not a format change.
5. **LC-verifiable commitment read (a lane).** Node endpoint serving per-slot heap openings;
   tab side is ready. Until then the commitment read is trusted-node — mitigate by querying
   ≥2 nodes and cross-checking, and SAY "trusted-node" in the extension UI.
6. **Multi-asset manifest discipline (later).** Slot 0 = blake3 of a path→blake3 manifest;
   verify manifest, then each fetched asset. DreggNet's content-root/`dregg-deploy` manifest is
   the design reference (but Poseidon2/off-ledger — don't import wholesale).

## The starbridge-native half (scout in flight)

To be grounded: servo byte-interception points (embedder traits vs internal fetch), the net-cap
choke point, dregg:// as the already-verified path, verdict-chip UX slots, fail-closed precedent.
One core, two skins — the native skin should share the hash/compare/refusal core with the
extension via the wasm/Rust boundary, not duplicate it.

## Honest UI language (binding, per the register)

Until rung 5: the extension says "checked against a node you chose" (trusted-node), never
"proven". Until rung 4: `*.dregg.works` flagship pages say "commitment: gateway receipt chain"
distinctly from "commitment: public ledger". The site copy at dregg.net/try and /deep already
carries this split (corrected 2026-07-08, twice).
