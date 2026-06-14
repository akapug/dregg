# Desktop OS / Servo-forward — BUILD STATUS

*Present-tense status of what is built in code vs. what is frontier, for the
desktop / web-surface research in this directory. The vision is settled in
[ARCHITECTURES.md](ARCHITECTURES.md), [DISTRIBUTED-SERVO-FACETS.md](DISTRIBUTED-SERVO-FACETS.md),
and [EXPLORATIONS.md](EXPLORATIONS.md); this note records the first compiling,
tested slice of it.*

## The cap discipline is REAL in code, two layers down

The desktop's central claim — **a window IS a `Capability{ target:
Surface(cell), rights }` on the one `(target, rights)` handle** — is not a
proposal. It is built and tested in `sel4/dregg-firmament/`:

- `Target::Surface { cell: CellId }` is a real third variant beside
  `Local{slot}` and `Distributed{cell}` (`sel4/dregg-firmament/src/lib.rs`).
  `Capability::surface(cell, rights)` mints one; it attenuates through the SAME
  `is_attenuation` (`granted ⊆ held`) gate as every other cap, with no
  special-casing.
- `SurfaceBacking` (`sel4/dregg-firmament/src/surface.rs`) implements the five
  cap-confined surface verbs — **create-surface / present / embed / grant-input
  / revoke** — against a REAL `dregg_cell::Ledger` + `dregg_turn::TurnExecutor`.
  `embed` runs the genuine `Effect::Introduce` (the four `apply_introduce`
  premises); a widening surface grant is rejected by the real executor with
  `DelegationDenied`; revoke darkens the glass synchronously at `n = 1`. All
  green in that crate's own tests.
- `compositor_pd` (`sel4/dregg-firmament/src/compositor_pd.rs`) is the minimal
  framebuffer multiplexer enforcing the scene teeth (T1 non-overlap / T2
  label-binding / T3 focus) on the EmulatedKernel.

So the firmament's "first milestone" from ARCHITECTURES.md (add `Target::Surface`
and prove it composes) is **landed**.

## NEW: `starbridge-web-surface/` — the web-specific layer

`/Users/ember/dev/breadstuffs/starbridge-web-surface/` is a standalone crate
(its own empty `[workspace]`, path-deps on the real `dregg-firmament` /
`dregg-cell` / `dregg-types`; builds with `cd starbridge-web-surface && cargo
test` without touching the root workspace — the `pg-dregg` / `dregg-firmament`
pattern). It is the WEB-SPECIFIC layer over the already-real surface cap model
and binds — never reinvents — the real types. Two deliverables:

### 1. The embedded web surface as a cap gate (`src/delegate.rs`)

Realizes [EMBEDDED-WEB-SURFACE.md](../EMBEDDED-WEB-SURFACE.md) §2/§4.1:

- `WebSurfaceDelegate` — a trait shaped one-to-one against libservo's real
  `WebViewDelegate`: `load_web_resource` / `allow_navigation` /
  `request_open_auxiliary_webview` / `request_permission` / `authenticate`.
- `SurfaceCapability` — a web surface IS a firmament `Capability{
  Surface(cell), rights }` (the real handle), carrying the web-relevant
  attenuations (the fetch/navigate origin allowlists, the permission set) as
  narrow-only caveats on top.
- `CapGatedDelegate` — a real impl where **each callback discharges the held
  cap**: a navigation/fetch/permission the cap does not permit is refused at the
  callback. The new-window mint (`request_open_auxiliary_webview`) routes through
  the GENUINE `dregg_cell::is_attenuation` — an iframe/popup is an attenuation
  that **cannot amplify** (the no-amplification keystone): a child asking to
  reach a new origin, or to widen window rights, is refused exactly as a widening
  window-share is `DelegationDenied`.
- Tests (green): a navigation the caps allow succeeds + commits the URL; one they
  don't is refused + leaves the committed URL untouched; an in-allowlist fetch
  continues while an out-of-allowlist fetch is intercepted with a cap-denied
  body; an attenuated child can fetch LESS than its parent; a child that tries to
  amplify (new origin, or wider window rights) is refused; permissions are
  default-deny and narrow-only; credentials are returned only for a scoped
  origin.

### 2. The `dregg://` web of cells (`src/web_of_cells.rs`)

Realizes [DISTRIBUTED-SERVO-FACETS.md](DISTRIBUTED-SERVO-FACETS.md) Facet 1:

- `DreggUri` — a `dregg://<cell>` link is a sturdy ref into a cell (the origin's
  content-addressed `CellId`).
- `WebOfCells::publish` commits a page's content hash into a REAL surface cell's
  state (slot 0) + binds a committed URL; `WebOfCells::fetch` resolves the
  `dregg://` ref as a verified cross-cell read returning an `AttestedResource`.
- `AttestedResource` — the attested-content envelope: `content_bytes` +
  `content_hash` (`blake3`) + `receipt_hash` + a GENUINE
  `dregg_types::AttestedRoot` whose `receipt_stream_root` is the REAL
  `merkle_root_of_receipt_hashes` (issue #80's v4 binding). `verify()` runs the
  full client-side chain — content-addressed → receipt-in-stream → real
  `AttestedRoot::verify_receipt_stream` reconstruction → quorum — and on any
  failure the caller renders "dregg: unattested content", never the bytes.
- `OriginChrome` — the trusted-path origin badge is drawn from the LEDGER (cell
  id + committed URL + the rights lineage + finality), never the page. A phishing
  page body's `https://yourbank.com` string does not appear in the badge.
- Tests (green): a `dregg://` ref is fetched end-to-end and its attestation
  verified; tampered content fails verification; a forged receipt-stream root is
  rejected; a node serving uncommitted bytes is caught at fetch; the origin
  chrome is derived from the ledger not the page.

A runnable demo of both facets:
`cd starbridge-web-surface && cargo run --example web_of_cells_demo`.

## The LIBSERVO SEAM — exactly where the real engine plugs in

The heavy libservo dependency (a multi-MB Rust codebase + a Metal/wgpu toolchain
that does not build cleanly in this environment) is **deliberately not linked**.
The seam is a single documented type, `MockSurface<D: WebSurfaceDelegate>`
(`starbridge-web-surface/src/delegate.rs`), standing in for the libservo
`WebView`, with a `// LIBSERVO SEAM` block giving the exact `WebViewDelegate`
impl that forwards each callback to `CapGatedDelegate`. Everything the gate
checks against — the cap model, `is_attenuation`, the no-amplification mint, the
`AttestedRoot` chain — is the REAL dregg machinery and is unchanged when the seam
closes. Only `MockSurface` is replaced.

## What the full build will still need (reported, not worked around)

These are the precise gaps the real (libservo-linked, full-executor) build
surfaces. None is reinvented here; each is named:

- **`Target::Surface` already exists** — no firmament change is needed for the
  surface cap itself. (The earlier "add the variant" milestone is done; this
  crate confirms it by building directly on `Capability::surface`.)
- **A web-relevant `EffectMask` facet.** Today the web caveats (fetch/navigate
  allowlists, permissions) live in `starbridge-web-surface`'s `SurfaceCapability`
  on top of the firmament window rights. ARCHITECTURES.md L7 / EMBEDDED-WEB-
  SURFACE.md §2 call for these to ride the real `cell/src/facet.rs` `EffectMask`
  (the free bits 24–31: `EFFECT_SURFACE_PAINT`/`RECEIVE_INPUT`/… and web
  facets). The `EffectMask` narrowing machinery is already proven non-vacuous
  (`rejects_effect_mask_widening`); assigning the web-relevant bits and moving
  the allowlists onto `CapabilityRef.allowed_effects` is the additive follow-up.
  Needs: no new mechanism — bit assignments in `cell/src/facet.rs` (a main-loop
  edit, not this crate's).
- **The fetch as a full executor turn.** The `dregg://` serve is modeled as a
  verified cell read against a real ledger whose surface cell carries the content
  commitment in slot 0, with a serve-receipt hashed into a real `AttestedRoot`.
  Wiring the serve as a full `Effect`-bearing `TurnExecutor` turn — so the
  receipt is the executor's own `TurnReceipt` (`turn/src/turn.rs`,
  `turn/src/witnessed_receipt.rs`), chained on the per-agent receipt chain — is
  the `ServedResourceCell` app-toolkit template (DISTRIBUTED-SERVO-FACETS.md
  §2.2). `dregg-turn`'s `receipt_hash` is the genuine leaf to use; this crate
  uses a domain-separated content+nonce commitment at the same altitude to stay
  decoupled from `dregg-turn`. Needs: the `ServedResourceCell` cell-program
  template + the resolver dialing a real `TurnExecutor`.
- **The full `dregg://<fed>/<cell>/<swiss>` link + netlayer dial.** This crate
  models the resolve+attest half against a local ledger. The federation locator,
  the `SwissTable::enliven` of the swiss number, and the `Netlayer::dial`
  (tcpip/relay/onion) all exist in `captp/` (`uri.rs`, `sturdy.rs`,
  `netlayer.rs`); binding them is the distributed-fetch follow-up named in
  DISTRIBUTED-SERVO-FACETS.md §6.
- **Quorum signature crypto.** The `AttestedRoot` here carries structural
  quorum signatures (`has_quorum()` count/size check) — the same boundary the
  `AttestedRoot` doc draws (full Ed25519/BLS verification is a higher layer, via
  the `hints` crate). The receipt-stream Merkle binding (`verify_receipt_stream`)
  IS cryptographically real.

## Verify

```
cd /Users/ember/dev/breadstuffs/starbridge-web-surface && cargo test
```

builds standalone (its own workspace) and runs the delegate + web-of-cells test
suites green.
