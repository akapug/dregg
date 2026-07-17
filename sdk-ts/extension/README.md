# dregg front door — a browser-extension trusted-path wallet

A Manifest-V3 browser extension that gives any web page a **dregg identity** and a
**human-confirmed `.turn()`** — built directly on `@dregg/sdk/browser`'s front
door (`Identity → .turn() → .sign() → .submit() → Receipt`, WebCrypto/@noble
ed25519). This is the **browser-extension front door** slice (e) of
`.docs-history-noclaude/WEB-FORWARD-EVERYWHERE.md`, built on the just-committed sdk-ts browser
surface.

## The security property: the page ASKS, the extension + user APPROVE, the key STAYS

```
  web page  ──window.dregg.turn(spec)──▶  content-script  ──port──▶  background
   (no key)        (describe a turn,         (isolated world,        (holds the
                    verbs only)               nonce channel)          Identity)
                                                                          │
                                                                   approval popup
                                                                   (you read the
                                                                    faithful
                                                                    explain())
                                                                          │
  web page  ◀────────── Receipt ──────────  content-script  ◀──port──  .sign().submit()
```

- The signing key lives **only** in the background service-worker (inside the
  SDK's `Identity`). It is never sent to a content script or a page. The most a
  page learns is the signer's **public** cell id and the **committed receipt**.
- A page can only **describe** a turn (verbs, as JSON — no key, no signature). The
  background builds it through `@dregg/sdk`'s authorized builder (there is **no
  `Unchecked` path**), signs it, and submits it **only after the user approves**.
- The approval popup renders the SDK's **anti-blind-signing** `explain()` reading
  — the per-effect plain language is derived from the *same term* that gets
  signed (each line carries the canonical `[sem <digest>]` tag bound to
  `Effect::hash`). An effect the wallet cannot read becomes an explicit
  **UNKNOWN — do not approve** warning; the screen can never show a blank for a
  blind signature.
- The signature is **byte-identical to the native SDK** (the same `@noble`
  ed25519 path the CLI/SDK pin to a golden vector) — the headless test asserts the
  submitted envelope equals the native-SDK envelope byte-for-byte.

## Layout

| File | Role |
| --- | --- |
| `manifest.json` | MV3: module service-worker, content script, popup, page-injected provider as a web-accessible resource. |
| `src/background.ts` | The service-worker — holds the `Identity` via `AgentRuntime`, runs the trusted-path mediator, opens the approval popup, submits iff approved. The key lives here. |
| `src/content.ts` | The trusted-path bridge — isolated-world content script: a nonce-scoped CustomEvent channel to the page + a `chrome.runtime` port to the background; stamps the verified page origin. |
| `src/page.ts` | `window.dregg` — the page-side provider (`identity()`, `isConnected()`, `turn(spec)`). Holds **no** key; mirrors the SDK's two-noun shape. |
| `src/popup.ts` + `popup.html` | Two faces — the identity display, and the **approval** gate that renders `explain()` + plain lines and Approve/Decline. |
| `src/mediator.ts` | `TrustedPathMediator` — the runtime-agnostic security heart: build → sign → show the reading → await the human gate → submit. |
| `src/spec.ts` | Hydrates a page's JSON turn spec into typed SDK effects, **pinning the source cell to the signer** (a page cannot smuggle a foreign `from`). |
| `src/explain-plain.ts` | Plain-language rendering + the UNKNOWN do-not-sign-blind guard, derived from the SDK's faithful `explainEffect`. |
| `src/protocol.ts` | The one narrow page↔extension message vocabulary (the key never appears in it). |
| `example-dapp.html` | A demo page exercising `window.dregg` (the page-asks side). |

`@dregg/sdk` is consumed from the sibling **sdk-ts source** via a build alias (see
`build.mjs`) — the extension is built *on* the SDK, and `esbuild` inlines the SDK
+ `@noble` into self-contained bundles (the published `dist/browser.mjs`
externalizes noble, which an extension bundle cannot do).

## Build, test (Docker — npm/node never on the host)

```sh
# from sdk-ts/extension, inside node:22-alpine with the sdk-ts dir mounted at /sdk:
docker run --rm -v "$PWD/..:/sdk" -w /sdk/extension node:22-alpine \
  sh -c "npm install && node build.mjs --all"      # → dist/ + test/.build/

docker run --rm -v "$PWD/..:/sdk" -w /sdk/extension node:22-alpine \
  sh -c "node build.mjs --tests && node --test 'test/*.test.mjs'"   # 7/7 green

docker run --rm -v "$PWD/..:/sdk" -w /sdk/extension node:22-alpine \
  sh -c "npx tsc --noEmit"                           # typecheck (EXIT 0)
```

The headless test (`test/mediator.test.mjs`) drives the same mediator the worker
uses, against a **mock node** (no network), and proves: (1) an unapproved request
is never submitted; (2) an approved request signs + submits → Receipt; (3) the
signature is byte-identical to the native SDK; (4) the key never leaves the
mediator; (5) the approval renders the real effects; (6) an unreadable effect
flags UNKNOWN; (7) a page cannot smuggle a foreign source cell.

## Load the extension (manual)

Chrome/Edge: `chrome://extensions` → enable Developer mode → **Load unpacked** →
select `sdk-ts/extension/`. Then open `example-dapp.html` (or any page) and use
`window.dregg`.

## What is tested vs. manual

- **Tested headlessly (Docker):** the whole trusted-path security path — build,
  sign, the human-gate decision, submit, byte-identical signatures, key
  containment, the anti-blind-signing reading, source-cell pinning. Plus the
  full TypeScript surface (`tsc --noEmit`) and a from-scratch bundle build.
- **Manual (real browser):** loading the unpacked MV3 extension, the page→content
  →background `postMessage`/port plumbing in a live Chrome, the popup rendering,
  and a real `.submit()` against a funded devnet cell. The plumbing is thin glue
  over the tested core; the security property lives in the tested mediator.

## The one honest seam

This front-door slice keeps the key at rest in `chrome.storage.local` for the
demo flow. The production at-rest hardening (BIP39 phrase + PBKDF2 + AES-256-GCM,
auto-lock) is the same shape the sibling wasm cipherclerk (`extension/`) already
ships, and is the named seam here. The security property this slice *proves* is
the **trusted-path mediation** — the key never reaches the page, authorization
stays inescapable, and the approval renders the real effects.
