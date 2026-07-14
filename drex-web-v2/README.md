# drex-web-v2 — the DrEX product frontend (seed)

A working seed of the DrEX frontend overhaul. Preact + htm + `@preact/signals`,
bundled by esbuild into one self-contained file (~19.6 KB gzipped, zero runtime
CDN requests). The extension (`window.dregg`) is the identity + wallet + signer;
this app is the orchestrator.

The full plan — assessment, architecture, per-mechanism / tier / sealed-bid /
composition / wallet / multichain component design, and the Open-first phased
sequence with per-phase ember-gated deploy dependencies — is in
`docs/deos/DREX-FRONTEND-OVERHAUL.md`.

This is a **separate surface** from the current `drex-web/` demo (`:8781`), the
offerings surface (`:8790`), and the games deploy. It runs on **`:8782`** and
does not disturb them.

## What the seed wires (real, Phase 1 / Open-first)

- **App shell** — header, node probe, extension/wallet status.
- **Wallet handshake** — detect the installed extension (`window.dregg` /
  `dregg:ready`), connect via `dregg.authorize`, pull the EVM address. Honest
  install prompt when no extension is present (no faked wallet).
- **Tier-dial (first-class)** — Open / Shielded / Dark, with the live
  viewer-lens: the same cleared ring drawn three ways (open = full flows,
  shielded = blurred amounts, dark = 🔒 sealed), reusing `drex-web/drex-viz.js`.
  Shielded/Dark are labelled previews (not live with real money).
- **Open-tier ring order-entry** — build a real batch → `POST /clear` → the REAL
  matcher (`drex_clear`: solver.rs ring match → verified_settle.rs kernel fold) →
  the real cleared receipt (ring, allocations, per-asset conservation,
  reject-polarity) → settle on the live node.
- **Sealed-bid commit→reveal** — the two-phase ceremony routed through the real
  extension (`dregg.sealedBid.commit` / `.reveal`: keccak256 + EIP-712 +
  secp256k1). The on-chain escrow post is labelled deploy-gated.
- **Mechanism rail + composition strip** — all 8 mechanisms and the
  deposit→shield→clear→settle journey, each with its honest live-state / grade.

## Run

```
npm install          # 6-package tree: preact, htm, @preact/signals, esbuild
npm run build        # esbuild → dist/app.js
node serve.mjs       # → http://127.0.0.1:8782
```

The `/clear` endpoint needs the `drex_clear` binary. It is found local-first
(`target/{release,debug}/drex_clear` — build with
`cargo build -p dregg-intent --bin drex_clear`), else the server shells to the
prebuilt matcher on the build host (`DREX_REMOTE`, default `persvati`).

`/settle` needs a live dregg node (`dregg-node run --port 8420 --enable-faucet
--prove-turns`); without one the UI shows the honest offline fallback and keeps
the labelled local clear.

## Dev (buildless)

`htm` needs no compiler, so `src/` is plain ESM. `npm run build -- --watch`
rebuilds `dist/app.js` on change while `node serve.mjs` serves.

## Honest scope

Live end-to-end today: the Open-tier ring clear + solo-node settle, and the
sealed-bid ceremony's cryptography (extension-signed). Shielded / Dark tiers, the
on-chain sealed-bid escrow, and the seven non-ring mechanisms are honestly
labelled previews that wire in per the phased plan. Nothing not-yet-live is shown
as live with real money.
