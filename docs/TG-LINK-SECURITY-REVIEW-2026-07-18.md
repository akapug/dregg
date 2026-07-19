# tg_link_page.rs security review — findings + fix plan (2026-07-18)

Adversarial (opus-class) review of the Telegram link ceremony CLIENT crypto, before device test.
VERDICT: **do NOT ship the passkey path as-is.** Server half (validate_init_data_at, verify_link_claim,
byte-pinned canonical message) is SOLID + the JS<->Rust byte parity is CONFIRMED correct. The client
CUSTODY is the weak part (weaker than extension/src/custody.ts).

## Must-fix before real use
1. **CRITICAL — Ed25519 lib from a CDN + no CSP.** `import ... from "https://esm.sh/@noble/ed25519@2.1.0"`
   with no CSP/SRI: an esm.sh/MITM compromise exfiltrates K on the passkey tap. Version-pin != integrity.
   FIX (in progress): @noble vendored same-origin (dreggnet-web/assets/noble-ed25519.js, committed). REMAINING:
   serve it at GET /tg/assets/noble-ed25519.js; change the page import to "/tg/assets/noble-ed25519.js";
   extract the inline module script to a served /tg/link/app.js asset; add CSP header
   `default-src 'none'; script-src 'self' https://telegram.org; style-src 'unsafe-inline';
   connect-src 'self'; img-src 'self' data:; base-uri 'none'; object-src 'none'`. (Discord Activities
   design independently requires this same vendoring — do once.)
2. **HIGH — silent new-K / no backup / auto-relink identity loss.** K's only durable copy is Telegram
   web-view localStorage (iOS evicts it); a missing blob auto-mints a NEW K and re-links (append-only
   latest-wins registry) -> Discord-you splits from Telegram-you, old K unrecoverable. FIX: derive K from a
   backed-up BIP39 mnemonic (extension parity) with explicit export; never auto-mint-on-missing-blob; on
   rebind detect "uid already links to root R" and require confirmation.

## Before real traffic (MED)
3. **Challenge not single-use** — post_tg_link (telegram_miniapp.rs ~:1255) never records the spent
   challenge via crate::replay; replayable within the 300s TTL. FIX: call crate::replay on success (keyed
   on nonce_and_exp).
4. **Passkey cancel silently downgrades to passphrase** — prfSecret catches ALL errors -> null -> "no PRF,
   use passphrase". A NotAllowedError (cancel) is indistinguishable from genuine no-PRF. FIX: distinguish
   unsupported (offer fallback) from failed/cancelled (retry, do NOT downgrade).
5. **Passphrase brute-forceable** — PBKDF2 210k (raise to >=600k, OWASP) + bare 10-char floor (add a real
   entropy check / generator). mode:"prf" blobs are NOT brute-forceable (authenticator-bound).
6. **Relay path shows a PLACEHOLDER** — displays `<your-root-pubkey-hex>` under "sign these exact bytes",
   so a literal signer signs the wrong message (fails closed -> BadSignature, so correctness not a hole,
   but the fallback is non-functional). FIX: render the real message only after the root pubkey is entered.

## Cleanup (LOW)
7. Zeroize the decrypted seed after signing (mirror custody.ts). 8. Align on HKDF + hashed PRF salt with
   the extension (harmless divergence; not interoperable but separate stores anyway).

## Solid, do not touch
JS linkClaimMessage == Rust link_claim_message byte-for-byte (pin test enforces); the initData gate;
fresh AES-GCM IV per encryption; mode:"prf" at-rest blob authenticator-bound.
