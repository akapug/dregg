# Cross-Platform Identity Linking — design (2026-07-17)

**Problem:** each frontend derives a SILOED custodial identity —
Discord `BLAKE3_derive_key("dregg-discord-bot-v1", bot_secret‖discord_uid)`,
Telegram `"dregg-telegram-bot-v1", telegram_secret‖telegram_uid` (both → AgentCipherclerk).
Same pattern, different master secret+domain+uid = different dregg identities. The Telegram
bot + its Mini App ARE one identity (telegram_miniapp derives via dreggnet_telegram::cipherclerk).
We want ONE human across platforms.

**The model: both platforms link to ONE root key K** (the user-held dregg Ed25519 key the
extension custody / passkey stack already holds). Cross-platform sameness is an identity-
RESOLUTION seam, not a signing change: resolve custodial_pubkey → root_pubkey before comparing
actors. Attribution stays honest (turn signed by the custodial derivation; resolution backed by
K's own signed claim).

## Reuse (already exists, tested)
- `discord-bot/src/commands/link_proof.rs` `check_link_proof` — the pure ownership-proof verb
  (pk derives/equals the linked cell, verify_strict over the challenge). Reuse verbatim.
- `discord-bot/src/commands/federation.rs` `/link-cipherclerk` — the pending half (records
  ExternalPending + a challenge). WOUND: challenge is deterministic (no nonce) → replayable.
- `webauth-core/src/challenge.rs` — stateless keyed-BLAKE3 nonce, 120s TTL, single-use
  (replay.rs). THE fix for the deterministic-challenge wound.
- `webauth-core/src/account_id.rs` — KERI stable account id from an inception pubkey (survives
  rotation). The deep-version anchor.
- `dreggnet-offerings/src/signed.rs` — `verify_signed` yields DreggIdentity = pubkey hex, the
  SAME handle custodial cipherclerks derive ("a signed actor and a custodial actor with the same
  key are the SAME identity"). `advance_signed` already lets K act as itself.
- `extension/src/offering-sign.ts` — the byte-pinned canonical-message signer discipline to mirror.
- `node/src/identity_export.rs` + starbridge_polis identity cell — the deep-version link record
  home (links as receipt-signed, witnessed KERI turns).

## Build — small first step (in order)
1. `link_claim.rs` (shared crate — webauth-core or dreggnet-offerings): canonical message
   `"dregg-identity-link-v1:" ‖ platform ‖ 0 ‖ platform_uid ‖ 0 ‖ platform_custodial_pubkey_hex
   ‖ 0 ‖ root_pubkey_hex ‖ 0 ‖ challenge`, a pure verifier (verify_strict, mirrors
   check_link_proof), + a byte-pin test + the forgery-suite shape (wrong-key/wrong-message/
   replayed-challenge/cross-platform-splice).
2. Discord: store `root_pubkey` at /link-prove promotion (today it checks the pubkey then throws
   it away, storing only cell_id); swap ownership_challenge → webauth_core::challenge (nonce'd).
3. Telegram: the ENTIRE ceremony (zero today) — a Mini App link page (extension/passkey signs
   the claim in-browser; initData authenticates the uid) + a TelegramStore link table.
4. Shared registry keyed by root_pubkey_hex (a node route beside /api/starbridge/identity/*, or a
   small shared store) + `resolve_root(custodial_pubkey) -> Option<root_pubkey>`; the offerings
   stack calls it before comparing actors.

## Deep version (later)
Link record as turns on K's identity cell (receipts + federation witnessing + verify_export);
handoff-certificate-backed scoped delegation; a "linked-platforms" credential for selective
disclosure ("prove I am the same human without revealing which Discord account"); rotation via
the KERI cell. One derivation trap to pin: check_link_proof uses the "default"-domain cell id,
webauth-core uses "dregg:account-identity:v1" — bind the RAW pubkey; each consumer derives its
own cell-id flavor.

## Sequencing note
This touches discord-bot + dreggnet-telegram + dreggnet-offerings/webauth-core — the SAME files
the in-flight audit-logging swarm edits. Land + commit the audit swarm (and the initData
signature-fix) FIRST for a clean base, THEN swarm the link build — two big overlapping swarms
gridlock on the shared files (the build-lock-contention lesson).
