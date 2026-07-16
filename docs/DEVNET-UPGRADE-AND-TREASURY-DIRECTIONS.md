# Devnet upgrade/migration + cross-chain treasury — directions (2026-07-13)

From two scouts. Both are INTEGRATIONS of existing pieces, not research.

**Status at HEAD:** the top-ranked recommendations are BUILT — the epoch manifest/handshake (`dregg-epoch`),
the multichain treasury view (`dregg-pay/src/multichain.rs::TreasuryView`), and the treasury joined into the
live bot's `PayState` (`discord-bot/src/pay.rs`). Per-item status is marked inline below; the un-marked
recommendations remain open directions.

## Upgrade / migration for fast-moving devnets
GOVERNING REALITY: the whole upgrade story is GIT-LOCKSTEP + FAIL-CLOSED — descriptors (light-client VKs, committed
in-repo at circuit/descriptors/), the registry fingerprint (V3_STAGED_REGISTRY_FP, a baked const), the StateConstraint/
HeapAtom vocab, and the slot-caveat tag set are all compile-time constants. "Upgrade" = everyone rebuilds against the same
git HEAD. SAFETY is well-built; LIVENESS/discovery is the gap.
- VK rotation: two classes — TAIL-APPEND (new descriptor rows at the tail, the [0..46) PI prefix untouched, no re-genesis)
  vs GEOMETRY-WIDEN flag-day (every cohort member's trace_width moves → an eyes-open re-genesis, ember-gated).
- Vocab growth: append-only (new variants declared LAST → postcard/serde by-index → content-addresses/factory-VKs
  byte-identical). New slot-caveat tags ride in PIs (off-AIR re-eval, VK UNCHANGED); an OLD verifier rejects a new tag as
  unknown = a verifier-code EPOCH, not a proving-key rotation. No explicit schema-version — the version is implicitly which
  variants the binary knows (git-lockstep).
- State: RE-GENESIS = WIPE+restart is the primary mechanism (new committee keys → new federation_id → a fresh chain; old
  data-dir archived). Content-addressed cell state is reproducible as DATA but the CHAIN is gone. A deliberate NO-MIGRATION
  design (the wire commitment == the cell commitment, so state needs no migration). In-place carry-forward is BUILT
  cross-epoch (`dregg-genesis-snapshot`, generalizing vat-migration's CellExportBundle from cross-federation to
  cross-epoch — see recommendation #3; the bridge fold its IVC history leg leans on is flagged UNSOUND).
- No global protocol version / wire negotiation — scattered per-subsystem format versions (refuse-newer, parse-older).

RECOMMENDED (ranked; priority #1 → #3 → #2):
1. **EPOCH MANIFEST + HANDSHAKE — BUILT (`dregg-epoch`).** A node advertises its epoch manifest on connect; a client
   compares against its own and KNOWS immediately whether it can talk + which tags will be accepted. [`EpochManifest`] is
   DERIVED from the real baked constants (V3_STAGED_REGISTRY_FP, the descriptor set, the slot-caveat tag vocabulary —
   never a hardcoded duplicate), and `check_compatibility` returns a typed `EpochCompat` verdict (compatible, or a
   specific actionable incompatibility). Converts implicit git-lockstep into an explicit DISCOVERABLE epoch — the answer
   to "how does a client know its epoch?". NAMED SEAM: the transport (serving/fetching the manifest on the live
   node-connect path) is the remaining deploy wire; the manifest derives Serialize/Deserialize so that wire carries it
   verbatim.
2. **DRIFT-TAXONOMY CI GATE — BUILT (`scripts/check-drift-taxonomy.sh`).** Classifies the descriptor delta against a
   base ref (UNCHANGED / TAIL-APPEND / GEOMETRY-WIDEN) and REFUSES a geometry-widen unless `DREGG_ALLOW_REGENESIS=1`
   (the eyes-open re-genesis flag); `check-descriptor-drift.sh` invokes it on every pass. Mechanizes "does this
   upgrade need a wipe?" — a tail-append passes, a geometry-widen is caught.
3. **GENESIS-FROM-SNAPSHOT — BUILT (`dregg-genesis-snapshot`).** Generalizes the CellExportBundle from cross-federation
   to cross-epoch: a re-genesis mints new keys but SEEDS the new chain with a frozen EXPORT of the old cell-set — each
   cell carries a cross-epoch MigrationVoucher + its IVC proof of history-from-old-genesis, and `seed_genesis` refuses
   on id/voucher/IVC mismatch (append-only content-address stability re-addresses the imported cells identically).
   Consumed by `dregg-season` as the season-boundary carry-forward; the unsound-fold caveat above is named in the
   crate header.
4. Tag-activation-height for the verifier-upgrade window (roll the verifier out accept-but-don't-require FIRST, then flip
   cells) — instead of everyone-rebuild-at-once.
5. Unify the scattered version fields under the one epoch manifest.

## Cross-chain treasury
The treasury accounting object (dual-asset: USDC=fuel/fail-closed-on-empty, $DREGG=pile) IS joined into the live bot:
`PayState` holds a `Treasury<SqliteTreasuryStore>` (persisted, restart-surviving) and `poll_and_credit` routes every
newly-detected payment through `Treasury::record_payment` (`discord-bot/src/pay.rs`). The multichain light-clients are
DEEP + REAL on the READ side (proof-of-holdings on Solana/Base/Cosmos), and dregg-interchain-gov aggregates all three
into ONE ProvenForeignHolding fact (chain_tag 0/1/2) — feeding both governance voting weight AND, via the view below,
the treasury.
RECOMMENDED (ranked):
1. **MULTICHAIN TREASURY VIEW — BUILT (`dregg-pay/src/multichain.rs::TreasuryView`):** the SAME ProvenForeignHolding
   facts pointed at the TREASURY's own declared `TreasurySlot`s per chain → a non-custodial treasury that PROVES "we
   hold X USDC on Base, Y $DREGG on Solana, Z on Cosmos" trustlessly, no new custody. A holding is COUNTED only when a
   real consensus proof backs it and it binds to a declared address/asset/chain; unproven or foreign-address facts are
   REJECTED (driving test: `dregg-interchain-gov/tests/multichain_treasury_view.rs`). Wired into the bot as
   `PayState::treasury_view`.
2. Join game revenue → treasury: the payment→`record_payment` loop is live; the seed-holding Solana watcher/sweeper
   still runs as a separate operator service (the bot polls a mock/devnet watcher in the interim — a named seam).
3. Cross-chain value MOVEMENT (real lift / honest ceiling) — nothing exists (Jupiter is Solana-only). The nicer endgame the
   code already names: a PROTOCOL-NATIVE on-ledger treasury (run budget as a conserved Effect::Transfer, no operator holds
   funds) — so no cross-chain custody is needed.
