# Devnet upgrade/migration + cross-chain treasury — directions (2026-07-13)

From two scouts. Both are INTEGRATIONS of existing pieces, not research.

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
  design (the wire commitment == the cell commitment, so state needs no migration). In-place carry-forward exists only as
  DESIGN (vat-migration's CellExportBundle + an IVC proof of history-from-genesis — cross-federation, not cross-epoch; the
  bridge fold it leans on is flagged UNSOUND).
- No global protocol version / wire negotiation — scattered per-subsystem format versions (refuse-newer, parse-older).

RECOMMENDED (ranked; priority #1 → #3 → #2):
1. **EPOCH MANIFEST + HANDSHAKE (highest-leverage, small build).** A node advertises {registry_fp, descriptor_set_tag,
   known_caveat_tags, wire_version, min_compatible} on connect; a client compares against its baked V3_STAGED_REGISTRY_FP +
   tag set and KNOWS immediately whether it can talk + which tags will be accepted. Converts implicit git-lockstep into an
   explicit DISCOVERABLE epoch — directly answers "how does a client know its epoch?" (today: no answer). Builds on
   constants that already exist.
2. DRIFT-TAXONOMY CI GATE: make check-descriptor-drift.sh EMIT the class (tail-append vs geometry-widen) + REFUSE to ship a
   geometry-widen without the eyes-open re-genesis flag. Mechanizes "does this upgrade need a wipe?".
3. GENESIS-FROM-SNAPSHOT (carry-forward, bigger, primitives exist): generalize the CellExportBundle from cross-federation
   to cross-epoch — a re-genesis mints new keys but SEEDS the new chain with a frozen EXPORT of the old cell-set, each cell
   carrying its IVC proof of history-from-old-genesis. The difference between "characters wiped every devnet bump" and
   "characters survive." No new crypto (append-only content-address stability re-addresses the imported cells identically).
4. Tag-activation-height for the verifier-upgrade window (roll the verifier out accept-but-don't-require FIRST, then flip
   cells) — instead of everyone-rebuild-at-once.
5. Unify the scattered version fields under the one epoch manifest.

## Cross-chain treasury
The treasury is Solana-only today (dual-asset: USDC=fuel/fail-closed-on-empty, $DREGG=pile), built but NOT joined into the
live bot (PayState has ledger+watcher, no Treasury/Sweeper — built+tested, unwired). The multichain light-clients are DEEP
+ REAL on the READ side (proof-of-holdings on Solana/Base/Cosmos), and dregg-interchain-gov ALREADY aggregates all three
into ONE ProvenForeignHolding fact (chain_tag 0/1/2) — but it feeds governance voting weight, not the treasury.
RECOMMENDED (ranked):
1. **MULTICHAIN TREASURY VIEW (small wire):** point ProvenForeignHolding at the TREASURY's addresses per chain → a
   non-custodial treasury that PROVES "we hold X USDC on Base, Y $DREGG on Solana, Z on Cosmos" trustlessly, no new custody.
   The reads + aggregation exist; Treasury needs per-chain holding fields + a verifier hook.
2. Join game revenue → treasury (the Sweeper is built, just not in the live PayState loop).
3. Cross-chain value MOVEMENT (real lift / honest ceiling) — nothing exists (Jupiter is Solana-only). The nicer endgame the
   code already names: a PROTOCOL-NATIVE on-ledger treasury (run budget as a conserved Effect::Transfer, no operator holds
   funds) — so no cross-chain custody is needed.
