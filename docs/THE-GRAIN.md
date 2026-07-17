# THE GRAIN — a hosted agent you can prove, fork, and own

A **grain** is a hosted agent whose every load-bearing property is a real dregg
primitive rather than a vendor promise. A conventional platform hosts an agent as
an opaque instance: you cannot copy it, roll it back, branch it, or prove what it
did — you trust the operator. A grain inverts that. The agent's mind is a
committed [`dregg_cell::Cell`], its authority is that cell's c-list, its work is a
turn/receipt chain, and its economics are a funded lease. Because the object is
the source of truth, everything already proven about cells, turns, and receipts
becomes true of the hosted agent.

The grain has three faces. Each is realized by a crate whose module docs cite this
file by face number.

## Face #1 — Unfoolable: "you can prove exactly what it did"

A grain's session **is** a turn/receipt chain, so a renter can re-witness what
their agent did while holding only the artifact the host hands back and re-running
nothing. This is the honest ladder **R0 → R1 → R2 → R3**, built by
`grain-verify/src/lib.rs` (the consumer side) and `grain-turn/src/lib.rs` (the
kernel-facing weld). Each rung's verifier runs every rung below it — one ladder,
not four bolted-on checks.

| rung | closes | verifier |
|------|--------|----------|
| **R0** | third-party forgery (the receipt key is a random persisted secret, not a public-derived one) + in-transit mutation of a real report | `GrainAttestation::verify` |
| **R1** | host rewrite / truncation, relative to a renter-acknowledged checkpoint (the renter countersigns `(head_root, num_turns)` with their own ed25519 key) | `GrainAttestation::verify_for_renter` |
| **R2** | receipts with no kernel behind them — every admitted action is a genuine committed executor turn on a grain turn-cell, and each receipt is a VIEW over a turn in the committed-turn manifest | `GrainAttestation::verify_r2` / `verify_r2_for_renter` |
| **R3** | host fabrication — execution integrity + completeness, folding the grain's finalized turns into ONE recursive-STARK aggregate re-witnessed against a VK anchor | `r3_verify` → the Lean-proven `Dregg2.Grain.R3Verify.r3VerifyCore` |

**What the ladder gives today.** R0–R2 are landed and verified. A holder of the
genuine signer key and tip detects in-transit mutation of a real report — a
forged, tampered, spliced, or reordered receipt, a mid-chain over-budget step, an
inflated headroom. R1 adds a renter anchor: the shown chain must carry at least as
many turns as the renter acknowledged (anti-truncation) and the acknowledged
position must hash to the countersigned head root (anti-rewrite). R2 ties each
receipt to a real kernel turn whose `calls_made` caveat metered the action
host-side.

**The honest gap.** R0–R2 are tamper-evidence plus a renter anchor plus kernel
linkage — not yet trustlessness, because the host that runs the session holds the
receipt key and nothing forces completeness. R3 is the leg that closes it: its
proved `r3_unfoolable` **reduces** the whole-history gap to the named
`RecursiveAggregation.EngineSound` STARK floor plus the R1 head binding — a genuine
reduction, not an unconditional proof. The exact machine-readable ask is the
`WHOLE_HISTORY_GAP` constant in `grain-verify/src/lib.rs`: mint each grain turn's
rotated wide-anchored EffectVM leg alongside the committed turn, and a live
session's real turns become the `FinalizedTurn`s the fold folds.

## Face #2 — Forkable: "the mind is a umem cell you own"

Because the mind is a committed cell, `grain-fork/src/lib.rs` makes fork, rewind,
and branch-and-stitch real on the hosting substrate:

- **fork** — copy the mind's committed image *at its checkpoint root* into a child
  grain under its own cap-confined lease. The child's genesis IS the parent's
  checkpoint root, so common ancestry is provable. State copies; **value and
  authority do not duplicate** — the mind carries no balance (value lives in the
  lease, its own obligor), and the child receives only the caps deliberately
  conferred, each of which the parent must actually hold.
- **rewind** — restore the mind to an earlier committed root, fail-closed on a
  boundary mismatch: the reified image must re-derive its sealed root under the
  kernel's sorted-Poseidon2 heap-root discipline, else the restore is refused and
  the live mind is untouched. History is committed states you re-inhabit, not a
  transcript.
- **stitch / absorb** — merge a child's divergent state back through the proven
  field-granular pushout plus the settlement-sound authority gate. Disjoint
  learnings fold clean; a same-address clash surfaces a first-class conflict, never
  a silent last-writer-wins; a cap revoked between branch and settlement is
  linear-dropped at the tip. The pushout and the gate are the proven pieces (the
  executable shadow of `Metatheory.SettlementSoundness`); the crate's contribution
  is welding them onto the hosted grain.

## Face #3 — Commons: the app store for hostable, shareable, forkable, pedigreed agents

`grain-commons/src/lib.rs` packages, publishes, discovers, and forks grains. Its
design principle is **compose, don't reimplement**: every guarantee is an existing
proven primitive wired into a market shape.

### §Commons

The four faces of the commons:

1. **Package an agent** — an agent config (cap bundle + budget + brain + roles) is
   packaged as a signed `.spk`. Provenance is the key: the App ID is the author's
   Ed25519 signing key, and a tampered package yields no installable grain.
2. **List & rent** — a listing is a *cell* (author key, `.spk` hash, listing
   terms, invariant digests) in a committed umem heap. Discover by App ID; rent =
   a priced quote whose numbers feed a real funded lease; a review is a receipted
   turn. "Rent = open a lease" is realized by feeding these numbers to
   `grain-fork::Grain::rent`.
3. **Fork with pedigree** — fork an installed grain's committed image into a fresh
   grain under a new owner, carrying a pedigree Merkle path that traces it to its
   author and every fork point.
4. **Hatch bounded sub-agents** — a genesis-agent mints sub-agents whose
   forever-invariant the executor enforces for the child's whole life, endowed with
   a strict attenuation of the genesis-agent's own caps.

## The confined body

`grain-jail/src/lib.rs` runs an untrusted *body* — a coding agent, a BYO binary —
as an OS-jailed subprocess behind the grain's `AgentBrain` seam. The body proposes
tool-calls over a line protocol; the drive loop cap-gates, meters, and receipts
each one unchanged, then feeds the verdict back. Because a confined brain *is* an
`AgentBrain`, the grain's lease, lifecycle, prepaid meter, checkpoint/fork/rewind,
and the R0→R2 attestation ladder all apply to a confined body with no change to the
drive path. The jail mechanism itself is the firmament `process-pd` sandbox.

## Where the pieces live

- The R-ladder consumer + R3 wiring: `grain-verify/src/lib.rs`.
- The R2 kernel-turn weld: `grain-turn/src/lib.rs`.
- Fork / rewind / stitch: `grain-fork/src/lib.rs`.
- The commons / app store: `grain-commons/src/lib.rs`.
- The confined body: `grain-jail/src/lib.rs`.
- Hosting substrate and economics: `docs/deos/GRAIN-HOMESERVER.md`; the confined
  body in depth: `docs/deos/GRAIN-CONFINED-BODY.md`; the market shape and the
  lease line: `docs/reference/grain-economy.md`.
- The system-wide guarantees the grain inherits: `docs/ASSURANCE.md`.

[`dregg_cell::Cell`]: the committed cell object — heap (durable working memory) +
c-list (authority).
