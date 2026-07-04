# starbridge-gallery

**A sealed-submission art gallery — commit-reveal curation with an on-ledger, tamper-proof
submission board.** Artists submit work to a juried gallery. To keep the jury honest and stop
artists copying or front-running each other, submissions are *sealed*: during a SUBMISSION
phase each artist commits a hash binding `(artist, piece, nonce)`; the curator closes
submissions; artists reveal; the curator features a piece for display. The gallery *is* a
factory-born cell whose installed `CellProgram` is the curation policy, re-checked by the
verified executor on every turn.

```
SUBMISSION ──close_submissions──▶ REVEAL ──curate──▶ CURATED
```

- **submit**            — an artist commits a sealed submission into the next free `WriteOnce`
  board slot (others see only the hash).
- **close_submissions** — the curator closes the open call (`SUBMISSION → REVEAL`).
- **reveal**            — an artist opens its piece; only a piece matching a committed seal is
  accepted.
- **curate**            — the curator features a piece (`REVEAL → CURATED`), writing
  `FEATURED` / `FEATURED_HASH`.

## The guarantees, one cell program

| Guarantee                         | How this cell enforces it | Scope |
|-----------------------------------|---------------------------|-------|
| **anti-tamper** (no swap after commit) | each board slot is `WriteOnce(SUBMIT_BASE + i)` — a sealed piece is frozen the instant it is committed; a piece cannot be swapped out from under the curator | every turn |
| **anti-rollback** (the call is one-way) | `Monotonic(PHASE)` floor (every method) + `StrictMonotonic(PHASE)` advance on `close_submissions` / `curate` — the phase never rewinds and never re-fires | every turn / advance |
| **frozen result** | `WriteOnce(CURATOR)` (seed) + `WriteOnce(FEATURED / FEATURED_HASH)` (curate) — the featured choice freezes once announced | every turn |
| **binding seal** | `seal = BLAKE3(artist ‖ piece ‖ nonce)` — a committed submission opens to *exactly* its piece (under collision-resistance); a swapped piece hashes to a different seal not on the board | crypto |

The commit phase is **on-ledger**: the anti-tamper guarantee is an *executor refusal*
(`WriteOnce`), not an in-process membership check. The in-process `Submission`/`Gallery` state
machine in `src/lib.rs` is the executable witness of the commit-reveal crypto (the seal
binding, the phase gate, the membership gate); the factory-born cell lifts the board onto the
ledger so swapping a committed piece is refused by the verified executor.

Built from dregg primitives only — `FactoryDescriptor`, `Effect::SetField` /
`Effect::EmitEvent`, Lane-G `StateConstraint` slot caveats. No domain-specific gallery
`Effect`, no `Authorization::Unchecked`, no placeholder signatures.

## Relationship to sealed-auction

Gallery and `sealed-auction` share the same commit-reveal core — both seal `(party, value,
nonce)`, gate reveals behind a closing phase, and freeze the committed board with `WriteOnce`.
They are **distinct surfaces**, not duplicates: sealed-auction awards a slot through *verified
settlement* (an asset ring folded through the per-asset executor); gallery *features a piece
for display/curation* and has no settlement leg. Gallery is the right home for "sealed entries
judged then shown"; sealed-auction is the right home for "sealed bids that pay out."

## The deos-native surface

The whole interaction is one composed `DeosApp` (`gallery_app`). The rights ladder
`Signature ⊂ Either ⊂ None` **is** the visitor ⊂ artist ⊂ curator roster:

- `view_gallery` — cap-only, `Signature` (a visitor browses);
- `submit` / `reveal` — gated (cap∧state), `Either` (an artist) — SUBMISSION / REVEAL
  preconditions;
- `close_submissions` / `curate` — gated (cap∧state), `None`/root (the curator) — SUBMISSION /
  REVEAL preconditions.

The gallery cell is published into the web-of-cells as a `dregg://` sturdyref and is
discoverable under `gallery` / `art`.

**The seam is closed.** The deos fire is two-tempo: a cap∧state precondition gate decides the
button in-band (nothing submitted on a miss — anti-ghost), then the full turn is submitted and
the executor re-enforces the installed program. So swapping a committed submission
(`WriteOnce`) and a phase that rewinds / does not advance (`StrictMonotonic`, strict) are
**real executor refusals in the fire path** — `tests/deos_seam.rs` proves each with both
polarities (the honest turn commits; the hostile turn is refused and commits nothing).
`tests/factory_birth.rs` proves the same teeth bite on a factory-born cell.

## Run the tests

```
cargo test -p starbridge-gallery
```
