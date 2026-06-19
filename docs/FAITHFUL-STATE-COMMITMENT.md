# Faithful state commitment — widen the in-circuit digest from 1 felt to 8 (THE light-client floor)

> **Status: design + build spec. This is the floor under every other light-client close.** Written after
> ember caught the laundering: I had accepted a 31-bit commitment as "the existing audited scheme." It is not
> audited — it is a documented, deferred half-migration (`pi.rs` `AUDIT[stage1-trace-widen]`), and it is the
> single most load-bearing soundness gap. Everything WAVE 0/1/2 forced (authority drift, selector, fee, the
> movers) forces the right *values* — but they all bind through this commitment, so the trust is only as strong
> as the commitment's collision resistance. Today that is ~31 bits for a light client.

## The hole (grounded, with file:line)

The published per-cell state commitment reserves **4 felts** (`pi.rs` `OLD_COMMIT_LEN = NEW_COMMIT_LEN = 4`).
But:
- The in-circuit hash `hash_many` (`circuit/src/poseidon2.rs`) runs the Poseidon2 sponge and **squeezes ONE
  element** (`// Squeeze: return first element` → `state.state[0]`). So the in-trace `STATE_COMMIT` column
  (`trace_rotated.rs` `B_STATE_COMMIT=38`, ONE column) holds **one BabyBear felt ≈ 30.9 bits**.
- The descriptor's `pi_binding` (`EffectVmEmitRotationV3.lean` `rotPins`) binds **that one felt** to PI
  position 0. The reserved positions 1..3 are **bound off-circuit by the executor's PI-matching loop**
  (`pi.rs`: *"positions 1..3 are bound to the canonical cell state by the executor … AUDIT[stage1-trace-widen]:
  the extra 3 PI elements get their security from the executor PI matching loop. Stage 2 widens the trace
  column."*).

So a **full node** (runs the executor) gets the 4-felt binding; a **light client** (proof only) gets only what
the AIR forces = **position 0 = one felt ≈ 31 bits**. A light client identifies "which state" by a 31-bit
value → two distinct cell-states colliding on it is ~2¹⁵·⁵ work (birthday) — **seconds on a laptop**. A prover
can build a fully-valid proof for state A whose committed value equals state B's, and the light client accepts
it as B. The value-forcing this session is real; the binding underneath it is 31-bit.

## The security target (measure, don't guess — match the proof's own soundness)

The deployed FRI config (`circuit/src/descriptor_ir2.rs`): `log_blowup = 6`, `19 queries`, `16 PoW bits`,
degree-4 extension (`BinomialExtensionField<BabyBear, 4>`). Conjectured FRI soundness ≈ `queries × log_blowup
+ pow` ≈ `19×6 + 16` ≈ **~130 bits**. The commitment's **collision** resistance must MATCH this — a weaker
commitment is the soundness floor regardless of how sound the proof is.

| squeeze width | digest bits (× 30.9) | collision (birthday, ÷2) | verdict |
|---|---|---|---|
| 1 felt (today, light client) | 30.9 | **~15 bits** | broken — seconds |
| 4 felts (reserved PI / doc "Stage 2") | 123.6 | **~62 bits** | below proof soundness — NOT trustworthy |
| **8 felts** | 247 | **~124 bits** | **matches ~130-bit FRI soundness — the faithful target** |

So the faithful width is **8 felts**, not the reserved 4. (Greenfield: we re-reserve the PI to 8. Shipping 4
would repeat the under-strength mistake — 2⁶² instead of 2¹⁵ — and still fail "actually trust.") Poseidon2
`WIDTH=16`, rate 4 → squeeze 4, permute, squeeze 4 = 8 output felts depending on the full input.

## The fix (Stage 2, faithful = 8 felts; emit from Lean, law #1)

1. **`hash_many_8`** (`poseidon2.rs`): the sponge squeeze returns **8 DISTINCT** felts (squeeze rate-4, permute,
   squeeze rate-4) — NOT eight copies of `state[0]`, NOT `[0]` replicated. Anti-laundering: a unit test that
   the 8 outputs are pairwise-distinct for a generic input and that flipping any one input bit changes all 8.
2. **In-trace**: `B_STATE_COMMIT` 1 column → **8 columns** (`B_STATE_COMMIT..+8`). The chain-carrier offsets,
   `B_SPAN`, `ROT_WIDTH` shift (a contained geometry change — the same NUM_PRE_LIMBS-style cascade the mover
   flag-days already proved tractable, but on the AFTER/BEFORE block span).
3. **In-circuit hash sites** (`EffectVmEmitRotationV3.lean` `rotV3SitesAt`/`wireCommitR`): the AIR constrains all
   8 squeezed felts from the Poseidon2 chip (the chip computes the full 16-element output state; expose 8).
4. **`rotPins`**: bind the **8** commit columns to the 8 reserved PI slots (re-reserve `{OLD,NEW}_COMMIT_LEN = 8`
   in `pi.rs`) — so the **proof** binds all 8, retiring the executor PI-matching loop for the commitment.
5. **Producer**: `compute_canonical_state_commitment_v9_felt` (`cell/src/commitment.rs`) returns **8 felts**
   (the final `hash_many` → `hash_many_8`); both producers (`rotation_witness::produce`,
   `compute_rotated_pre_limbs`) fill the 8 columns.
6. **Differential**: extend `effect_vm_commit_lean_differential` + `RotatedCommitDifferential.lean` to bind all
   8 felts (deployed `compute_…_v9` byte-equals the Lean `RH`/`recStateCommit`, all 8).

## The anti-laundering teeth (the verification that this isn't fake-widened)

- **DISTINCTNESS**: the 8 squeezed felts are pairwise-distinct + each depends on the full input (no `[0]×8`).
- **THE COLLISION-DISTINGUISHING TOOTH** (the light-client bite): two cell-states differing ONLY in a high
  position (e.g. one byte of `fields[15]`, or a permission tag) produce **proof-bound commitments that differ in
  ≥1 of the 8 felts** — and a proof for state A is REJECTED by `verifyBatch` when checked against state B's
  8-felt commitment, with NO executor. This is what makes "the light client trusts the commitment" TRUE.
- **NO DOWNGRADE**: honest turns prove+verify with the 8-felt commit; the whole rotated suite green; drift PASS.
- **AXIOM-CLEAN**: the `wireCommitR_binds` keystone lifts to 8 felts under the same `Poseidon2SpongeCR` floor
  (now genuinely load-bearing at full width, not 1-of-4).

## Why this comes first

Every prior close (WAVE 0/1/2, fee, identity, selector) forces values that bind *through* this commitment. At
1 felt they bind through a 31-bit door. At 8 felts they bind through a ~124-bit door matching the proof's own
soundness — and only then does "a light client running verifyBatch can actually trust the published (pre,post)"
become true. This is the floor; it should have been first.
