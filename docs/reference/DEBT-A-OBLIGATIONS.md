# DEBT-A — the remaining obligations, codex-facing (2026-07-10)

> Hand-off spec for a proof-engineering pass (codex or lanes). Each obligation is stated as an EXACT Lean target
> plus an **anti-toy constraint** — the property a discharge MUST have to count, derived from a real scope failure
> already found tonight. A green proof that violates the anti-toy constraint is a LIE, not a discharge. The
> integrator (me) gates every result by reading the ARGUMENT, not the name or the green.
>
> Companion: `CARRIER-CENSUS.md` (the ledger + every finding), `GOAL-HONEST-VERIFICATION.md` (the trail).

## The anti-toy constraints (paid for in real findings — violate ANY of these and it does not count)
1. **Deployed field, not a demo.** `BabyBear = ZMod 2013265921`, NOT `ZMod 5`. (`BabyBearFriField.lean`.)
2. **Deployed VM, not the abstract one.** The soundness must land on `VmTrace` / `EffectVmDescriptor2`, NOT the
   toy `Step State Effect` with single-step `satisfiesTransition`. (THE KEYSTONE finding, `b064b99b9`.)
3. **Deployed permutation, not a constant.** Any `permOut`/chip table must be the KAT-bit-exact
   `Poseidon2BabyBearW16.perm`, NOT `fun _ => List.replicate CHIP_OUT_LANES 0`. (`permOutZ`, `810d0dc65`.)
4. **Sampled queries, not `Finset.univ`.** FRI soundness must be the `num_queries = 38` sampled bound, NOT
   `Q = univ` (which gives fake exactness `d = 0`). (`e35a79a2f`.)
5. **Deployed arity.** The fold is up to 8-to-1 (`PROD_FRI_MAX_LOG_ARITY = 3`), not 2-to-1. (`b404d4b9f`; the
   arity-`2^k` lemma is PROVED, `3ab1c78ed`.)
6. **No carrier as a hypothesis.** A `class`/`def : Prop` (StarkSound, AlgoStarkSound, FriExtract, ChipTableSoundN,
   FriProximity) taken as a hypothesis is an ASSUMPTION `#assert_axioms` cannot see — relabeling is not proving.
   Every gap is an EXPLICIT DATA hypothesis reducible to the floor, or it is not done.
7. **No degeneracy.** A bound variable unused in the conclusion, a `True` premise, a `witVerify := fun _ => true`,
   a `hcode_sat` whose codeword is unused — all collapse to "assume the conclusion." (`3ee8b5ee8`, `c5ffb25c5`.)
8. **Read the argument, not the shape.** A `:= true` field may be a redundancy discharged one call down
   (`merklePaths` is — Merkle is in `friQueryCheck`). Trace the accept path before crying hole OR claiming green.

## The floor (the honest TCB — reducing to these IS done)
`Poseidon2SpongeCR` / `HashCR` (concrete-hash CR) · the lattice/DL floor · `leanc`/FFI · a NAMED FRI-soundness
assumption at the deployed params IF one is genuinely irreducible. NOTHING else.

## PROVED (committed, audited by type — reusable bricks)
- #1 `ChipTableSoundN` @ the real `Poseidon2BabyBearW16.perm` — `Satisfied2FaithfulDeployed.lean` `37b121f55`
  (serves `Satisfied2Faithful`'s 26 sites; NOTE `structure Satisfied2` has ZERO chip-table fields).
- #2 FRI sampled-query soundness `(1−δ)^k`, k=38, δ=7/16 (unique-decoding), err<2⁻³¹ — `FriQuerySoundness.lean`.
- #3 The `FriProximity` bridge (geometric ⟶ operational), 3 explicit hyps — `FriProximityBridge.lean`.
- #6 arity-`2^k` folding (`fold_close_of_arity_challenges`, constant `n²·d`, deployed n=8) — `FriFoldArity.lean`.
- #7 LogUp bus soundness (Haböck + Schwartz–Zippel, `logup_forged_lookup_sound`) — `LogUpSoundness.lean`.
- AIR half: `MainAirAccept ⟹ Satisfied2` for `transferV3`, 6/8 legs — `AirChecksSatisfied.lean` + `AirLegsDischarged.lean`.
- `AlgoStarkSoundInstance.lean` `b064b99b9` — CARRIER-FREE reduction of `AlgoStarkSound` to ONE seam (below).

## REMAINING OBLIGATIONS

### K — THE KEYSTONE (in flight, `OodQuotientConsistency.lean`): `verifyAlgo accepts ⟹ MainAirAccept`
Target: `verifyAlgo @ fullChecks (view pi π) = true → MainAirAccept hash transferV3 t` over the DEPLOYED trace.
Argument: OOD quotient-consistency — verifyAlgo checks `C(ζ) = Z_H(ζ)·q(ζ)` at a Fiat-Shamir OOD ζ; FRI proves
`q` low-degree; Schwartz–Zippel on ζ ⟹ `C = Z_H·q` as polynomials ⟹ `C` vanishes on the rows ⟹ `MainAirAccept`.
Anti-toy: constraints 2 (deployed `VmTrace`), 4/5 (the FRI low-degree input is #2/#6, not `Q=univ`), 7.
**FORK the in-flight lane reports:** if `MainAirAccept`/`arithResidual` is a `Polynomial` ⟹ this is a bounded SZ
proof (closable). If it is a raw per-row `ℤ` evaluation ⟹ obligation **K′** below is the real (DEBT-B-sized) work.

### K′ (conditional) — the toy→deployed VM refinement
If `MainAirAccept` has no polynomial structure: interpolate the deployed `VmTrace` columns as polynomials over the
BabyBear evaluation domain, define the constraint composition `C` as a `Polynomial`, and connect it to the
FRI-committed quotient — so the FRI proximity (#2/#6) lands on the deployed trace, not `Step State Effect`. This is
a data-refinement campaign, the same SHAPE as DEBT-B's finite-map work. Scope it as its own multi-brick effort.

### #5 — DeployedRefines / the verifyBatch ARCHITECTURE decision (EMBER-GATED, not a proof)
`verifyBatch` is `opaque` (`CircuitSoundness.lean:353`). To make `StarkSound` a theorem, pick:
- **(A)** `def verifyBatch := verifyBatchModel` (= `verifyAlgo @ fullChecks && extra`) + carry `DeployedMatchesModel`
  as a KAT correspondence (harness EXISTS: `dregg-lean-ffi/circuit_differential.rs` + `goldens/`). Cost: an import
  cycle to resolve + ~25/42-file ripple. Residual after: `leanc` + the KAT corpus (same status as
  `Poseidon2BabyBearW16`'s bit-exactness — validation, not ∀-proof).
- **(B)** keep it opaque, name `StarkSound` an explicit floor/TCB item with its caveats.
This is a design choice. Do NOT pick it in a proof lane; surface it to ember.

### #4 — FriExtract (SEPARATE campaign: the recursive/aggregated apex)
NOT single-batch. `AlgoStarkSound.extract` produces a trace, not a child proof; `FriExtract` is the in-circuit
recursion-verifier's soundness (SNARK-of-a-fixed-verifier). Its committed witness is HOLLOW (`3ee8b5ee8`, over
`witVerify := fun _ => true`). A real `FriExtract` needs in-circuit⟹native knowledge extraction + `oracle_binding`
(HashCR). Own campaign; do not conflate with the single-batch StarkSound path.

### residuals on proved bricks (small, real)
- #2's union-bound → transcript-measure wiring. #7's deployed bus COLUMN LAYOUT (hbus is reduced, not discharged).
- #3's `hplumb` (Merkle→HashCR) + `hcode_sat`. The 2 table-emptiness facts + pub-link in `AlgoStarkSoundInstance`.

## THE ENDGAME (composition order, once K lands)
K (`verifyAlgo ⟹ MainAirAccept`) + `AlgoStarkSoundInstance` (`MainAirAccept ⟹ AlgoStarkSound`) ⟹ a real
`instance : AlgoStarkSound` at transferV3, modulo {floor: hbus/Merkle-HashCR; data: table-emptiness, pub-link}.
Then `StarkSound = AlgoStarkSound + DeployedRefines`, and DeployedRefines ⟶ (A) or (B) above. FriExtract stays a
separate campaign for the recursive apex.
