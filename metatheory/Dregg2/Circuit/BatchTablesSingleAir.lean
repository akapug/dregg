import Dregg2.Circuit.FriVerifier
import Dregg2.Tactics

/-!
# Dregg2.Circuit.BatchTablesSingleAir — the FAITHFUL single-AIR OOD quotient check

## Why this file exists (P4 — SingleAirQuotientRetarget)

`FriVerifier.batchTablesCheck` (`FriVerifier.lean:688`) checks the per-table OOD
quotient identity by reading THREE FREE record fields off `TableOpening` —
`constraintEval`, `vanishingAtZeta`, `quotientAtZeta` — and asserting
`constraintEval = vanishingAtZeta · quotientAtZeta`. Those fields are opaque
prover-chosen scalars: the model NEVER computes the folded AIR constraint from an
alpha-RLC, NEVER recomposes the quotient from its chunks, and NEVER uses the
verifier-computed `inv_vanishing`. It denotes the WRONG Rust — it would accept a
proof that carries any consistent `(C, Z_H, q)` triple regardless of how those
values relate to the actual constraint polynomial, the actual quotient chunks, or
the actual RLC challenge.

The deployed single-AIR path is `p3_uni_stark::verify_constraints`
(`plonky3 82cfad7, uni-stark/src/verifier.rs:103`), driven from
`circuit/src/effect_vm/verify.rs`. It does exactly this:

  * `air.eval(&mut folder)` accumulates the constraints with the RLC challenge
    `alpha` via the folder's `assert_zero`: `accumulator = accumulator * alpha +
    constraint` (`uni-stark/src/folder.rs:215-217`). So the folded constraint value
    is the HORNER RLC `C(ζ) = Σ_i c_i(ζ) · alpha^{n-1-i}`, NOT a free scalar.
  * `recompose_quotient_from_chunks` (`verifier.rs:59`) reconstructs `q(ζ) =
    Σ_c zps_c · chunk_c(ζ)` from the OPENED quotient chunks and the Lagrange
    chunk-selector coefficients `zps`. So the quotient value is a RECOMPOSITION of
    the opened chunks, NOT a free scalar.
  * the acceptance test is `folded_constraints * sels.inv_vanishing == quotient`
    (`verifier.rs:157`), where `sels.inv_vanishing = 1 / Z_H(ζ)` is COMPUTED by the
    verifier from the trace domain (`selectors_at_point`). Equivalently
    `C(ζ) = Z_H(ζ) · q(ζ)`, but the Rust literally multiplies by the computed
    inverse.

`batchTablesCheckUnified` below models the identity in the Rust's own shape:
`foldedConstraints · invVanishing = recomposedQuotient`, with `invVanishing` PINNED
to be the genuine inverse of the (recomputed) vanishing `Z_H(ζ) = ζ^{2^db} − 1`.
`foldedConstraints` and `recomposedQuotient` are DERIVED from the constraint-eval
list + alpha and the chunk list + zps respectively — closing all three gaps the
free-field model left open.

This module is ADDITIVE: it defines a new opening record `SingleAirOpening` and a
new check `batchTablesCheckUnified`. It does not touch `TableOpening`,
`batchTablesCheck`, `fullChecks`, or `verifyAlgoUnified`. The wiring residual is
NAMED at the end of the file.
-/

namespace Dregg2.Circuit.BatchTablesSingleAir

open Dregg2.Circuit.FriVerifier

/-- One AIR instance opened at the Fiat-Shamir OOD point `ζ`, carrying the DERIVATION
INPUTS the deployed single-AIR verifier consumes (not the pre-collapsed scalars the
free-field model carried):

  * `zeta` — the OOD point `ζ` (`verifier.rs:391`);
  * `degreeBits`/`expectedDegreeBits` — the trace-domain size `n = 2^degreeBits` and
    the VK-pinned value it must equal (the `validate_degree_bits` / range-table
    `LIMB_BITS` pin);
  * `alpha` — the constraint-RLC challenge sampled AFTER the trace commitment
    (`verifier.rs:379`);
  * `constraintEvals` — the per-constraint evaluations `c_i(ζ)` the AIR emits, in
    `assert_zero` emission order (what `air.eval` folds);
  * `zps` — the Lagrange chunk-selector coefficients (one per quotient chunk),
    computed in `recompose_quotient_from_chunks` (`verifier.rs:67-83`);
  * `quotientChunks` — the OPENED quotient-chunk evaluations `chunk_c(ζ)`;
  * `vanishing` — the vanishing value `Z_H(ζ) = ζ^{2^degreeBits} − 1`;
  * `invVanishing` — the verifier-COMPUTED `sels.inv_vanishing = 1/Z_H(ζ)`;
  * `logupCumSum` — this instance's net contribution to the logup interaction bus. -/
structure SingleAirOpening (F : Type) where
  zeta : F
  degreeBits : Nat
  expectedDegreeBits : Nat
  alpha : F
  constraintEvals : List F
  zps : List F
  quotientChunks : List F
  vanishing : F
  invVanishing : F
  logupCumSum : F

/-- **The folded AIR constraint `C(ζ)`**, DERIVED not carried. Mirrors the deployed
folder accumulator (`folder.rs:215-217`: `accumulator = accumulator * alpha +
constraint`) exactly — a left Horner fold of the per-constraint evaluations with the
RLC challenge `alpha`, giving `Σ_i c_i · alpha^{n-1-i}`. The free-field model FAKED
this as an opaque `constraintEval` scalar. -/
def foldedConstraints {F : Type} (A : FieldArith F) (o : SingleAirOpening F) : F :=
  o.constraintEvals.foldl (fun acc c => A.add (A.mul acc o.alpha) c) A.zero

/-- **The recomposed quotient `q(ζ)`**, DERIVED not carried. Mirrors
`recompose_quotient_from_chunks` (`verifier.rs:87-95`): `Σ_c zps_c · chunk_c(ζ)`, the
Lagrange-weighted sum of the OPENED quotient-chunk evaluations. The free-field model
FAKED this as an opaque `quotientAtZeta` scalar; tampering an opened chunk now
genuinely moves this value. -/
def recomposedQuotient {F : Type} (A : FieldArith F) (o : SingleAirOpening F) : F :=
  (o.zps.zip o.quotientChunks).foldr
    (fun p acc => A.add (A.mul p.1 p.2) acc) A.zero

/-- The logup interaction-bus running sum across instances (`add`-fold from `zero`),
mirroring `busSum` for the free-field model. -/
def busSumSA {F : Type} (A : FieldArith F) (os : List (SingleAirOpening F)) : F :=
  (os.map (fun o => o.logupCumSum)).foldr A.add A.zero

/-- **The faithful single-AIR OOD check for one instance.** Four teeth, each mapping
to a concrete Rust line:

  1. `degreeBits = expectedDegreeBits` — the VK degree pin (`validate_degree_bits`);
  2. `Z_H(ζ) + 1 = ζ^{2^degreeBits}` — the vanishing recompute (semiring form of
     `Z_H(ζ) = ζ^n − 1`, `n = 2^degreeBits`);
  3. `Z_H(ζ) · invVanishing = 1` — `invVanishing` is the GENUINE inverse the verifier
     computes (`selectors_at_point`), not a free prover scalar. This tooth is entirely
     ABSENT from the free-field model, which never used `inv_vanishing`;
  4. `foldedConstraints · invVanishing = recomposedQuotient` — the deployed acceptance
     test `folded_constraints * sels.inv_vanishing == quotient` (`verifier.rs:157`),
     with BOTH sides derived from the real inputs. -/
def singleAirOk {F : Type} [DecidableEq F]
    (A : FieldArith F) (o : SingleAirOpening F) : Bool :=
  decide (o.degreeBits = o.expectedDegreeBits)
    && decide (A.add o.vanishing A.one = A.pow o.zeta (2 ^ o.degreeBits))
    && decide (A.mul o.vanishing o.invVanishing = A.one)
    && decide (A.mul (foldedConstraints A o) o.invVanishing = recomposedQuotient A o)

/-- **The faithful batch/single-AIR table check.** Runs `singleAirOk` on every opened
instance and checks the logup bus nets to `zero`. Drop-in replacement for
`batchTablesCheck` that denotes the RIGHT Rust (the deployed uni-stark
`verify_constraints`). -/
def batchTablesCheckUnified {F : Type} [DecidableEq F]
    (A : FieldArith F) (os : List (SingleAirOpening F)) : Bool :=
  os.all (singleAirOk A) && decide (busSumSA A os = A.zero)

/-! ## The teeth (REAL, proven). -/

/-- **Tampered-quotient tooth.** If the derived quotient identity
`foldedConstraints · invVanishing = recomposedQuotient` FAILS, the instance REJECTS.
Because `recomposedQuotient` is `Σ zps_c · chunk_c`, tampering ANY opened quotient
chunk (or any constraint eval / alpha) moves a side and trips this — a prover cannot
forge the quotient. -/
theorem singleAirOk_rejects_tampered_quotient {F : Type} [DecidableEq F]
    (A : FieldArith F) (o : SingleAirOpening F)
    (h : A.mul (foldedConstraints A o) o.invVanishing ≠ recomposedQuotient A o) :
    singleAirOk A o = false := by
  unfold singleAirOk
  rw [Bool.and_eq_false_iff]; right
  exact decide_eq_false h

#assert_axioms singleAirOk_rejects_tampered_quotient

/-- **Forged-inverse tooth** (the field the free-field model never had). If the
carried `invVanishing` is NOT the genuine inverse of the recomputed vanishing
`Z_H(ζ)`, the instance REJECTS — so the acceptance test `folded · invVanishing =
quotient` cannot be satisfied by choosing a bogus `invVanishing`; it is pinned to the
verifier's computed `1/Z_H(ζ)`. -/
theorem singleAirOk_rejects_forged_inverse {F : Type} [DecidableEq F]
    (A : FieldArith F) (o : SingleAirOpening F)
    (h : A.mul o.vanishing o.invVanishing ≠ A.one) :
    singleAirOk A o = false := by
  unfold singleAirOk
  rw [Bool.and_eq_false_iff]; left
  rw [Bool.and_eq_false_iff]; right
  exact decide_eq_false h

#assert_axioms singleAirOk_rejects_forged_inverse

/-- **Wrong-degree tooth.** A declared `degreeBits` differing from the VK-expected
value REJECTS (the range-table `LIMB_BITS` / `validate_degree_bits` pin). -/
theorem singleAirOk_rejects_wrong_degree {F : Type} [DecidableEq F]
    (A : FieldArith F) (o : SingleAirOpening F)
    (h : o.degreeBits ≠ o.expectedDegreeBits) :
    singleAirOk A o = false := by
  unfold singleAirOk
  rw [Bool.and_eq_false_iff]; left
  rw [Bool.and_eq_false_iff]; left
  rw [Bool.and_eq_false_iff]; left
  exact decide_eq_false h

#assert_axioms singleAirOk_rejects_wrong_degree

/-- **Tampered-quotient propagates to the batch.** A single instance whose quotient
identity fails REJECTS the whole `batchTablesCheckUnified` (`List.all` is false once
any element is). -/
theorem batchTablesCheckUnified_rejects_tampered_quotient {F : Type} [DecidableEq F]
    (A : FieldArith F) (os : List (SingleAirOpening F)) (o : SingleAirOpening F)
    (hmem : o ∈ os)
    (h : A.mul (foldedConstraints A o) o.invVanishing ≠ recomposedQuotient A o) :
    batchTablesCheckUnified A os = false := by
  unfold batchTablesCheckUnified
  rw [Bool.and_eq_false_iff]; left
  rw [List.all_eq_false]
  exact ⟨o, hmem, by rw [singleAirOk_rejects_tampered_quotient A o h]; decide⟩

#assert_axioms batchTablesCheckUnified_rejects_tampered_quotient

/-- **Unbalanced-bus tooth.** If the logup cumulative sums do not net to `zero`, the
batch REJECTS — a prover cannot inject unmatched bus messages. -/
theorem batchTablesCheckUnified_rejects_unbalanced_bus {F : Type} [DecidableEq F]
    (A : FieldArith F) (os : List (SingleAirOpening F))
    (h : busSumSA A os ≠ A.zero) :
    batchTablesCheckUnified A os = false := by
  unfold batchTablesCheckUnified
  rw [Bool.and_eq_false_iff]; right
  exact decide_eq_false h

#assert_axioms batchTablesCheckUnified_rejects_unbalanced_bus

/-! ## Executable non-vacuity over `ℤ` (genuine ring arithmetic + bus cancellation).

An honest single-AIR instance ACCEPTS; a tampered quotient CHUNK, a tampered
constraint eval, a forged inverse, a wrong degree, and an unbalanced bus all REJECT.
The vanishing is chosen invertible over `ℤ` (`Z_H = 1` at `ζ = 2`, `degreeBits = 0`)
so the genuine-inverse tooth has real content without needing a prime field. -/
section NonVacuity

/-- The `ℤ` field-op bundle: `pow` is manual repeated `mul` (no `HPow ℤ ℕ` imported),
so the `#guard`s evaluate real ring arithmetic. Mirrors `FriVerifier`'s `intArithSA`. -/
private def intArithSA : FieldArith Int :=
  { add := (· + ·), mul := (· * ·), zero := 0, one := 1,
    pow := fun b n => Nat.rec 1 (fun _ acc => b * acc) n }

-- ζ=2, db=0 ⇒ pow 2 (2^0) = pow 2 1 = 2·(pow 2 0) = 2·1 = 2, and Z_H = ζ−1 = 1.
#guard intArithSA.pow 2 (2 ^ 0) = 2

/-- Honest instance at `ζ = 2`, `degreeBits = 0`: `Z_H(2) = 2 − 1 = 1`,
`invVanishing = 1`. `alpha = 3`, constraint evals `[2, 4]` ⇒ Horner fold
`(0·3+2)·3+4 = 10`. Quotient chunk `[10]` with `zps = [1]` ⇒ recomposed `10`.
Identity: `10 · 1 = 10`. Bus contribution `+5`. -/
private def honestAir : SingleAirOpening Int :=
  { zeta := 2, degreeBits := 0, expectedDegreeBits := 0, alpha := 3,
    constraintEvals := [2, 4], zps := [1], quotientChunks := [10],
    vanishing := 1, invVanishing := 1, logupCumSum := 5 }

/-- A matching honest instance whose bus contribution `−5` cancels `honestAir`'s `+5`.
`alpha = 2`, constraint evals `[3]` ⇒ fold `3`; chunk `[3]`, `zps = [1]` ⇒ recomposed
`3`; `3 · 1 = 3`. -/
private def honestAir2 : SingleAirOpening Int :=
  { zeta := 2, degreeBits := 0, expectedDegreeBits := 0, alpha := 2,
    constraintEvals := [3], zps := [1], quotientChunks := [3],
    vanishing := 1, invVanishing := 1, logupCumSum := -5 }

/-- `honestAir` with a TAMPERED opened quotient chunk (`[10] → [11]`): `recomposedQuotient`
moves to `11` while `foldedConstraints · invVanishing = 10`, so the OOD identity fails. -/
private def tamperedQuotientAir : SingleAirOpening Int :=
  { honestAir with quotientChunks := [11] }

-- The derived quantities compute the way the Rust does.
#guard foldedConstraints intArithSA honestAir = 10          -- Horner RLC of [2,4] with alpha=3
#guard recomposedQuotient intArithSA honestAir = 10         -- Σ zps·chunk = 1·10

-- Single-instance: honest ACCEPTS; each tamper REJECTS.
#guard singleAirOk intArithSA honestAir = true
#guard singleAirOk intArithSA tamperedQuotientAir = false                        -- tampered chunk
#guard singleAirOk intArithSA { honestAir with constraintEvals := [2, 5] } = false -- tampered constraint
#guard singleAirOk intArithSA { honestAir with invVanishing := 2 } = false        -- forged inverse
#guard singleAirOk intArithSA { honestAir with degreeBits := 1 } = false          -- wrong degree

-- Batch: honest two-instance batch (bus cancels) ACCEPTS; tamper / unbalance REJECT.
#guard batchTablesCheckUnified intArithSA [honestAir, honestAir2] = true
#guard batchTablesCheckUnified intArithSA [tamperedQuotientAir, honestAir2] = false -- tampered quotient
#guard batchTablesCheckUnified intArithSA
    [{ honestAir with logupCumSum := 6 }, honestAir2] = false                  -- unbalanced bus

/-- Non-vacuity as a theorem (not just `#guard`): the honest batch accepts AND a
tampered-quotient batch rejects — the check SEPARATES the two, so it is not
constantly-true. -/
theorem batchTablesCheckUnified_accepts_honest :
    batchTablesCheckUnified (F := Int) intArithSA [honestAir, honestAir2] = true := by
  decide

theorem batchTablesCheckUnified_rejects_tampered_fixture :
    batchTablesCheckUnified (F := Int) intArithSA
        [tamperedQuotientAir, honestAir2] = false := by
  decide

#assert_axioms batchTablesCheckUnified_accepts_honest
#assert_axioms batchTablesCheckUnified_rejects_tampered_fixture

end NonVacuity

/-! ## NAMED residual — wiring `batchTablesCheckUnified` into `verifyAlgoUnified`

`verifyAlgoUnified` (`FriChallengerUnified.lean:180`) runs `fullChecks core A toNat
params.powBits` whose `batchTables` conjunct (`FriVerifier.lean:718`) is
`fun proof _betas => batchTablesCheck A proof` — the WRONG-Rust free-field check this
module retargets. To make the deployed single-AIR quotient path FAITHFUL end-to-end,
three edits are needed (all deferred to the supervisor merge — none is done here, so
this stays a NAMED residual, not an axiom):

  1. **Carry the derivation inputs on the proof.** `BatchProofData`
     (`FriVerifier.lean:382`) currently exposes only the collapsed scalars via
     `tableOpenings : List (TableOpening F)`. Add an additive field
     `singleAirOpenings : List (SingleAirOpening F) := []` (or migrate `TableOpening`
     to carry `alpha`/`constraintEvals`/`zps`/`quotientChunks`/`invVanishing`). This
     is the one shared-struct change and must be reported precisely when taken.

  2. **Retarget the `batchTables` conjunct.** Define a `fullChecksFaithful` variant of
     `fullChecks` with
     `batchTables := fun proof _betas => batchTablesCheckUnified A proof.singleAirOpenings`,
     and a `verifyAlgoUnifiedFaithful` that uses it. Keep `fullChecks`/`verifyAlgoUnified`
     intact (additive variant, per the coordination rule).

  3. **Bind `alpha` and `zeta` to the transcript.** `singleAirOpening.alpha` must equal
     the `deriveTranscript` constraint-RLC challenge (sampled after the trace commitment,
     `verifier.rs:379`) and `singleAirOpening.zeta` must equal the one-thread ζ already
     bound by `unifiedTranscriptChecks` (`proof.oodPoint = d.ζ`, `FriChallengerUnified.lean:171`).
     Without this bind, `alpha`/`zeta` remain free prover choices and the RLC-fold is
     defeatable — this is the transcript-binding tooth the *quotient* retarget still owes,
     the exact analogue of the `betasBound` fix for the fold betas.

Teeth already proven here (`singleAirOk_rejects_tampered_quotient`,
`_rejects_forged_inverse`, `_rejects_wrong_degree`, `batchTablesCheckUnified_rejects_*`)
transport to the wired verifier the moment conjunct 2 lands, exactly as the
`batchTablesCheck` teeth transported through `fullChecks`. -/

end Dregg2.Circuit.BatchTablesSingleAir
