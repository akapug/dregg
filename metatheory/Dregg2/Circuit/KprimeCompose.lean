/-
# `Dregg2.Circuit.KprimeCompose` — the K′ chain COMPOSED end-to-end.

Tonight's three K′ pieces exist separately in the tree:

  (a) K′(a) — `FieldIntegerLift.ood_forces_mainAirAccept_field_of_residuals`: the OOD landing on the
      REAL `VmTrace`, with the domain axis (`vanishingPoly t`, `hZrow`) and the interpolation axis
      (`TraceColumnInterp.constraintPoly_eval_eq_arithResidual`) already discharged;
  (b) K′(b) — `TraceColumnInterp.constraintPoly`: the committed trace-column interpolation of every
      arithmetic constraint (baked into (a) via `OodInterpF.hCrow`);
  (c) K′(c) — `OodQuotientConsistency.rlc_batch_split_of_combined`: the RLC constraint-batching
      split, from the ONE combined identity `verifyAlgo` delivers to the per-constraint residuals.

This file COMPOSES them into one theorem over the DEPLOYED BabyBear field (`ZMod 2013265921`):
from (i) the single RLC-COMBINED OOD identity `∑ᵢ Rᵢ(ζ)·αⁱ = 0` (the shape `verifyAlgo` checks),
(ii) `α`/`ζ` non-exceptional (Fiat–Shamir), and (iii) the domain cap `t.rows.length ≤ 2^27`,
conclude `MainAirAcceptF d t`. Inside the composition NO interpolation, domain, or RLC residual
remains open: the per-constraint residuals `Rᵢ` are the MODELED ones (`constraintPoly` minus
`vanishingPoly · qp`, both committed objects), the split is the REAL `rlc_batch_split_of_combined`,
and the landing is the REAL `ood_forces_mainAirAccept_field_of_residuals`.

## The ONE remaining honest identification (`hCombinedIsRlc`)

`verifyAlgo`'s `TableOpening.constraintEval` is an OPAQUE field element; the tree does not (yet)
prove that it equals the RLC `∑ᵢ (Cᵢ(ζ) − Z_H(ζ)·qᵢ(ζ))·αⁱ` of the MODELED per-constraint
residuals — that is the commitment-opening link. The outer theorem
`kprime_compose_of_tableIdentity` therefore carries it as ONE clearly-named Prop HYPOTHESIS,
`hCombinedIsRlc` (never an axiom): given the table identity `constraintEval = vanishingAtZeta ·
quotientAtZeta` that `verifyAlgo_accept_forces_table_identity` extracts from acceptance, plus
`hCombinedIsRlc`, the whole chain closes to `MainAirAcceptF d t`.

## FIRE

`kprime_compose_fires` runs the full composition on the committed toy descriptor
`AirChecksSatisfied.dArith` (one REAL arithmetic gate `col 0 = 0`) and the committed honest trace
`tHonest`, with every hypothesis — including `hCombinedIsRlc` — actually DISCHARGED (the honest
all-zero column interpolates to the zero polynomial, so the modeled residuals vanish and both
non-exceptionality sets are empty). The hypothesis package is satisfiable; the composition is not
vacuous.
-/
import Dregg2.Circuit.FieldIntegerLift
import Dregg2.Circuit.OodQuotientConsistency

namespace Dregg2.Circuit.KprimeCompose

open Polynomial
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.AirChecksSatisfied
open Dregg2.Circuit.BabyBearFriField
open Dregg2.Circuit.TraceColumnInterp
open Dregg2.Circuit.OodQuotientConsistency
open Dregg2.Circuit.FieldIntegerLift
open Dregg2.Exec.CircuitEmit (EmittedExpr)

/-! ## §1 — The modeled per-constraint OOD residual vector. -/

/-- **The `i`-th MODELED per-constraint OOD residual at ζ** — `Rᵢ(ζ) = Cᵢ(ζ) − Z_H(ζ)·qᵢ(ζ)`, with
`Cᵢ` the COMMITTED trace-column interpolation `constraintPoly d t (d.constraints[i])` (K′(b)) and
`Z_H` the COMMITTED domain vanisher `vanishingPoly t` (K′(a)'s discharged axis). These are exactly
the coefficients of the RLC batching polynomial the split (K′(c)) runs on; out-of-range indices
contribute `0` (they never arise under `Finset.range d.constraints.length`). -/
noncomputable def constraintResidualAtZeta (d : EffectVmDescriptor2) (t : VmTrace)
    (ζ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear) (i : ℕ) : BabyBear :=
  if h : i < d.constraints.length then
    (constraintPoly d t (d.constraints[i]'h)).eval ζ
      - (vanishingPoly t).eval ζ * (qp (d.constraints[i]'h)).eval ζ
  else 0

/-! ## §2 — The composition: combined RLC identity ⟹ `MainAirAcceptF`. -/

/-- **K′ COMPOSED (inner form).** From the SINGLE combined OOD identity
`∑ᵢ Rᵢ(ζ)·αⁱ = 0` over the modeled per-constraint residuals (the RLC-batched shape `verifyAlgo`
checks), a non-exceptional batching challenge `α`, a non-exceptional OOD point `ζ`, and the
deployed domain cap, conclude the canonical field AIR acceptance `MainAirAcceptF d t`.

The chain, with NO open interpolation/domain/RLC residual inside:
`rlc_batch_split_of_combined` (K′(c), Schwartz–Zippel in α) splits the combined identity into the
per-constraint `hood`; `vanishingPoly t` supplies the domain axis; and
`ood_forces_mainAirAccept_field_of_residuals` (K′(a), Schwartz–Zippel in ζ, with K′(b)'s
interpolation baked in) lands `MainAirAcceptF`. -/
theorem kprime_compose (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize)
    (ζ α : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (hCombined : ∑ i ∈ Finset.range d.constraints.length,
        constraintResidualAtZeta d t ζ qp i * α ^ i = 0)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZeta d t ζ qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t := by
  have hsplit := rlc_batch_split_of_combined d.constraints.length
    (constraintResidualAtZeta d t ζ qp) α hCombined hαnonexc
  refine ood_forces_mainAirAccept_field_of_residuals d t hcap ζ qp ?_ hζnonexc
  intro c hc _
  obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hc
  have h0 := hsplit i hi
  unfold constraintResidualAtZeta at h0
  rw [dif_pos hi, hci] at h0
  exact sub_eq_zero.mp h0

/-- **K′ COMPOSED (outer, verifier-facing form).** `verifyAlgo` acceptance delivers, per opened
table, the identity `constraintEval = vanishingAtZeta · quotientAtZeta` on OPAQUE field elements
(`verifyAlgo_accept_forces_table_identity`). The ONE honest identification the tree does not yet
prove is that the combined table residual `constraintEval − vanishingAtZeta·quotientAtZeta` IS the
RLC of the MODELED per-constraint residuals — carried here as the single named Prop hypothesis
`hCombinedIsRlc` (the commitment-opening link; NOT an axiom). Everything else is closed:
table identity + `hCombinedIsRlc` ⟹ combined RLC identity ⟹ (by `kprime_compose`)
`MainAirAcceptF d t`. -/
theorem kprime_compose_of_tableIdentity (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize)
    (ζ α : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (constraintEval vanishingAtZeta quotientAtZeta : BabyBear)
    (hTable : constraintEval = vanishingAtZeta * quotientAtZeta)
    (hCombinedIsRlc : constraintEval - vanishingAtZeta * quotientAtZeta
        = ∑ i ∈ Finset.range d.constraints.length,
            constraintResidualAtZeta d t ζ qp i * α ^ i)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZeta d t ζ qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t :=
  kprime_compose d t hcap ζ α qp
    (by rw [← hCombinedIsRlc, hTable, sub_self]) hαnonexc hζnonexc

/-! ## §3 — FIRE: the whole composition runs on the committed `dArith`/`tHonest`, every hypothesis
discharged (including `hCombinedIsRlc`). -/

/-- The honest all-zero column interpolates to the ZERO polynomial: every node value of the
Lagrange interpolation is `0` (real rows read `zRow`, off-the-end reads `zeroAsg`), and the
interpolation map is linear. -/
theorem colPoly_tHonest_zero : colPoly tHonest 0 = 0 := by
  have hv : (fun i => ((tHonest.rows.getD i zeroAsg 0 : ℤ) : BabyBear)) = (0 : ℕ → BabyBear) := by
    funext i
    rcases i with _ | _ | i <;> simp [tHonest, zRow, zeroAsg, List.getD]
  unfold colPoly rowPoly
  rw [hv]
  exact map_zero _

/-- The modeled composition polynomial of `dArith`'s one real gate over the honest trace is the
zero polynomial (the gate reads exactly the all-zero column). -/
theorem constraintPoly_dArith_tHonest_zero :
    constraintPoly dArith tHonest (.base (.gate (.var 0))) = 0 := by
  simp only [constraintPoly, exprPoly, colPoly_tHonest_zero, mul_zero]

/-- With the honest quotient choice `qp = 0`, EVERY modeled per-constraint residual of
`dArith`/`tHonest` at ζ = 5 vanishes — the residual vector is literally the zero function. -/
theorem constraintResidualAtZeta_dArith_tHonest_zero :
    constraintResidualAtZeta dArith tHonest 5 (fun _ => 0) = (fun _ => 0) := by
  funext i
  unfold constraintResidualAtZeta
  split
  · next h =>
      have hi0 : i = 0 := by
        have h1 : i < 1 := by simpa [dArith] using h
        omega
      subst hi0
      rw [show dArith.constraints[0]'h = VmConstraint2.base (.gate (.var 0)) from rfl,
        constraintPoly_dArith_tHonest_zero]
      simp
  · rfl

/-- **FIRE — the composed K′ chain actually runs.** On the committed toy descriptor `dArith` (one
REAL arithmetic gate `col 0 = 0`) and the committed honest trace `tHonest`, EVERY hypothesis of
`kprime_compose_of_tableIdentity` is discharged — the table identity (`0 = 0·0`), the
`hCombinedIsRlc` identification (both sides compute to `0`), and both non-exceptionality sets
(empty, since the modeled residual polynomials are `0`) — and the composition produces the same
`MainAirAcceptF dArith tHonest` the committed `honest_mainAirAcceptF` exhibits. The hypothesis
package is SATISFIABLE; the composition is not vacuous. -/
theorem kprime_compose_fires : MainAirAcceptF dArith tHonest :=
  kprime_compose_of_tableIdentity dArith tHonest
    (by norm_num [tHonest, domainSize])
    5 7 (fun _ => 0) 0 0 0
    (by ring)
    (by rw [constraintResidualAtZeta_dArith_tHonest_zero]; simp)
    (by rw [constraintResidualAtZeta_dArith_tHonest_zero]
        simp [exceptionalSet, rlcResidualPoly])
    (by intro c hc _
        simp only [dArith, List.mem_singleton] at hc
        subst hc
        rw [constraintPoly_dArith_tHonest_zero]
        simp [exceptionalSet])

#assert_axioms kprime_compose
#assert_axioms kprime_compose_of_tableIdentity
#assert_axioms colPoly_tHonest_zero
#assert_axioms constraintPoly_dArith_tHonest_zero
#assert_axioms constraintResidualAtZeta_dArith_tHonest_zero
#assert_axioms kprime_compose_fires

end Dregg2.Circuit.KprimeCompose
