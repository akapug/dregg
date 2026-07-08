/-
# `Dregg2.Crypto.HermineSelfTargetMSIS` — the SelfTargetMSIS discharge of `u ≠ 0`.

This file gives the discharge of the `u ≠ 0` leg of the Hermine/Raccoon MSIS reduction that Dilithium
and Raccoon ACTUALLY use — **SelfTargetMSIS** — and it SUPERSEDES the ROLE of the `IsUnit (c − c')`
challenge-difference-invertibility route in `Dregg2.Crypto.HermineDischarge`.

## Why the invertibility route is not the load-bearing argument

`HermineDischarge.lossiness_discharges_nonzero` discharges `u ≠ 0` from MLWE lossiness **plus** the
hypothesis `IsUnit (c − c')` — that the difference of two distinct challenges is a unit in `R_q`. That is
correct mathematics, but it is only satisfiable in a *partially-splitting* ring (the Lyubashevsky–Seiler
regime, `n = 2^k` with `k ≤ 8`), OUTSIDE the deployed regime. At Dilithium/Raccoon parameters the ring is
`ℤ_q[X]/(X²⁵⁶+1)` with `q ≈ 8380417`, and the bound that would force a challenge difference to be a unit is
`‖c − c'‖ < q^(1/256) ≈ 1.06 < 2` — no nonzero challenge difference is that small. So `IsUnit (c − c')`
is *not achievable at deployed parameters*; the `InvertibilityHadamard`/tight/norm suite is a real but
alternative construction (`k ≤ 8`), not the argument Hermine's security actually rests on.

## What Dilithium and Raccoon actually use: SelfTargetMSIS

The Fiat–Shamir challenge is bound INTO the M-SIS relation. A forgery is a short `(z, c, u')` with
`H([A | t | I] · (z, c, u') ‖ M) = c` — the challenge is a *fixed point* of the random oracle on the
augmented instance. Rearranged, that is exactly the Hermine verify equation `A·z = u' + c·t` (i.e.
`A·z − c·t − u' = 0 ⟺ [A | −t | −I]·(z, c, u') = 0`). Two forked forgeries share the commitment `u' = w`
but carry DISTINCT challenges `c ≠ c'`. Subtracting the two verify equations cancels the commitment:

  `A·(z − z') = (c − c')·t`, i.e. `[A | t]·(z − z', −(c − c')) = 0`,

a solution of Module-SIS on the augmented map `[A | t]`. Its non-triviality is FREE: the challenge sits in
its own coordinate of the solution vector, so `c ≠ c'` forces `−(c − c') ≠ 0` DIRECTLY — no unit, no
invertibility, and (unlike the invertibility route) no MLWE-lossiness needed for this leg. This is strictly
cleaner than `HermineDischarge`: the `u ≠ 0` obligation is discharged by `c ≠ c'` alone.

We reuse `HermineThreshold.verify` (so the SelfTargetMSIS relation is the SAME verify object) and the
extractor `Hermine.hermine_special_soundness_extracts_relation` (the subtraction step, no invertibility),
and land the difference as a genuine `Lattice.IsMSISSolution` on the augmented `[A | t]` map.
-/
import Dregg2.Crypto.HermineMSIS
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.ZMod.Basic

namespace Dregg2.Crypto.HermineSelfTargetMSIS

open Dregg2.Crypto.Lattice

/-! ### The augmented short-norm on `M × R_q` (the `[A | t]` solution space). -/

section ProdNorm
variable {P Q : Type*} [AddCommGroup P] [ShortNorm P] [AddCommGroup Q] [ShortNorm Q]

/-- The coordinate-sum seminorm on the augmented solution space `M × R_q`: the solution vector of the
`[A | t]` map carries the response difference in the first coordinate and the challenge difference in the
second, so its shortness is the sum of the two coordinate norms. -/
scoped instance instShortNormProd : ShortNorm (P × Q) where
  nrm p := nrm p.1 + nrm p.2
  nrm_zero := by simp [nrm_zero]
  nrm_neg p := by simp [nrm_neg]
  nrm_add_le a b := by
    show nrm (a.1 + b.1) + nrm (a.2 + b.2) ≤ (nrm a.1 + nrm a.2) + (nrm b.1 + nrm b.2)
    calc nrm (a.1 + b.1) + nrm (a.2 + b.2)
          ≤ (nrm a.1 + nrm b.1) + (nrm a.2 + nrm b.2) :=
            Nat.add_le_add (nrm_add_le _ _) (nrm_add_le _ _)
      _ = (nrm a.1 + nrm a.2) + (nrm b.1 + nrm b.2) := by ring

end ProdNorm

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- The augmented map `[A | t] : M × R_q → N`, `(m, r) ↦ A·m + r·t`. Its kernel encodes the
SelfTargetMSIS relation: `[A | t]·(z, c') = 0 ⟺ A·z = −c'·t`, and a forked forgery's difference
`(z − z', −(c − c'))` lands in it. Built from the public matrix `A` and the public key `t` alone — the
signer's secret `s` never appears (the whole point of SelfTargetMSIS over the invertibility route). -/
def augmented (A : M →ₗ[Rq] N) (t : N) : (M × Rq) →ₗ[Rq] N :=
  A.coprod (LinearMap.toSpanSingleton Rq N t)

omit [ShortNorm Rq] [ShortNorm M] [ShortNorm N] in
@[simp] theorem augmented_apply (A : M →ₗ[Rq] N) (t : N) (m : M) (r : Rq) :
    augmented A t (m, r) = A m + r • t := by
  simp [augmented, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]

/-- **The SelfTargetMSIS relation.** A short `(z, c, u')` — `z` the response, `c` the challenge (bound into
the relation by the random oracle), `u'` the commitment — satisfying the Hermine/Dilithium verify equation
`A·z = u' + c·t`. Defined against `HermineThreshold.verify`, so it IS the same verify object; a forgery is
exactly a solution of this relation on the augmented instance `[A | t | I]` (the verify equation is that
relation rearranged). -/
def IsSelfTargetMSISSolution (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (z : M) (c : Rq) (u' : N) : Prop :=
  nrm z ≤ β ∧ nrm c ≤ β ∧ nrm u' ≤ β ∧ HermineThreshold.verify A t u' c z

omit [ShortNorm N] in
/-- **THE DISCHARGE — `c ≠ c'` alone yields a NONZERO short MSIS solution (no invertibility).** Two
forgeries `(z, c, w)` and `(z', c', w)` on the SAME commitment `w`, both short and accepting against public
key `t`, with distinct challenges `c ≠ c'`: their difference `(z − z', −(c − c'))` is a genuine Module-SIS
solution for the augmented map `[A | t]`. All three MSIS obligations are DERIVED:
* **kernel** — subtracting the verify equations cancels `w`: `A·(z − z') = (c − c')·t` (the extractor, no
  invertibility), so `[A | t]·(z − z', −(c − c')) = A·(z − z') − (c − c')·t = 0`;
* **short** — `‖(z − z', −(c − c'))‖ = ‖z − z'‖ + ‖c − c'‖ ≤ (β_z + β_z) + (β_c + β_c)` (triangle, both
  legs short: `z, z'` are accepted responses and `c, c'` are challenges);
* **NONZERO** — this is the headline: the challenge occupies the SECOND coordinate of the solution vector,
  so `c ≠ c'` forces `−(c − c') ≠ 0` DIRECTLY, hence the vector is nonzero. No `IsUnit (c − c')`, no MLWE
  lossiness, no `u ≠ 0` hypothesis — `c ≠ c'` is the whole discharge. -/
theorem selftarget_extract_nonzero
    (A : M →ₗ[Rq] N) (t w : N) (c c' : Rq) (z z' : M) (βz βc : ℕ)
    (hz : nrm z ≤ βz) (hz' : nrm z' ≤ βz) (hc : nrm c ≤ βc) (hc' : nrm c' ≤ βc)
    (hne : c ≠ c')
    (h1 : HermineThreshold.verify A t w c z)
    (h2 : HermineThreshold.verify A t w c' z') :
    IsMSISSolution (augmented A t) ((βz + βz) + (βc + βc)) (z - z', -(c - c')) := by
  refine ⟨?_, ?_, ?_⟩
  · -- NONZERO, derived from `c ≠ c'` via the challenge coordinate — the SelfTargetMSIS payoff.
    intro h
    rw [Prod.mk_eq_zero] at h
    exact hne (sub_eq_zero.mp (neg_eq_zero.mp h.2))
  · -- SHORT: coordinate-sum norm, both coordinates bounded by the triangle inequality.
    show nrm (z - z') + nrm (-(c - c')) ≤ (βz + βz) + (βc + βc)
    rw [nrm_neg]
    exact Nat.add_le_add
      (le_trans (nrm_sub_le z z') (Nat.add_le_add hz hz'))
      (le_trans (nrm_sub_le c c') (Nat.add_le_add hc hc'))
  · -- KERNEL: the extractor cancels the shared commitment `w`, then `[A | t]` sends the difference to 0.
    have hrel : A (z - z') = (c - c') • t :=
      Dregg2.Crypto.Hermine.hermine_special_soundness_extracts_relation A t w c c' z z' h1 h2
    rw [augmented_apply, hrel, neg_smul, add_neg_cancel]

/-- **The full reduction, discharged via SelfTargetMSIS.** A forked Hermine forgery — two SelfTargetMSIS
solutions on the same commitment `w` with `c ≠ c'` — yields a Module-SIS solution on the augmented map
`[A | t]`, with NO `u ≠ 0` hypothesis and NO invertibility. Strictly cleaner than the invertibility route:
MLWE lossiness is not even invoked for the non-triviality leg — it comes for free from `c ≠ c'`. -/
theorem forked_forgery_yields_msis_solution_selftarget
    (A : M →ₗ[Rq] N) (t w : N) (c c' : Rq) (z z' : M) (β : ℕ)
    (hne : c ≠ c')
    (hforge : IsSelfTargetMSISSolution A t β z c w)
    (hforge' : IsSelfTargetMSISSolution A t β z' c' w) :
    ∃ v, IsMSISSolution (augmented A t) ((β + β) + (β + β)) v := by
  obtain ⟨hz, hc, _hw, h1⟩ := hforge
  obtain ⟨hz', hc', _hw', h2⟩ := hforge'
  exact ⟨_, selftarget_extract_nonzero A t w c c' z z' β β hz hz' hc hc' hne h1 h2⟩

/-- **Post-quantum unforgeability, down to the line, via SelfTargetMSIS.** If Module-SIS is hard for the
augmented map `[A | t]` at the extracted bound, then no forked Hermine forgery with `c ≠ c'` exists — a
forgery would produce an `IsMSISSolution`, contradicting `MSISHard`. The only irreducible floor left is
MSIS hardness itself; the `u ≠ 0` leg is fully discharged by `c ≠ c'` (no MLWE, no invertibility). -/
theorem no_forgery_under_msis_selftarget
    (A : M →ₗ[Rq] N) (t w : N) (c c' : Rq) (z z' : M) (β : ℕ)
    (hne : c ≠ c')
    (hforge : IsSelfTargetMSISSolution A t β z c w)
    (hforge' : IsSelfTargetMSISSolution A t β z' c' w)
    (hard : MSISHard (augmented A t) ((β + β) + (β + β))) : False :=
  hard (forked_forgery_yields_msis_solution_selftarget A t w c c' z z' β hne hforge hforge')

#assert_axioms augmented_apply
#assert_axioms selftarget_extract_nonzero
#assert_axioms forked_forgery_yields_msis_solution_selftarget
#assert_axioms no_forgery_under_msis_selftarget

/-! ### Teeth — a concrete instance where `c ≠ c'` is load-bearing.

`A = id`, key `t = 1`, commitment `w = 0`, over `ZMod 5`. Two accepting forgeries `(z=1, c=1)` and
`(z'=2, c'=2)` share `w` with `c ≠ c'`; the reduction FIRES and hands back a genuine nonzero MSIS solution
`(z − z', −(c − c')) = (4, 1)` (second coordinate `1 ≠ 0`). Flip to `c = c'` and the challenge coordinate
collapses to `0` — the vector loses its guaranteed non-triviality. So `c ≠ c'` is the tooth. -/

section Teeth

/-- A toy challenge/module ring for the concrete instance. -/
abbrev Fq := ZMod 5

/-- The zero seminorm — every element is `0`-short — so the teeth isolate the NON-TRIVIALITY (the `c ≠ c'`
leg), not shortness. A valid `ShortNorm`. -/
scoped instance : ShortNorm Fq where
  nrm _ := 0
  nrm_zero := rfl
  nrm_neg _ := rfl
  nrm_add_le _ _ := Nat.zero_le _

/-- **Non-vacuity + `c ≠ c'` FIRES.** The abstract reduction, instantiated on real `ZMod 5` data with
`c ≠ c'`, produces an actual `IsMSISSolution` — the hypothesis set is inhabited and the discharge runs. -/
example :
    IsMSISSolution (augmented (LinearMap.id : Fq →ₗ[Fq] Fq) (1 : Fq)) ((0 + 0) + (0 + 0))
      ((1 : Fq) - 2, -((1 : Fq) - 2)) :=
  selftarget_extract_nonzero (LinearMap.id : Fq →ₗ[Fq] Fq) (1 : Fq) (0 : Fq)
    (1 : Fq) (2 : Fq) (1 : Fq) (2 : Fq) 0 0
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [HermineThreshold.verify]) (by simp [HermineThreshold.verify])

-- `c ≠ c'` ⇒ the challenge coordinate of the extracted solution is NONZERO (the vector is a real solution).
#guard decide (-((1 : Fq) - 2) ≠ 0)
-- `c = c'` ⇒ the challenge coordinate COLLAPSES to zero (non-triviality is lost) — the tooth.
#guard decide (-((1 : Fq) - 1) = 0)
-- The augmented map sends the extracted vector to 0 (kernel membership), arithmetic-checked.
#guard decide (((1 : Fq) - 2) + (-((1 : Fq) - 2)) * 1 = 0)

end Teeth

end Dregg2.Crypto.HermineSelfTargetMSIS
