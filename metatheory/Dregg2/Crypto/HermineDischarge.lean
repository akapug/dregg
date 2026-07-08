/-
# `Dregg2.Crypto.HermineDischarge` — discharging the `u ≠ 0` leg of the MSIS reduction.

`HermineMSIS.forked_forgery_yields_msis_solution` produced an MSIS solution `u = (z−z') − (c−c')·s`
*given* `u ≠ 0`, and named that as the MLWE-hides-the-secret leg. This file DISCHARGES it — replaces the
bare hypothesis with a derivation from two more-fundamental, honestly-named parameter properties:

* **MLWE lossiness.** The public key `t = A·s` does NOT pin the signer's secret: there are (at least)
  two distinct short preimages `s ≠ s'` with `A·s = A·s' = t`. This is exactly what Module-LWE buys —
  the secret is information-theoretically hidden among the consistent short preimages. A reduction that
  set up the key itself knows both.
* **Challenge-difference invertibility.** `c − c'` is a UNIT in `R_q`. For the Dilithium/Raccoon
  challenge space (small, sparse polynomials over a well-chosen `q`) the difference of two distinct
  challenges is invertible — a standard, parameter-level lemma.

From these, at least one of the two candidate vectors `(z−z') − (c−c')·s` and `(z−z') − (c−c')·s'` is
NONZERO (were both zero, `(c−c')·(s − s') = 0`, and cancelling the unit `c − c'` forces `s = s'`). So a
forked forgery yields an MSIS solution WITHOUT assuming `u ≠ 0`: the non-triviality is derived. What
remains irreducible is only the *hardness* of MLWE/MSIS themselves (the `Lattice` floor) — the LEG is
gone.
-/
import Dregg2.Crypto.HermineMSIS

namespace Dregg2.Crypto.HermineDischarge

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineMSIS

variable {Rq : Type*} [CommRing Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **Cancelling a unit scalar.** If `c − c'` is a unit and `(c − c') • x = 0`, then `x = 0`. -/
theorem smul_eq_zero_of_isUnit {c c' : Rq} (hinv : IsUnit (c - c')) {x : M}
    (hx : (c - c') • x = 0) : x = 0 := by
  obtain ⟨u, hu⟩ := hinv
  have hx' : (↑u : Rq) • x = 0 := by rw [hu]; exact hx
  have := congrArg (fun y => (↑u⁻¹ : Rq) • y) hx'
  simpa only [smul_smul, Units.inv_mul, one_smul, smul_zero] using this

/-- **The discharge.** Under MLWE lossiness (two distinct short preimages `s ≠ s'` of the same key) and
challenge-difference invertibility (`c − c'` a unit), at least one of the two extracted vectors is
nonzero. Were both zero, `(z−z') = (c−c')·s = (c−c')·s'`, so `(c−c')·(s − s') = 0`, and the unit cancels
to give `s = s'` — contradiction. So the reduction always has a nonzero candidate. -/
theorem lossiness_discharges_nonzero (s s' : M) (c c' : Rq) (z z' : M)
    (hss : s ≠ s') (hinv : IsUnit (c - c')) :
    (z - z') - (c - c') • s ≠ 0 ∨ (z - z') - (c - c') • s' ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨h0, h0'⟩ := h
  rw [sub_eq_zero] at h0 h0'
  have heq : (c - c') • (s - s') = 0 := by
    rw [smul_sub, ← h0, ← h0', sub_self]
  exact hss (sub_eq_zero.mp (smul_eq_zero_of_isUnit hinv heq))

/-- **The reduction, with `u ≠ 0` DISCHARGED.** A forked Hermine forgery against a key `t = A·s = A·s'`
with two distinct short preimages (MLWE lossiness) and an invertible challenge difference yields an MSIS
solution — no `u ≠ 0` hypothesis; it is derived. Whichever candidate `lossiness_discharges_nonzero`
certifies nonzero is fed to `forked_forgery_yields_msis_solution` (the verify facts transport across
`A·s = A·s'`). What is left is only the MLWE-lossiness + invertibility parameter facts and the MSIS
hardness floor — the honest irreducible core. -/
theorem forked_forgery_yields_msis_solution_discharged
    (A : M →ₗ[Rq] N) (s s' : M) (w : N) (c c' : Rq) (z z' : M) (βz βcs : ℕ)
    (hss : s ≠ s') (ht : A s = A s') (hinv : IsUnit (c - c'))
    (hz : nrm z ≤ βz) (hz' : nrm z' ≤ βz)
    (hcs : nrm ((c - c') • s) ≤ βcs) (hcs' : nrm ((c - c') • s') ≤ βcs)
    (h1 : HermineThreshold.verify A (A s) w c z)
    (h2 : HermineThreshold.verify A (A s) w c' z') :
    ∃ u, IsMSISSolution A (βz + βz + βcs) u := by
  rcases lossiness_discharges_nonzero s s' c c' z z' hss hinv with hne | hne'
  · exact ⟨_, forked_forgery_yields_msis_solution A s w c c' z z' βz βcs hz hz' hcs h1 h2 hne⟩
  · exact ⟨_, forked_forgery_yields_msis_solution A s' w c c' z z' βz βcs hz hz' hcs'
              (ht ▸ h1) (ht ▸ h2) hne'⟩

#assert_axioms smul_eq_zero_of_isUnit
#assert_axioms lossiness_discharges_nonzero
#assert_axioms forked_forgery_yields_msis_solution_discharged

end Dregg2.Crypto.HermineDischarge
