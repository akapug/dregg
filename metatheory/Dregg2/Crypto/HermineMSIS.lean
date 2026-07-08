/-
# `Dregg2.Crypto.HermineMSIS` — the reduction: a Hermine FORGERY yields an MSIS solution.

This is the payoff above `Dregg2.Crypto.Lattice`'s irreducible line. It composes the Hermine extractor
with the norm-bound leg to show that a forking-lemma forgery HANDS YOU a Module-SIS solution — a short,
nonzero vector in the kernel of the public matrix `A`. So `MSIS` hardness (assumed, never proved)
implies Hermine is unforgeable: the full post-quantum reduction, down to the line and no further.

The vector extracted is `u = (z − z') − (c − c')·s`, where the two forked transcripts share the
commitment `w` and differ in the challenge:
* `A·u = 0` — from the extractor `A(z−z') = (c−c')·t` and the key relation `t = A·s`, so
  `A(z−z') = A((c−c')·s)`, hence `u ∈ ker A`. (Unconditional linear algebra.)
* `u` is SHORT — the norm-bound leg: `‖u‖ ≤ ‖z‖ + ‖z'‖ + ‖(c−c')·s‖`, all short. (The triangle
  inequality from `Lattice.ShortNorm`, the leg most treatments leave implicit.)
* `u ≠ 0` — this is EXACTLY the MLWE-hides-the-secret step: `u = 0` means the forger reproduced
  `(c−c')·s` from `s`, which recovering the short secret from the public key `t = A·s` (Module-LWE)
  rules out. We thread it as an explicit hypothesis and NAME it as the MLWE leg — not papered over.
-/
import Dregg2.Crypto.Lattice
import Dregg2.Crypto.HermineThreshold
import Dregg2.Crypto.HermineExtractor

namespace Dregg2.Crypto.HermineMSIS

open Dregg2.Crypto.Lattice

variable {Rq : Type*} [CommRing Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N]

/-- **A forked Hermine forgery yields an MSIS solution.** Two accepting transcripts sharing the
commitment `w` with challenges `c ≠ c'` (implicit in the extractor), against the public key `t = A·s`
of a signer with short secret `s`, with `z, z'` short (the acceptance bound `βz`) and `(c−c')·s` short
(`βcs`, since `c−c'` is small): the vector `u = (z−z') − (c−c')·s` is a genuine Module-SIS solution for
`A` at bound `βz + βz + βcs` — provided `u ≠ 0` (the MLWE leg). Its kernel membership is unconditional;
its shortness is the norm-bound leg; only its non-triviality rests on MLWE. -/
theorem forked_forgery_yields_msis_solution
    (A : M →ₗ[Rq] N) (s : M) (w : N) (c c' : Rq) (z z' : M) (βz βcs : ℕ)
    (hz : nrm z ≤ βz) (hz' : nrm z' ≤ βz) (hcs : nrm ((c - c') • s) ≤ βcs)
    (h1 : HermineThreshold.verify A (A s) w c z)
    (h2 : HermineThreshold.verify A (A s) w c' z')
    (hu : (z - z') - (c - c') • s ≠ 0) :
    IsMSISSolution A (βz + βz + βcs) ((z - z') - (c - c') • s) := by
  refine ⟨hu, ?_, ?_⟩
  · -- SHORT: ‖u‖ ≤ ‖z-z'‖ + ‖(c-c')·s‖ ≤ (‖z‖+‖z'‖) + βcs ≤ (βz+βz) + βcs
    calc nrm ((z - z') - (c - c') • s)
          ≤ nrm (z - z') + nrm ((c - c') • s) := nrm_sub_le _ _
      _ ≤ (nrm z + nrm z') + nrm ((c - c') • s) := Nat.add_le_add_right (nrm_sub_le z z') _
      _ ≤ (βz + βz) + βcs := Nat.add_le_add (Nat.add_le_add hz hz') hcs
  · -- KERNEL: A u = A(z-z') - A((c-c')·s) = (c-c')·(A s) - (c-c')·(A s) = 0
    have hrel : A (z - z') = (c - c') • (A s) :=
      Dregg2.Crypto.Hermine.hermine_special_soundness_extracts_relation A (A s) w c c' z z' h1 h2
    rw [map_sub, map_smul, hrel, sub_self]

/-- **Post-quantum unforgeability, down to the line.** If Module-SIS is hard for `A` at the extracted
bound, then no forked Hermine forgery exists (with the non-triviality the MLWE leg supplies): a forgery
would produce an `IsMSISSolution`, contradicting `MSISHard`. This is the reduction complete — Hermine
unforgeability rests on MLWE (`u ≠ 0`) + MSIS (`hard`), the two named lattice carriers, and nothing
else. -/
theorem no_forgery_under_msis
    (A : M →ₗ[Rq] N) (s : M) (w : N) (c c' : Rq) (z z' : M) (βz βcs : ℕ)
    (hz : nrm z ≤ βz) (hz' : nrm z' ≤ βz) (hcs : nrm ((c - c') • s) ≤ βcs)
    (h1 : HermineThreshold.verify A (A s) w c z)
    (h2 : HermineThreshold.verify A (A s) w c' z')
    (hu : (z - z') - (c - c') • s ≠ 0)
    (hard : MSISHard A (βz + βz + βcs)) : False :=
  hard ⟨_, forked_forgery_yields_msis_solution A s w c c' z z' βz βcs hz hz' hcs h1 h2 hu⟩

#assert_axioms forked_forgery_yields_msis_solution
#assert_axioms no_forgery_under_msis

end Dregg2.Crypto.HermineMSIS
