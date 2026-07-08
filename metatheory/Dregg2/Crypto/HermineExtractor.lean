/-
# `Dregg2.Crypto.HermineExtractor` — the lattice special-soundness extractor: two accepting
Raccoon/Hermine transcripts sharing a commitment yield the MSIS/MLWE relation.

The post-quantum analog of `Dregg2.Crypto.SchnorrExtractor`. A forking-lemma rewinding of a
Raccoon/Hermine forger produces two ACCEPTING transcripts `(w, c, z)` and `(w, c', z')` with the SAME
commitment `w` and DIFFERENT challenges. Special soundness says the pair DETERMINES a lattice
relation: subtracting the two verification equations `A·z = w + c·t` and `A·z' = w + c'·t` gives
`A·(z - z') = (c - c')·t` — a preimage relation for the public key `t` under the public matrix `A`.
When `c - c'` is invertible (we take `R` a field for the model; in the deployed scheme the challenge
set is chosen so challenge differences are units), the extractor produces an explicit preimage
`(c - c')⁻¹·(z - z')` of `t`. So a forked Hermine forger yields a preimage of `t` — the MSIS/MLWE
break — exactly as a forked Schnorr forger yields the discrete log.

Boundary (named lattice carriers, NOT proved here): the forking PROBABILITY (that rewinding a
random-oracle forger yields two such transcripts) is the ROM statistical carrier, and the SHORTNESS
of the extracted vector `z - z'` (short `z`, `z'` give a short difference — the vector that actually
breaks MSIS/MLWE) is the norm-side carrier; neither is module algebra. The EXTRACTOR — the clean
linear-algebra content of special soundness — is what this file discharges, over the same abstract
module verifier `HermineThreshold.verify`, reused verbatim.
-/
import Dregg2.Crypto.HermineThreshold

namespace Dregg2.Crypto.Hermine

open Dregg2.Crypto.HermineThreshold

section Ring

variable {R : Type*} [CommRing R] {M N : Type*}
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- **Hermine special soundness — two accepting transcripts with a shared commitment extract the
lattice relation.** If `(w, c, z)` and `(w, c', z')` both verify against public key `t` (same
commitment `w`), then `A·(z - z') = (c - c')·t`: subtracting the two verification equations
`A·z = w + c·t` and `A·z' = w + c'·t` cancels the commitment. This is the module analog of the
Schnorr forking extractor's subtraction step — the difference `z - z'` is a (short, by the norm
carrier) solution relating `t` to the lattice, i.e. the MSIS/MLWE break a forked forger hands over.
No invertibility of `c - c'` is needed for the relation itself. -/
theorem hermine_special_soundness_extracts_relation
    (A : M →ₗ[R] N) (t w : N) (c c' : R) (z z' : M)
    (h1 : verify A t w c z) (h2 : verify A t w c' z') :
    A (z - z') = (c - c') • t := by
  simp only [verify] at h1 h2
  rw [map_sub, h1, h2, add_sub_add_left_eq_sub, ← sub_smul]

/-- **Non-vacuity: the extractor is correct on honest transcripts.** For an honest signer with
secret `s` and mask `y`, answering two challenges with the real Raccoon responses `z = y + c·s`,
`z' = y + c'·s` (which verify, by `raccoon_sig_verifies`), the extracted difference satisfies
`A·(z - z') = (c - c')·(A s)` — the true relation on the real public key `t = A·s`. The hypotheses
of `hermine_special_soundness_extracts_relation` are inhabited and its conclusion recovers the
genuine relation; the extractor is not a tautology. -/
theorem extractor_is_correct (A : M →ₗ[R] N) (s y : M) (c c' : R) :
    A ((y + c • s) - (y + c' • s)) = (c - c') • A s :=
  hermine_special_soundness_extracts_relation A (A s) (A y) c c' (y + c • s) (y + c' • s)
    (raccoon_sig_verifies A s y c) (raccoon_sig_verifies A s y c')

end Ring

section FieldModel

variable {K : Type*} [Field K] {M N : Type*}
  [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]

/-- The special-soundness extractor over the field model: from two transcripts' challenges and
responses, the candidate preimage of the public key `t` under `A`. Its SHORTNESS (short `z`, `z'`
and small `(c - c')⁻¹`-scaling in the deployed ring) is the MSIS/MLWE norm carrier, out of scope. -/
def extractPreimage (c c' : K) (z z' : M) : M := (c - c')⁻¹ • (z - z')

/-- **Hermine special soundness, division step — the extracted vector is a preimage of the public
key.** With `c ≠ c'` (so `c - c'` is a unit in the field `K`), the extractor's output maps to `t`
under the public matrix: `A·((c - c')⁻¹·(z - z')) = t`. The lattice mirror of
`schnorr_special_soundness_extracts_dl`'s division by `e - e'`: a forger yields an explicit
(short, by the norm carrier) preimage of the public key — the MSIS/MLWE break. -/
theorem hermine_special_soundness_extracts_preimage
    (A : M →ₗ[K] N) (t w : N) (c c' : K) (z z' : M) (hne : c ≠ c')
    (h1 : verify A t w c z) (h2 : verify A t w c' z') :
    A (extractPreimage c c' z z') = t := by
  have hd : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have hrel := hermine_special_soundness_extracts_relation A t w c c' z z' h1 h2
  simp only [extractPreimage]
  rw [map_smul, hrel, inv_smul_smul₀ hd]

/-- The same division step stated on the public-key side: `t` is determined by the two transcripts,
`t = (c - c')⁻¹ · A·(z - z')`. -/
theorem hermine_special_soundness_extracts_key
    (A : M →ₗ[K] N) (t w : N) (c c' : K) (z z' : M) (hne : c ≠ c')
    (h1 : verify A t w c z) (h2 : verify A t w c' z') :
    t = (c - c')⁻¹ • A (z - z') := by
  have hd : c - c' ≠ 0 := sub_ne_zero.mpr hne
  rw [hermine_special_soundness_extracts_relation A t w c c' z z' h1 h2, inv_smul_smul₀ hd]

/-- **Non-vacuity, field model: the extractor recovers the TRUE secret.** On honest responses
`z = y + c·s`, `z' = y + c'·s` with `c ≠ c'`, `extractPreimage` computes `s` itself — the actual
short witness, not merely some preimage. The lattice mirror of Schnorr's `extractor_is_correct`
division witness. -/
theorem extractor_recovers_secret (s y : M) (c c' : K) (hne : c ≠ c') :
    extractPreimage c c' (y + c • s) (y + c' • s) = s := by
  have hd : c - c' ≠ 0 := sub_ne_zero.mpr hne
  simp only [extractPreimage]
  rw [add_sub_add_left_eq_sub, ← sub_smul, inv_smul_smul₀ hd]

/-- **End-to-end witness.** Honest transcripts (`raccoon_sig_verifies`) satisfy the
special-soundness hypotheses, and running the preimage extractor on them re-derives the real public
key `A·s` — the theorems compose on real inputs, so no hypothesis set is vacuous. -/
theorem extractor_composes_on_honest_transcripts
    (A : M →ₗ[K] N) (s y : M) (c c' : K) (hne : c ≠ c') :
    A (extractPreimage c c' (y + c • s) (y + c' • s)) = A s :=
  hermine_special_soundness_extracts_preimage A (A s) (A y) c c' (y + c • s) (y + c' • s) hne
    (raccoon_sig_verifies A s y c) (raccoon_sig_verifies A s y c')

end FieldModel

#assert_axioms hermine_special_soundness_extracts_relation
#assert_axioms extractor_is_correct
#assert_axioms hermine_special_soundness_extracts_preimage
#assert_axioms hermine_special_soundness_extracts_key
#assert_axioms extractor_recovers_secret
#assert_axioms extractor_composes_on_honest_transcripts

end Dregg2.Crypto.Hermine
