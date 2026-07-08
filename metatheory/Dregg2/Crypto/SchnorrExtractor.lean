/-
# `Dregg2.Crypto.SchnorrExtractor` — the Schnorr special-soundness extractor: two accepting
transcripts sharing a commitment yield the discrete log.

This is the algebraic heart of the forking lemma. A forking-lemma rewinding of a Schnorr forger
produces two ACCEPTING transcripts `(R, e, z)` and `(R, e', z')` with the SAME commitment `R` and
DIFFERENT challenges `e ≠ e'`. Special soundness says those two transcripts DETERMINE the witness:
the scalar `(z - z') / (e - e')` is the discrete log of `pk` in base `g`. So a Schnorr forger yields
the DL secret — the reduction from Schnorr unforgeability to discrete-log hardness is this file's
theorem composed with the forking probability bound.

Boundary: the forking PROBABILITY (that rewinding a random-oracle forger yields two such transcripts)
is the ROM statistical carrier and is NOT proved here. The EXTRACTOR — the clean algebraic content of
special soundness — is what this file discharges, over the same abstract group `SchnorrVerifies`
already uses (`Dregg2.Crypto.Frost`), verifier reused verbatim.
-/
import Dregg2.Crypto.Frost

namespace Dregg2.Crypto.Schnorr

open Dregg2.Crypto.Frost

variable {S : Type*} [Field S] {G : Type*} [AddCommGroup G] [Module S G]

/-- The special-soundness extractor: from two transcripts' challenges and responses, the candidate
discrete-log witness. -/
def extractWitness (e e' z z' : S) : S := (z - z') / (e - e')

/-- **Schnorr special soundness — two accepting transcripts with a shared commitment extract the
discrete log.** If `(R, e, z)` and `(R, e', z')` both verify against `pk` (same commitment `R`,
different challenges `e ≠ e'`), then the extracted scalar `(z - z') / (e - e')` IS the discrete log:
`pk = ((z - z') / (e - e')) • g`. Subtracting the two verification equations gives
`(z - z') • g = (e - e') • pk`; since `e - e' ≠ 0` is a unit in the field `S`, dividing yields the
witness. This is exactly what a forking-lemma rewinding produces, so a Schnorr forger yields the DL
secret. -/
theorem schnorr_special_soundness_extracts_dl (g pk R : G) (e e' z z' : S)
    (hne : e ≠ e')
    (h1 : SchnorrVerifies g pk R e z)
    (h2 : SchnorrVerifies g pk R e' z') :
    pk = extractWitness e e' z z' • g := by
  have hd : e - e' ≠ 0 := sub_ne_zero.mpr hne
  have hsub : (z - z') • g = (e - e') • pk := by
    rw [sub_smul, h1, h2, sub_smul, add_sub_add_left_eq_sub]
  have hpk : pk = (e - e')⁻¹ • ((z - z') • g) := by
    rw [hsub, inv_smul_smul₀ hd]
  rw [hpk, smul_smul, extractWitness, div_eq_inv_mul]

/-- **Non-vacuity: the extractor recovers the TRUE secret.** For an honest signer with secret `x`
and nonce `k`, answering two different challenges `e ≠ e'` with the real responses `z = k + e·x`,
`z' = k + e'·x`, the extracted witness `(z - z') / (e - e')` EQUALS `x`. The extractor is not a
tautology — on genuinely-signed pairs it computes the actual discrete log. -/
theorem extractor_is_correct (x k e e' : S) (hne : e ≠ e') :
    extractWitness e e' (k + e * x) (k + e' * x) = x := by
  have hd : e - e' ≠ 0 := sub_ne_zero.mpr hne
  have hnum : (k + e * x) - (k + e' * x) = (e - e') * x := by ring
  rw [extractWitness, hnum, mul_div_cancel_left₀ x hd]

/-- **End-to-end witness.** The honest transcripts (`schnorr_sig_verifies` from `Frost`) satisfy the
special-soundness hypotheses, and running the extractor theorem on them re-derives `x • g` — the two
theorems compose on real inputs, so neither hypothesis set is vacuous. -/
theorem extractor_composes_on_honest_transcripts (g : G) (x k e e' : S) (hne : e ≠ e') :
    x • g = extractWitness e e' (k + e * x) (k + e' * x) • g :=
  schnorr_special_soundness_extracts_dl g (x • g) (k • g) e e' (k + e * x) (k + e' * x) hne
    (schnorr_sig_verifies g x k e) (schnorr_sig_verifies g x k e')

#assert_axioms schnorr_special_soundness_extracts_dl
#assert_axioms extractor_is_correct
#assert_axioms extractor_composes_on_honest_transcripts

end Dregg2.Crypto.Schnorr
