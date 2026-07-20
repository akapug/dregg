/-
# `Dregg2.Crypto.SignCoreSpec` — extending "IS the FIPS 204 spec" to the SIGN direction.

`VerifyCoreEqSpec.verifyCore_eq_challengeMatches_and_norm` proved the flagship VERIFY result: the byte-exact executable
`MlDsaVerifyReal.verifyCore` accepts EXACTLY when the FIPS 204 Algorithm 8 acceptance predicate holds, for
ALL inputs, `#assert_axioms`-clean. This file carries the same machinery to SIGN
(`MlDsaSignReal.signCore`, FIPS 204 Algorithm 7 `Sign_internal`, deterministic `rnd = 0`).

It closes two things, both by REUSING the verify algebra — nothing about the ML-DSA ring is reproved, because
sign and verify share the SAME ring `R_q = ℤ_q[X]/(X²⁵⁶+1)` (`q = 8380417`):

## 1. Ring-computation faithfulness (∀, `#assert_axioms`-clean)

`signCore` (FIPS 204 Alg-7) computes its ring quantities with the same fast NTT path the verifier uses. Under
the coeff-array → `R_q` bridge `VerifyCoreEqSpec.toRq`, each maps to exactly the FIPS 204 `Sign_internal`
ring expression — i.e. to the corresponding field of the abstract `Fips204Spec.MlDsaParams.sign`:

* `signRing_z`     — the response `z = y + c·s1`: `toRq (addPoly y (intt(ĉ ⊙ ŝ1))) = toRq y + toRq c · toRq s1`
  (reuses `toRq_add` + `toRq_nttMul`). This is the abstract `y + c • s1`.
* `signRing_ct0`   — the hint correction `c·t0`: `toRq (intt(ĉ ⊙ t̂0)) = toRq c · toRq t0` (`= toRq_nttMul`).
  This is the abstract `c • t0` (the `MakeHint` first argument is `−(c • t0)`).
* `signRing_wmcs2` — the low-bits base `w − c·s2`: `toRq (subPoly w (intt(ĉ ⊙ ŝ2))) = toRq w − toRq c · toRq s2`
  (reuses `toRq_sub` + `toRq_nttMul`; the subtrahend is `intt`-reduced, `< q`, via `intt_lt`).
* `signRing_makehint_base` — the `MakeHint` base `w − c·s2 + c·t0`: `toRq (addPoly (w − c·s2) (c·t0)) =
  toRq w − toRq c · toRq s2 + toRq c · toRq t0`. This is the abstract `A y - c • s2 + c • t0` (the second
  `MakeHint` argument). `makeHintPoly` reads exactly these two `ℤ_q` polynomials (`r = (w−c·s2 + c·t0) mod q`
  via `addQ`, `rz = w − c·s2`).
* `signRing_w_row` — the commitment `w = A·y` per row: verifyCore's / signCore's per-row `for l`
  `addPoly`-fold of `Â_il ⊙ ŷ_l`, under `intt` then `toRq`, is the `R_q`-sum `Σ_l toRq A_il · toRq y_l`
  (reuses `toRq_intt_addFold` + `toRq_intt_zero`). This is the abstract `A y` (matrix–vector row).

These are the same three reused legs (`toRq_add`/`toRq_sub`, `toRq_nttMul`, `toRq_intt_addFold`) that closed
the verify matmul; they are stated in the `(ntt ·)(ntt ·)` / normal-domain-matrix SHAPE, exactly as
`VerifyCoreEqSpec.toRq_intt_matmul_row`.

## 2. `sign_produces_spec_valid` — sign→verify correctness routed through the proven verify=spec

The security-meaningful direction. `MlDsaSignReal.sign_produces_valid_sig` establishes
`verifyCore acvpPk acvpMsg acvpCtx (signCore acvpSk acvpMsg acvpCtx) = true` on the NIST ACVP keypair. Feeding that through
the PROVEN (but self-referential — it bisects verifyCore) `verifyCore_eq_challengeMatches_and_norm`, the signature `signCore` produces satisfies the FIPS 204 Algorithm 8 verify
PREDICATE: the SHAKE challenge fixed-point (`VerifyCoreSpec.challengeMatches`) AND the response norm bound
`‖z‖∞ < γ₁−β`. This is honest sign→verify correctness, and it is NON-VACUOUS — a concrete genuine ML-DSA-65
`(sk, pk, msg)` (the `fips204` v0.4.6 vectors), the same anti-fake witness the sign brick pins.

## HONEST RESIDUALS (named, not laundered)

* **The full `signCore = Sign_internal` byte identity** (with the rejection loop) is NOT reproved here
  symbolically; `MlDsaSignReal.sign_matches_acvp_deterministic` pins it byte-for-byte on the NIST ACVP vector
  (`native_decide`). The loop is a `partial def`; the ring-faithful lemmas above are its per-iteration ring
  content, and `sign_produces_spec_valid` certifies the accepted iteration against the FIPS verify predicate.
* **`ExpandMask` = spec** and **the rejection-loop termination/bounds** (`‖z‖∞ < γ₁−β`, `‖r0‖∞ < γ₂−β`,
  hint weight ≤ ω) are the sign-only surface with no verify counterpart. The bounds that make an iteration
  ACCEPTED are exactly what `sign_produces_spec_valid` observes holding (they are the two conjuncts it
  extracts); ExpandMask's `BitUnpack` round-trip is the same `unpackBits_packBits` pattern already CLOSED in
  `VerifyCoreEqSpec` (at the γ₁ = 2¹⁹ width, `cbits = 20`), left unwired here.
* **`Â_il = ntt(A_il)`** (NTT-domain matrix ↔ normal-domain matrix). `signRing_w_row` is stated in the
  normal-domain `(ntt t.1)(ntt t.2)` shape; identifying it with signCore's already-NTT-domain `expandA`
  matrix `Â` needs `ntt ∘ intt = id` for-all (today only `MlDsaRing.ntt_intt_id`, one `native_decide`
  sample). This is the IDENTICAL residual on the verify side (`toRq_intt_matmul_row` has the same shape) — a
  faithful-NTT fact, not a hardness carrier.
* **The abstract `MlDsaParams.sign` instance over `R_q^k`** (constructing `A : R_q^l →ₗ R_q^k` as a
  `LinearMap`) is not built — as on the verify side, we stop at the per-row/per-coefficient `toRq` identities
  and name the module-map wiring as frontier.
-/
import Dregg2.Crypto.VerifyCoreEqSpec
import Dregg2.Crypto.MlDsaSignReal

namespace Dregg2.Crypto.SignCoreSpec

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt pointwiseMul addPoly subPoly
  pointwiseMul_size pointwiseMul_lt zeroPoly_lt intt_lt)
open Dregg2.Crypto.VerifyCoreEqSpec (toRq toRq_add toRq_sub toRq_nttMul toRq_intt_addFold toRq_intt_zero)
open Dregg2.Crypto.MlDsaSignReal (signCore acvpSk acvpPk acvpMsg acvpCtx makeHintPoly)
open Dregg2.Crypto.MlDsaVerifyReal (verifyCore infNormZ zBound)
open Dregg2.Crypto.MlDsaCodec (sigDecode paramK)

/-! ## 1. Ring-computation faithfulness — signCore's ring quantities ARE the FIPS 204 `Sign_internal`
expressions, under the shared `toRq : Poly → R_q` bridge. Each reuses the verify algebra. -/

/-- **The response `z = y + c·s1`** (FIPS 204 Alg-7 line 20), faithful to `R_q`. signCore computes
`z_l = addPoly y_l (intt (ĉ ⊙ ŝ1_l))`; under `toRq` this is `toRq y_l + toRq c · toRq s1_l` — the abstract
`Fips204Spec.MlDsaParams.sign` field `y + c • s1`, per coordinate. Reuses `toRq_add` + `toRq_nttMul`. -/
theorem signRing_z (y c s1 : Poly) (hc : c.size = 256) (hs : s1.size = 256) :
    toRq (addPoly y (intt (pointwiseMul (ntt c) (ntt s1)))) = toRq y + toRq c * toRq s1 := by
  rw [toRq_add, toRq_nttMul c s1 hc hs]

/-- **The hint correction `c·t0`** (FIPS 204 Alg-7 line 25), faithful to `R_q`. `toRq (intt (ĉ ⊙ t̂0)) =
toRq c · toRq t0` — the abstract `c • t0` (the `MakeHint` first argument is `−(c • t0)`). This is exactly
`toRq_nttMul` at `(c, t0)`. -/
theorem signRing_ct0 (c t0 : Poly) (hc : c.size = 256) (ht : t0.size = 256) :
    toRq (intt (pointwiseMul (ntt c) (ntt t0))) = toRq c * toRq t0 :=
  toRq_nttMul c t0 hc ht

/-- **The low-bits base `w − c·s2`** (FIPS 204 Alg-7 line 21, the `r = w − c·s2` whose `LowBits` gate the
loop), faithful to `R_q`. signCore computes `wmcs2_i = subPoly w_i (intt (ĉ ⊙ ŝ2_i))`; under `toRq` this is
`toRq w_i − toRq c · toRq s2_i`. The subtrahend `intt (ĉ ⊙ ŝ2_i)` is `intt`-reduced (`< q`, via `intt_lt`),
so `toRq_sub` applies. -/
theorem signRing_wmcs2 (w c s2 : Poly) (hc : c.size = 256) (hs : s2.size = 256) :
    toRq (subPoly w (intt (pointwiseMul (ntt c) (ntt s2)))) = toRq w - toRq c * toRq s2 := by
  rw [toRq_sub w (intt (pointwiseMul (ntt c) (ntt s2)))
        (fun i _ => le_of_lt (intt_lt _ (pointwiseMul_size _ _) (pointwiseMul_lt _ _) i)),
      toRq_nttMul c s2 hc hs]

/-- **The `MakeHint` base `w − c·s2 + c·t0`** (FIPS 204 Alg-7 line 26, the second `MakeHint` argument),
faithful to `R_q`. `toRq (addPoly (w − c·s2) (c·t0)) = toRq w − toRq c · toRq s2 + toRq c · toRq t0` — the
abstract `A y - c • s2 + c • t0`. `MlDsaSignReal.makeHintPoly` reads exactly these `ℤ_q` polynomials: its
per-coefficient `r = (wmcs2[j] + ct0[j]) mod q` is `(addPoly (w−c·s2) (c·t0))[j]` (`addQ = (·+·) mod q`),
its `rz = wmcs2[j]` is `(w − c·s2)[j]` (recovered by `signRing_wmcs2`). Reuses `toRq_add`. -/
theorem signRing_makehint_base (w c s2 t0 : Poly)
    (hc : c.size = 256) (hs2 : s2.size = 256) (ht0 : t0.size = 256) :
    toRq (addPoly (subPoly w (intt (pointwiseMul (ntt c) (ntt s2))))
                  (intt (pointwiseMul (ntt c) (ntt t0))))
      = toRq w - toRq c * toRq s2 + toRq c * toRq t0 := by
  rw [toRq_add, signRing_wmcs2 w c s2 hc hs2, signRing_ct0 c t0 hc ht0]

/-- **The commitment `w = A·y` per row** (FIPS 204 Alg-7 line 12), faithful to `R_q`. signCore's per-row
`for l` fold `az ← addPoly az (Â_il ⊙ ŷ_l)` over the mask, under `intt` then `toRq`, is the `R_q`-module
matrix–vector row `Σ_l toRq A_il · toRq y_l` — the abstract `A y`. Reuses `toRq_intt_addFold` (the fold
linearity engine) + `toRq_intt_zero`; stated in the normal-domain `(ntt t.1)(ntt t.2)` shape, exactly as the
verify side's `VerifyCoreEqSpec.toRq_intt_matmul_row`. -/
theorem signRing_w_row (terms : List (Poly × Poly))
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) :
    toRq (intt (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms))
      = (terms.map (fun t => toRq t.1 * toRq t.2)).sum := by
  rw [toRq_intt_addFold terms hterm zeroPoly (by simp [zeroPoly]) zeroPoly_lt, toRq_intt_zero, zero_add]

#assert_axioms signRing_z
#assert_axioms signRing_ct0
#assert_axioms signRing_wmcs2
#assert_axioms signRing_makehint_base
#assert_axioms signRing_w_row

/-! ## 2. `sign_produces_spec_valid` — the honest signature satisfies the FIPS 204 verify PREDICATE.

Composing `MlDsaSignReal.sign_produces_valid_sig` (verifyCore accepts signCore's honest output, `native_decide`
on the genuine `fips204` v0.4.6 keypair) with the PROVEN `VerifyCoreEqSpec.verifyCore_eq_challengeMatches_and_norm` (verifyCore =
the FIPS 204 Algorithm 8 acceptance predicate, ∀). The `native_decide` is the concrete WITNESS only — it is
NOT inside any ∀-theorem; the equivalence it rides (`verifyCore_eq_challengeMatches_and_norm`) is `#assert_axioms`-clean. -/

/-- The honest sign-produced signature's hint decodes to `k = 6` polynomials, so `verifyCore_eq_challengeMatches_and_norm`'s
hypothesis is inhabited on the sign output. -/
theorem sign_hint_size :
    (sigDecode (signCore acvpSk.toList acvpMsg.toList acvpCtx.toList)).2.2.size = paramK := by
  native_decide

/-- **`sign_produces_spec_valid` — SIGN→VERIFY correctness via the proven verify=spec.** The signature
`signCore` produces on the honest keypair satisfies BOTH FIPS 204 Algorithm 8 acceptance conditions: the
SHAKE challenge fixed-point (`VerifyCoreSpec.challengeMatches`) AND the response norm bound `‖z‖∞ < γ₁−β`.
Derived by feeding `MlDsaSignReal.sign_produces_valid_sig` through the ∀-proven `verifyCore_eq_challengeMatches_and_norm` — the
security-meaningful direction, routed through the flagship verify=spec result. NON-VACUOUS: a concrete
genuine NIST ACVP ML-DSA-65 `(sk, pk, msg, ctx)`, and both conjuncts genuinely hold. -/
theorem sign_produces_spec_valid :
    VerifyCoreSpec.challengeMatches acvpPk.toList acvpMsg.toList acvpCtx.toList
        (signCore acvpSk.toList acvpMsg.toList acvpCtx.toList) = true
      ∧ infNormZ (sigDecode (signCore acvpSk.toList acvpMsg.toList acvpCtx.toList)).2.1 < zBound :=
  (VerifyCoreEqSpec.verifyCore_eq_challengeMatches_and_norm acvpPk.toList acvpMsg.toList acvpCtx.toList
      (signCore acvpSk.toList acvpMsg.toList acvpCtx.toList)
      sign_hint_size).mp MlDsaSignReal.sign_produces_valid_sig

end Dregg2.Crypto.SignCoreSpec
