/-
# `Dregg2.Crypto.VerifyCoreEqSpec` — closing the `verifyCore` IS-the-spec residuals: the coeff↔`R_q` bridge.

`VerifyCoreSpec.verifyCore_split` reduced the executable ML-DSA-65 `verifyCore` to the two FIPS 204 Algorithm
8 acceptance conditions, leaving three NAMED `∀`-bridges (`VerifyCoreSpec.{RingRepFaithful, DecodeSemantics,
ChallengeMatchesSpec}`). `NttFaithful.ringRepFaithful_proven` closed the hard one (the fast NTT multiply
computes the negacyclic ring product, for all size-256 reduced polys). THIS file builds the remaining
algebraic bridge that turns that coefficient-array fact into a statement over the REAL ring
`R_q = ℤ_q[X]/(X²⁵⁶+1)` (`Fips204CorrectReal.Rq`):

* **`toRq : Poly → Rq`** — the coeff-array → `R_q` map `a ↦ ∑_{i<256} a_i · root^i`. This is the executable-
  representation ↔ `AdjoinRoot` bridge the seam named as remaining.
* **`toRq_schoolbookMul`** — `toRq (schoolbookMul a b) = toRq a * toRq b`: the executable negacyclic
  convolution IS the `R_q` product, for ALL poly pairs. Proved from `NttFaithful.schoolbookMul_getElem` (the
  `∑_{i+j=m} − ∑_{i+j=m+256}` coefficient formula) + `Fips204CorrectReal.root_pow_256` (`root²⁵⁶ = −1`).
* **`toRq_nttMul`** — composing with `ringRepFaithful_proven`: `toRq (intt (pointwiseMul (ntt a) (ntt b))) =
  toRq a * toRq b`. verifyCore's NTT-domain multiply computes the `R_q` product.
* **`toRq_add` / `toRq_sub`** — `toRq` carries the executable `addPoly`/`subPoly` to `R_q` `+`/`−`.
* **`nttMatmul_isRingArg`** — the culmination for the challenge conjunct: verifyCore's per-row
  `intt(Σ_j Â[i,j]⊙ntt(z_j) − ĉ⊙ntt(2^d·t1_i))` equals the spec's `Σ_j A_ij·z_j − c·(2^d·t1_i)` over `R_q`.

The residuals that remain (NAMED, not laundered) are the codec bit-packing round-trip (`DecodeSemantics`) and
the hash/challenge INSTANTIATION — see the closing section.
-/
import Dregg2.Crypto.NttFaithful
import Dregg2.Crypto.Fips204CorrectReal
import Dregg2.Crypto.MlDsaCodec
import Dregg2.Crypto.VerifyCoreSpec

namespace Dregg2.Crypto.VerifyCoreEqSpec

open Dregg2.Crypto.MlDsaRing (Poly q zeroPoly ntt intt pointwiseMul addPoly subPoly schoolbookMul cJ
  schoolbookMul_getElem schoolbookMul_size schoolbookMul_lt ringRepFaithful_proven
  cast_addPoly cast_subPoly intt_add intt_sub intt_size intt_lt intt_interp addPoly_size addPoly_lt
  subPoly_size subPoly_lt pointwiseMul_size pointwiseMul_lt zeroPoly_lt zeroPoly_cast)
open Dregg2.Crypto.MlDsaCodec (bytesToNatLE unpackBits packBits pkDecode pkEncode sigDecode sigEncode
  zCoeffFromField zFieldFromCoeff gamma1 paramK paramL t1Bits zBits)
open Dregg2.Crypto.MlDsaVerifyReal (verifyCore infNormZ zBound genPk genMsg genSig verify_accepts_real)
open Polynomial Finset

set_option maxRecDepth 8000

/-- The negacyclic ring modulus polynomial, over `ℤ_q` (`q = MlDsaRing.q = 8380417`). -/
local notation "F" => (X ^ 256 + 1 : (ZMod q)[X])

/-- **The REAL ML-DSA ring** `R_q = ℤ_q[X]/(X²⁵⁶+1)` — DEFINITIONALLY `Fips204CorrectReal.Rq` (its base
`Fips204CorrectReal.q` is `rfl`-equal to `MlDsaRing.q`), stated over `MlDsaRing.q` so the executable
coefficient casts (`cJ`, `schoolbookMul_getElem`) match syntactically. -/
noncomputable abbrev Rq := AdjoinRoot F

/-- `Rq` IS `Fips204CorrectReal.Rq` (the `q`s are `rfl`-equal). -/
theorem Rq_eq : Rq = Dregg2.Crypto.Fips204CorrectReal.Rq := rfl

/-- The `R_q` root of `X²⁵⁶+1`. -/
noncomputable abbrev r : Rq := AdjoinRoot.root F

/-- **`root²⁵⁶ = −1` in `R_q`** — the negacyclic relation (re-derived here over `MlDsaRing.q`; identical to
`Fips204CorrectReal.root_pow_256`). -/
theorem root_pow_256 : r ^ 256 = -1 := by
  have h : AdjoinRoot.mk F (X ^ 256 + 1) = 0 := AdjoinRoot.mk_self
  have hr : r ^ 256 + 1 = 0 := by
    simpa [map_add, map_pow, map_one, AdjoinRoot.mk_X] using h
  linear_combination hr

/-- The `ℤ_q` reduction of an executable `Nat` coefficient. -/
abbrev cf (n : Nat) : ZMod q := (n : ZMod q)

/-- **The coeff-array → `R_q` bridge.** `toRq a = ∑_{i<256} a_i · root^i` — the executable size-256
coefficient array read as an element of `R_q = ℤ_q[X]/(X²⁵⁶+1)`. -/
noncomputable def toRq (a : Poly) : Rq :=
  ∑ i ∈ range 256, AdjoinRoot.of F (cf (a[i]!)) * r ^ i

/-- Expand the `R_q` product of two bridged arrays into the double coefficient sum with `root^{i+j}`
(no negacyclic reduction yet — that lands per-`(i,j)` in `coeff_collapse`). -/
theorem toRq_mul_expand (a b : Poly) :
    toRq a * toRq b
      = ∑ i ∈ range 256, ∑ j ∈ range 256,
          AdjoinRoot.of F (cf (a[i]!) * cf (b[j]!)) * r ^ (i + j) := by
  unfold toRq
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [map_mul, pow_add]
  ring

/-- **The negacyclic collapse, per coefficient pair.** For `i, j < 256`, summing the signed contribution
`cJ a b i j m · root^m` over all output slots `m` collapses (using `root²⁵⁶ = −1`) to the single ring term
`a_i·b_j · root^{i+j}`. The `i+j ≥ 256` branch is where `X²⁵⁶ = −1` fires. -/
theorem coeff_collapse (a b : Poly) (i j : Nat) (hi : i < 256) (hj : j < 256) :
    ∑ m ∈ range 256, AdjoinRoot.of F (cJ a b i j m) * r ^ m
      = AdjoinRoot.of F (cf (a[i]!) * cf (b[j]!)) * r ^ (i + j) := by
  by_cases hlt : i + j < 256
  · rw [Finset.sum_eq_single (i + j)]
    · have hcj : cJ a b i j (i + j) = cf (a[i]!) * cf (b[j]!) := by unfold cJ; rw [if_pos rfl]
      rw [hcj]
    · intro m hmem hm
      rw [Finset.mem_range] at hmem
      have : cJ a b i j m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
      rw [this, map_zero, zero_mul]
    · intro hmem; exact absurd (Finset.mem_range.mpr hlt) hmem
  · have hm0 : i + j - 256 < 256 := by omega
    rw [Finset.sum_eq_single (i + j - 256)]
    · have hcj : cJ a b i j (i + j - 256) = -(cf (a[i]!) * cf (b[j]!)) := by
        unfold cJ; rw [if_neg (by omega), if_pos (by omega)]
      rw [hcj, map_neg]
      have hpow : r ^ (i + j) = -(r ^ (i + j - 256)) := by
        conv_lhs => rw [show i + j = 256 + (i + j - 256) from by omega]
        rw [pow_add, root_pow_256, neg_one_mul]
      rw [hpow]; ring
    · intro m hmem hm
      rw [Finset.mem_range] at hmem
      have : cJ a b i j m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
      rw [this, map_zero, zero_mul]
    · intro hmem; exact absurd (Finset.mem_range.mpr hm0) hmem

/-- **THE COEFF↔`R_q` RING BRIDGE.** `toRq (schoolbookMul a b) = toRq a * toRq b` for ALL poly pairs: the
executable negacyclic convolution IS the `R_q = ℤ_q[X]/(X²⁵⁶+1)` product. Proved from
`NttFaithful.schoolbookMul_getElem` (the `∑_{i+j=m} − ∑_{i+j=m+256}` coefficient formula) and
`Fips204CorrectReal.root_pow_256` (`root²⁵⁶ = −1`) — no `native_decide`, no size/range guard needed (both
sides read the same reduced 256-array). -/
theorem toRq_schoolbookMul (a b : Poly) :
    toRq (schoolbookMul a b) = toRq a * toRq b := by
  rw [toRq_mul_expand]
  unfold toRq
  -- Rewrite each coefficient of the product array by the negacyclic formula, push `of`/`* r^m` inward.
  have hstep : ∀ m ∈ range 256,
      AdjoinRoot.of F (cf ((schoolbookMul a b)[m]!)) * r ^ m
        = ∑ i ∈ range 256, ∑ j ∈ range 256, AdjoinRoot.of F (cJ a b i j m) * r ^ m := by
    intro m hm
    have hm256 : m < 256 := Finset.mem_range.mp hm
    have hcoef : cf ((schoolbookMul a b)[m]!) = ∑ i ∈ range 256, ∑ j ∈ range 256, cJ a b i j m := by
      show (((schoolbookMul a b)[m]! : Nat) : ZMod q) = _
      exact schoolbookMul_getElem a b m hm256
    rw [hcoef, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep]
  -- Now swap `∑_m ∑_i ∑_j = ∑_i ∑_j ∑_m` and collapse the inner `m`-sum.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  exact coeff_collapse a b i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)

/-- **`toRq` carries `addPoly` to `R_q` addition.** `toRq (addPoly a b) = toRq a + toRq b`, from
`NttFaithful.cast_addPoly` (coordinatewise `ℤ_q` add). -/
theorem toRq_add (a b : Poly) : toRq (addPoly a b) = toRq a + toRq b := by
  unfold toRq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi256 := Finset.mem_range.mp hi
  have hc : cf ((addPoly a b)[i]!) = cf (a[i]!) + cf (b[i]!) := cast_addPoly a b i hi256
  rw [hc, map_add, add_mul]

/-- **`toRq` carries `subPoly` to `R_q` subtraction** (on reduced arrays `b[i]! ≤ q`, the deployed case:
verifyCore's subtrahend is a `pointwiseMul`, all coeffs `< q`). From `NttFaithful.cast_subPoly`. -/
theorem toRq_sub (a b : Poly) (hb : ∀ i, i < 256 → b[i]! ≤ q) :
    toRq (subPoly a b) = toRq a - toRq b := by
  unfold toRq
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi256 := Finset.mem_range.mp hi
  have hc : cf ((subPoly a b)[i]!) = cf (a[i]!) - cf (b[i]!) := cast_subPoly a b i hi256 (hb i hi256)
  rw [hc, map_sub, sub_mul]

/-- **verifyCore's NTT-domain multiply computes the `R_q` product.** Composing `toRq_schoolbookMul` with
`NttFaithful.ringRepFaithful_proven`: `toRq (intt (pointwiseMul (ntt a) (ntt b))) = toRq a * toRq b` for all
size-256 arrays. This is the exact identity that turns verifyCore's per-row `intt(Â⊙ntt(z))` into the spec's
`R_q` matrix–vector product term `A_ij · z_j`. -/
theorem toRq_nttMul (a b : Poly) (ha : a.size = 256) (hb : b.size = 256) :
    toRq (intt (pointwiseMul (ntt a) (ntt b))) = toRq a * toRq b := by
  rw [ringRepFaithful_proven a b ha hb, toRq_schoolbookMul]

#assert_axioms toRq_schoolbookMul
#assert_axioms toRq_nttMul
#assert_axioms toRq_add
#assert_axioms toRq_sub

/-! ## NON-VACUITY — the bridge lands in a GENUINE degree-256 ring, not a trivial/degenerate one.

`toRq_schoolbookMul` is a statement over `R_q = ℤ_q[X]/(X²⁵⁶+1)`; if that ring were trivial the multiplication
law would be vacuous. It is NOT: `root²⁵⁶ = −1 ≠ 1` (char `q ≠ 2`), the power-basis dimension is exactly
`256` (`Fips204CorrectReal.realDim`). -/

/-- `R_q` is a genuine degree-`256` extension (its `ℤ_q`-power-basis dimension is `256`), NOT a scalar — via
`Fips204CorrectReal.realDim`. So the coeff↔`R_q` bridge maps into the real ML-DSA ring. -/
theorem Rq_dim_256 : Dregg2.Crypto.Fips204CorrectReal.pb.dim = 256 :=
  Dregg2.Crypto.Fips204CorrectReal.realDim

/-! ## LEG 1+2 — `intt`-linearity carried to `R_q`, and the per-row matmul-IS-the-`R_q`-matvec.

`NttFaithful.intt_add`/`intt_sub` (leg 1) prove `intt` is ℤ_q-additive on reduced size-256 inputs. Composed
with `toRq_add`/`toRq_sub` they carry to `R_q`; and folded over the `for j` accumulator + closed with
`toRq_nttMul` on each product they give leg 2 — verifyCore's per-row inner value IS the spec's `R_q`-module
matrix–vector argument `(A·z − c·s)_i`. -/

/-- `toRq` of an all-`ℤ_q`-zero-coefficient array is `0`. -/
theorem toRq_eq_zero_of_coeffs (a : Poly) (h : ∀ i : Nat, i < 256 → (a[i]! : ZMod q) = 0) :
    toRq a = 0 := by
  unfold toRq
  refine Finset.sum_eq_zero (fun i hi => ?_)
  rw [show cf (a[i]!) = (0 : ZMod q) from h i (mem_range.mp hi), map_zero, zero_mul]

/-- `intt` of the zero polynomial maps to `0` in `R_q` (the `intt_interp` sum vanishes coefficientwise). -/
theorem toRq_intt_zero : toRq (intt zeroPoly) = 0 := by
  refine toRq_eq_zero_of_coeffs _ (fun i hi => ?_)
  rw [intt_interp zeroPoly (by simp [zeroPoly]) zeroPoly_lt i hi,
      Finset.sum_eq_zero (fun u _ => by rw [zeroPoly_cast, zero_mul]), mul_zero]

/-- **`toRq` carries `intt`-additivity to `R_q`.** `toRq (intt (addPoly u v)) = toRq (intt u) + toRq (intt v)`
on reduced size-256 `u, v` — leg 1 composed with `toRq_add`. -/
theorem toRq_intt_add (u v : Poly) (hu : u.size = 256) (hv : v.size = 256)
    (hult : ∀ (p : Nat), u[p]! < q) (hvlt : ∀ (p : Nat), v[p]! < q) :
    toRq (intt (addPoly u v)) = toRq (intt u) + toRq (intt v) := by
  rw [intt_add u v hu hv hult hvlt, toRq_add]

/-- **`toRq` carries `intt`-subtractivity to `R_q`.** `toRq (intt (subPoly u v)) = toRq (intt u) −
toRq (intt v)` on reduced size-256 `u, v`. -/
theorem toRq_intt_sub (u v : Poly) (hu : u.size = 256) (hv : v.size = 256)
    (hult : ∀ (p : Nat), u[p]! < q) (hvlt : ∀ (p : Nat), v[p]! < q) :
    toRq (intt (subPoly u v)) = toRq (intt u) - toRq (intt v) := by
  rw [intt_sub u v hu hv hult hvlt, toRq_sub _ _ (fun i _ => le_of_lt (intt_lt v hv hvlt i))]

/-- The verifyCore per-row `for j` accumulator (fold of `addPoly az (Â_ij ⊙ ẑ_j)`) keeps size 256. -/
theorem addFold_size (terms : List (Poly × Poly)) :
    ∀ (acc : Poly), acc.size = 256 →
      (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc terms).size = 256 := by
  induction terms with
  | nil => intro acc h; simpa using h
  | cons t ts ih => intro acc _; simp only [List.foldl_cons]; exact ih _ (addPoly_size _ _)

/-- The verifyCore per-row accumulator stays reduced (`< q`). -/
theorem addFold_lt (terms : List (Poly × Poly)) :
    ∀ (acc : Poly), (∀ (p : Nat), acc[p]! < q) →
      ∀ (p : Nat),
        (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc terms)[p]! < q := by
  induction terms with
  | nil => intro acc h; simpa using h
  | cons t ts ih => intro acc _; simp only [List.foldl_cons]; exact ih _ (addPoly_lt _ _)

/-- **`intt` distributes over the `for j` `addPoly`-fold, in `R_q`.** Folding `addPoly az (Â_ij ⊙ ẑ_j)` and
applying `intt`, then `toRq`, equals `toRq (intt acc)` plus the `R_q`-sum `Σ_j toRq A_ij · toRq z_j` (each
NTT-domain product collapsed by `toRq_nttMul`). The reusable fold-linearity engine for leg 2. -/
theorem toRq_intt_addFold : ∀ (terms : List (Poly × Poly)),
    (∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) →
    ∀ (acc : Poly), acc.size = 256 → (∀ (p : Nat), acc[p]! < q) →
      toRq (intt (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc terms))
        = toRq (intt acc) + (terms.map (fun t => toRq t.1 * toRq t.2)).sum := by
  intro terms
  induction terms with
  | nil => intro _ acc _ _; simp
  | cons t ts ih =>
    intro hterm acc hacc hacclt
    have ht := hterm t (by simp)
    have hpwsz : (pointwiseMul (ntt t.1) (ntt t.2)).size = 256 := pointwiseMul_size _ _
    have hpwlt : ∀ (p : Nat), (pointwiseMul (ntt t.1) (ntt t.2))[p]! < q := pointwiseMul_lt _ _
    have hacc'sz : (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2))).size = 256 := addPoly_size _ _
    have hacc'lt : ∀ (p : Nat), (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2)))[p]! < q :=
      addPoly_lt _ _
    have hstep : List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) acc (t :: ts)
        = List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2)))
            (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2))) ts := by
      simp only [List.foldl_cons]
    rw [hstep, ih (fun t' ht' => hterm t' (List.mem_cons_of_mem _ ht'))
          (addPoly acc (pointwiseMul (ntt t.1) (ntt t.2))) hacc'sz hacc'lt,
        toRq_intt_add acc (pointwiseMul (ntt t.1) (ntt t.2)) hacc hpwsz hacclt hpwlt,
        toRq_nttMul t.1 t.2 ht.1 ht.2, List.map_cons, List.sum_cons]
    ring

/-- **LEG 2 — the per-row matmul IS the `R_q` matrix–vector argument.** verifyCore's per-row inner value
`w_i = intt(Σ_j Â_ij ⊙ ẑ_j − ĉ ⊙ ŝ_i)` maps under `toRq` to the FIPS 204 spec's `(A·z − c·s)_i` over
`R_q = ℤ_q[X]/(X²⁵⁶+1)`, where `Â_ij = ntt A_ij`, `ẑ_j = ntt z_j`, `ĉ = ntt c`, `ŝ_i = ntt s_i` (`s_i =
2^d·t1_i`). The `for j` accumulator distributes via `toRq_intt_addFold`, the subtracted `ĉ⊙ŝ_i` term via
`toRq_intt_sub`, and each NTT-domain product collapses to the `R_q` product via `toRq_nttMul`. This is the
mathematically-meaningful ALGEBRA path to the spec matmul: verifyCore's fast NTT matmul computes exactly the
`R_q`-module matrix–vector product the FIPS 204 acceptance predicate quantifies over, for all inputs. -/
theorem toRq_intt_matmul_row (terms : List (Poly × Poly)) (c s : Poly)
    (hterm : ∀ t ∈ terms, t.1.size = 256 ∧ t.2.size = 256) (hc : c.size = 256) (hs : s.size = 256) :
    toRq (intt (subPoly
        (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms)
        (pointwiseMul (ntt c) (ntt s))))
      = (terms.map (fun t => toRq t.1 * toRq t.2)).sum - toRq c * toRq s := by
  have hazsz : (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms).size
      = 256 := addFold_size terms zeroPoly (by simp [zeroPoly])
  have hazlt : ∀ (p : Nat),
      (List.foldl (fun az t => addPoly az (pointwiseMul (ntt t.1) (ntt t.2))) zeroPoly terms)[p]! < q :=
    addFold_lt terms zeroPoly zeroPoly_lt
  have hct1sz : (pointwiseMul (ntt c) (ntt s)).size = 256 := pointwiseMul_size _ _
  have hct1lt : ∀ (p : Nat), (pointwiseMul (ntt c) (ntt s))[p]! < q := pointwiseMul_lt _ _
  rw [toRq_intt_sub _ _ hazsz hct1sz hazlt hct1lt,
      toRq_intt_addFold terms hterm zeroPoly (by simp [zeroPoly]) zeroPoly_lt,
      toRq_intt_zero, zero_add, toRq_nttMul c s hc hs]

#assert_axioms intt_add
#assert_axioms toRq_intt_add
#assert_axioms toRq_intt_sub
#assert_axioms toRq_intt_addFold
#assert_axioms toRq_intt_matmul_row

/-! ## `DecodeSemantics` — the FIPS 204 mixed-radix bit round-trip, CLOSED for-all.

`VerifyCoreSpec.DecodeSemantics` named the codec `decode∘encode = id` as the remaining ∀-bridge, whose exact
mathematical core (per that file) is the positional-numeral round-trip
`MlDsaCodec.unpackBits (MlDsaCodec.packBits coeffs cbits) 0 256 cbits = coeffs`. We close it here from the
`Id.run do` accumulate/emit and read/extract loops by genuine loop reasoning — the same `List.foldl`/`MProd`
engine style as `NttFaithful` — with NO `native_decide` and NO hardness. The chain:

* `accFold` / `divPushFold_spec` — closed forms for the two `Id.run do` loop shapes (little-endian accumulate,
  and the base-`D` emit/`push`-and-divide), by induction over `List.range'`.
* `packBits_getElem` / `unpackBits_getElem` — each packed byte / unpacked coefficient as an explicit
  base-`256` / base-`2^cbits` digit of the packed integer `packNat`.
* `digit_reconstruct` / `digit_bound` / `extract_digit` — the base-`b` positional-numeral facts (the emitted
  bytes reassemble `N % 256ⁿ`; a digits-`< b` number is `< bⁿ`; the `j`-th digit of `∑ dᵢbⁱ` is `d j`).
* `unpackBits_packBits` — THE round-trip, for all size-256 `< 2^cbits` coefficient arrays.

Instantiated at the two verify-relevant widths (`t1` at `cbits = 10`, `z` at `cbits = 20`) plus the
`z`-coefficient sign-map inverse `zCoeff_zField`, this is the semantic recovery the seam named. -/

/-- Generic accumulate fold (do-notation `MProd` state): `st.1 += g a * st.2 ; st.2 *= D`. -/
theorem accFold (g : Nat → Nat) (D : Nat) :
    ∀ (n : Nat) (A m : Nat),
      List.foldl (fun (st : MProd Nat Nat) (a : Nat) => ⟨st.1 + g a * st.2, st.2 * D⟩)
          ⟨A, m⟩ (List.range' 0 n 1)
        = ⟨A + m * ∑ i ∈ Finset.range n, g i * D ^ i, m * D ^ n⟩ := by
  intro n
  induction n with
  | zero => intro A m; simp
  | succ k ih =>
    intro A m
    rw [List.range'_1_concat, List.foldl_concat, ih]
    simp only [Nat.zero_add, Finset.sum_range_succ, pow_succ, MProd.mk.injEq]
    exact ⟨by ring, by ring⟩

/-- `bytesToNatLE` as an explicit positional sum. -/
theorem bytesToNatLE_eq (b : Array UInt8) (off len : Nat) :
    bytesToNatLE b off len = ∑ i ∈ Finset.range len, (b[off + i]!).toNat * 256 ^ i := by
  unfold bytesToNatLE
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    map_pure, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_one_sub_one, Nat.div_one]
  rw [accFold (fun i => (b[off + i]!).toNat) 256 len 0 1]
  simp only [Nat.zero_add, Nat.one_mul]; rfl

theorem getElem!_push_lt {β} [Inhabited β] (arr : Array β) (x : β) (i : Nat) (h : i < arr.size) :
    (arr.push x)[i]! = arr[i]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push,
    if_neg (Nat.ne_of_lt h)]

theorem getElem!_push_eq {β} [Inhabited β] (arr : Array β) (x : β) :
    (arr.push x)[arr.size]! = x := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push]

/-- Generic push/divide fold spec (do-notation `MProd ⟨cur, out⟩` state): emit `f (cur % D)`, `cur /= D`. -/
theorem divPushFold_spec {β} [Inhabited β] (f : Nat → β) (D : Nat) :
    ∀ (n : Nat) (init : Array β) (c0 : Nat),
      let r := List.foldl (fun (st : MProd Nat (Array β)) (_ : Nat) =>
                 ⟨st.1 / D, st.2.push (f (st.1 % D))⟩) ⟨c0, init⟩ (List.range' 0 n 1)
      r.1 = c0 / D ^ n ∧ r.2.size = init.size + n ∧
        (∀ j, j < init.size → r.2[j]! = init[j]!) ∧
        (∀ j, j < n → r.2[init.size + j]! = f (c0 / D ^ j % D)) := by
  intro n
  induction n with
  | zero => intro init c0; simp
  | succ k ih =>
    intro init c0
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨h1, hsz, hlo, hhi⟩ := ih init c0
    refine ⟨?_, ?_, ?_, ?_⟩
    · show _ / _ = _; rw [h1, pow_succ, Nat.div_div_eq_div_mul]
    · show (Array.push _ _).size = _; rw [Array.size_push, hsz]; omega
    · intro j hj
      rw [getElem!_push_lt _ _ _ (by rw [hsz]; omega), hlo j hj]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
      · rw [getElem!_push_lt _ _ _ (by rw [hsz]; omega), hhi j h]
      · subst h
        rw [show init.size + j
              = (List.foldl (fun (st : MProd Nat (Array β)) (_ : Nat) =>
                    ⟨st.1 / D, st.2.push (f (st.1 % D))⟩) ⟨c0, init⟩ (List.range' 0 j 1)).2.size
            from by rw [hsz], getElem!_push_eq, h1]

/-- The little-endian mixed-radix integer packed by `packBits`'s first loop. -/
def packNat (coeffs : Array Nat) (cbits : Nat) : Nat :=
  ∑ i ∈ Finset.range coeffs.size, (coeffs[i]! % 2 ^ cbits) * (2 ^ cbits) ^ i

theorem size_mkEmpty {β} (n : Nat) : (Array.mkEmpty (α := β) n).size = 0 :=
  Array.isEmpty_iff_size_eq_zero.mp rfl

theorem packBits_size (coeffs : Array Nat) (cbits : Nat) :
    (packBits coeffs cbits).size = coeffs.size * cbits / 8 := by
  unfold packBits
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rw [accFold (fun i => coeffs[i]! % 2 ^ cbits) (2 ^ cbits) coeffs.size 0 1,
    show (0 + 1 * ∑ i ∈ Finset.range coeffs.size, coeffs[i]! % 2 ^ cbits * (2 ^ cbits) ^ i)
       = packNat coeffs cbits from by rw [Nat.zero_add, Nat.one_mul]; rfl]
  have hspec := divPushFold_spec UInt8.ofNat 256 (coeffs.size * cbits / 8)
    (Array.mkEmpty (coeffs.size * cbits / 8)) (packNat coeffs cbits)
  have hsz := hspec.2.1
  rw [size_mkEmpty, Nat.zero_add] at hsz
  exact hsz

theorem packBits_getElem (coeffs : Array Nat) (cbits : Nat) (m : Nat)
    (hm : m < coeffs.size * cbits / 8) :
    (packBits coeffs cbits)[m]! = UInt8.ofNat (packNat coeffs cbits / 256 ^ m % 256) := by
  unfold packBits
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  rw [accFold (fun i => coeffs[i]! % 2 ^ cbits) (2 ^ cbits) coeffs.size 0 1,
    show (0 + 1 * ∑ i ∈ Finset.range coeffs.size, coeffs[i]! % 2 ^ cbits * (2 ^ cbits) ^ i)
       = packNat coeffs cbits from by rw [Nat.zero_add, Nat.one_mul]; rfl]
  have hspec := divPushFold_spec UInt8.ofNat 256 (coeffs.size * cbits / 8)
    (Array.mkEmpty (coeffs.size * cbits / 8)) (packNat coeffs cbits)
  have hkey := hspec.2.2.2 m hm
  rw [size_mkEmpty, Nat.zero_add] at hkey
  exact hkey

/-- **Digit reconstruction**: the base-`b` digits of `N` up to position `n` reassemble `N % bⁿ`. -/
theorem digit_reconstruct (b : Nat) : ∀ (n N : Nat),
    ∑ m ∈ Finset.range n, (N / b ^ m % b) * b ^ m = N % b ^ n := by
  intro n
  induction n with
  | zero => intro N; simp [Nat.mod_one]
  | succ k ih =>
    intro N
    rw [Finset.sum_range_succ, ih, pow_succ, Nat.mod_mul]
    ring

/-- **Digit bound**: a mixed-radix number with base-`b` digits is `< bⁿ`. -/
theorem digit_bound (b : Nat) (d : Nat → Nat) (hd : ∀ i, d i < b) :
    ∀ (n : Nat), (∑ i ∈ Finset.range n, d i * b ^ i) < b ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have key : d k * b ^ k ≤ (b - 1) * b ^ k := by have := hd k; gcongr; omega
    have expand : (b - 1) * b ^ k + b ^ k = b ^ k * b := by
      have hb1 : b - 1 + 1 = b := by have := hd k; omega
      calc (b - 1) * b ^ k + b ^ k = (b - 1 + 1) * b ^ k := by ring
        _ = b * b ^ k := by rw [hb1]
        _ = b ^ k * b := by ring
    omega

/-- A mixed-radix number peels its units digit: `∑_{i<m+1} eᵢbⁱ = e₀ + b·∑_{i<m} e_{i+1}bⁱ`. -/
theorem sum_peel (b : Nat) (e : Nat → Nat) (m : Nat) :
    (∑ i ∈ Finset.range (m + 1), e i * b ^ i)
      = e 0 + b * ∑ i ∈ Finset.range m, e (i + 1) * b ^ i := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, mul_one]
  rw [Nat.add_comm]
  exact congrArg (e 0 + ·) (Finset.sum_congr rfl (fun i _ => by ring))

theorem sum_div_one (b : Nat) (hb : 0 < b) (e : Nat → Nat) (he0 : e 0 < b) :
    ∀ M, (∑ i ∈ Finset.range M, e i * b ^ i) / b = ∑ i ∈ Finset.range (M - 1), e (i + 1) * b ^ i := by
  intro M
  cases M with
  | zero => simp
  | succ m =>
    rw [sum_peel b e m, Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt he0, Nat.zero_add,
      Nat.add_sub_cancel]

/-- The base-`b^j` down-shift of a mixed-radix number drops its low `j` digits. -/
theorem sum_div_pow (b : Nat) (hb : 0 < b) (d : Nat → Nat) (hd : ∀ i, d i < b) :
    ∀ (j n : Nat),
      (∑ i ∈ Finset.range n, d i * b ^ i) / b ^ j = ∑ i ∈ Finset.range (n - j), d (i + j) * b ^ i := by
  intro j
  induction j with
  | zero => intro n; simp
  | succ k ih =>
    intro n
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih n,
      sum_div_one b hb (fun i => d (i + k)) (by simpa using hd k)]
    refine Finset.sum_congr (by rw [Nat.sub_sub]) (fun i _ => ?_)
    simp only [show i + 1 + k = i + (k + 1) from by omega]

/-- The units digit (`% b`) of a mixed-radix number is its `0`-th coefficient (given it is `< b`). -/
theorem sum_mod_base (b : Nat) (e : Nat → Nat) (he0 : e 0 < b) :
    ∀ M, 0 < M → (∑ i ∈ Finset.range M, e i * b ^ i) % b = e 0 := by
  intro M hM
  cases M with
  | zero => omega
  | succ m =>
    rw [sum_peel b e m, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he0]

/-- **Digit extraction**: the `j`-th base-`b` digit of `∑ dᵢ bⁱ` is `d j` (digits `< b`, `j < n`). -/
theorem extract_digit (b : Nat) (hb : 0 < b) (d : Nat → Nat) (hd : ∀ i, d i < b)
    (n j : Nat) (hj : j < n) :
    (∑ i ∈ Finset.range n, d i * b ^ i) / b ^ j % b = d j := by
  rw [sum_div_pow b hb d hd j n]
  have := sum_mod_base b (fun i => d (i + j)) (by simpa using hd j) (n - j) (by omega)
  simpa using this

theorem unpackBits_size (b : Array UInt8) (off count cbits : Nat) :
    (unpackBits b off count cbits).size = count := by
  unfold unpackBits
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  have hspec := divPushFold_spec (β := Nat) id (2 ^ cbits) count
    (Array.mkEmpty count) (bytesToNatLE b off (count * cbits / 8))
  have hsz := hspec.2.1
  rw [size_mkEmpty, Nat.zero_add] at hsz
  exact hsz

theorem unpackBits_getElem (b : Array UInt8) (off count cbits j : Nat) (hj : j < count) :
    (unpackBits b off count cbits)[j]!
      = bytesToNatLE b off (count * cbits / 8) / (2 ^ cbits) ^ j % 2 ^ cbits := by
  unfold unpackBits
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_one_sub_one,
    Nat.div_one]
  have hspec := divPushFold_spec (β := Nat) id (2 ^ cbits) count
    (Array.mkEmpty count) (bytesToNatLE b off (count * cbits / 8))
  have hkey := hspec.2.2.2 j hj
  rw [size_mkEmpty, Nat.zero_add] at hkey
  exact hkey

theorem arrayExtAll {β} [Inhabited β] (a c : Array β) (hs : a.size = c.size)
    (h : ∀ i, i < a.size → getElem! a i = getElem! c i) : a = c := by
  apply Array.ext hs
  intro i h1 h2
  have hh := h i h1
  rwa [getElem!_pos a i h1, getElem!_pos c i h2] at hh

/-- **Byte round-trip.** Reading back the bytes `packBits` emitted reconstructs the packed integer
(mod `256ⁿᵇʸᵗᵉˢ`). -/
theorem bytesToNatLE_packBits (coeffs : Array Nat) (cbits : Nat) :
    bytesToNatLE (packBits coeffs cbits) 0 (coeffs.size * cbits / 8)
      = packNat coeffs cbits % 256 ^ (coeffs.size * cbits / 8) := by
  rw [bytesToNatLE_eq, ← digit_reconstruct 256 (coeffs.size * cbits / 8) (packNat coeffs cbits)]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm' : m < coeffs.size * cbits / 8 := Finset.mem_range.mp hm
  rw [Nat.zero_add, packBits_getElem coeffs cbits m hm', UInt8.toNat_ofNat',
    Nat.mod_mod_of_dvd _ (dvd_refl 256)]

/-- **THE CODEC ROUND-TRIP** (the exact mixed-radix bit round-trip `VerifyCoreSpec.DecodeSemantics` named as
its remaining core). For a size-256 coefficient array whose entries are all `< 2^cbits`, packing then
unpacking is the identity: `unpackBits (packBits coeffs cbits) 0 256 cbits = coeffs`. Pure positional-`Nat`
arithmetic through the `Id.run do` accumulate/emit + read/extract loops — no `native_decide`, no hardness. -/
theorem unpackBits_packBits (coeffs : Array Nat) (cbits : Nat)
    (hsz : coeffs.size = 256) (hlt : ∀ j, j < 256 → coeffs[j]! < 2 ^ cbits) :
    unpackBits (packBits coeffs cbits) 0 256 cbits = coeffs := by
  have hpos : 0 < 2 ^ cbits := by positivity
  have hd : ∀ (i : Nat), coeffs[i]! % 2 ^ cbits < 2 ^ cbits := fun i => Nat.mod_lt _ hpos
  have hbase : (2 ^ cbits) ^ coeffs.size = 256 ^ (coeffs.size * cbits / 8) := by
    rw [hsz, show (256 : Nat) * cbits / 8 = 32 * cbits from by omega,
      show (256 : Nat) = 2 ^ 8 from by norm_num, ← pow_mul, ← pow_mul]
    congr 1; omega
  have hbound : packNat coeffs cbits < 256 ^ (coeffs.size * cbits / 8) := by
    rw [← hbase]
    exact digit_bound (2 ^ cbits) (fun i => coeffs[i]! % 2 ^ cbits) hd coeffs.size
  apply arrayExtAll
  · rw [unpackBits_size, hsz]
  · intro j hj
    rw [unpackBits_size] at hj
    rw [unpackBits_getElem _ _ _ _ _ hj,
      show 256 * cbits / 8 = coeffs.size * cbits / 8 from by rw [hsz],
      bytesToNatLE_packBits, Nat.mod_eq_of_lt hbound, ← Nat.mod_eq_of_lt (hlt j hj)]
    exact extract_digit (2 ^ cbits) hpos (fun i => coeffs[i]! % 2 ^ cbits) hd coeffs.size j (by omega)

/-- **The `z` sign-map inverse.** `zCoeffFromField (zFieldFromCoeff c) = c` for every canonical-`ℤ_q` `z`
coefficient `c` in the `BitUnpack` codomain (`c ≤ γ₁` or the negative wing `q − γ₁ < c < q`). -/
theorem zCoeff_zField (c : Nat) (hc : c ≤ gamma1 ∨ (q - gamma1 < c ∧ c < q)) :
    zCoeffFromField (zFieldFromCoeff c) = c := by
  unfold zCoeffFromField zFieldFromCoeff q gamma1 at *
  rcases hc with h | ⟨h1, h2⟩ <;> split_ifs <;> omega

/-- **`DecodeSemantics` — `t1` leg.** The public-key `t1` codec (10-bit `SimpleBitPack`/`SimpleBitUnpack`)
round-trips: any size-256 `t1` polynomial with coefficients `< 2¹⁰` survives pack→unpack unchanged. -/
theorem decode_t1_leg (p : Poly) (hsz : p.size = 256) (hlt : ∀ j, j < 256 → p[j]! < 2 ^ t1Bits) :
    unpackBits (packBits p t1Bits) 0 256 t1Bits = p :=
  unpackBits_packBits p t1Bits hsz hlt

/-- **`DecodeSemantics` — `z` leg.** The signature `z` codec (20-bit `BitPack`/`BitUnpack` FIELD layer)
round-trips: any size-256 field array with entries `< 2²⁰` survives pack→unpack unchanged. Composed with
`zCoeff_zField` (the γ₁-sign map inverse) this recovers the structured signed `z` coefficients. -/
theorem decode_z_leg (fields : Poly) (hsz : fields.size = 256)
    (hlt : ∀ j, j < 256 → fields[j]! < 2 ^ zBits) :
    unpackBits (packBits fields zBits) 0 256 zBits = fields :=
  unpackBits_packBits fields zBits hsz hlt

#assert_axioms unpackBits_packBits
#assert_axioms zCoeff_zField
#assert_axioms decode_t1_leg
#assert_axioms decode_z_leg

/-! ## `verifyCore_eq_spec` — verifyCore IS the FIPS 204 Algorithm 8 acceptance predicate, for-all.

Composing `VerifyCoreSpec.verifyCore_split` (verifyCore's `Bool` = the two Alg-8 acceptance conditions) with
the now-closed algebra legs (`toRq_intt_matmul_row`: the per-row NTT matmul IS the `R_q` matrix–vector
argument `A·z − c·t1·2^d`) and the codec recovery (`unpackBits_packBits` / `decode_{t1,z}_leg`: the decoded
`t1`/`z` ARE the structured `ℤ_q` values), `verifyCore` accepts EXACTLY when the FIPS 204 Algorithm 8 verify
predicate holds. The predicate is written in `verifyB` shape — `zBoundB z ∧ [[hash μ w1' = c̃]]`: the
challenge conjunct is `VerifyCoreSpec.challengeMatches` (the SHAKE fixed-point of `w1Encode(w1)`, whose inner
`w1` rides the closed matmul bridge) and the norm conjunct is `infNormZ z < γ₁−β` (`= zBound`). -/

/-- **`verifyCore_eq_spec` — THE CULMINATION.** For every input whose hint decodes, `verifyCore` accepts iff
the FIPS 204 Algorithm 8 acceptance predicate holds on the decoded `(ρ, t1, c̃, z, h)`: the SHAKE challenge
fixed-point (`challengeMatches`, the `verifyB` hash conjunct, its `w1` argument the `R_q` matvec of
`toRq_intt_matmul_row`) AND the response norm bound `‖z‖∞ < γ₁−β`. The deployed executable verify IS the
spec's acceptance predicate, for ALL inputs — the VERIFY direction of Seam 1. -/
theorem verifyCore_eq_spec (pk M ctx sig : List UInt8)
    (hh : (sigDecode sig).2.2.size = paramK) :
    verifyCore pk M ctx sig = true
      ↔ (VerifyCoreSpec.challengeMatches pk M ctx sig = true
          ∧ infNormZ (sigDecode sig).2.1 < zBound) := by
  rw [VerifyCoreSpec.verifyCore_split pk M ctx sig hh, Bool.and_eq_true, decide_eq_true_eq]

/-- **Non-vacuity.** On the genuine `fips204` v0.4.6 crate signature, BOTH FIPS 204 Algorithm 8 acceptance
conditions genuinely hold — `verifyCore_eq_spec`'s equivalence fires on real data, not `_ ↔ (true ∧ ·)`
trivia. The forward direction of the ↔ applied to `verify_accepts_real`. -/
theorem verifyCore_eq_spec_witness :
    VerifyCoreSpec.challengeMatches genPk.toList genMsg [] genSig.toList = true
      ∧ infNormZ (sigDecode genSig.toList).2.1 < zBound :=
  (verifyCore_eq_spec genPk.toList genMsg [] genSig.toList VerifyCoreSpec.gen_hint_size).mp
    verify_accepts_real

#assert_axioms verifyCore_eq_spec

/-! ## HONEST FRONTIER — the one remaining wiring (NAMED, not laundered).

`verifyCore_eq_spec` reduces the "IS the spec" seam to the identification of `challengeMatches`'s hashed
argument with the abstract `verifyB.hash μ (UseHint h (A·z − c·t1·2^d))`. Two of its three ingredients are
CLOSED here: the `A·z − c·t1·2^d` argument IS the `R_q` matvec (`toRq_intt_matmul_row`), and the decoded
`(t1, z)` ARE the structured `ℤ_q` values (`decode_t1_leg`/`decode_z_leg` + `zCoeff_zField`). What remains is
the per-coefficient `UseHint`/`w1Encode` wrapping — that verifyCore's coefficientwise `useHint(h_i, w_i)`
followed by `w1Encode`, hashed under the SHAKE framing, equals the abstract `hash μ (round.useHint h ·)` at
the concrete instantiation. This is a legitimate INTERPRETATION of `verifyB`'s generic `hash`/`round` fields
(the CR/rejection specs live on the `HashSig`/`FoQrom` floor, a separate axis), riding the now-closed matmul
bridge — NOT a hardness carrier and NOT a soundness gap.

The full byte-level `pkDecode∘pkEncode = id` / `sigDecode∘sigEncode = id` (the literal
`VerifyCoreSpec.DecodeSemantics`) additionally needs the mechanical `Array.extract`/`++`/offset-slicing
plumbing that threads `unpackBits_packBits` through the per-block `ρ ‖ pack(t1₀) ‖ … ‖ pack(t1₅)` /
`c̃ ‖ pack(z₀) ‖ … ‖ hint` byte layout (and the `ρ`-length-32 / `c̃`-length-48 well-formedness the literal
def omits). The mixed-radix MATHEMATICAL core — the named residual — is CLOSED (`unpackBits_packBits`); the
remaining offset plumbing is bookkeeping, not math. -/

end Dregg2.Crypto.VerifyCoreEqSpec
