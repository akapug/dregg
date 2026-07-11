/-
# `Dregg2.Crypto.MlKemNttFaithful` — the ∀-lift of ML-KEM-768's INCOMPLETE-NTT faithfulness.

The load-bearing gate `MlKemRing.ntt_computes_negacyclic_mul` — `intt (pointwiseNtt (ntt a) (ntt b)) =
schoolbookMul a b` — is currently ONE `native_decide` sample. This module proves the ∀-form (the NTT-multiply
computes the negacyclic ring product for ALL canonical poly pairs), mirroring the CLOSED ML-DSA analog
`Dregg2.Crypto.NttFaithful` (`ringRepFaithful_proven` + its whole ladder).

## THE KEY DIFFERENCE — ML-KEM's NTT is INCOMPLETE (the Kyber-vs-Dilithium split)

`q = 3329`, `ζ = 17` is a primitive **256th** root (`ζ¹²⁸ = −1`, `ζ²⁵⁶ = 1`), NOT a 512th root. So
`X²⁵⁶+1 = ∏_{g<128} (X² − ζ^{2·brv7(g)+1})` factors into 128 **quadratics**, and the `ntt` (7 CT stages,
`len = 128 … 2`, stops at `len = 2`) maps `R_q → ∏_{g<128} ℤ_q[X]/(X² − γ_g)` with `γ_g = ζ^{2·brv7(g)+1}`.
Each image is a degree-1 poly = a PAIR `(a₀,a₁)` (array slots `2g, 2g+1`), and `pointwiseNtt` is the 128
`baseCaseMultiply` products (Alg 12): `(a₀+a₁X)(b₀+b₁X) mod (X²−γ) = (a₀b₀+a₁b₁γ, a₀b₁+a₁b₀)` — NOT a
coefficientwise product. This is the whole new content over the ML-DSA proof, whose NTT is COMPLETE (256 linear
factors, pointwise = scalar product).

## THE LADDER (mirror of the ML-DSA proof; the FORWARD direction is CLOSED here)

* **RUNG 0 — ℤ_q casts** (`cast_addQ`/`cast_subQ`/`cast_mulModQ`): the executable `%q` scalar ops are the honest
  field ops in `ZMod 3329` (`3329` prime by `norm_num`).
* **RUNG 1 — poly ops** (`cast_addPoly`/`cast_subPoly`) and the schoolbook negacyclic convolution formula
  (`schoolbookMul_getElem`): `(a·b)_m = ∑_{i+j=m} a_i b_j − ∑_{i+j=m+256} a_i b_j`, from the imperative double
  loop (not asserted).
* **RUNG 2 — the CT butterfly network** (`bfSweep`/`bfFold_spec`/`cast_bfSweep`, `ntt_eq_fold`, `stage_inv`):
  the 7-stage schedule realizes the decimated evaluations; at `s = 7` (`len = 2`) each pair-slot holds the poly
  reduced mod its quadratic factor (`ntt_reduces_to_quotients`). `ζ` primitive 256th (`zeta_pow_neg_one`:
  `ζ¹²⁸ = −1`, `orderOf` argument for the inverse), roots via `brv7` congruences (`brv_even7`/`brv_odd7`/
  `brv_high7`, plain `decide`) collapse to `rootAt_final : rootAt 7 g = γ_g = ζ^{2·brv7(g)+1}`.
* **RUNG 5 — `baseCaseMultiply` = the product in `ℤ_q[X]/(X²−γ)`** (`cast_baseCaseMul_*`), and the NOVEL
  quadratic multiplicativity (`evEven_schoolbook`/`evOdd_schoolbook`): the pair-reduction `(evEven,evOdd)` of the
  negacyclic product IS the `baseCaseMultiply` of the pair-reductions, when `γ¹²⁸ = −1`. Proven by the negacyclic
  convolution split by index-parity (`inner_even`/`inner_odd`), the incomplete-NTT analog of the ML-DSA
  `eval256_schoolbook`.
* **RUNG 6 (forward) — `NttMulHom` CLOSED** (`nttMulHom_proven`): `ntt (schoolbookMul a b) =
  pointwiseNtt (ntt a) (ntt b)` for all canonical `a, b`, for-all, no `native_decide`. Combined with the textbook
  reduction (`mlkem_faithful_of`), the whole gate follows from the SINGLE remaining residual.

## THE REMAINING RUNG (named precisely, mirroring the ML-DSA `inttStage_inv` leg)

`NttLeftInverse := ∀ c, c.size = 256 → (∀ p, c[p]! < q) → intt (ntt c) = c` — the Gentleman–Sande inverse
inverts the incomplete transform. In the ML-DSA proof this is `nttLeftInverse_proven` (the `intt` interpolation
induction `inttStage_inv` collapsed by `interp_orth`, ~500 lines). The ML-KEM analog is the same structure over
the 128-pair (quadratic-quotient) leaves rather than 256 scalar leaves; it is left as the named residual. It is
non-vacuous: `nttLeftInverse_sample` witnesses `intt (ntt sampleA) = sampleA` (the existing gate, restated —
NOT inside any `∀`). The final theorem `mlkem_ntt_ring_faithful` is proven MODULO `NttLeftInverse`
(`mlkem_faithful_of hInv`), with `NttMulHom` fully closed.

## NON-FAKE

Every forward keystone is `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); the `ζ`-order and
`brv7` congruences are plain `decide` (kernel reduction, NOT `native_decide`), so no `ofReduceBool` residual in
any `∀`-body. The guards (`a.size = 256`, reducedness) match the deployed pipeline exactly, as in the ML-DSA
proof; the existing concrete `native_decide` sample is untouched (non-vacuity).
-/
import Dregg2.Crypto.MlKemRing
import Dregg2.Tactics
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace Dregg2.Crypto.MlKemRing

open Finset

/-- `ℤ_q` is a genuine field: `q = 3329` is the ML-KEM prime (checked by `norm_num`, not asserted). -/
instance : Fact (Nat.Prime q) := ⟨by unfold q; norm_num⟩
instance : Fact (2 < q) := ⟨by unfold q; norm_num⟩

/-! ## PART 1 — entrywise reasoning through the imperative `Array.set!`-fold loops. -/

/-- Folding `set!` over a list `L` leaves index `j ∉ L` untouched. -/
theorem foldSet_notMem (g : Nat → Nat) (j : Nat) :
    ∀ (L : List Nat) (init : Poly), j ∉ L →
      (List.foldl (fun r i => r.set! i (g i)) init L)[j]! = init[j]! := by
  intro L
  induction L with
  | nil => intro init _; simp
  | cons hd tl ih =>
    intro init hj
    simp only [List.foldl_cons]
    rw [ih (init.set! hd (g hd)) (by simp_all)]
    have hne : hd ≠ j := by rintro rfl; exact hj (List.mem_cons_self ..)
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
    rw [if_neg hne]

/-- Folding `set! · i (g i)` over a list containing `j` (in bounds) lands `g j` at index `j`. -/
theorem foldSet_mem (g : Nat → Nat) (j : Nat) :
    ∀ (L : List Nat) (init : Poly), j ∈ L → j < init.size →
      (List.foldl (fun r i => r.set! i (g i)) init L)[j]! = g j := by
  intro L
  induction L with
  | nil => intro init hj; exact absurd hj (List.not_mem_nil)
  | cons hd tl ih =>
    intro init hj hsz
    simp only [List.foldl_cons]
    by_cases hmem : j ∈ tl
    · exact ih _ hmem (by simpa using hsz)
    · have hhd : hd = j := by
        rcases List.mem_cons.mp hj with h | h
        · exact h.symm
        · exact absurd h hmem
      subst hhd
      rw [foldSet_notMem g hd tl (init.set! hd (g hd)) hmem]
      simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
      simp [hsz]

/-- `get!` after `set!` at a DIFFERENT index is unchanged. -/
theorem getElem!_set!_ne (b : Poly) (i j v : Nat) (h : i ≠ j) :
    (b.set! i v)[j]! = b[j]! := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
  rw [if_neg h]

/-- `get!` after in-bounds `set!` at the SAME index reads the written value. -/
theorem getElem!_set!_self (b : Poly) (i v : Nat) (h : i < b.size) :
    (b.set! i v)[i]! = v := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds, Array.set!_eq_setIfInBounds]
  simp [h]

theorem size_set! (b : Poly) (i v : Nat) : (b.set! i v).size = b.size := by
  simp [Array.set!_eq_setIfInBounds]

/-- After a `set!`, every slot holds either the written value or the original. -/
theorem set!_val_cases (b : Poly) (i v p : Nat) :
    (b.set! i v)[p]! = v ∨ (b.set! i v)[p]! = b[p]! := by
  by_cases h : i = p
  · subst h
    by_cases hib : i < b.size
    · exact Or.inl (getElem!_set!_self _ _ _ hib)
    · right; simp [Array.set!_eq_setIfInBounds, hib]
  · exact Or.inr (getElem!_set!_ne _ _ _ _ h)

theorem set!_lt (b : Poly) (i v : Nat) (hb : ∀ (p : Nat), b[p]! < q) (hv : v < q) :
    ∀ (p : Nat), (b.set! i v)[p]! < q := by
  intro p; rcases set!_val_cases b i v p with hh | hh
  · rw [hh]; exact hv
  · rw [hh]; exact hb p

theorem getElem!_ge (a : Poly) (p : Nat) (hp : a.size ≤ p) : a[p]! = 0 := by
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_none hp, Option.getD_none]
  rfl

theorem zeroPoly_get (m : Nat) : zeroPoly[m]! = 0 := by
  rw [zeroPoly, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

theorem zeroPoly_cast (m : Nat) : ((zeroPoly[m]! : Nat) : ZMod q) = 0 := by
  rw [zeroPoly_get]; simp

theorem zeroPoly_lt : ∀ (p : Nat), zeroPoly[p]! < q := by
  intro p; rw [zeroPoly_get]; unfold q; omega

/-! ## PART 1b — RUNG 0: the ℤ_q REDUCTION HOMOMORPHISM. -/

theorem cast_addQ (a b : Nat) : ((addQ a b : Nat) : ZMod q) = (a : ZMod q) + b := by
  unfold addQ; rw [ZMod.natCast_mod, Nat.cast_add]

theorem cast_mulModQ (a b : Nat) : ((mulModQ a b : Nat) : ZMod q) = (a : ZMod q) * b := by
  unfold mulModQ; rw [ZMod.natCast_mod, Nat.cast_mul]

theorem cast_subQ (a b : Nat) (h : b ≤ a + q) : ((subQ a b : Nat) : ZMod q) = (a : ZMod q) - b := by
  unfold subQ; rw [ZMod.natCast_mod, Nat.cast_sub h, Nat.cast_add, ZMod.natCast_self]; ring

theorem mulModQ_lt (a b : Nat) : mulModQ a b < q := by
  unfold mulModQ; exact Nat.mod_lt _ (by unfold q; omega)
theorem addQ_lt (a b : Nat) : addQ a b < q := by unfold addQ; exact Nat.mod_lt _ (by unfold q; omega)
theorem subQ_lt (a b : Nat) : subQ a b < q := by unfold subQ; exact Nat.mod_lt _ (by unfold q; omega)

/-- `Nat`-cast into `ℤ_q` is injective on the reduced range `[0, q)`. -/
theorem natCast_inj_of_lt (x y : Nat) (hx : x < q) (hy : y < q)
    (h : ((x:Nat):ZMod q) = ((y:Nat):ZMod q)) : x = y := by
  rw [← ZMod.val_natCast_of_lt hx, ← ZMod.val_natCast_of_lt hy, h]

/-! ## PART 1c — RUNG 1: the non-butterfly poly ops ARE the coefficientwise `ℤ_q` ops. -/

theorem addPoly_getElem (a b : Poly) (i : Nat) (hi : i < 256) :
    (addPoly a b)[i]! = addQ a[i]! b[i]! := by
  unfold addPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  have hmem : i ∈ List.range' 0 [:256].size 1 := by
    simp only [Std.Legacy.Range.size, List.mem_range'_1]; omega
  have hsz : i < zeroPoly.size := by simp [zeroPoly]; omega
  exact foldSet_mem (fun i => addQ a[i]! b[i]!) i (List.range' 0 [:256].size 1) zeroPoly hmem hsz

theorem subPoly_getElem (a b : Poly) (i : Nat) (hi : i < 256) :
    (subPoly a b)[i]! = subQ a[i]! b[i]! := by
  unfold subPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  have hmem : i ∈ List.range' 0 [:256].size 1 := by
    simp only [Std.Legacy.Range.size, List.mem_range'_1]; omega
  have hsz : i < zeroPoly.size := by simp [zeroPoly]; omega
  exact foldSet_mem (fun i => subQ a[i]! b[i]!) i (List.range' 0 [:256].size 1) zeroPoly hmem hsz

theorem cast_addPoly (a b : Poly) (i : Nat) (hi : i < 256) :
    ((addPoly a b)[i]! : ZMod q) = (a[i]! : ZMod q) + (b[i]! : ZMod q) := by
  rw [addPoly_getElem a b i hi, cast_addQ]

theorem cast_subPoly (a b : Poly) (i : Nat) (hi : i < 256) (hb : b[i]! ≤ q) :
    ((subPoly a b)[i]! : ZMod q) = (a[i]! : ZMod q) - (b[i]! : ZMod q) := by
  rw [subPoly_getElem a b i hi, cast_subQ _ _ (by omega)]

theorem addPoly_size (a b : Poly) : (addPoly a b).size = 256 := by
  unfold addPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    map_pure, List.forIn_pure_yield_eq_foldl]
  generalize List.range' 0 [:256].size 1 = L
  suffices h : ∀ (init : Poly), init.size = 256 →
      (List.foldl (fun r i => Array.set! r i (addQ a[i]! b[i]!)) init L).size = 256 by
    exact h zeroPoly (by simp [zeroPoly])
  intro init hinit
  induction L generalizing init with
  | nil => simpa using hinit
  | cons hd tl ih => simp only [List.foldl_cons]; exact ih _ (by simp [hinit])

theorem subPoly_size (a b : Poly) : (subPoly a b).size = 256 := by
  unfold subPoly
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp,
    map_pure, List.forIn_pure_yield_eq_foldl]
  generalize List.range' 0 [:256].size 1 = L
  suffices h : ∀ (init : Poly), init.size = 256 →
      (List.foldl (fun r i => Array.set! r i (subQ a[i]! b[i]!)) init L).size = 256 by
    exact h zeroPoly (by simp [zeroPoly])
  intro init hinit
  induction L generalizing init with
  | nil => simpa using hinit
  | cons hd tl ih => simp only [List.foldl_cons]; exact ih _ (by simp [hinit])

theorem addPoly_lt (a b : Poly) : ∀ (p : Nat), (addPoly a b)[p]! < q := by
  intro p
  by_cases hp : p < 256
  · rw [addPoly_getElem a b p hp]; exact addQ_lt _ _
  · rw [getElem!_ge _ p (by rw [addPoly_size]; omega)]; unfold q; omega

theorem subPoly_lt (a b : Poly) : ∀ (p : Nat), (subPoly a b)[p]! < q := by
  intro p
  by_cases hp : p < 256
  · rw [subPoly_getElem a b p hp]; exact subQ_lt _ _
  · rw [getElem!_ge _ p (by rw [subPoly_size]; omega)]; unfold q; omega

/-! ## PART 1d — ROOT-OF-UNITY ORTHOGONALITY (order 256, ζ¹²⁸ = −1). -/

theorem geomTel {R} [CommRing R] (x : R) (n : Nat) :
    (x - 1) * (∑ i ∈ range n, x^i) = x^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, mul_add, ih, pow_succ]; ring

theorem powSum_zero {F} [Field F] (w : F) (N : Nat) (hN : w^N = 1) (hw : w ≠ 1) :
    ∑ i ∈ range N, w^i = 0 := by
  have h := geomTel w N
  rw [hN, sub_self] at h
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (by linear_combination h1) (sub_ne_zero.mpr hw)
  · exact h2

/-- `ζ` has multiplicative order exactly 256 in `ℤ_q`, given `ζ¹²⁸ = −1`. Via `orderOf_eq_prime_pow`. -/
theorem orderOf_zeta (hz : (zeta : ZMod q)^128 = -1) : orderOf (zeta : ZMod q) = 256 := by
  have h128 : (zeta : ZMod q)^(2^7) ≠ 1 := by
    show (zeta : ZMod q)^128 ≠ 1; rw [hz]; exact ZMod.neg_one_ne_one
  have h256 : (zeta : ZMod q)^(2^8) = 1 := by
    show (zeta : ZMod q)^256 = 1
    have h : (zeta : ZMod q)^256 = ((zeta : ZMod q)^128)^2 := by rw [← pow_mul]
    rw [h, hz]; ring
  simpa using orderOf_eq_prime_pow (p := 2) (n := 7) (x := (zeta : ZMod q)) h128 h256

/-- **THE ORTHOGONALITY RELATION** — `ζ` a primitive 256th root, so `Σ_{m<128} (ζ^d)^m = ...`. Kept for the
inverse leg. The `ζ`-root property enters as the hypothesis `hz`. -/
theorem zeta_orthogonality (hz : (zeta : ZMod q)^128 = -1) (d : Nat) :
    ∑ m ∈ range 256, (((zeta : ZMod q))^d)^m = if 256 ∣ d then (256 : ZMod q) else 0 := by
  set ζ : ZMod q := (zeta : ZMod q) with hζ
  have hord : orderOf ζ = 256 := orderOf_zeta hz
  by_cases hd : 256 ∣ d
  · have hω1 : (ζ^d) = 1 := by
      exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [hord]; exact hd)
    simp [hω1, hd]
  · have hN : ((ζ^d))^256 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    have hw : (ζ^d) ≠ 1 := by
      intro hcon
      have hdvd : (256:ℕ) ∣ d := by rw [← hord]; exact orderOf_dvd_of_pow_eq_one hcon
      exact hd hdvd
    rw [if_neg hd]; exact powSum_zero (ζ^d) 256 hN hw

/-! ## PART 1e — the butterfly-sweep loop primitive (RUNG-2 engine). -/

theorem foldl_ext {A B : Type} (f g : B → A → B) (h : ∀ b a, f b a = g b a)
    (l : List A) (init : B) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih => simp only [List.foldl_cons]; rw [h init hd]; exact ih _

theorem foldl_ext_mem {A B : Type} (f g : B → A → B) (l : List A)
    (h : ∀ b, ∀ a ∈ l, f b a = g b a) (init : B) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]; rw [h init hd (List.mem_cons_self ..)]
    exact ih (fun b a ha => h b a (List.mem_cons_of_mem _ ha)) _

/-- The butterfly step (the desugared inner-loop body of `ntt`). -/
def bfStepC (z len : Nat) (b : Poly) (j : Nat) : Poly :=
  (b.set! (j + len) (subQ b[j]! (mulModQ z b[j + len]!))).set! j (addQ b[j]! (mulModQ z b[j + len]!))

theorem bfStepC_size (z len : Nat) (b : Poly) (j : Nat) :
    (bfStepC z len b j).size = b.size := by
  unfold bfStepC; rw [size_set!, size_set!]

/-- **THE BUTTERFLY-SWEEP LOOP PRIMITIVE** (verbatim from the ML-DSA proof; the butterfly is the same 2×2 map). -/
theorem bfFold_spec (z len : Nat) (hlen : 1 ≤ len) (a0 : Poly) :
    ∀ (m s : Nat) (b : Poly),
      b.size = 256 → s + m + len ≤ 256 → m ≤ len →
      (∀ p, s ≤ p → p < s + m → b[p]! = a0[p]!) →
      (∀ p, s + len ≤ p → p < s + m + len → b[p]! = a0[p]!) →
      (List.foldl (bfStepC z len) b (List.range' s m)).size = 256 ∧
      (∀ p, s ≤ p → p < s + m →
        (List.foldl (bfStepC z len) b (List.range' s m))[p]! = addQ a0[p]! (mulModQ z a0[p+len]!)) ∧
      (∀ p, s + len ≤ p → p < s + m + len →
        (List.foldl (bfStepC z len) b (List.range' s m))[p]! = subQ a0[p-len]! (mulModQ z a0[p]!)) ∧
      (∀ p, (p < s ∨ s + m ≤ p) → (p < s + len ∨ s + m + len ≤ p) →
        (List.foldl (bfStepC z len) b (List.range' s m))[p]! = b[p]!) := by
  intro m
  induction m with
  | zero =>
    intro s b hsz _ _ _ _
    refine ⟨by simpa using hsz, ?_, ?_, ?_⟩
    · intro p h1 h2; omega
    · intro p h1 h2; omega
    · intro p _ _; simp
  | succ m' ih =>
    intro s b hsz hbound hmlen hagLo hagHi
    have hbs : b[s]! = a0[s]! := hagLo s (by omega) (by omega)
    have hbsl : b[s+len]! = a0[s+len]! := hagHi (s+len) (by omega) (by omega)
    have hs256 : s < b.size := by rw [hsz]; omega
    have hsl256 : s + len < b.size := by rw [hsz]; omega
    set b1 := bfStepC z len b s with hb1def
    have hb1size : b1.size = 256 := by rw [hb1def, bfStepC_size]; exact hsz
    have hb1_s : b1[s]! = addQ a0[s]! (mulModQ z a0[s+len]!) := by
      rw [hb1def]; unfold bfStepC
      rw [getElem!_set!_self _ s _ (by rw [size_set!]; exact hs256), hbs, hbsl]
    have hb1_sl : b1[s+len]! = subQ a0[s]! (mulModQ z a0[s+len]!) := by
      rw [hb1def]; unfold bfStepC
      rw [getElem!_set!_ne _ s (s+len) _ (by omega),
          getElem!_set!_self _ (s+len) _ hsl256, hbs, hbsl]
    have hb1_other : ∀ p, p ≠ s → p ≠ s + len → b1[p]! = b[p]! := by
      intro p hps hpsl
      rw [hb1def]; unfold bfStepC
      rw [getElem!_set!_ne _ s p _ (by omega), getElem!_set!_ne _ (s+len) p _ (by omega)]
    have hrange : List.range' s (m'+1) = s :: List.range' (s+1) m' := by
      rw [List.range'_succ]
    have hagLo1 : ∀ p, s+1 ≤ p → p < s+1+m' → b1[p]! = a0[p]! := by
      intro p h1 h2
      rw [hb1_other p (by omega) (by omega)]
      exact hagLo p (by omega) (by omega)
    have hagHi1 : ∀ p, s+1+len ≤ p → p < s+1+m'+len → b1[p]! = a0[p]! := by
      intro p h1 h2
      rw [hb1_other p (by omega) (by omega)]
      exact hagHi p (by omega) (by omega)
    obtain ⟨ihsz, ihlo, ihhi, ihun⟩ :=
      ih (s+1) b1 hb1size (by omega) (by omega) hagLo1 hagHi1
    rw [hrange, List.foldl_cons, ← hb1def]
    refine ⟨ihsz, ?_, ?_, ?_⟩
    · intro p h1 h2
      by_cases hp : p = s
      · subst hp
        rw [ihun p (by omega) (by omega), hb1_s]
      · rw [ihlo p (by omega) (by omega)]
    · intro p h1 h2
      by_cases hp : p = s + len
      · subst hp
        rw [ihun (s+len) (by omega) (by omega), hb1_sl, Nat.add_sub_cancel]
      · rw [ihhi p (by omega) (by omega)]
    · intro p hlo hhi
      rw [ihun p (by omega) (by omega)]
      exact hb1_other p (by omega) (by omega)

/-- One full butterfly sweep over `[start, start+len)` — a VERBATIM copy of `ntt`'s innermost `for j` loop. -/
def bfSweep (z start len : Nat) (a0 : Poly) : Poly := Id.run do
  let mut a := a0
  for j in [start : start + len] do
    let t := mulModQ z a[j + len]!
    a := a.set! (j + len) (subQ a[j]! t)
    a := a.set! j (addQ a[j]! t)
  return a

theorem bfSweep_eq_foldl (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly) :
    bfSweep z start len a0 = List.foldl (bfStepC z len) a0 (List.range' start len) := by
  unfold bfSweep
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure]
  have hsize : [start:start+len].size = len := by
    simp only [Std.Legacy.Range.size]; omega
  rw [hsize]
  refine foldl_ext _ _ ?_ _ _
  intro b j
  unfold bfStepC
  congr 1
  rw [getElem!_set!_ne _ (j+len) j _ (by omega)]

theorem bfSweep_getElem (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly)
    (hsz : a0.size = 256) (hbound : start + 2 * len ≤ 256) :
    (∀ p, start ≤ p → p < start + len →
      (bfSweep z start len a0)[p]! = addQ a0[p]! (mulModQ z a0[p+len]!)) ∧
    (∀ p, start + len ≤ p → p < start + 2 * len →
      (bfSweep z start len a0)[p]! = subQ a0[p-len]! (mulModQ z a0[p]!)) ∧
    (∀ p, (p < start ∨ start + 2 * len ≤ p) →
      (bfSweep z start len a0)[p]! = a0[p]!) := by
  rw [bfSweep_eq_foldl z start len hlen a0]
  obtain ⟨_, hlo, hhi, hun⟩ :=
    bfFold_spec z len hlen a0 len start a0 hsz (by omega) (le_refl _)
      (fun p _ _ => rfl) (fun p _ _ => rfl)
  refine ⟨?_, ?_, ?_⟩
  · intro p h1 h2; exact hlo p h1 (by omega)
  · intro p h1 h2; exact hhi p (by omega) (by omega)
  · intro p h; apply hun p <;> omega

theorem cast_bfSweep (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly)
    (hsz : a0.size = 256) (hbound : start + 2 * len ≤ 256) :
    (∀ p, start ≤ p → p < start + len →
      ((bfSweep z start len a0)[p]! : ZMod q)
        = (a0[p]! : ZMod q) + (z : ZMod q) * (a0[p+len]! : ZMod q)) ∧
    (∀ p, start + len ≤ p → p < start + 2 * len →
      ((bfSweep z start len a0)[p]! : ZMod q)
        = (a0[p-len]! : ZMod q) - (z : ZMod q) * (a0[p]! : ZMod q)) := by
  obtain ⟨hlo, hhi, _⟩ := bfSweep_getElem z start len hlen a0 hsz hbound
  constructor
  · intro p h1 h2
    rw [hlo p h1 h2, cast_addQ, cast_mulModQ]
  · intro p h1 h2
    rw [hhi p h1 h2, cast_subQ _ _ (by have := mulModQ_lt z a0[p]!; omega), cast_mulModQ]

theorem bfSweep_size (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly) (h : a0.size = 256) :
    (bfSweep z start len a0).size = 256 := by
  rw [bfSweep_eq_foldl z start len hlen a0]
  suffices hgen : ∀ (L : List Nat) (b : Poly), b.size = 256 →
      (List.foldl (bfStepC z len) b L).size = 256 by exact hgen _ a0 h
  intro L
  induction L with
  | nil => intro b hb; simpa using hb
  | cons hd tl ih => intro b hb; simp only [List.foldl_cons]; exact ih _ (by rw [bfStepC_size]; exact hb)

theorem bfStepC_lt (z len : Nat) (b : Poly) (j : Nat) (hb : ∀ (p:Nat), b[p]! < q) :
    ∀ (p:Nat), (bfStepC z len b j)[p]! < q := by
  unfold bfStepC
  exact set!_lt _ _ _ (set!_lt _ _ _ hb (subQ_lt _ _)) (addQ_lt _ _)

theorem foldl_bfStepC_lt (z len : Nat) :
    ∀ (L : List Nat) (b : Poly), (∀ (p:Nat), b[p]!<q) →
      ∀ (p:Nat), (List.foldl (bfStepC z len) b L)[p]! < q := by
  intro L; induction L with
  | nil => intro b hb p; simpa using hb p
  | cons hd tl ih => intro b hb; exact ih _ (bfStepC_lt z len b hd hb)

theorem bfSweep_lt (z start len : Nat) (hlen : 1 ≤ len) (a0 : Poly) (h : ∀ (p:Nat), a0[p]!<q) :
    ∀ (p:Nat), (bfSweep z start len a0)[p]! < q := by
  rw [bfSweep_eq_foldl z start len hlen a0]; exact foldl_bfStepC_lt z len _ a0 h

/-! ## PART 1g — the SCHOOLBOOK (negacyclic) product coefficient formula. -/

def rowSweep (a b : Poly) (i : Nat) (c0 : Poly) : Poly := Id.run do
  let mut c := c0
  for j in [0:256] do
    let prod := mulModQ a[i]! b[j]!
    let k := i + j
    if k < 256 then c := c.set! k (addQ c[k]! prod)
    else c := c.set! (k - 256) (subQ c[k - 256]! prod)
  return c

def schoolbookCleanDo (a b : Poly) : Poly := Id.run do
  let mut c := zeroPoly
  for i in [0:256] do
    c := rowSweep a b i c
  return c

def RowStep (a b : Poly) (i : Nat) (c : Poly) (j : Nat) : Poly :=
  if i + j < 256 then c.set! (i+j) (addQ c[i+j]! (mulModQ a[i]! b[j]!))
  else c.set! (i+j-256) (subQ c[i+j-256]! (mulModQ a[i]! b[j]!))

/-- Signed `ℤ_q` contribution of coefficient pair `(i,j)` to output slot `m`. -/
def cJ (a b : Poly) (i j m : Nat) : ZMod q :=
  if i + j = m then ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q)
  else if i + j = m + 256 then -(((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q))
  else 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem sbk_clean (a b : Poly) : schoolbookMul a b = schoolbookCleanDo a b := by
  unfold schoolbookMul schoolbookCleanDo rowSweep; rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem rowSweep_fold (a b : Poly) (i : Nat) (c0 : Poly) :
    rowSweep a b i c0 = List.foldl (RowStep a b i) c0 (List.range' 0 256 1) := by
  unfold rowSweep RowStep
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8000 in
theorem forIn_zeroPoly_fold (f : Nat → Poly → Poly) :
    (Id.run do
      let mut c := zeroPoly
      for i in [0:256] do
        c := f i c
      return c)
      = List.foldl (fun c i => f i c) zeroPoly (List.range' 0 256 1) := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem sbk_outer (a b : Poly) :
    schoolbookCleanDo a b
      = List.foldl (fun c i => rowSweep a b i c) zeroPoly (List.range' 0 256 1) :=
  forIn_zeroPoly_fold (fun i c => rowSweep a b i c)

set_option maxRecDepth 8000 in
theorem rowAccum (a b : Poly) (i : Nat) (hi : i < 256) :
    ∀ (nj : Nat) (c : Poly), c.size = 256 →
      (List.foldl (RowStep a b i) c (List.range' 0 nj 1)).size = 256 ∧
      ∀ m, m < 256 →
        (((List.foldl (RowStep a b i) c (List.range' 0 nj 1))[m]! : Nat) : ZMod q)
          = ((c[m]! : Nat) : ZMod q) + ∑ j ∈ range nj, cJ a b i j m := by
  intro nj
  induction nj with
  | zero =>
    intro c hc; refine ⟨by simpa using hc, ?_⟩
    intro m hm
    simp only [List.range'_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ nj ih =>
    intro c hc
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    obtain ⟨ihsz, ihval⟩ := ih c hc
    set A := List.foldl (RowStep a b i) c (List.range' 0 nj 1) with hAdef
    have hstep : (RowStep a b i A nj).size = 256 := by
      unfold RowStep; by_cases hk : i + nj < 256
      · rw [if_pos hk, size_set!]; exact ihsz
      · rw [if_neg hk, size_set!]; exact ihsz
    refine ⟨hstep, ?_⟩
    intro m hm
    rw [Finset.sum_range_succ]
    unfold RowStep
    by_cases hk : i + nj < 256
    · rw [if_pos hk]
      by_cases hm2 : m = i + nj
      · subst hm2
        rw [getElem!_set!_self A (i+nj) _ (by rw [ihsz]; omega), cast_addQ, cast_mulModQ, ihval (i+nj) hm]
        have hcj : cJ a b i nj (i+nj) = ((a[i]! : Nat) : ZMod q) * ((b[nj]! : Nat) : ZMod q) := by
          unfold cJ; rw [if_pos rfl]
        rw [hcj]; ring
      · rw [getElem!_set!_ne A (i+nj) m _ (by omega), ihval m hm]
        have hcj : cJ a b i nj m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [hcj, add_zero]
    · rw [if_neg hk]
      by_cases hm2 : m = i + nj - 256
      · subst hm2
        rw [getElem!_set!_self A (i+nj-256) _ (by rw [ihsz]; omega),
            cast_subQ _ _ (by have := mulModQ_lt a[i]! b[nj]!; omega), cast_mulModQ, ihval _ hm]
        have hcj : cJ a b i nj (i+nj-256) = -(((a[i]! : Nat) : ZMod q) * ((b[nj]! : Nat) : ZMod q)) := by
          unfold cJ; rw [if_neg (by omega), if_pos (by omega)]
        rw [hcj]; ring
      · rw [getElem!_set!_ne A (i+nj-256) m _ (by omega), ihval m hm]
        have hcj : cJ a b i nj m = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [hcj, add_zero]

set_option maxRecDepth 8000 in
theorem outerAccum (a b : Poly) :
    ∀ (ni : Nat), ni ≤ 256 → ∀ (c : Poly), c.size = 256 →
      (List.foldl (fun c i => rowSweep a b i c) c (List.range' 0 ni 1)).size = 256 ∧
      ∀ m, m < 256 →
        (((List.foldl (fun c i => rowSweep a b i c) c (List.range' 0 ni 1))[m]! : Nat) : ZMod q)
          = ((c[m]! : Nat) : ZMod q) + ∑ i ∈ range ni, ∑ j ∈ range 256, cJ a b i j m := by
  intro ni
  induction ni with
  | zero => intro _ c hc; refine ⟨by simpa using hc, ?_⟩; intro m hm; simp
  | succ ni ih =>
    intro hni c hc
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    obtain ⟨ihsz, ihval⟩ := ih (by omega) c hc
    set A := List.foldl (fun c i => rowSweep a b i c) c (List.range' 0 ni 1) with hAdef
    obtain ⟨rssz, rsval⟩ := rowAccum a b ni (by omega) 256 A ihsz
    refine ⟨?_, ?_⟩
    · show (rowSweep a b ni A).size = 256
      rw [rowSweep_fold]; exact rssz
    · intro m hm
      rw [Finset.sum_range_succ]
      show (((rowSweep a b ni A)[m]! : Nat) : ZMod q) = _
      rw [rowSweep_fold, rsval m hm, ihval m hm]; ring

/-- **THE NEGACYCLIC COEFFICIENT FORMULA** (`ℤ_q`, from the imperative double loop). -/
theorem schoolbookMul_getElem (a b : Poly) (m : Nat) (hm : m < 256) :
    (((schoolbookMul a b)[m]! : Nat) : ZMod q)
      = ∑ i ∈ range 256, ∑ j ∈ range 256, cJ a b i j m := by
  rw [sbk_clean, sbk_outer]
  obtain ⟨_, hval⟩ := outerAccum a b 256 (le_refl _) zeroPoly (by simp [zeroPoly])
  rw [hval m hm, zeroPoly_cast, zero_add]

theorem schoolbookMul_size (a b : Poly) : (schoolbookMul a b).size = 256 := by
  rw [sbk_clean, sbk_outer]
  exact (outerAccum a b 256 (le_refl _) zeroPoly (by simp [zeroPoly])).1

theorem RowStep_lt (a b : Poly) (i : Nat) (c : Poly) (j : Nat) (hc : ∀ (p:Nat), c[p]!<q) :
    ∀ (p:Nat), (RowStep a b i c j)[p]! < q := by
  unfold RowStep; split
  · exact set!_lt _ _ _ hc (addQ_lt _ _)
  · exact set!_lt _ _ _ hc (subQ_lt _ _)

theorem foldl_RowStep_lt (a b : Poly) (i : Nat) :
    ∀ (L : List Nat) (c : Poly), (∀ (p:Nat), c[p]!<q) →
      ∀ (p:Nat), (List.foldl (RowStep a b i) c L)[p]!<q := by
  intro L; induction L with
  | nil => intro c hc p; simpa using hc p
  | cons hd tl ih => intro c hc; exact ih _ (RowStep_lt a b i c hd hc)

theorem rowSweep_lt (a b : Poly) (i : Nat) (c : Poly) (hc : ∀ (p:Nat), c[p]!<q) :
    ∀ (p:Nat), (rowSweep a b i c)[p]!<q := by
  rw [rowSweep_fold]; exact foldl_RowStep_lt a b i _ c hc

theorem foldl_outer_lt (a b : Poly) :
    ∀ (L : List Nat) (c : Poly), (∀ (p:Nat), c[p]!<q) →
      ∀ (p:Nat), (List.foldl (fun c i => rowSweep a b i c) c L)[p]!<q := by
  intro L; induction L with
  | nil => intro c hc p; simpa using hc p
  | cons hd tl ih => intro c hc; exact ih _ (rowSweep_lt a b hd c hc)

theorem schoolbookMul_lt (a b : Poly) : ∀ (p:Nat), (schoolbookMul a b)[p]!<q := by
  rw [sbk_clean, sbk_outer]
  exact foldl_outer_lt a b _ zeroPoly (fun p => by rw [zeroPoly_get p]; unfold q; omega)

/-! ## PART 2 — the peel `ntt = nttFold` (7 stages), the twiddle-in-field cast, and the CT stage invariant. -/

def nttCleanDo (w : Poly) : Poly := Id.run do
  let mut a := w
  let mut i := 1
  for s in [0:7] do
    let len := 128 >>> s
    let nblk := 128 / len
    for blk in [0:nblk] do
      let start := blk * 2 * len
      let z := zetaTwiddle i
      i := i + 1
      a := bfSweep z start len a
  return a

def nttFold (w : Poly) : Poly :=
  (List.foldl (fun (st : Poly × Nat) (s : Nat) =>
      List.foldl (fun (st2 : Poly × Nat) (blk : Nat) =>
          (bfSweep (zetaTwiddle st2.2) (blk * 2 * (128 >>> s)) (128 >>> s) st2.1, st2.2 + 1))
        st (List.range' 0 (128 / (128 >>> s)) 1))
    (w, 1) (List.range' 0 7 1)).1

set_option maxHeartbeats 800000 in
set_option maxRecDepth 8000 in
theorem do_eq_fold (w : Poly) : nttCleanDo w = nttFold w := by
  unfold nttCleanDo nttFold
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  refine Eq.trans ?_ (congrArg Prod.fst (foldl_ext_mem _ _ _ (fun st s _ => rfl) (w, 1)))
  rfl

theorem ntt_eq_fold (w : Poly) : ntt w = nttFold w := by
  rw [show ntt w = nttCleanDo w by unfold ntt nttCleanDo bfSweep; rfl, do_eq_fold]

/-! ### The twiddle cast — `zetaTwiddle k = ζ^{brv7 k}` in the field. -/

def pstep (st : Nat × Nat × Nat) (_ : Nat) : Nat × Nat × Nat :=
  (mulModQ st.1 st.1, st.2.1 / 2, if st.2.1 % 2 == 1 then mulModQ st.2.2 st.1 else st.2.2)

theorem powModQ_eq_fold (base e : Nat) :
    powModQ base e = (List.foldl pstep (base % q, e, 1) (List.range' 0 32 1)).2.2 := by
  unfold powModQ
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    ← apply_ite, List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

theorem pow_fold_inv (b0 ex0 : Nat) : ∀ (n res : Nat),
    (((List.range' 0 n 1).foldl pstep (b0, ex0, res)).2.2 : ZMod q)
        = (res : ZMod q) * (b0 : ZMod q) ^ (ex0 % 2 ^ n)
      ∧ (((List.range' 0 n 1).foldl pstep (b0, ex0, res)).1 : ZMod q) = (b0 : ZMod q) ^ (2 ^ n)
      ∧ (((List.range' 0 n 1).foldl pstep (b0, ex0, res)).2.1 = ex0 / 2 ^ n) := by
  intro n
  induction n with
  | zero => intro res; simp [Nat.mod_one]
  | succ n ih =>
    intro res
    rw [List.range'_1_concat, List.foldl_concat]
    obtain ⟨ih1, ih2, ih3⟩ := ih res
    set S := (List.range' 0 n 1).foldl pstep (b0, ex0, res) with hS
    have hpow : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
    have hmul : ex0 % 2 ^ (n + 1) = ex0 % 2 ^ n + 2 ^ n * (ex0 / 2 ^ n % 2) := by
      rw [hpow, Nat.mod_mul]
    unfold pstep
    refine ⟨?_, ?_, ?_⟩
    · by_cases hpar : (S.2.1 % 2 == 1) = true
      · rw [if_pos hpar]
        have hpar2 : S.2.1 % 2 = 1 := by simpa using hpar
        rw [cast_mulModQ, ih1, ih2]
        have hodd : ex0 / 2 ^ n % 2 = 1 := by rw [← ih3]; exact hpar2
        rw [hmul, hodd, mul_one, pow_add]; ring
      · rw [if_neg hpar, ih1]
        have hpar2 : S.2.1 % 2 = 0 := by
          have : ¬ S.2.1 % 2 = 1 := by simpa using hpar
          omega
        have heven : ex0 / 2 ^ n % 2 = 0 := by rw [← ih3]; exact hpar2
        rw [hmul, heven, mul_zero, add_zero]
    · rw [cast_mulModQ, ih2, ← pow_add, ← two_mul, ← pow_succ']
    · rw [ih3, Nat.div_div_eq_div_mul, ← pow_succ]

theorem cast_powModQ (base e : Nat) (he : e < 2 ^ 32) :
    ((powModQ base e : Nat) : ZMod q) = (base : ZMod q) ^ e := by
  rw [powModQ_eq_fold, (pow_fold_inv (base % q) e 32 1).1, Nat.mod_eq_of_lt he, Nat.cast_one,
      one_mul, ZMod.natCast_mod]

def brvStep (b : Nat × Nat) (_ : Nat) : Nat × Nat := (b.1 * 2 + b.2 % 2, b.2 / 2)

theorem brv7_eq_fold (k : Nat) : brv7 k = ((List.range' 0 7 1).foldl brvStep (0, k)).1 := by
  unfold brv7
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  rfl

theorem brv_fold_lt : ∀ (n x : Nat), ((List.range' 0 n 1).foldl brvStep (0, x)).1 < 2 ^ n := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [List.range'_1_concat, List.foldl_concat]
    have hih := ih x
    have hmod : ((List.range' 0 n 1).foldl brvStep (0, x)).2 % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hpow : (2 : Nat) ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
    set S := (List.range' 0 n 1).foldl brvStep (0, x) with hS
    unfold brvStep
    omega

theorem brv7_lt (k : Nat) : brv7 k < 128 := by
  rw [brv7_eq_fold]; have := brv_fold_lt 7 k; norm_num at this ⊢; omega

theorem cast_zetaTwiddle (k : Nat) :
    ((zetaTwiddle k : Nat) : ZMod q) = (zeta : ZMod q) ^ (brv7 k) := by
  unfold zetaTwiddle
  exact cast_powModQ zeta (brv7 k) (lt_of_lt_of_le (brv7_lt k) (by norm_num))

/-! ### The `brv7` congruences (order 256) and `rootAt` closed form. -/

set_option maxRecDepth 100000 in
theorem zeta_pow_neg_one : (zeta : ZMod q)^128 = -1 := by
  unfold zeta q; decide

theorem zeta_pow_add128 (e : Nat) : (zeta:ZMod q)^(e + 128) = -(zeta:ZMod q)^e := by
  rw [pow_add, zeta_pow_neg_one]; ring

set_option maxRecDepth 4000 in
theorem brv_even7 (n : Nat) (hn : n < 64) : 2 * brv7 (2*n) = brv7 n := by
  simp only [brv7_eq_fold]; revert hn; revert n; decide

set_option maxRecDepth 4000 in
theorem brv_odd7 (n : Nat) (hn : n < 64) : 2 * brv7 (2*n+1) = brv7 n + 128 := by
  simp only [brv7_eq_fold]; revert hn; revert n; decide

set_option maxRecDepth 4000 in
theorem brv_high7 (n : Nat) (hn : n < 64) : brv7 (64 + n) = brv7 n + 1 := by
  simp only [brv7_eq_fold]; revert hn; revert n; decide

theorem sum_range_two_mul {M} [AddCommMonoid M] (f : Nat → M) (n : Nat) :
    ∑ u ∈ range (2*n), f u = ∑ v ∈ range n, f (2*v) + ∑ v ∈ range n, f (2*v+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 from by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, Finset.sum_range_succ]
    abel

/-- The 128 negacyclic quadratic-factor roots `γ_g = ζ^{2·brv7(g)+1}` (the `X²−γ_g` moduli). -/
def evalRoot (m : Nat) : ZMod q := (zeta : ZMod q)^(2 * brv7 m + 1)

theorem evalRoot_pow128 (m : Nat) : (evalRoot m)^128 = -1 := by
  unfold evalRoot
  rw [← pow_mul]
  have : (2 * brv7 m + 1) * 128 = 128 * (2*brv7 m) + 128 := by ring
  rw [this, pow_add, pow_mul, zeta_pow_neg_one]
  rw [show ((-1:ZMod q))^(2*brv7 m) = 1 by rw [pow_mul]; simp]
  ring

/-- The root a slot's segment is being evaluated at, after `s` code stages, segment `g`. -/
def rootAt (s g : Nat) : ZMod q :=
  match s with
  | 0 => (zeta:ZMod q)^(2*brv7 (1+g))
  | s+1 => (if g % 2 = 0 then (1:ZMod q) else -1) * (zeta:ZMod q)^(brv7 (2^s + g/2))

theorem rootAt_even_step (s blk : Nat) :
    rootAt (s+1) (2*blk) = (zeta:ZMod q)^(brv7 (2^s + blk)) := by
  simp [rootAt, Nat.mul_mod_right]

theorem rootAt_odd_step (s blk : Nat) :
    rootAt (s+1) (2*blk+1) = -(zeta:ZMod q)^(brv7 (2^s + blk)) := by
  have h1 : (2*blk+1) % 2 = 1 := by omega
  have h2 : (2*blk+1) / 2 = blk := by omega
  simp [rootAt, h1, h2]

/-- `rootAt s g = ζ^{2·brv7(2^s+g)}` for the input levels `s ≤ 6`, `g < 2^s`. -/
theorem rootAt_closed (s g : Nat) (hs : s ≤ 6) (hg : g < 2^s) :
    rootAt s g = (zeta:ZMod q)^(2 * brv7 (2^s + g)) := by
  match s with
  | 0 => simp [rootAt, pow_zero]
  | s+1 =>
    rcases Nat.even_or_odd g with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hc' : g = 2 * c := by omega
      subst hc'
      have hclt : c < 2^s := by
        have h2 : 2^(s+1) = 2^s + 2^s := by rw [pow_succ]; ring
        omega
      have hc64 : 2^s + c < 64 := by
        have hpow : 2^s ≤ 2^5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2^5 = 32 := by norm_num
        omega
      rw [rootAt_even_step]
      have := brv_even7 (2^s + c) hc64
      have hh : 2^(s+1) + 2*c = 2*(2^s+c) := by rw [pow_succ]; ring
      rw [hh, ← this]
    · subst hc
      have hclt : c < 2^s := by
        have h2 : 2^(s+1) = 2^s + 2^s := by rw [pow_succ]; ring
        omega
      have hc64 : 2^s + c < 64 := by
        have hpow : 2^s ≤ 2^5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        have : 2^5 = 32 := by norm_num
        omega
      rw [rootAt_odd_step]
      have := brv_odd7 (2^s + c) hc64
      have hh : 2^(s+1) + (2*c+1) = 2*(2^s+c)+1 := by rw [pow_succ]; ring
      rw [hh, this, zeta_pow_add128]

/-- At the final level `s = 7`, `rootAt 7 m = evalRoot m = ζ^{2·brv7(m)+1}`. -/
theorem rootAt_final (m : Nat) (hm : m < 128) : rootAt 7 m = evalRoot m := by
  unfold evalRoot
  rcases Nat.even_or_odd m with ⟨blk, hb⟩ | ⟨blk, hb⟩
  · have hb' : m = 2 * blk := by omega
    subst hb'
    have hblk : blk < 64 := by omega
    rw [show (7:Nat) = 6+1 from rfl, rootAt_even_step]
    have hp : (2:Nat)^6 = 64 := by norm_num
    rw [hp, brv_high7 blk hblk, brv_even7 blk hblk]
  · subst hb
    have hblk : blk < 64 := by omega
    rw [show (7:Nat) = 6+1 from rfl, rootAt_odd_step]
    have hp : (2:Nat)^6 = 64 := by norm_num
    rw [hp, brv_high7 blk hblk]
    have ho := brv_odd7 blk hblk
    rw [ho]
    rw [show brv7 blk + 128 + 1 = (brv7 blk + 1) + 128 from by ring, zeta_pow_add128]

/-! ### numeric helpers + the fold structure (`nttUpto`) + `block_char` + `stage_inv`. -/

theorem shr_pow (s : Nat) (hs : s ≤ 8) : 256 >>> s = 2^(8-s) := by
  rw [Nat.shiftRight_eq_div_pow, show (256:Nat) = 2^8 from rfl, Nat.pow_div hs (by norm_num)]
theorem shl_pow (s : Nat) (hs : s ≤ 7) : 128 >>> s = 2^(7-s) := by
  rw [Nat.shiftRight_eq_div_pow, show (128:Nat) = 2^7 from rfl, Nat.pow_div hs (by norm_num)]
theorem len_pos (s : Nat) (hs : s ≤ 7) : 1 ≤ 128 >>> s := by
  rw [shl_pow s hs]; exact Nat.one_le_two_pow
theorem L_eq_2len (s : Nat) (hs : s ≤ 7) : 256 >>> s = 2 * (128 >>> s) := by
  rw [shr_pow s (by omega), shl_pow s hs, ← pow_succ']
  congr 1; omega
theorem seg_total (s : Nat) (hs : s ≤ 8) : 2^s * (256 >>> s) = 256 := by
  rw [shr_pow s hs, ← pow_add, show s + (8-s) = 8 from by omega]; norm_num
theorem nblk_pow (n : Nat) (hn : n ≤ 7) : 128 / (128 >>> n) = 2^n := by
  rw [shl_pow n hn, show (128:Nat) = 2^7 from rfl, Nat.pow_div (by omega) (by norm_num)]
  congr 1; omega
theorem shr_succ (n : Nat) (hn : n ≤ 7) : 256 >>> (n+1) = 128 >>> n := by
  rw [shr_pow (n+1) (by omega), shl_pow n hn]; congr 1; omega

def blockFn (s : Nat) (st2 : Poly × Nat) (blk : Nat) : Poly × Nat :=
  (bfSweep (zetaTwiddle st2.2) (blk * 2 * (128 >>> s)) (128 >>> s) st2.1, st2.2 + 1)

def stageStep (s : Nat) (st : Poly × Nat) : Poly × Nat :=
  List.foldl (blockFn s) st (List.range' 0 (128 / (128 >>> s)) 1)

def nttUpto (n : Nat) (w : Poly) : Poly × Nat :=
  List.foldl (fun st s => stageStep s st) (w, 1) (List.range' 0 n 1)

theorem nttFold_eq (w : Poly) : nttFold w = (nttUpto 7 w).1 := by
  unfold nttFold nttUpto stageStep blockFn; rfl

theorem nttUpto_succ (n : Nat) (w : Poly) : nttUpto (n+1) w = stageStep n (nttUpto n w) := by
  unfold nttUpto
  rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]

theorem foldl_blockFn_snd (s : Nat) (l : List Nat) (st : Poly × Nat) :
    (List.foldl (blockFn s) st l).2 = st.2 + l.length := by
  induction l generalizing st with
  | nil => simp
  | cons hd tl ih => simp only [List.foldl_cons]; rw [ih]; simp [blockFn]; omega

set_option maxHeartbeats 1000000 in
/-- **Inner block-fold characterization** (one full CT stage, positionwise, Nat-level; twiddle `c0+blk`). -/
theorem block_char (s : Nat) (hs : s ≤ 6) (a_in : Poly) (hsz : a_in.size = 256) (c0 : Nat) :
    ∀ nb, nb ≤ 2^s →
      ((List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1.size = 256) ∧
      (∀ p, nb * (256>>>s) ≤ p → p < 256 →
          (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1[p]! = a_in[p]!) ∧
      (∀ blk, blk < nb → ∀ p, blk*(256>>>s) ≤ p → p < blk*(256>>>s)+(128>>>s) →
          (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1[p]!
            = addQ a_in[p]! (mulModQ (zetaTwiddle (c0+blk)) a_in[p+(128>>>s)]!)) ∧
      (∀ blk, blk < nb → ∀ p, blk*(256>>>s)+(128>>>s) ≤ p → p < blk*(256>>>s)+(256>>>s) →
          (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1[p]!
            = subQ a_in[p-(128>>>s)]! (mulModQ (zetaTwiddle (c0+blk)) a_in[p]!)) := by
  set len := 128 >>> s with hlendef
  set L := 256 >>> s with hLdef
  have hlen1 : 1 ≤ len := len_pos s (by omega)
  have hL2 : L = 2 * len := L_eq_2len s (by omega)
  have hLtot : 2^s * L = 256 := seg_total s (by omega)
  have hmono : ∀ i j : Nat, i ≤ j → i * L ≤ j * L := fun i j h => Nat.mul_le_mul_right _ h
  intro nb
  induction nb with
  | zero =>
    intro _; refine ⟨by simpa using hsz, ?_, ?_, ?_⟩
    · intro p _ _; simp
    · intro blk hblk; omega
    · intro blk hblk; omega
  | succ nb ih =>
    intro hnb
    have hnb' : nb ≤ 2^s := by omega
    obtain ⟨ihsz, ihun, ihlo, ihhi⟩ := ih hnb'
    have hcnt : (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).2 = c0 + nb := by
      rw [foldl_blockFn_snd]; simp
    set A := (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1 with hAdef
    have hstart : nb * 2 * len = nb * L := by rw [hL2]; ring
    have hAeq : (List.foldl (blockFn s) (a_in, c0) (List.range' 0 (nb+1) 1)).1
        = bfSweep (zetaTwiddle (c0+nb)) (nb * L) len A := by
      rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
      have hbf1 : (blockFn s (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)) nb).1
          = bfSweep (zetaTwiddle ((List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).2))
              (nb * 2 * len) len (List.foldl (blockFn s) (a_in, c0) (List.range' 0 nb 1)).1 := rfl
      rw [hbf1, hcnt, ← hAdef, hstart]
    set z := zetaTwiddle (c0+nb) with hzdef
    have hnbL : nb * L + L ≤ 256 := by
      have h1 := hmono (nb+1) (2^s) (by omega)
      have h2 : (nb+1) * L = nb * L + L := by ring
      rw [hLtot] at h1; omega
    have hbound : nb * L + 2 * len ≤ 256 := by rw [← hL2]; exact hnbL
    obtain ⟨hlo, hhi, hunt⟩ := bfSweep_getElem z (nb*L) len hlen1 A (by rw [hAdef]; exact ihsz) hbound
    have hApsize : (List.foldl (blockFn s) (a_in, c0) (List.range' 0 (nb+1) 1)).1.size = 256 := by
      rw [hAeq]; exact bfSweep_size z (nb*L) len hlen1 A (by rw [hAdef]; exact ihsz)
    refine ⟨hApsize, ?_, ?_, ?_⟩
    · intro p hp1 hp2
      rw [hAeq]
      have hpge : nb * L + 2 * len ≤ p := by
        have hh : (nb+1) * L = nb * L + L := by ring
        rw [← hL2]; omega
      rw [hunt p (Or.inr hpge), hAdef]
      exact ihun p (by omega) hp2
    · intro blk hblk p hp1 hp2
      rw [hAeq]
      rcases Nat.lt_or_ge blk nb with hlt | hge
      · have hpltnbL : p < nb * L := by
          have h1 : (blk+1) * L ≤ nb * L := hmono (blk+1) nb (by omega)
          have h3 : (blk+1)*L = blk*L + L := by ring
          omega
        rw [hunt p (Or.inl hpltnbL), hAdef]
        exact ihlo blk hlt p hp1 hp2
      · have hblkeq : blk = nb := by omega
        subst blk
        rw [hlo p (by omega) (by omega)]
        have hAp : A[p]! = a_in[p]! := by rw [hAdef]; exact ihun p (by omega) (by omega)
        have hAplen : A[p+len]! = a_in[p+len]! := by
          rw [hAdef]; exact ihun (p+len) (by omega) (by omega)
        rw [hAp, hAplen]
    · intro blk hblk p hp1 hp2
      rw [hAeq]
      rcases Nat.lt_or_ge blk nb with hlt | hge
      · have hpltnbL : p < nb * L := by
          have h1 : (blk+1) * L ≤ nb * L := hmono (blk+1) nb (by omega)
          have h3 : (blk+1)*L = blk*L + L := by ring
          omega
        rw [hunt p (Or.inl hpltnbL), hAdef]
        exact ihhi blk hlt p hp1 hp2
      · have hblkeq : blk = nb := by omega
        subst blk
        have hp2' : p < nb * L + 2 * len := by rw [← hL2]; omega
        rw [hhi p (by omega) hp2']
        have hAplen : A[p-len]! = a_in[p-len]! := by
          rw [hAdef]; exact ihun (p-len) (by omega) (by omega)
        have hAp : A[p]! = a_in[p]! := by rw [hAdef]; exact ihun p (by omega) (by omega)
        rw [hAplen, hAp]

theorem split_collapse (len Lval nn i' : Nat) (hL : Lval = 2*len) (r : ZMod q) (w : Poly) :
    ∑ u ∈ range (2*2^nn), (w[i'+u*len]! : ZMod q) * r^u
      = (∑ v ∈ range (2^nn), (w[i'+v*Lval]! : ZMod q) * (r^2)^v)
        + r * (∑ v ∈ range (2^nn), (w[i'+len+v*Lval]! : ZMod q) * (r^2)^v) := by
  rw [sum_range_two_mul]
  congr 1
  · apply Finset.sum_congr rfl; intro v _
    rw [show i' + 2*v*len = i' + v*Lval from by rw [hL]; ring, pow_mul]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro v _
    rw [show i' + (2*v+1)*len = i' + len + v*Lval from by rw [hL]; ring,
        show r^(2*v+1) = r*(r^2)^v from by rw [pow_succ, ← pow_mul]; ring]
    ring

set_option maxHeartbeats 2000000 in
/-- **THE CT STAGE INVARIANT.** After `n` code stages (`n ≤ 7`), array slot `g·L_n+i` holds the `ℤ_q`-eval of
the `g`-th decimated subsequence at its root `rootAt n g`. Counter component `= 2^n`. -/
theorem stage_inv (w : Poly) (hw : w.size = 256) :
    ∀ n, n ≤ 7 →
      (nttUpto n w).1.size = 256 ∧
      (nttUpto n w).2 = 2^n ∧
      ∀ g i, g < 2^n → i < 256 >>> n →
        ((nttUpto n w).1[g * (256 >>> n) + i]! : ZMod q)
          = ∑ u ∈ range (2^n), (w[i + u * (256 >>> n)]! : ZMod q) * (rootAt n g)^u := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨by simpa [nttUpto] using hw, by simp [nttUpto], ?_⟩
    intro g i hg hi
    have hg0 : g = 0 := by omega
    subst hg0
    simp only [nttUpto, List.range'_zero, List.foldl_nil, pow_zero, Nat.zero_mul, Nat.zero_add,
      range_one, Finset.sum_singleton, Nat.add_zero, pow_zero, mul_one]
  | succ n ih =>
    intro hn1
    have hn6 : n ≤ 6 := by omega
    obtain ⟨ihsz, ihcnt, ihform⟩ := ih (by omega)
    set len := 128 >>> n with hlendef
    have hL2 : (256 >>> n) = 2 * len := L_eq_2len n (by omega)
    have hLn1 : (256 >>> (n+1)) = len := shr_succ n (by omega)
    have hpow2 : (2:Nat)^(n+1) = 2 * 2^n := by rw [pow_succ]; ring
    have hpowpos : 1 ≤ 2^n := Nat.one_le_two_pow
    have hstage : nttUpto (n+1) w = List.foldl (blockFn n) (nttUpto n w) (List.range' 0 (2^n) 1) := by
      rw [nttUpto_succ]; unfold stageStep; rw [nblk_pow n (by omega)]
    set a_in := (nttUpto n w).1 with haindef
    have hain_c : (nttUpto n w).2 = 2^n := ihcnt
    obtain ⟨bsz, bun, blo, bhi⟩ :=
      block_char n hn6 a_in ihsz (nttUpto n w).2 (2^n) (le_refl _)
    have hpair : (nttUpto n w) = (a_in, (nttUpto n w).2) := by rw [haindef]
    rw [hpair] at hstage
    have htw : ∀ blk, (nttUpto n w).2 + blk = 2^n + blk := by
      intro blk; rw [hain_c]
    refine ⟨?_, ?_, ?_⟩
    · rw [hstage]; exact bsz
    · rw [nttUpto_succ]; unfold stageStep
      rw [nblk_pow n (by omega), foldl_blockFn_snd, hain_c]
      have : (List.range' 0 (2^n) 1).length = 2^n := by simp
      rw [this]; omega
    · intro g i hg hi
      rw [hLn1] at hi ⊢
      rcases Nat.even_or_odd g with ⟨blk, hgb⟩ | ⟨blk, hgb⟩
      · have hgb' : g = 2 * blk := by omega
        subst hgb'
        have hblk : blk < 2^n := by
          have := hg; rw [hpow2] at this; omega
        have hpos : 2*blk*len + i = blk*(256>>>n) + i := by rw [hL2]; ring
        rw [hpos]
        have hp1 : blk*(256>>>n) ≤ blk*(256>>>n)+i := by omega
        have hp2 : blk*(256>>>n)+i < blk*(256>>>n)+len := by omega
        rw [hstage, blo blk hblk (blk*(256>>>n)+i) hp1 hp2]
        rw [cast_addQ, cast_mulModQ, htw blk, cast_zetaTwiddle]
        have e1 : (a_in[blk*(256>>>n)+i]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[i + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          have := ihform blk i hblk (by rw [hL2]; omega); rw [haindef]; exact this
        have e2 : (a_in[blk*(256>>>n)+i+len]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[(i+len) + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          have := ihform blk (i+len) hblk (by rw [hL2]; omega)
          rw [haindef]
          rw [show blk*(256>>>n)+i+len = blk*(256>>>n)+(i+len) from by ring]
          exact this
        rw [e1, e2]
        have hr : rootAt (n+1) (2*blk) = (zeta:ZMod q)^(brv7 (2^n+blk)) := rootAt_even_step n blk
        have hrho : rootAt n blk = ((zeta:ZMod q)^(brv7 (2^n+blk)))^2 := by
          rw [rootAt_closed n blk hn6 hblk, ← pow_mul]; ring_nf
        rw [hr, hpow2, split_collapse len (256>>>n) n i hL2 _ w, ← hrho]
      · subst hgb
        have hblk : blk < 2^n := by
          have := hg; rw [hpow2] at this; omega
        have hpos : (2*blk+1)*len + i = blk*(256>>>n)+len+i := by rw [hL2]; ring
        rw [hpos]
        have hp1 : blk*(256>>>n)+len ≤ blk*(256>>>n)+len+i := by omega
        have hp2 : blk*(256>>>n)+len+i < blk*(256>>>n)+(256>>>n) := by rw [hL2]; omega
        rw [hstage, bhi blk hblk (blk*(256>>>n)+len+i) hp1 hp2]
        rw [cast_subQ _ _ (by have := mulModQ_lt (zetaTwiddle ((nttUpto n w).2 + blk)) a_in[blk*(256>>>n)+len+i]!; omega),
            cast_mulModQ, htw blk, cast_zetaTwiddle]
        have e1 : (a_in[blk*(256>>>n)+len+i-len]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[i + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          rw [show blk*(256>>>n)+len+i-len = blk*(256>>>n)+i from by omega]
          have := ihform blk i hblk (by rw [hL2]; omega); rw [haindef]; exact this
        have e2 : (a_in[blk*(256>>>n)+len+i]! : ZMod q)
            = ∑ v ∈ range (2^n), (w[(i+len) + v*(256>>>n)]! : ZMod q) * (rootAt n blk)^v := by
          have := ihform blk (i+len) hblk (by rw [hL2]; omega)
          rw [haindef, show blk*(256>>>n)+len+i = blk*(256>>>n)+(i+len) from by ring]
          exact this
        rw [e1, e2]
        have hr : rootAt (n+1) (2*blk+1) = -(zeta:ZMod q)^(brv7 (2^n+blk)) := rootAt_odd_step n blk
        have hrho : rootAt n blk = (-(zeta:ZMod q)^(brv7 (2^n+blk)))^2 := by
          rw [rootAt_closed n blk hn6 hblk, neg_pow, ← pow_mul]; ring_nf
        rw [hr, hpow2, split_collapse len (256>>>n) n i hL2 _ w, ← hrho]
        ring

/-! ## PART 3 — the incomplete-NTT reduces to the QUADRATIC QUOTIENTS. -/

/-- Even/odd half-evaluations: the two coefficients of `w mod (X²−γ)`. -/
def evEven (a : Poly) (γ : ZMod q) : ZMod q := ∑ u ∈ range 128, (a[2*u]! : ZMod q) * γ^u
def evOdd  (a : Poly) (γ : ZMod q) : ZMod q := ∑ u ∈ range 128, (a[2*u+1]! : ZMod q) * γ^u

/-- **CT STAGE-INVARIANT COLLAPSE (size-256).** After 7 stages the pair-slot `(2g, 2g+i)` holds the reduction
of `a` mod its quadratic factor `X²−γ_g`: `(ntt a)[2g+i]! = Σ_{u<128} a[i+2u]·γ_g^u`. -/
theorem ntt_reduces_to_quotients (a : Poly) (ha : a.size = 256) (g : Nat) (hg : g < 128)
    (i : Nat) (hi : i < 2) :
    ((ntt a)[2*g+i]! : ZMod q) = ∑ u ∈ range 128, (a[i + u*2]! : ZMod q) * (evalRoot g)^u := by
  obtain ⟨_, _, hform⟩ := stage_inv a ha 7 (by omega)
  have hg8 : g < 2^7 := by rw [show (2:Nat)^7 = 128 from by norm_num]; exact hg
  have h := hform g i hg8 (by rw [show (256 >>> 7) = 2 from by decide]; exact hi)
  rw [show (256 >>> 7) = 2 from by decide, show (2:Nat)^7 = 128 from by norm_num] at h
  rw [ntt_eq_fold, nttFold_eq]
  rw [show 2*g+i = g*2+i from by ring, h, rootAt_final g hg]

theorem ntt_even (a : Poly) (ha : a.size = 256) (g : Nat) (hg : g < 128) :
    ((ntt a)[2*g]! : ZMod q) = evEven a (evalRoot g) := by
  have h := ntt_reduces_to_quotients a ha g hg 0 (by omega)
  rw [show 2*g+0 = 2*g from by ring] at h
  rw [h]; unfold evEven
  apply Finset.sum_congr rfl; intro u _
  rw [show 0 + u*2 = 2*u from by ring]

theorem ntt_odd (a : Poly) (ha : a.size = 256) (g : Nat) (hg : g < 128) :
    ((ntt a)[2*g+1]! : ZMod q) = evOdd a (evalRoot g) := by
  have h := ntt_reduces_to_quotients a ha g hg 1 (by omega)
  rw [h]; unfold evOdd
  apply Finset.sum_congr rfl; intro u _
  rw [show 1 + u*2 = 2*u+1 from by ring]

/-! ## PART 4 (RUNG 5) — the QUADRATIC base-case multiplicativity (the NOVEL incomplete-NTT content).

`baseCaseMultiply` is the product in `ℤ_q[X]/(X²−γ)`; the pair-reduction `(evEven, evOdd)` of the negacyclic
product IS that product of the pair-reductions, when `γ¹²⁸ = −1`. Proven by the negacyclic convolution split by
index-parity (the incomplete-NTT analog of the ML-DSA scalar `eval256_schoolbook`). -/

theorem gamma_pow_add128 (γ : ZMod q) (hγ : γ^128 = -1) (e : Nat) : γ^(e+128) = -γ^e := by
  rw [pow_add, hγ]; ring

/-- Contribution of pair `(i,j)` to the EVEN half-eval: `Σ_w cJ(i,j,2w)·γ^w = a_i b_j γ^{(i+j)/2}` if `i+j`
even, else `0` (the wrap `X²⁵⁶=−1` absorbed by `γ¹²⁸=−1`). -/
theorem inner_even (a b : Poly) (γ : ZMod q) (hγ : γ^128 = -1) (i j : Nat)
    (hi : i < 256) (hj : j < 256) :
    ∑ w ∈ range 128, cJ a b i j (2*w) * γ^w
      = if (i+j) % 2 = 0 then ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q) * γ^((i+j)/2) else 0 := by
  by_cases hpar : (i+j) % 2 = 0
  · rw [if_pos hpar]
    by_cases hk : i + j < 256
    · set w0 := (i+j)/2 with hw0
      have hw0lt : w0 < 128 := by omega
      have h2w0 : 2 * w0 = i + j := by omega
      rw [Finset.sum_eq_single w0]
      · have : cJ a b i j (2*w0) = ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q) := by
          unfold cJ; rw [h2w0, if_pos rfl]
        rw [this]
      · intro w hwmem hw
        have hwlt : w < 128 := mem_range.mp hwmem
        have : cJ a b i j (2*w) = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [this, zero_mul]
      · intro hmem; exact absurd (mem_range.mpr hw0lt) hmem
    · have hge : 256 ≤ i + j := by omega
      set w0 := (i+j-256)/2 with hw0
      have hw0lt : w0 < 128 := by omega
      have h2w0 : 2 * w0 = i + j - 256 := by omega
      have hw0e : w0 + 128 = (i+j)/2 := by omega
      rw [Finset.sum_eq_single w0]
      · have hcj : cJ a b i j (2*w0) = -(((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q)) := by
          unfold cJ; rw [if_neg (by omega), if_pos (by omega)]
        rw [hcj, ← hw0e, gamma_pow_add128 γ hγ w0]; ring
      · intro w hwmem hw
        have hwlt : w < 128 := mem_range.mp hwmem
        have : cJ a b i j (2*w) = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [this, zero_mul]
      · intro hmem; exact absurd (mem_range.mpr hw0lt) hmem
  · rw [if_neg hpar]
    apply Finset.sum_eq_zero
    intro w hwmem
    have : cJ a b i j (2*w) = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
    rw [this, zero_mul]

/-- Contribution of pair `(i,j)` to the ODD half-eval. -/
theorem inner_odd (a b : Poly) (γ : ZMod q) (hγ : γ^128 = -1) (i j : Nat)
    (hi : i < 256) (hj : j < 256) :
    ∑ w ∈ range 128, cJ a b i j (2*w+1) * γ^w
      = if (i+j) % 2 = 1 then ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q) * γ^((i+j)/2) else 0 := by
  by_cases hpar : (i+j) % 2 = 1
  · rw [if_pos hpar]
    by_cases hk : i + j < 256
    · set w0 := (i+j)/2 with hw0
      have hw0lt : w0 < 128 := by omega
      have h2w0 : 2 * w0 + 1 = i + j := by omega
      rw [Finset.sum_eq_single w0]
      · have : cJ a b i j (2*w0+1) = ((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q) := by
          unfold cJ; rw [h2w0, if_pos rfl]
        rw [this]
      · intro w hwmem hw
        have hwlt : w < 128 := mem_range.mp hwmem
        have : cJ a b i j (2*w+1) = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [this, zero_mul]
      · intro hmem; exact absurd (mem_range.mpr hw0lt) hmem
    · have hge : 256 ≤ i + j := by omega
      set w0 := (i+j-256)/2 with hw0
      have hw0lt : w0 < 128 := by omega
      have h2w0 : 2 * w0 + 1 = i + j - 256 := by omega
      have hw0e : w0 + 128 = (i+j)/2 := by omega
      rw [Finset.sum_eq_single w0]
      · have hcj : cJ a b i j (2*w0+1) = -(((a[i]! : Nat) : ZMod q) * ((b[j]! : Nat) : ZMod q)) := by
          unfold cJ; rw [if_neg (by omega), if_pos (by omega)]
        rw [hcj, ← hw0e, gamma_pow_add128 γ hγ w0]; ring
      · intro w hwmem hw
        have hwlt : w < 128 := mem_range.mp hwmem
        have : cJ a b i j (2*w+1) = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
        rw [this, zero_mul]
      · intro hmem; exact absurd (mem_range.mpr hw0lt) hmem
  · rw [if_neg hpar]
    apply Finset.sum_eq_zero
    intro w hwmem
    have : cJ a b i j (2*w+1) = 0 := by unfold cJ; rw [if_neg (by omega), if_neg (by omega)]
    rw [this, zero_mul]

/-- Split a `range 256 × range 256` double sum into the four index-parity classes (`2u/2u+1`, `2v/2v+1`). -/
theorem sum2_parity (F : Nat → Nat → ZMod q) :
    ∑ i ∈ range 256, ∑ j ∈ range 256, F i j
      = ∑ u ∈ range 128, ∑ v ∈ range 128,
          (F (2*u) (2*v) + F (2*u) (2*v+1) + F (2*u+1) (2*v) + F (2*u+1) (2*v+1)) := by
  rw [show (256:Nat) = 2*128 from rfl, sum_range_two_mul (fun i => ∑ j ∈ range (2*128), F i j) 128]
  rw [Finset.sum_congr rfl (fun u _ => sum_range_two_mul (fun j => F (2*u) j) 128),
      Finset.sum_congr rfl (fun u _ => sum_range_two_mul (fun j => F (2*u+1) j) 128)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]; ring

/-- The LHS triple-sum form of an even/odd half-eval of `schoolbookMul` (parity `r ∈ {0,1}` picks the slot). -/
theorem half_eval_triple (a b : Poly) (γ : ZMod q) (r : Nat) (hr : r < 2) :
    (∑ u ∈ range 128, ((schoolbookMul a b)[2*u+r]! : ZMod q) * γ^u)
      = ∑ i ∈ range 256, ∑ j ∈ range 256, ∑ w ∈ range 128, cJ a b i j (2*w+r) * γ^w := by
  rw [Finset.sum_congr rfl (fun u hu => by
    rw [schoolbookMul_getElem a b (2*u+r) (by have := mem_range.mp hu; omega), Finset.sum_mul,
        Finset.sum_congr rfl (fun i _ => Finset.sum_mul _ _ _)])]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.sum_comm]

/-- Convert a double sum of products into the product of sums (the `∑∑ (fᵤ·gᵥ) = (∑f)(∑g)` collapse). -/
theorem double_to_product (f g : Nat → ZMod q) :
    (∑ u ∈ range 128, ∑ v ∈ range 128, f u * g v) = (∑ u ∈ range 128, f u) * (∑ v ∈ range 128, g v) := by
  rw [Finset.sum_mul_sum]

/-- **EVEN half-eval is a quadratic-quotient ring hom**: `evEven (a·b) γ = evEven a·evEven b + γ·evOdd a·evOdd b`
when `γ¹²⁸ = −1`. The `c₀` component of `baseCaseMultiply`. -/
theorem evEven_schoolbook (a b : Poly) (γ : ZMod q) (hγ : γ^128 = -1) :
    evEven (schoolbookMul a b) γ = evEven a γ * evEven b γ + γ * (evOdd a γ * evOdd b γ) := by
  unfold evEven evOdd
  have h0 : (∑ u ∈ range 128, ((schoolbookMul a b)[2*u]! : ZMod q) * γ^u)
      = ∑ u ∈ range 128, ((schoolbookMul a b)[2*u+0]! : ZMod q) * γ^u := by simp
  rw [h0, half_eval_triple a b γ 0 (by omega)]
  simp only [Nat.add_zero]
  rw [sum2_parity (fun i j => ∑ w ∈ range 128, cJ a b i j (2*w) * γ^w)]
  have hcollapse : ∀ u ∈ range 128, (∑ v ∈ range 128,
        ((∑ w ∈ range 128, cJ a b (2*u) (2*v) (2*w) * γ^w)
          + (∑ w ∈ range 128, cJ a b (2*u) (2*v+1) (2*w) * γ^w)
          + (∑ w ∈ range 128, cJ a b (2*u+1) (2*v) (2*w) * γ^w)
          + (∑ w ∈ range 128, cJ a b (2*u+1) (2*v+1) (2*w) * γ^w)))
      = ∑ v ∈ range 128,
          (((a[2*u]! : Nat) : ZMod q) * γ^u * (((b[2*v]! : Nat) : ZMod q) * γ^v)
            + γ * (((a[2*u+1]! : Nat) : ZMod q) * γ^u * (((b[2*v+1]! : Nat) : ZMod q) * γ^v))) := by
    intro u hu; apply Finset.sum_congr rfl; intro v hv
    have hu128 : u < 128 := mem_range.mp hu
    have hv128 : v < 128 := mem_range.mp hv
    rw [inner_even a b γ hγ (2*u) (2*v) (by omega) (by omega),
        inner_even a b γ hγ (2*u) (2*v+1) (by omega) (by omega),
        inner_even a b γ hγ (2*u+1) (2*v) (by omega) (by omega),
        inner_even a b γ hγ (2*u+1) (2*v+1) (by omega) (by omega),
        if_pos (show (2*u+2*v)%2 = 0 by omega), if_neg (show ¬(2*u+(2*v+1))%2 = 0 by omega),
        if_neg (show ¬(2*u+1+2*v)%2 = 0 by omega), if_pos (show (2*u+1+(2*v+1))%2 = 0 by omega),
        show (2*u+2*v)/2 = u+v by omega, show (2*u+1+(2*v+1))/2 = u+v+1 by omega]
    ring
  rw [Finset.sum_congr rfl hcollapse,
      ← double_to_product (fun u => ((a[2*u]! : Nat) : ZMod q) * γ^u) (fun v => ((b[2*v]! : Nat) : ZMod q) * γ^v),
      ← double_to_product (fun u => ((a[2*u+1]! : Nat) : ZMod q) * γ^u) (fun v => ((b[2*v+1]! : Nat) : ZMod q) * γ^v)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- **ODD half-eval is a quadratic-quotient ring hom**: `evOdd (a·b) γ = evEven a·evOdd b + evOdd a·evEven b`.
The `c₁` component of `baseCaseMultiply`. -/
theorem evOdd_schoolbook (a b : Poly) (γ : ZMod q) (hγ : γ^128 = -1) :
    evOdd (schoolbookMul a b) γ = evEven a γ * evOdd b γ + evOdd a γ * evEven b γ := by
  unfold evEven evOdd
  rw [half_eval_triple a b γ 1 (by omega)]
  rw [sum2_parity (fun i j => ∑ w ∈ range 128, cJ a b i j (2*w+1) * γ^w)]
  have hcollapse : ∀ u ∈ range 128, (∑ v ∈ range 128,
        ((∑ w ∈ range 128, cJ a b (2*u) (2*v) (2*w+1) * γ^w)
          + (∑ w ∈ range 128, cJ a b (2*u) (2*v+1) (2*w+1) * γ^w)
          + (∑ w ∈ range 128, cJ a b (2*u+1) (2*v) (2*w+1) * γ^w)
          + (∑ w ∈ range 128, cJ a b (2*u+1) (2*v+1) (2*w+1) * γ^w)))
      = ∑ v ∈ range 128,
          (((a[2*u]! : Nat) : ZMod q) * γ^u * (((b[2*v+1]! : Nat) : ZMod q) * γ^v)
            + ((a[2*u+1]! : Nat) : ZMod q) * γ^u * (((b[2*v]! : Nat) : ZMod q) * γ^v)) := by
    intro u hu; apply Finset.sum_congr rfl; intro v hv
    have hu128 : u < 128 := mem_range.mp hu
    have hv128 : v < 128 := mem_range.mp hv
    rw [inner_odd a b γ hγ (2*u) (2*v) (by omega) (by omega),
        inner_odd a b γ hγ (2*u) (2*v+1) (by omega) (by omega),
        inner_odd a b γ hγ (2*u+1) (2*v) (by omega) (by omega),
        inner_odd a b γ hγ (2*u+1) (2*v+1) (by omega) (by omega),
        if_neg (show ¬(2*u+2*v)%2 = 1 by omega), if_pos (show (2*u+(2*v+1))%2 = 1 by omega),
        if_pos (show (2*u+1+2*v)%2 = 1 by omega), if_neg (show ¬(2*u+1+(2*v+1))%2 = 1 by omega),
        show (2*u+(2*v+1))/2 = u+v by omega, show (2*u+1+2*v)/2 = u+v by omega]
    ring
  rw [Finset.sum_congr rfl hcollapse,
      ← double_to_product (fun u => ((a[2*u]! : Nat) : ZMod q) * γ^u) (fun v => ((b[2*v+1]! : Nat) : ZMod q) * γ^v),
      ← double_to_product (fun u => ((a[2*u+1]! : Nat) : ZMod q) * γ^u) (fun v => ((b[2*v]! : Nat) : ZMod q) * γ^v)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro u _
  rw [← Finset.sum_add_distrib]

/-! ## PART 5 — `pointwiseNtt` entrywise + the `baseCaseMultiply` casts + `NttMulHom` CLOSED. -/

/-- The `pointwiseNtt` inner step (matches the desugared loop body). -/
def pnStep (a b : Poly) (c : Poly) (i : Nat) : Poly :=
  match baseCaseMultiply a[2*i]! a[2*i+1]! b[2*i]! b[2*i+1]! (powModQ zeta (2 * brv7 i + 1)) with
  | (c0, c1) => (c.set! (2*i) c0).set! (2*i+1) c1

theorem pnStep_size (a b : Poly) (c : Poly) (i : Nat) : (pnStep a b c i).size = c.size := by
  unfold pnStep; rw [size_set!, size_set!]

theorem pointwiseNtt_eq_fold (a b : Poly) :
    pointwiseNtt a b = List.foldl (pnStep a b) zeroPoly (List.range' 0 128 1) := by
  unfold pointwiseNtt pnStep
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', bind_pure_comp, map_pure,
    List.forIn_pure_yield_eq_foldl, bind_pure, Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

/-- Entrywise formula for `pointwiseNtt` from the imperative loop: slot `2i` = `.1`, slot `2i+1` = `.2`. -/
theorem pnFold (a b : Poly) : ∀ (nb : Nat), nb ≤ 128 →
    (List.foldl (pnStep a b) zeroPoly (List.range' 0 nb 1)).size = 256 ∧
    ∀ i, i < nb →
      (List.foldl (pnStep a b) zeroPoly (List.range' 0 nb 1))[2*i]!
        = (baseCaseMultiply a[2*i]! a[2*i+1]! b[2*i]! b[2*i+1]! (powModQ zeta (2 * brv7 i + 1))).1 ∧
      (List.foldl (pnStep a b) zeroPoly (List.range' 0 nb 1))[2*i+1]!
        = (baseCaseMultiply a[2*i]! a[2*i+1]! b[2*i]! b[2*i+1]! (powModQ zeta (2 * brv7 i + 1))).2 := by
  intro nb
  induction nb with
  | zero => intro _; refine ⟨by simp [zeroPoly], ?_⟩; intro i hi; omega
  | succ nb ih =>
    intro hnb
    obtain ⟨ihsz, ihval⟩ := ih (by omega)
    rw [List.range'_1_concat, List.foldl_concat, Nat.zero_add]
    set A := List.foldl (pnStep a b) zeroPoly (List.range' 0 nb 1) with hAdef
    set g := powModQ zeta (2 * brv7 nb + 1) with hgdef
    have hstepdef : pnStep a b A nb
        = (A.set! (2*nb) (baseCaseMultiply a[2*nb]! a[2*nb+1]! b[2*nb]! b[2*nb+1]! g).1).set!
            (2*nb+1) (baseCaseMultiply a[2*nb]! a[2*nb+1]! b[2*nb]! b[2*nb+1]! g).2 := by
      unfold pnStep
      rfl
    have hnewsz : (pnStep a b A nb).size = 256 := by rw [pnStep_size]; exact ihsz
    refine ⟨hnewsz, ?_⟩
    intro i hi
    by_cases hin : i < nb
    · obtain ⟨hlo, hhi⟩ := ihval i hin
      rw [hstepdef]
      constructor
      · rw [getElem!_set!_ne _ (2*nb+1) (2*i) _ (by omega), getElem!_set!_ne _ (2*nb) (2*i) _ (by omega)]
        exact hlo
      · rw [getElem!_set!_ne _ (2*nb+1) (2*i+1) _ (by omega), getElem!_set!_ne _ (2*nb) (2*i+1) _ (by omega)]
        exact hhi
    · have hieq : i = nb := by omega
      subst hieq
      rw [hstepdef]
      constructor
      · rw [getElem!_set!_ne _ (2*i+1) (2*i) _ (by omega),
            getElem!_set!_self _ (2*i) _ (by rw [ihsz]; omega)]
      · rw [getElem!_set!_self _ (2*i+1) _ (by rw [size_set!, ihsz]; omega)]

theorem pointwiseNtt_size (a b : Poly) : (pointwiseNtt a b).size = 256 := by
  rw [pointwiseNtt_eq_fold]; exact (pnFold a b 128 (le_refl _)).1

theorem pointwiseNtt_even (a b : Poly) (i : Nat) (hi : i < 128) :
    (pointwiseNtt a b)[2*i]!
      = (baseCaseMultiply a[2*i]! a[2*i+1]! b[2*i]! b[2*i+1]! (powModQ zeta (2 * brv7 i + 1))).1 := by
  rw [pointwiseNtt_eq_fold]; exact ((pnFold a b 128 (le_refl _)).2 i hi).1

theorem pointwiseNtt_odd (a b : Poly) (i : Nat) (hi : i < 128) :
    (pointwiseNtt a b)[2*i+1]!
      = (baseCaseMultiply a[2*i]! a[2*i+1]! b[2*i]! b[2*i+1]! (powModQ zeta (2 * brv7 i + 1))).2 := by
  rw [pointwiseNtt_eq_fold]; exact ((pnFold a b 128 (le_refl _)).2 i hi).2

theorem pointwiseNtt_lt (a b : Poly) : ∀ (p : Nat), (pointwiseNtt a b)[p]! < q := by
  intro p
  by_cases hp : p < 256
  · -- p is either 2i or 2i+1
    rcases Nat.even_or_odd p with ⟨i, hpe⟩ | ⟨i, hpo⟩
    · have hpe' : p = 2*i := by omega
      subst hpe'
      rw [pointwiseNtt_even a b i (by omega)]; unfold baseCaseMultiply; exact addQ_lt _ _
    · subst hpo
      rw [show 2*i+1 = 2*i+1 from rfl, pointwiseNtt_odd a b i (by omega)]
      unfold baseCaseMultiply; exact addQ_lt _ _
  · rw [getElem!_ge _ p (by rw [pointwiseNtt_size]; omega)]; unfold q; omega

theorem cast_baseCaseMul_fst (a0 a1 b0 b1 gamma : Nat) :
    ((baseCaseMultiply a0 a1 b0 b1 gamma).1 : ZMod q)
      = (a0 : ZMod q) * (b0 : ZMod q) + ((a1 : ZMod q) * (b1 : ZMod q)) * (gamma : ZMod q) := by
  show ((addQ (mulModQ a0 b0) (mulModQ (mulModQ a1 b1) gamma) : Nat) : ZMod q) = _
  rw [cast_addQ, cast_mulModQ, cast_mulModQ, cast_mulModQ]

theorem cast_baseCaseMul_snd (a0 a1 b0 b1 gamma : Nat) :
    ((baseCaseMultiply a0 a1 b0 b1 gamma).2 : ZMod q)
      = (a0 : ZMod q) * (b1 : ZMod q) + (a1 : ZMod q) * (b0 : ZMod q) := by
  show ((addQ (mulModQ a0 b1) (mulModQ a1 b0) : Nat) : ZMod q) = _
  rw [cast_addQ, cast_mulModQ, cast_mulModQ]

theorem cast_gamma (i : Nat) :
    ((powModQ zeta (2 * brv7 i + 1) : Nat) : ZMod q) = evalRoot i := by
  unfold evalRoot
  exact cast_powModQ zeta (2 * brv7 i + 1) (by have := brv7_lt i; omega)

/-! ### The forward residual props + the textbook reduction. -/

/-- **Residual A — the inverse transform is a genuine left inverse** (size-256 + reduced-guarded). This is the
SINGLE remaining rung (`intt ∘ ntt = id`), mirroring the ML-DSA `nttLeftInverse_proven` over the 128-pair leaves;
non-vacuous by `nttLeftInverse_sample`. -/
def NttLeftInverse : Prop := ∀ c : Poly, c.size = 256 → (∀ (p : Nat), c[p]! < q) → intt (ntt c) = c

/-- **Residual B — `ntt` is a ring homomorphism** to the quadratic-quotient product ring. **CLOSED** below. -/
def NttMulHom : Prop := ∀ a b : Poly, a.size = 256 → b.size = 256 →
  ntt (schoolbookMul a b) = pointwiseNtt (ntt a) (ntt b)

/-- Every coefficient of `ntt w` is reduced (`< q`) when the input is. -/
theorem ntt_lt (w : Poly) (hw : ∀ (p:Nat), w[p]!<q) : ∀ (p:Nat), (ntt w)[p]! < q := by
  intro p
  rw [ntt_eq_fold, nttFold_eq]
  -- reduced-range invariant threaded through nttUpto
  suffices h : ∀ n, n ≤ 7 → ∀ (p:Nat), (nttUpto n w).1[p]! < q by exact h 7 (by omega) p
  intro n
  induction n with
  | zero => intro _ p; simpa [nttUpto] using hw p
  | succ n ih =>
    intro hn p
    rw [nttUpto_succ]
    unfold stageStep
    -- one stage preserves reducedness
    suffices hgen : ∀ (L : List Nat) (st : Poly × Nat), (∀ (p:Nat), st.1[p]!<q) →
        ∀ (p:Nat), (List.foldl (blockFn n) st L).1[p]! < q by
      exact hgen _ (nttUpto n w) (fun p => ih (by omega) p) p
    intro L; induction L with
    | nil => intro st hst p; simpa using hst p
    | cons hd tl ihL =>
      intro st hst
      exact ihL (blockFn n st hd) (fun p => by
        unfold blockFn; exact bfSweep_lt _ _ _ (len_pos n (by omega)) st.1 hst p)

theorem ntt_size (w : Poly) (hw : w.size = 256) : (ntt w).size = 256 := by
  rw [ntt_eq_fold, nttFold_eq]; exact (stage_inv w hw 7 (by omega)).1

/-- Entry-level `NttMulHom` at the even slot `2g` — the `c₀` component. -/
theorem nttMul_entry_even (a b : Poly) (ha : a.size = 256) (hb : b.size = 256) (g : Nat) (hg : g < 128) :
    (ntt (schoolbookMul a b))[2*g]! = (pointwiseNtt (ntt a) (ntt b))[2*g]! := by
  have hsab : (schoolbookMul a b).size = 256 := schoolbookMul_size a b
  have hX : (ntt (schoolbookMul a b))[2*g]! < q := ntt_lt _ (schoolbookMul_lt a b) (2*g)
  have hY : (pointwiseNtt (ntt a) (ntt b))[2*g]! < q := pointwiseNtt_lt _ _ (2*g)
  apply natCast_inj_of_lt _ _ hX hY
  rw [ntt_even (schoolbookMul a b) hsab g hg,
      evEven_schoolbook a b (evalRoot g) (evalRoot_pow128 g),
      pointwiseNtt_even (ntt a) (ntt b) g hg, cast_baseCaseMul_fst,
      ntt_even a ha g hg, ntt_odd a ha g hg, ntt_even b hb g hg, ntt_odd b hb g hg, cast_gamma]
  ring

/-- Entry-level `NttMulHom` at the odd slot `2g+1` — the `c₁` component. -/
theorem nttMul_entry_odd (a b : Poly) (ha : a.size = 256) (hb : b.size = 256) (g : Nat) (hg : g < 128) :
    (ntt (schoolbookMul a b))[2*g+1]! = (pointwiseNtt (ntt a) (ntt b))[2*g+1]! := by
  have hsab : (schoolbookMul a b).size = 256 := schoolbookMul_size a b
  have hX : (ntt (schoolbookMul a b))[2*g+1]! < q := ntt_lt _ (schoolbookMul_lt a b) (2*g+1)
  have hY : (pointwiseNtt (ntt a) (ntt b))[2*g+1]! < q := pointwiseNtt_lt _ _ (2*g+1)
  apply natCast_inj_of_lt _ _ hX hY
  rw [ntt_odd (schoolbookMul a b) hsab g hg,
      evOdd_schoolbook a b (evalRoot g) (evalRoot_pow128 g),
      pointwiseNtt_odd (ntt a) (ntt b) g hg, cast_baseCaseMul_snd,
      ntt_even a ha g hg, ntt_odd a ha g hg, ntt_even b hb g hg, ntt_odd b hb g hg]

theorem nttMulHom_guarded (a b : Poly) (ha : a.size = 256) (hb : b.size = 256) :
    ntt (schoolbookMul a b) = pointwiseNtt (ntt a) (ntt b) := by
  have hsab : (schoolbookMul a b).size = 256 := schoolbookMul_size a b
  apply Array.ext
  · rw [ntt_size _ hsab, pointwiseNtt_size]
  · intro m h1 _
    have hm : m < 256 := by rw [ntt_size _ hsab] at h1; exact h1
    rw [(getElem!_pos (ntt (schoolbookMul a b)) m (by rw [ntt_size _ hsab]; exact hm)).symm,
        (getElem!_pos (pointwiseNtt (ntt a) (ntt b)) m (by rw [pointwiseNtt_size]; exact hm)).symm]
    rcases Nat.even_or_odd m with ⟨g, hgm⟩ | ⟨g, hgm⟩
    · have hgm' : m = 2*g := by omega
      subst hgm'
      exact nttMul_entry_even a b ha hb g (by omega)
    · subst hgm
      exact nttMul_entry_odd a b ha hb g (by omega)

theorem nttMulHom_proven : NttMulHom := fun a b ha hb => nttMulHom_guarded a b ha hb

/-- **THE TEXTBOOK REDUCTION.** The incomplete-NTT multiply computes the negacyclic ring product, given the two
standard NTT-correctness facts: `intt` inverts, and `ntt` diagonalizes into the quadratic quotients. Proof:
`intt (pointwiseNtt (ntt a) (ntt b)) = intt (ntt (schoolbookMul a b)) = schoolbookMul a b`. With `NttMulHom`
CLOSED, the whole gate follows from the SINGLE `NttLeftInverse` residual. -/
theorem mlkem_faithful_of (hInv : NttLeftInverse) :
    ∀ a b : Poly, a.size = 256 → b.size = 256 →
      intt (pointwiseNtt (ntt a) (ntt b)) = schoolbookMul a b := by
  intro a b ha hb
  rw [← nttMulHom_proven a b ha hb]
  exact hInv (schoolbookMul a b) (schoolbookMul_size a b) (schoolbookMul_lt a b)

/-! ## NON-VACUITY — both residuals HOLD on the wraparound sample (`native_decide` witnesses, NOT in any ∀). -/

theorem nttLeftInverse_sample : intt (ntt sampleA) = sampleA := by native_decide

theorem nttMulHom_sample :
    ntt (schoolbookMul sampleA sampleB) = pointwiseNtt (ntt sampleA) (ntt sampleB) := by native_decide

/-! ## Axiom gate — every FORWARD keystone ⊆ {propext, Classical.choice, Quot.sound}.
The `ζ`-order (`zeta_pow_neg_one`) and `brv7` congruences are plain `decide` (kernel reduction, NOT
`native_decide`), so no `ofReduceBool` residual leaks into any `∀`-theorem. The two `native_decide` witnesses
above (`nttLeftInverse_sample`, `nttMulHom_sample`) are concrete non-vacuity samples — deliberately NOT gated. -/
#assert_axioms cast_addQ
#assert_axioms cast_subQ
#assert_axioms cast_mulModQ
#assert_axioms cast_addPoly
#assert_axioms cast_subPoly
#assert_axioms zeta_pow_neg_one
#assert_axioms orderOf_zeta
#assert_axioms zeta_orthogonality
#assert_axioms bfFold_spec
#assert_axioms cast_bfSweep
#assert_axioms ntt_eq_fold
#assert_axioms cast_powModQ
#assert_axioms cast_zetaTwiddle
#assert_axioms brv_even7
#assert_axioms brv_odd7
#assert_axioms brv_high7
#assert_axioms rootAt_closed
#assert_axioms rootAt_final
#assert_axioms block_char
#assert_axioms stage_inv
#assert_axioms ntt_reduces_to_quotients
#assert_axioms ntt_even
#assert_axioms ntt_odd
#assert_axioms schoolbookMul_getElem
#assert_axioms schoolbookMul_size
#assert_axioms schoolbookMul_lt
#assert_axioms inner_even
#assert_axioms inner_odd
#assert_axioms sum2_parity
#assert_axioms evEven_schoolbook
#assert_axioms evOdd_schoolbook
#assert_axioms cast_baseCaseMul_fst
#assert_axioms cast_baseCaseMul_snd
#assert_axioms cast_gamma
#assert_axioms pnFold
#assert_axioms pointwiseNtt_even
#assert_axioms pointwiseNtt_odd
#assert_axioms pointwiseNtt_lt
#assert_axioms ntt_lt
#assert_axioms ntt_size
#assert_axioms nttMul_entry_even
#assert_axioms nttMul_entry_odd
#assert_axioms nttMulHom_guarded
#assert_axioms nttMulHom_proven
#assert_axioms mlkem_faithful_of

end Dregg2.Crypto.MlKemRing
