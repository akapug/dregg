/-
# Dregg2.Circuit.FriFoldArity — FRI folding soundness at DEPLOYED arity `2^k` (8-to-1).

**The gap (measured, committed `c9e8439ad`).** `circuit/src/plonky3_prover.rs:98` sets
`PROD_FRI_MAX_LOG_ARITY = 3`, so the shipped FRI folds up to **8-to-1** per round. But
`FriSoundness.lean` proves distance-preservation only for the arity-`2` squaring quotient
(`FriGeom.q`, 2-to-1) via the **two-challenge** Vandermonde reconstruction
(`fold_close_of_two_alpha`). Instantiating that at the deployed field/rate (bricks 1–3) does
NOT close the arity gap — the folding MAP itself differs. This file closes it: it generalizes
the geometry, the decomposition, and the KEY LEMMA to arity `n = 2^k`, and instantiates at the
deployed `k = 3` over BabyBear.

**Honest scope (first sentence).** `fold_close_of_arity_challenges` IS PROVED for GENERAL
arity `n` (no `sorry`, no smuggled hardness), with the DERIVED distance constant `n^2 · d`
(for `n = 2^k` this is `4^k · d`; at `k = 1` it recovers the arity-2 lemma's `4d` exactly),
and it IS instantiated at the deployed `k = 3` (`n = 8`) over BabyBear (`friSetupK8`), where
both teeth fire: an honest degree-`< 8` codeword reconstructs `0`-close from `8` distinct
challenges (`fHon8_reconstruct`), and a concrete far word (the frequency-`8` word
`x ↦ (-1)^x`) admits NO `8` distinct good challenges (`f0_no_injective_good`) — its
good-challenge set has `< 8` elements (`f0_good_card_lt`). The one extra hypothesis the
generalization needs beyond arity 2 — that the `2^k` fiber values are **pairwise distinct**
(so the fiber Vandermonde inverts) — is PROVED for the BabyBear instance from `omega16`'s
order-`16` (`pC_repsC_inj`), never assumed.

**The reconstruction (BBHR18, size-`n` Vandermonde).** Arity 2 solves a `2×2` system from
two challenges (`α₁ ≠ α₂`). Here: `n` DISTINCT challenges give `n` fold equations
`Σ_{j<n} αᵢ^j · Cⱼf(y) = gᵢ(y)`; the challenge Vandermonde `A = vandermonde α` is invertible
(`det_vandermonde_ne_zero_iff`, `α` injective), so `Cⱼf = Σᵢ A⁻¹[j,i]·gᵢ ∈ C'` off the union
`T = ⋃ᵢ disagree(Fold αᵢ f, gᵢ)`. Reassembly (`unfold_closed`) gives `h ∈ C` with
`f = h` off `q⁻¹(T)`; `|q⁻¹(T)| ≤ n·|T| ≤ n·(n·d) = n²·d`.

Rests only on `Mathlib` (`Matrix.vandermonde`, `det_vandermonde_ne_zero_iff`, nonsingular
inverse) and — for the instance — `omega16`'s order (`BabyBearFriDeployed`). Sibling
`Dregg2/Crypto/MlDsaSignReal.lean` is modified in the working tree; this file does not touch it.
-/
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Field.GeomSum
import Dregg2.Circuit.FriSoundness
import Dregg2.Circuit.BabyBearFriDeployed

namespace Dregg2.Circuit.FriFoldArity

set_option linter.unusedSectionVars false

open Dregg2.Circuit.FriSoundness
open scoped BigOperators Matrix

/-! ## §1. The arity-`n` coset geometry.

The FRI domain `L` (`ι`) maps to `L^n = L^(2^k)` (`κ`) by the power-`n` quotient `q`. Each
fiber has exactly `n` points, indexed by `reps y : Fin n → ι`. The single structural axiom the
reconstruction needs — beyond `q ∘ reps = id` and fiber-covering — is that the `n` **fiber
VALUES** `p (reps y ·)` are pairwise DISTINCT: that is exactly what makes the fiber Vandermonde
invertible (the arity-2 file got this for free from `p (σ (rep y)) = - p (rep y)` with `2 ≠ 0`;
at arity `n` it becomes the honest primitive-`n`-th-root condition, PROVED for BabyBear in §5). -/

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ}

/-- The arity-`n` coset geometry: the power-`n` quotient `q`, the point value `p`, and the `n`
fiber representatives `reps y : Fin n → ι`, with fiber values pairwise distinct. -/
structure FriGeomK (F ι κ : Type*) [Field F] (n : ℕ) where
  /-- The power-`n` quotient `L → L^n`. -/
  q : ι → κ
  /-- The point value (`x`'s field value). -/
  p : ι → F
  /-- The `n` fiber representatives over each `y ∈ κ`. -/
  reps : κ → Fin n → ι
  /-- Every representative squares (powers) back to `y`. -/
  q_reps : ∀ y i, q (reps y i) = y
  /-- **The fiber values are pairwise distinct** — the primitive-`n`-th-root condition that
  makes the fiber Vandermonde invertible (the honest arity-`n` generalization of `2 ≠ 0`). -/
  p_reps_inj : ∀ y, Function.Injective (fun i => p (reps y i))
  /-- Every `x` is one of the `n` representatives of its fiber. -/
  q_fiber : ∀ x, ∃ i, x = reps (q x) i

variable (G : FriGeomK F ι κ n)

/-- Local: `mulVec` is the row·vector dot product, unfolded to a sum. -/
theorem mulVec_eq (M : Matrix (Fin n) (Fin n) F) (v : Fin n → F) (i : Fin n) :
    (M *ᵥ v) i = ∑ j, M i j * v j := rfl

/-- The **fiber Vandermonde** at `y`: `V[i,j] = (p (reps y i))^j`. Invertible because the fiber
values are pairwise distinct (`p_reps_inj`). -/
noncomputable def fiberV (y : κ) : Matrix (Fin n) (Fin n) F :=
  Matrix.vandermonde (fun i => G.p (G.reps y i))

theorem fiberV_isUnit_det (y : κ) : IsUnit (fiberV G y).det :=
  isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr (G.p_reps_inj y))

/-- The vector of fiber values of `f` over `y`. -/
def fvec (f : ι → F) (y : κ) : Fin n → F := fun i => f (G.reps y i)

/-- The **`n`-ary decomposition components** at `y`: the coefficient vector recovered by the
inverse fiber Vandermonde — the arity-`n` analogue of the even/odd `(E f, O f)` pair. -/
noncomputable def comps (f : ι → F) (y : κ) : Fin n → F := (fiberV G y)⁻¹ *ᵥ fvec G f y

/-- The `j`-th component `Cⱼ f : κ → F`. Arity 2 has just `C₀ = E`, `C₁ = O`. -/
noncomputable def Cj (j : Fin n) (f : ι → F) : κ → F := fun y => comps G f y j

/-- **The arity-`n` FRI fold** with challenge `α`: `Fold α f (y) = Σ_{j<n} α^j · Cⱼf(y)` — the
value at `α` of the degree-`< n` interpolant of the fiber (arity 2: `E f + α·O f`). -/
noncomputable def Fold (α : F) (f : ι → F) : κ → F := fun y => ∑ j : Fin n, α ^ (j : ℕ) * Cj G j f y

/-- **Reassembly** `(Fin n → κ → F) → (ι → F)`: `Σ_j p(x)^j · Dⱼ(q x)` (arity 2: `unfoldF`). -/
noncomputable def reassemble (D : Fin n → κ → F) : ι → F := fun x => ∑ j : Fin n, (G.p x) ^ (j : ℕ) * D j (G.q x)

/-- **The fundamental `n`-ary decomposition identity** (the `self_decomp` analogue): for every
`x`, `f(x) = Σ_{j<n} p(x)^j · Cⱼf(q x)`. Proved from `V · V⁻¹ = 1`: evaluating the recovered
coefficients at `p(x)` (a row of the fiber Vandermonde) returns the fiber value `f(x)`. -/
theorem self_decomp (f : ι → F) (x : ι) :
    f x = ∑ j : Fin n, (G.p x) ^ (j : ℕ) * Cj G j f (G.q x) := by
  obtain ⟨i₀, hx⟩ := G.q_fiber x
  have hV : (fiberV G (G.q x)) *ᵥ comps G f (G.q x) = fvec G f (G.q x) := by
    rw [comps, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (fiberV_isUnit_det G (G.q x)),
      Matrix.one_mulVec]
  have h2 := congrFun hV i₀
  rw [mulVec_eq] at h2
  have hentry : ∀ j, (fiberV G (G.q x)) i₀ j = (G.p x) ^ (j : ℕ) := by
    intro j; rw [fiberV, Matrix.vandermonde_apply, ← hx]
  simp only [hentry] at h2
  rw [fvec, ← hx] at h2
  exact h2.symm

/-! ## §2. The arity-`n` FRI setup and folding completeness. -/

/-- The arity-`n` FRI setup: geometry + domain code `C` + folded code `C'`, with the two RS
closure facts — reassembly lands in `C`, and each component of a codeword is a folded codeword
(`n`-ary completeness). Discharged for a genuine BabyBear instance in §4/§5. -/
structure FriSetupK (F ι κ : Type*) [Field F] [DecidableEq F]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (n : ℕ) where
  geom : FriGeomK F ι κ n
  C : Submodule F (ι → F)
  C' : Submodule F (κ → F)
  /-- **Reassembly closure**: reassembling `n` folded codewords lands in the domain code. -/
  unfold_closed : ∀ D : Fin n → κ → F, (∀ j, D j ∈ C') → reassemble geom D ∈ C
  /-- **`n`-ary folding completeness**: each component of a codeword is a folded codeword. -/
  foldC_mem : ∀ f ∈ C, ∀ j, Cj geom j f ∈ C'

variable (S : FriSetupK F ι κ n)

/-- `Fold` as a `C'`-linear combination of the components. -/
theorem fold_eq_sum_smul (α : F) (f : ι → F) :
    Fold S.geom α f = ∑ j : Fin n, α ^ (j : ℕ) • Cj S.geom j f := by
  funext y; simp [Fold, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **COMPLETENESS**: folding a codeword with ANY challenge yields a codeword of `C'`. -/
theorem fold_complete {f : ι → F} (hf : f ∈ S.C) (α : F) : Fold S.geom α f ∈ S.C' := by
  rw [fold_eq_sum_smul]
  exact Submodule.sum_mem _ (fun j _ => S.C'.smul_mem _ (S.foldC_mem f hf j))

/-! ## §3. THE KEY LEMMA — distance preservation at arity `n` (the heart of the generalization). -/

/-- **Pullback cardinality**: the `q`-preimage of `P ⊆ κ` has `≤ n · |P|` points (each `y` has
`n` representatives). The arity-2 file's `pullback_card_le` had `2·|P|`. -/
theorem pullback_card_le (P : Finset κ) :
    (Finset.univ.filter (fun x : ι => G.q x ∈ P)).card ≤ n * P.card := by
  have hsub : (Finset.univ.filter (fun x : ι => G.q x ∈ P))
      ⊆ (P ×ˢ (Finset.univ : Finset (Fin n))).image (fun pr => G.reps pr.1 pr.2) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨i, hi⟩ := G.q_fiber x
    exact Finset.mem_image.mpr ⟨(G.q x, i), Finset.mem_product.mpr ⟨hx.2, Finset.mem_univ i⟩, hi.symm⟩
  calc (Finset.univ.filter (fun x : ι => G.q x ∈ P)).card
      ≤ ((P ×ˢ (Finset.univ : Finset (Fin n))).image (fun pr => G.reps pr.1 pr.2)).card :=
        Finset.card_le_card hsub
    _ ≤ (P ×ˢ (Finset.univ : Finset (Fin n))).card := Finset.card_image_le
    _ = n * P.card := by
        rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]

/-- **THE KEYSTONE — `fold_close_of_arity_challenges`.** If for `n` DISTINCT challenges
`α : Fin n → F` (injective) every `Fold (α i) f` is `d`-close to the folded code `C'`, then `f`
is `n²·d`-close to the domain code `C`.

*Proof (BBHR18, size-`n` Vandermonde).* Let `gᵢ ∈ C'` witness closeness, `Tᵢ = disagree(Fold αᵢ
f, gᵢ)` (`|Tᵢ| ≤ d`), `T = ⋃ᵢ Tᵢ`. Off `T`, the `n` equations `Σⱼ αᵢ^j·Cⱼf(y) = gᵢ(y)` are the
mulVec `A · (Cf y) = (gᵢ y)ᵢ` for `A = vandermonde α`; `A` is invertible (`α` injective), so
`Cⱼf(y) = Σᵢ A⁻¹[j,i]·gᵢ(y) = Dⱼ(y)` with `Dⱼ = Σᵢ A⁻¹[j,i]•gᵢ ∈ C'`. Then `h = reassemble D ∈
C` agrees with `f` off `q⁻¹(T)` (by `self_decomp`); `|q⁻¹(T)| ≤ n·|T| ≤ n·(n·d) = n²·d`. -/
theorem fold_close_of_arity_challenges {f : ι → F} {α : Fin n → F}
    (hα : Function.Injective α) {d : ℕ}
    (h : ∀ i, closeN S.C' d (Fold S.geom (α i) f)) :
    closeN S.C (n ^ 2 * d) f := by
  classical
  choose g hgC hgcard using h
  set G := S.geom with hGdef
  set A : Matrix (Fin n) (Fin n) F := Matrix.vandermonde α with hA
  have hAdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hα)
  set D : Fin n → κ → F := fun j => ∑ i, A⁻¹ j i • g i with hD
  have hDC : ∀ j, D j ∈ S.C' := fun j => Submodule.sum_mem _ (fun i _ => S.C'.smul_mem _ (hgC i))
  set T : Finset κ := Finset.univ.biUnion (fun i => disagree (Fold G (α i) f) (g i)) with hT
  have hTcard : T.card ≤ n * d := by
    calc T.card ≤ ∑ i, (disagree (Fold G (α i) f) (g i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, d := Finset.sum_le_sum (fun i _ => hgcard i)
      _ = n * d := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Off `T`, the components equal the reconstructed codewords.
  have hkey : ∀ y ∉ T, ∀ j, Cj G j f y = D j y := by
    intro y hyT j
    have hcol : A *ᵥ comps G f y = (fun i => g i y) := by
      funext i
      have hfold : Fold G (α i) f y = g i y := by
        have hmem : y ∉ disagree (Fold G (α i) f) (g i) := fun hy =>
          hyT (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hy⟩)
        rw [mem_disagree, not_not] at hmem; exact hmem
      rw [mulVec_eq]
      have hrow : (∑ j, A i j * comps G f y j) = Fold G (α i) f y := by
        simp only [Fold, Cj, hA, Matrix.vandermonde_apply]
      rw [hrow, hfold]
    have hcomps : comps G f y = A⁻¹ *ᵥ (fun i => g i y) := by
      rw [← hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hAdet, Matrix.one_mulVec]
    show comps G f y j = D j y
    rw [hcomps, mulVec_eq]
    simp only [hD, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  -- Reassemble.
  set h' : ι → F := reassemble G D with hh'
  have hh'C : h' ∈ S.C := S.unfold_closed D hDC
  have hfh : ∀ x : ι, G.q x ∉ T → f x = h' x := by
    intro x hx
    rw [self_decomp G f x, hh', reassemble]
    exact Finset.sum_congr rfl (fun j _ => by rw [hkey (G.q x) hx j])
  have hsub : disagree f h' ⊆ Finset.univ.filter (fun x : ι => G.q x ∈ T) := by
    intro x hx
    rw [mem_disagree] at hx
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ x, by by_contra hxT; exact hx (hfh x hxT)⟩
  refine ⟨h', hh'C, ?_⟩
  calc (disagree f h').card
      ≤ (Finset.univ.filter (fun x : ι => G.q x ∈ T)).card := Finset.card_le_card hsub
    _ ≤ n * T.card := pullback_card_le G T
    _ ≤ n * (n * d) := Nat.mul_le_mul_left _ hTcard
    _ = n ^ 2 * d := by ring

/-- **THE EXCEPTIONAL BOUND (generalizing `exceptional_subsingleton`).** A word `f ∉ C` admits
NO `n` distinct "good" challenges: the arity-2 subsingleton (`< 2` good) becomes `< n` good. -/
theorem no_injective_good {f : ι → F} (hf : f ∉ S.C) :
    ¬ ∃ α : Fin n → F, Function.Injective α ∧ ∀ i, Fold S.geom (α i) f ∈ S.C' := by
  rintro ⟨α, hinj, hg⟩
  have hclose : ∀ i, closeN S.C' 0 (Fold S.geom (α i) f) :=
    fun i => closeN_zero_iff_mem.mpr (hg i)
  have hcl := fold_close_of_arity_challenges S hinj hclose
  rw [Nat.mul_zero] at hcl
  exact hf (closeN_zero_iff_mem.mp hcl)

/-- **The `< n` cardinality form**: the good-challenge set of a far `f` has `< n` elements. -/
theorem good_challenge_card_lt {f : ι → F} (hf : f ∉ S.C) (s : Finset F)
    (hs : ∀ α ∈ s, Fold S.geom α f ∈ S.C') : s.card < n := by
  by_contra hle
  rw [not_lt] at hle
  have hcard : Fintype.card (Fin n) ≤ Fintype.card (s : Set F) := by
    simpa [Fintype.card_fin, Fintype.card_coe] using hle
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  refine no_injective_good S hf ⟨fun i => (e i : F), ?_, fun i => hs _ (e i).2⟩
  intro a b hab
  exact e.injective (Subtype.ext hab)

/-! ## §4. The DEPLOYED-ARITY instance: `k = 3`, `n = 8`, over BabyBear.

`PROD_FRI_MAX_LOG_ARITY = 3` ⇒ the shipped fold is 8-to-1. We build a genuine arity-`8`
BabyBear `FriSetupK` on the size-`16` coset (`ι = Fin 16`, `κ = Fin 2`): `p(x) = ω₁₆^x`,
`q(x) = x mod 2`, the `8` fiber representatives `reps y i = (y + 2i) mod 16`. `ω₁₆` is the
primitive `16`-th root of `BabyBearFriDeployed`; its order-`16` gives the fiber-value
distinctness the arity-`n` geometry demands. `C = {x ↦ Σ_{j<8} c_j·(ω₁₆^x)^j}` is the
degree-`< 8` RS code (dim `8` of `16`, so far words EXIST); `C'` = constants. -/

open Dregg2.Circuit.BabyBearFriDeployed (omega16)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

/-- `q(x) = x mod 2 : Fin 2` — the power-`8` quotient (`(ω₁₆^x)^8 = (-1)^x` depends on `x mod 2`). -/
def qC : Fin 16 → Fin 2 := fun x => ⟨(x : ℕ) % 2, Nat.mod_lt _ (by norm_num)⟩

/-- `p(x) = ω₁₆^x`. -/
noncomputable def pC : Fin 16 → BabyBear := fun x => omega16 ^ (x : ℕ)

/-- The `8` fiber representatives `reps y i = (y + 2i) mod 16`. -/
def repsC : Fin 2 → Fin 8 → Fin 16 := fun y i => ⟨((y : ℕ) + 2 * (i : ℕ)) % 16, Nat.mod_lt _ (by norm_num)⟩

theorem qC_repsC : ∀ y i, qC (repsC y i) = y := by decide

theorem qC_fiber : ∀ x : Fin 16, ∃ i, x = repsC (qC x) i := by decide

/-- **Fiber-value distinctness from `ω₁₆`'s order `16`** — the arity-`8` primitive-root
condition, PROVED (the `128`-case kernel check on the concrete BabyBear powers `ω₁₆^{0..15}`). -/
theorem pC_repsC_inj : ∀ y : Fin 2, Function.Injective (fun i : Fin 8 => pC (repsC y i)) := by
  intro y i i' h
  fin_cases y <;> fin_cases i <;> fin_cases i' <;> first | rfl | (revert h; decide)

/-- The deployed arity-`8` BabyBear geometry. -/
noncomputable def friGeomK8 : FriGeomK BabyBear (Fin 16) (Fin 2) 8 where
  q := qC
  p := pC
  reps := repsC
  q_reps := qC_repsC
  p_reps_inj := pC_repsC_inj
  q_fiber := qC_fiber

/-- The domain code `C = {x ↦ Σ_{j<8} c_j·(ω₁₆^x)^j}` — the degree-`< 8` Reed-Solomon code. -/
noncomputable def codeC8 : Submodule BabyBear (Fin 16 → BabyBear) where
  carrier := {f | ∃ c : Fin 8 → BabyBear, f = fun x => ∑ j : Fin 8, c j * (pC x) ^ (j : ℕ)}
  zero_mem' := ⟨0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨c, rfl⟩ ⟨c', rfl⟩
    refine ⟨c + c', ?_⟩
    funext x
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp [add_mul])
  smul_mem' := by
    rintro a f ⟨c, rfl⟩
    refine ⟨a • c, ?_⟩
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_assoc])

/-- The folded code `C'` = constants. -/
noncomputable def codeC'8 : Submodule BabyBear (Fin 2 → BabyBear) where
  carrier := {g | ∃ a : BabyBear, g = fun _ => a}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩; exact ⟨a + b, rfl⟩
  smul_mem' := by rintro c f ⟨a, rfl⟩; exact ⟨c • a, by funext _; rfl⟩

/-- **The deployed arity-`8` BabyBear FRI setup** — closures PROVED (not assumed). -/
noncomputable def friSetupK8 : FriSetupK BabyBear (Fin 16) (Fin 2) 8 where
  geom := friGeomK8
  C := codeC8
  C' := codeC'8
  unfold_closed := by
    intro D hD
    choose a ha using hD
    refine ⟨a, ?_⟩
    funext x
    simp only [reassemble, friGeomK8, ha]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_comm])
  foldC_mem := by
    intro f hf j
    obtain ⟨c, rfl⟩ := hf
    refine ⟨c j, ?_⟩
    funext y
    show comps friGeomK8 _ y j = c j
    have hfvec : fvec friGeomK8 (fun x => ∑ i : Fin 8, c i * (pC x) ^ (i : ℕ)) y
        = fiberV friGeomK8 y *ᵥ c := by
      funext k
      rw [mulVec_eq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [fiberV, Matrix.vandermonde_apply]
      simp only [friGeomK8]
      rw [mul_comm]
    rw [comps, hfvec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (fiberV_isUnit_det friGeomK8 y),
      Matrix.one_mulVec]

/-! ## §5. Teeth at the deployed arity — both polarities.

FIRES: an honest degree-`< 8` codeword folds into `C'` for every challenge, and `8` DISTINCT
challenges reconstruct it `0`-close (the KEYSTONE, non-vacuous). BITES: a concrete FAR word
(the frequency-`8` word `x ↦ (-1)^x`, which is NOT degree-`< 8`) admits NO `8` distinct good
challenges — its good set has `< 8` elements. -/

/-- The honest codeword coefficients `2 + 3·(ω₁₆^x)`. -/
noncomputable def cHon8 : Fin 8 → BabyBear := ![2, 3, 0, 0, 0, 0, 0, 0]

/-- An honest degree-`< 8` codeword. -/
noncomputable def fHon8 : Fin 16 → BabyBear := fun x => ∑ j : Fin 8, cHon8 j * (pC x) ^ (j : ℕ)

theorem fHon8_mem : fHon8 ∈ friSetupK8.C := ⟨cHon8, rfl⟩

/-- **Tooth (FIRES): completeness** — the honest codeword folds into `C'` for every challenge. -/
theorem fHon8_fold_complete (α : BabyBear) : Fold friSetupK8.geom α fHon8 ∈ friSetupK8.C' :=
  fold_complete friSetupK8 fHon8_mem α

/-- `8` distinct challenges `chal8 i = (i : BabyBear)`. -/
noncomputable def chal8 : Fin 8 → BabyBear := fun i => ((i : ℕ) : BabyBear)

theorem chal8_inj : Function.Injective chal8 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> first | rfl | (revert h; decide)

/-- **Tooth (FIRES): the KEYSTONE at deployed arity `8`, non-vacuous.** The honest codeword,
folded by `8` DISTINCT challenges (all `0`-close by completeness), is reconstructed `8²·0 = 0`-
close to `C` — a genuine low-degree word survives `8` folds. -/
theorem fHon8_reconstruct : closeN friSetupK8.C (8 ^ 2 * 0) fHon8 :=
  fold_close_of_arity_challenges friSetupK8 chal8_inj
    (fun i => closeN_zero_iff_mem.mpr (fold_complete friSetupK8 fHon8_mem (chal8 i)))

/-- The **frequency-`8` far word** `f₀(x) = (-1)^x = (ω₁₆^8)^x` — orthogonal to every
degree-`< 8` monomial under the DFT functional `φ` below, hence NOT in `C`. -/
noncomputable def f0 : Fin 16 → BabyBear := fun x => (-1 : BabyBear) ^ (x : ℕ)

/-- The frequency-`8` DFT functional `φ(f) = Σ_x (-1)^x · f(x)`. It annihilates `C` (each
degree-`< 8` monomial sums to `0` over the full period) but not `f₀`. -/
noncomputable def phi (f : Fin 16 → BabyBear) : BabyBear := ∑ x : Fin 16, (-1 : BabyBear) ^ (x : ℕ) * f x

/-- `φ` annihilates every codeword: each monomial `(ω₁₆^x)^j` (`j < 8`) is a full-period
geometric sum `Σ_x (-(ω₁₆^j))^x = 0` (`-(ω₁₆^j) ≠ 1` and `(-(ω₁₆^j))^16 = 1`). -/
theorem phi_zero_on_C : ∀ f ∈ codeC8, phi f = 0 := by
  rintro f ⟨c, rfl⟩
  simp only [phi, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have hr : (-(omega16 ^ (j : ℕ))) ≠ 1 := by fin_cases j <;> decide
  have h16 : (omega16 ^ (16 : ℕ)) = 1 := by decide
  have hr16 : (-(omega16 ^ (j : ℕ))) ^ (16 : ℕ) = 1 := by
    rw [neg_pow, ← pow_mul, Nat.mul_comm, pow_mul, h16, one_pow, mul_one]; decide
  have hrewrite : (∑ x : Fin 16, (-1 : BabyBear) ^ (x : ℕ) * (c j * (pC x) ^ (j : ℕ)))
      = c j * ∑ x : Fin 16, (-(omega16 ^ (j : ℕ))) ^ (x : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have hx : (-(omega16 ^ (j : ℕ))) ^ (x : ℕ)
        = (-1 : BabyBear) ^ (x : ℕ) * omega16 ^ ((x : ℕ) * (j : ℕ)) := by
      rw [neg_pow, ← pow_mul, Nat.mul_comm (j : ℕ) (x : ℕ)]
    rw [hx, pC, ← pow_mul]
    ring
  rw [hrewrite, Fin.sum_univ_eq_sum_range (fun k => (-(omega16 ^ (j : ℕ))) ^ k) 16,
    geom_sum_eq hr 16, hr16, sub_self, zero_div, mul_zero]

/-- `φ(f₀) = 16 ≠ 0`: the frequency-`8` word registers on its own functional. -/
theorem phi_f0 : phi f0 = 16 := by
  have hone : ∀ x : Fin 16, (-1 : BabyBear) ^ (x : ℕ) * f0 x = 1 := by
    intro x
    show (-1 : BabyBear) ^ (x : ℕ) * (-1 : BabyBear) ^ (x : ℕ) = 1
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  rw [phi, Finset.sum_congr rfl (fun x _ => hone x)]
  simp [Finset.card_univ]

/-- **Tooth (BITES): the far word is genuinely far** — `f₀ ∉ C` (`φ f₀ = 16 ≠ 0 = φ` on `C`). -/
theorem f0_not_mem : f0 ∉ friSetupK8.C := by
  intro h
  have h0 : phi f0 = 0 := phi_zero_on_C f0 h
  rw [phi_f0] at h0
  exact absurd h0 (by decide)

/-- **Tooth (BITES): the EXCEPTIONAL bound at deployed arity `8`** — the far word `f₀` admits
NO `8` distinct good challenges (`no_injective_good` at `n = 8`). -/
theorem f0_no_injective_good :
    ¬ ∃ α : Fin 8 → BabyBear, Function.Injective α ∧ ∀ i, Fold friSetupK8.geom (α i) f0 ∈ friSetupK8.C' :=
  no_injective_good friSetupK8 f0_not_mem

/-- **Tooth (BITES, cardinality form)**: `f₀`'s good-challenge set has `< 8` elements. -/
theorem f0_good_card_lt (s : Finset BabyBear) (hs : ∀ α ∈ s, Fold friSetupK8.geom α f0 ∈ friSetupK8.C') :
    s.card < 8 :=
  good_challenge_card_lt friSetupK8 f0_not_mem s hs

/-! ## §6. Axiom hygiene — the keystone + instance + teeth rest only on the kernel axioms plus
`omega16`'s order (a `decide` fact), no `sorry`, no smuggled hardness. -/

#assert_axioms fold_close_of_arity_challenges
#assert_axioms no_injective_good
#assert_axioms good_challenge_card_lt
#assert_axioms fHon8_reconstruct
#assert_axioms f0_not_mem
#assert_axioms f0_no_injective_good
#assert_axioms f0_good_card_lt

end Dregg2.Circuit.FriFoldArity
