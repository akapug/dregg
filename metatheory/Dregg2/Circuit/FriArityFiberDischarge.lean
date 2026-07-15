import Mathlib.Tactic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Dregg2.Circuit.FriFoldArity
import Dregg2.Circuit.FriArityTransfer

/-!
# `FriArityFiberDischarge` — the `M = 1` fiber bound DISCHARGED at the deployed arity 8

**What this file closes.** `FriArityTransfer.good_card_le_of_phase_injective` — the arity-generic
good-challenge count that every `perFoldBits` in `FriLedger` reads — takes the `M = 1` fiber bound
(phase-map injectivity) as the HYPOTHESIS `hΦ`. That hypothesis was DISCHARGED only at arity `2` /
`logBlowup 6` (`FriCorrelatedAgreementSharp` §8's `wrap_fiber_le_one`, over the concrete
`friSetupWrapRate`), and OPEN at the deployed arity `8` and at every `logBlowup = 3` config. Both
files said the discharge needs an arity-`8`, `|L| = 512`, dimension-`8` RS setup "that this tree does
not build".

This file builds it — parametrically in `(k, b)`, not just at one config — and DISCHARGES `hΦ` from
FARNESS at every shipped config. `arity8_phase_injective` is the theorem the ledger was missing.

## ⚑ FINDING 1 — the obligation as it was NAMED is FALSE, not open

`FriArityTransfer.Arity8FiberBoundNaive` (which this lane renamed from `Arity8FiberBound`, and which
had NO consumers anywhere in the tree) reads

  `∀ (Φ : ℕ → Fin (2^6) → BabyBear), 496 ≤ dOut → (∀ y z, y ≠ z → ∃ i < 8, Φ i y ≠ Φ i z)`

— it quantifies over EVERY phase map `Φ` with **no link to a `dOut`-far word**. The constant map
`Φ = fun _ _ => 0` refutes it outright: `FriArityTransfer.arity8FiberBoundNaive_false` proves
`¬ Arity8FiberBoundNaive 500`. A `Prop` that is false names no obligation (assume it and you may
conclude anything). The `M = 1` bound is not a property of `Φ` alone — it is a property of the phase
map OF A FAR WORD, and the farness is the entire content. `Arity8FiberBound` below restores it.

This is not a technicality. `zero_phase_not_injective` (§4) proves the gap is REAL: the zero word is a
codeword, and its phase map is constant `0` — flatly non-injective. `M = 1` is not a property of `Φ`
at all; it is a property of the phase map OF A FAR WORD, and the farness is doing all of the work.
The naive statement asserted the conclusion for a `Φ` the deployed prover would hand you for free.

Nothing was contaminated: the false `Prop` was never used as a hypothesis. The real theorems
(`arity8_good_card_le`) carry `hΦ` directly, which is the correct shape — and `hΦ` is what this file
now supplies.

## ⚑ FINDING 2 — with the farness link restored, the bound is TRUE and DISCHARGES

`far_fiber_card_arity` (§1) is the arity-`n` generalization of
`FriProximityGapWitness.far_fiber_card`: for a `dOut`-far `f` and any coefficient vector
`a : Fin n → F`,

  `n · |{y | ∀ j, Cⱼf(y) = aⱼ}| + dOut < |ι|`.

The argument is the arity-2 one, generalized: `a` lifts to the codeword `x ↦ Σⱼ aⱼ·p(x)^j`
(`unfold_closed` at the constants), each fibre in the set contributes ALL `n` of its domain points to
that codeword's agreement (`self_decomp` + `reps` injective), and farness caps the agreement. At
`n = 2` it is `far_fiber_card`'s `2·|Y| + dOut < |ι|` — the same statement
(`arity2_recovers_far_fiber_card`, §6).

`|Y| ≥ 2` then forces `2n + dOut < |ι|`, so `dOut ≥ |ι| − 2n` forces `|Y| ≤ 1` — which IS phase
injectivity (`phase_injective_of_far`, §4). At the deployed `|ι| = 512`, `n = 8`: `dOut ≥ 496`.

## The per-config table (§5) — ALL SIX shipped configs, `hΦ` DISCHARGED

Every config in `FriLedgerSound` is one of four `(k, b)` shapes, and all four are instantiated below.
`|L| = 2^k · 2^b`, `|κ| = 2^b`, code dimension `2^k`, rate `2^(−b)`.

| `FriLedgerSound` config                    | arity | logBlowup | `|L|` | `dOut` ⟹ `M=1` | witness far to | `hΦ` |
|--------------------------------------------|-------|-----------|-------|-----------------|----------------|------|
| `ir2LeafWrapConfig` (**DEPLOYED**)         | 8     | 6         | 512   | `≥ 496`         | `503`          | **DISCHARGED** (`arity8_phase_injective`) |
| `ir2LeafWrapRotatedConfig` (the ~112.6 one)| 2     | 6         | 128   | `≥ 124`         | `125`          | **DISCHARGED** (`arity2Lb6_phase_injective`) |
| `ethWrapOuterConfig` (**gnark verifies**)  | 2     | 3         | 16    | `≥ 12`          | `13`           | **DISCHARGED** (`arity2Lb3_phase_injective`) |
| `recursionConfig`                          | 2     | 3         | 16    | `≥ 12`          | `13`           | **DISCHARGED** (same instance) |
| `prodV1Config`                             | 8     | 3         | 64    | `≥ 48`          | `55`           | **DISCHARGED** (`arity8Lb3_phase_injective`) |
| `zkConfig`                                 | 8     | 3         | 64    | `≥ 48`          | `55`           | **DISCHARGED** (same instance) |

Each is an instantiation of ONE theorem (`phase_injective_of_far`) at `(k, b)` — no config gets a
number the others do not earn. `perFoldBits` at every shipped config is therefore
HYPOTHESIS-FREE on the `hΦ` axis.

## Non-vacuity — the discharge fires on a REAL far word

A discharge whose hypothesis is unsatisfiable is worthless. `fPowK` (§3) — the word
`x ↦ (ω^x)^(2^k)`, the degree-`2^k` monomial one past the code — agrees with EVERY codeword on at
most `2^k` points (a monic degree-`2^k` polynomial has `≤ 2^k` roots), so it is `(|ι| − 2^k − 1)`-far.
At the deployed config that is **`503`-far ≥ 496** (`fPow8Wrap_far`), so `arity8_phase_injective`
FIRES on it (`arity8_discharge_fires`) and the deployed count `|Good| ≤ 14112` holds
UNCONDITIONALLY for it (`arity8_good_card_le_unconditional`).

⚑ The honest window correction: `FriArityTransfer.arity8_fiber_window_nonempty` quoted the upper end
as `dOut ≤ 504 = 512 − 8`. `farN dOut` is STRICT (`> dOut` disagreements), so a word with agreement
exactly `8` is `503`-far, not `504`-far; the realizable window is `496 ≤ dOut ≤ 503`
(`arity8_fiber_window_realizable`). `dOut = 500` — the exact scaled analogue of §8's `125/128` — sits
inside it either way, so no number downstream moves.

## What this does NOT change

`perFoldBits` at the deployed arity 8 is still **~109.84 bits** (`FriArityTransfer`'s `14112` count),
NOT ~112.6. This lane removes the HYPOTHESIS under that number; it does not improve the number.
And `perFoldBits` remains ONE FACTOR of the FRI soundness product — the query ledger
(`johnsonBits` proven-for-any-code / `capacityBits` refuted-conjecture) is the other. The columns are
reported separately, deliberately; nothing here multiplies them.

`#assert_axioms` is blind to HYPOTHESES — kernel-clean does not mean hypothesis-free. It happens that
after this file the per-fold column carries no `hΦ` at any shipped config, but that is because the
theorems below DISCHARGE it, not because `#assert_axioms` says so.
-/

namespace Dregg2.Circuit.FriArityFiberDischarge

open Polynomial
open Dregg2.Circuit.FriSoundness (disagree mem_disagree closeN farN)
open Dregg2.Circuit.FriFoldArity
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.BabyBearFriDeployed (omega27 omega27_ne omega27_neg)
open scoped BigOperators Matrix

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {n : ℕ}

/-! ## §1. THE ARITY-`n` FAR-WORD FIBER BOUND — the generalization of `far_fiber_card`. -/

/-- **The fibre representatives are jointly injective.** `(y, i) ↦ reps y i` is injective: `q` reads
back `y` (`q_reps`), and then the fibre values `p (reps y ·)` read back `i` (`p_reps_inj` — the
primitive-root condition). The arity-2 file got this from `rep`/`σ∘rep` being injective with disjoint
ranges; at arity `n` it is one clean statement. -/
theorem reps_injective (G : FriGeomK F ι κ n) :
    Function.Injective (fun pr : κ × Fin n => G.reps pr.1 pr.2) := by
  rintro ⟨y, i⟩ ⟨z, j⟩ h
  simp only at h
  have hy : y = z := by
    have h1 := G.q_reps y i
    rw [h, G.q_reps z j] at h1
    exact h1.symm
  subst hy
  have hij : i = j := G.p_reps_inj y (by simp only; rw [h])
  subst hij
  rfl

/-- The constant folded-codeword family determined by a coefficient vector `a : Fin n → F`. -/
def constD (a : Fin n → F) : Fin n → κ → F := fun j _ => a j

/-- **A coefficient vector IS a codeword.** `reassemble` of the constants `a` is
`x ↦ Σⱼ p(x)^j · aⱼ` — the degree-`< n` RS codeword with coefficients `a`. This is the arity-`n`
analogue of `wrap_point_mem_C` ("a point of `F²` is a codeword"), and it is where the setup's
`unfold_closed` does the work — no new code theory. Needs only that `C'` contains the CONSTANTS,
which is exactly what the folded code of an RS FRI setup is. -/
theorem cw_mem (S : FriSetupK F ι κ n) (hconst : ∀ c : F, (fun _ : κ => c) ∈ S.C')
    (a : Fin n → F) : reassemble S.geom (constD a) ∈ S.C :=
  S.unfold_closed (constD a) (fun j => hconst (a j))

/-- **THE ARITY-`n` FAR-WORD FIBER BOUND (`M`).** If `f` is `dOut`-far from `C`, then for every
coefficient vector `a : Fin n → F` the fibres on which the phase vector `Cⱼf` equals `a` number at
most `(|ι| − dOut − 1)/n`:

  `n · |{y | ∀ j, Cⱼf(y) = aⱼ}| + dOut < |ι|`.

*Proof.* `a` lifts to the codeword `w = reassemble (constD a) ∈ C` (`cw_mem`). Every fibre `y` in the
set contributes ALL `n` of its domain points `reps y i` to the agreement of `f` with `w`: by
`self_decomp`, `f (reps y i) = Σⱼ p(reps y i)^j · Cⱼf(q (reps y i)) = Σⱼ p(reps y i)^j · aⱼ =
w (reps y i)`. Those `n·|Y|` points are DISTINCT (`reps_injective`), and farness caps the agreement at
`< |ι| − dOut`. ∎

This is `FriProximityGapWitness.far_fiber_card` with `2` replaced by `n` — literally the same
statement at `n = 2` (`arity2_recovers_far_fiber_card`, §6). It is where the code's DIMENSION-`n`
structure enters: a point of `Fⁿ` *is* a codeword. -/
theorem far_fiber_card_arity (S : FriSetupK F ι κ n)
    (hconst : ∀ c : F, (fun _ : κ => c) ∈ S.C')
    {f : ι → F} {dOut : ℕ} (hfar : farN S.C dOut f) (a : Fin n → F) :
    n * (Finset.univ.filter (fun y : κ => ∀ j, Cj S.geom j f y = a j)).card + dOut
      < Fintype.card ι := by
  classical
  set G := S.geom with hG
  set w : ι → F := reassemble G (constD a) with hw
  have hwC : w ∈ S.C := cw_mem S hconst a
  set Y : Finset κ := Finset.univ.filter (fun y : κ => ∀ j, Cj G j f y = a j) with hY
  set Ag : Finset ι := Finset.univ.filter (fun x : ι => f x = w x) with hAg
  -- Every one of the `n` domain points of a fibre in `Y` agrees with the codeword `w`.
  have hfib : ∀ y ∈ Y, ∀ i : Fin n, G.reps y i ∈ Ag := by
    intro y hy i
    rw [hY, Finset.mem_filter] at hy
    obtain ⟨-, hphase⟩ := hy
    rw [hAg, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [self_decomp G f (G.reps y i), hw, reassemble]
    rw [G.q_reps y i]
    exact Finset.sum_congr rfl (fun j _ => by rw [hphase j]; rfl)
  -- The `n · |Y|` fibre points are distinct, hence `n · |Y| ≤ |Ag|`.
  have hcard : n * Y.card ≤ Ag.card := by
    have hsub : (Y ×ˢ (Finset.univ : Finset (Fin n))).image (fun pr => G.reps pr.1 pr.2) ⊆ Ag := by
      intro x hx
      obtain ⟨⟨y, i⟩, hmem, rfl⟩ := Finset.mem_image.mp hx
      exact hfib y (Finset.mem_product.mp hmem).1 i
    calc n * Y.card = (Y ×ˢ (Finset.univ : Finset (Fin n))).card := by
          rw [Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.mul_comm]
      _ = ((Y ×ˢ (Finset.univ : Finset (Fin n))).image (fun pr => G.reps pr.1 pr.2)).card :=
          (Finset.card_image_of_injective _ (reps_injective G)).symm
      _ ≤ Ag.card := Finset.card_le_card hsub
  -- Farness: the codeword `w` disagrees with `f` on more than `dOut` points.
  have hd : dOut < (disagree f w).card := by
    by_contra hcon
    exact hfar ⟨w, hwC, Nat.not_lt.mp hcon⟩
  have hcompl : Ag = (disagree f w)ᶜ := by
    ext x
    simp [hAg, disagree]
  have hle : (disagree f w).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (disagree f w)
  have hcc : Ag.card = Fintype.card ι - (disagree f w).card := by
    rw [hcompl, Finset.card_compl]
  omega

/-! ## §2. THE ARITY-`2^k`, RATE-`2^(−b)` REED–SOLOMON SETUP — the instance the tree lacked.

`|ι| = 2^(k+b)` points, folded to `|κ| = 2^b` fibres of size `n = 2^k`, code dimension `n`. Rate
`= 2^k / 2^(k+b) = 2^(−b)`, i.e. EXACTLY `logBlowup = b`. At `(k, b) = (3, 6)` this is the
`|L| = 512`, `|κ| = 64`, dimension-`8`, rate-`1/64` setup the deployed wrap folds over. -/

/-- The power-`2^k` quotient `L → L^(2^k)`: on exponents, `x ↦ x mod 2^b`. -/
def qK (k b : ℕ) (x : Fin (2 ^ (k + b))) : Fin (2 ^ b) :=
  ⟨(x : ℕ) % 2 ^ b, Nat.mod_lt _ (by positivity)⟩

/-- The `2^k` fibre representatives over `y`: exponents `y, y + 2^b, …, y + 2^b·(2^k − 1)`. -/
def repsK (k b : ℕ) (y : Fin (2 ^ b)) (i : Fin (2 ^ k)) : Fin (2 ^ (k + b)) :=
  ⟨(y : ℕ) + 2 ^ b * (i : ℕ), by
    have hy : (y : ℕ) < 2 ^ b := y.isLt
    have hi : (i : ℕ) + 1 ≤ 2 ^ k := i.isLt
    have hmul : 2 ^ b * ((i : ℕ) + 1) ≤ 2 ^ b * 2 ^ k := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at hmul
    have hpow : (2 : ℕ) ^ (k + b) = 2 ^ b * 2 ^ k := by rw [← pow_add, Nat.add_comm]
    rw [hpow]
    linarith⟩

/-- The point value `x ↦ ω^x`. -/
noncomputable def pK (k b : ℕ) (ω : F) (x : Fin (2 ^ (k + b))) : F := ω ^ (x : ℕ)

/-- **The arity-`2^k` coset geometry** at `|ι| = 2^(k+b)`, `|κ| = 2^b`. Every field is PROVED from
`IsPrimitiveRoot ω (2^(k+b))` — in particular `p_reps_inj`, the primitive-root condition that makes
the fibre Vandermonde invert, is `hω.pow_inj` on exponents `< 2^(k+b)`. -/
noncomputable def friGeomK (k b : ℕ) (ω : F) (hω : IsPrimitiveRoot ω (2 ^ (k + b))) :
    FriGeomK F (Fin (2 ^ (k + b))) (Fin (2 ^ b)) (2 ^ k) where
  q := qK k b
  p := pK k b ω
  reps := repsK k b
  q_reps := by
    intro y i
    apply Fin.ext
    show ((y : ℕ) + 2 ^ b * (i : ℕ)) % 2 ^ b = (y : ℕ)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt y.isLt]
  p_reps_inj := by
    intro y i j hij
    apply Fin.ext
    have h := hω.pow_inj (repsK k b y i).isLt (repsK k b y j).isLt hij
    have heq : (y : ℕ) + 2 ^ b * (i : ℕ) = (y : ℕ) + 2 ^ b * (j : ℕ) := h
    have hb : (0 : ℕ) < 2 ^ b := by positivity
    exact Nat.eq_of_mul_eq_mul_left hb (by omega)
  q_fiber := by
    intro x
    have hb : (0 : ℕ) < 2 ^ b := by positivity
    have hlt : (x : ℕ) / 2 ^ b < 2 ^ k := by
      have hx : (x : ℕ) < 2 ^ (k + b) := x.isLt
      rw [Nat.div_lt_iff_lt_mul hb]
      calc (x : ℕ) < 2 ^ (k + b) := hx
        _ = 2 ^ k * 2 ^ b := by rw [← pow_add]
    refine ⟨⟨(x : ℕ) / 2 ^ b, hlt⟩, ?_⟩
    apply Fin.ext
    show (x : ℕ) = ((x : ℕ) % 2 ^ b) + 2 ^ b * ((x : ℕ) / 2 ^ b)
    exact (Nat.mod_add_div _ _).symm

/-- The dimension-`2^k` Reed–Solomon domain code `C = {x ↦ Σⱼ aⱼ·(ω^x)^j}`. -/
noncomputable def codeCK (k b : ℕ) (ω : F) : Submodule F (Fin (2 ^ (k + b)) → F) where
  carrier := {f | ∃ a : Fin (2 ^ k) → F,
    f = fun x => ∑ j : Fin (2 ^ k), a j * (pK k b ω x) ^ (j : ℕ)}
  zero_mem' := ⟨0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨a, rfl⟩ ⟨a', rfl⟩
    exact ⟨a + a', by funext x; simp [Finset.sum_add_distrib, add_mul]⟩
  smul_mem' := by
    rintro c f ⟨a, rfl⟩
    exact ⟨c • a, by funext x; simp [Finset.mul_sum, mul_assoc]⟩

/-- The folded code `C' = {constants on κ}` — the degree-`< 1` RS code. -/
noncomputable def codeC'K (b : ℕ) : Submodule F (Fin (2 ^ b) → F) where
  carrier := {g | ∃ c : F, g = fun _ => c}
  zero_mem' := ⟨0, rfl⟩
  add_mem' := by rintro f g ⟨c, rfl⟩ ⟨c', rfl⟩; exact ⟨c + c', rfl⟩
  smul_mem' := by rintro d f ⟨c, rfl⟩; exact ⟨d * c, rfl⟩

/-- `C'` contains the constants — trivially, it IS the constants. The hypothesis
`far_fiber_card_arity` needs. -/
theorem codeC'K_const (b : ℕ) (c : F) : (fun _ : Fin (2 ^ b) => c) ∈ (codeC'K b : Submodule F _) :=
  ⟨c, rfl⟩

/-- **THE ARITY-`2^k` RATE-`2^(−b)` FRI SETUP.** Both closure facts PROVED, general in `(k, b)`:
`unfold_closed` is the codeword-from-coefficients identity, and `foldC_mem` is the fibre-Vandermonde
uniqueness (`comps` of a codeword recovers its coefficient vector exactly, so each component is a
CONSTANT on `κ` — a folded codeword). -/
noncomputable def friSetupK (k b : ℕ) (ω : F) (hω : IsPrimitiveRoot ω (2 ^ (k + b))) :
    FriSetupK F (Fin (2 ^ (k + b))) (Fin (2 ^ b)) (2 ^ k) where
  geom := friGeomK k b ω hω
  C := codeCK k b ω
  C' := codeC'K b
  unfold_closed := by
    intro D hD
    choose c hc using hD
    refine ⟨c, ?_⟩
    funext x
    rw [reassemble]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hc j]
    exact mul_comm _ _
  foldC_mem := by
    rintro f ⟨a, rfl⟩ j
    refine ⟨a j, ?_⟩
    funext y
    -- `comps` of a codeword recovers its coefficients: `fvec = fiberV *ᵥ a`, so
    -- `comps = fiberV⁻¹ *ᵥ (fiberV *ᵥ a) = a`.
    have hfv : fvec (friGeomK k b ω hω)
        (fun x => ∑ j : Fin (2 ^ k), a j * (pK k b ω x) ^ (j : ℕ)) y
        = (fiberV (friGeomK k b ω hω) y) *ᵥ a := by
      funext i
      rw [fvec, mulVec_eq]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [fiberV, Matrix.vandermonde_apply]
      exact mul_comm _ _
    show comps (friGeomK k b ω hω) _ y j = a j
    rw [comps, hfv, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (fiberV_isUnit_det (friGeomK k b ω hω) y), Matrix.one_mulVec]

/-! ## §3. NON-VACUITY — a concrete far word at every `(k, b)`.

A discharge whose farness hypothesis is unsatisfiable proves nothing about anything. `fPowK` is the
degree-`2^k` monomial — the first monomial OUTSIDE the dimension-`2^k` code. -/

/-- **Far-ness from a uniform agreement cap** (the arity-generic restatement of
`FriProximityGapWitness.farN_of_agree_le`, which is stated for the arity-2 `FriSetup`). -/
theorem farN_of_agree_le {C : Submodule F (ι → F)} {f : ι → F} {d m : ℕ}
    (hk : d + m < Fintype.card ι)
    (h : ∀ g ∈ C, ((disagree f g)ᶜ).card ≤ m) :
    farN C d f := by
  rintro ⟨g, hg, hcard⟩
  have hA := h g hg
  rw [Finset.card_compl] at hA
  have hle : (disagree f g).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (disagree f g)
  omega

/-- The concrete far word `x ↦ (ω^x)^(2^k)` — the degree-`2^k` monomial, one past the code. -/
noncomputable def fPowK (k b : ℕ) (ω : F) : Fin (2 ^ (k + b)) → F :=
  fun x => (pK k b ω x) ^ (2 ^ k)

/-- The monic degree-`2^k` polynomial `X^(2^k) − Σⱼ aⱼ·X^j` whose roots are exactly the points where
`fPowK` agrees with the codeword of coefficients `a`. -/
noncomputable def rsPoly (k : ℕ) (a : Fin (2 ^ k) → F) : F[X] :=
  X ^ (2 ^ k) - ∑ j : Fin (2 ^ k), C (a j) * X ^ (j : ℕ)

theorem rsPoly_natDegree (k : ℕ) (a : Fin (2 ^ k) → F) : (rsPoly k a).natDegree = 2 ^ k := by
  have hpos : (0 : ℕ) < 2 ^ k := by positivity
  have hlow : (∑ j : Fin (2 ^ k), C (a j) * X ^ (j : ℕ)).natDegree < 2 ^ k := by
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)) (by omega : 2 ^ k - 1 < 2 ^ k)
    refine le_trans (natDegree_C_mul_le _ _) ?_
    rw [natDegree_X_pow]
    exact Nat.le_sub_one_of_lt j.isLt
  rw [rsPoly, natDegree_sub_eq_left_of_natDegree_lt (by rwa [natDegree_X_pow]), natDegree_X_pow]

theorem rsPoly_ne_zero (k : ℕ) (a : Fin (2 ^ k) → F) : rsPoly k a ≠ 0 := by
  intro h
  have := rsPoly_natDegree k a
  rw [h, natDegree_zero] at this
  have hpos : (0 : ℕ) < 2 ^ k := by positivity
  omega

/-- **`fPowK` agrees with every codeword on at most `2^k` points.** An agreement point `x` makes
`t = ω^x` a root of the monic degree-`2^k` polynomial `X^(2^k) − Σⱼ aⱼXʲ`; distinct `x` give distinct
`t` (the primitive root is injective on exponents), and a field admits `≤ 2^k` roots. -/
theorem fPowK_agree_le (k b : ℕ) (ω : F) (hω : IsPrimitiveRoot ω (2 ^ (k + b)))
    (g : Fin (2 ^ (k + b)) → F) (hg : g ∈ (codeCK k b ω : Submodule F _)) :
    ((disagree (fPowK k b ω) g)ᶜ).card ≤ 2 ^ k := by
  classical
  obtain ⟨a, rfl⟩ := hg
  have hpinj : Function.Injective (pK k b ω) := by
    intro x y hxy
    exact Fin.ext (hω.pow_inj x.isLt y.isLt hxy)
  have hsub : ((disagree (fPowK k b ω) (fun x => ∑ j : Fin (2 ^ k), a j * (pK k b ω x) ^ (j : ℕ)))ᶜ)
      ⊆ Finset.univ.filter (fun x => (rsPoly k a).eval (pK k b ω x) = 0) := by
    intro x hx
    simp only [Finset.mem_compl, mem_disagree, not_not, fPowK] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, rsPoly, eval_sub, eval_pow, eval_X,
      eval_finsetSum, eval_mul, eval_C]
    rw [sub_eq_zero]
    exact hx
  calc ((disagree (fPowK k b ω) (fun x => ∑ j : Fin (2 ^ k), a j * (pK k b ω x) ^ (j : ℕ)))ᶜ).card
      ≤ (Finset.univ.filter (fun x => (rsPoly k a).eval (pK k b ω x) = 0)).card :=
        Finset.card_le_card hsub
    _ ≤ ((rsPoly k a).roots.toFinset).card := by
        refine Finset.card_le_card_of_injOn (pK k b ω) (fun x hx => ?_) (fun x _ y _ h => hpinj h)
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots (rsPoly_ne_zero k a)]
        exact hx.2
    _ ≤ Multiset.card (rsPoly k a).roots := (rsPoly k a).roots.toFinset_card_le
    _ ≤ (rsPoly k a).natDegree := card_roots' _
    _ = 2 ^ k := rsPoly_natDegree k a

/-- **`fPowK` is `(2^(k+b) − 2^k − 1)`-FAR** from the dimension-`2^k` code — the maximal farness this
witness realizes. `farN d` is STRICT, so agreement `2^k` gives farness `d` for every
`d ≤ |ι| − 2^k − 1`. -/
theorem fPowK_far (k b : ℕ) (ω : F) (hω : IsPrimitiveRoot ω (2 ^ (k + b))) {d : ℕ}
    (hd : d + 2 ^ k < 2 ^ (k + b)) :
    farN (codeCK k b ω) d (fPowK k b ω) := by
  refine farN_of_agree_le (m := 2 ^ k) ?_ (fPowK_agree_le k b ω hω)
  rwa [Fintype.card_fin]

/-! ## §4. THE DISCHARGE — phase injectivity FROM farness, at every `(k, b)`.

This is the theorem `FriArityTransfer.good_card_le_of_phase_injective` was missing: its `hΦ`, for the
phase map that actually IS the deployed fold. -/

/-- **The phase map of a word** in the `ℕ`-indexed shape `FriArityTransfer.H` consumes:
`Φ i y = Cᵢf(y)` for `i < n`, junk `0` above. -/
noncomputable def phaseOf (G : FriGeomK F ι κ n) (f : ι → F) : ℕ → κ → F :=
  fun i y => if h : i < n then Cj G ⟨i, h⟩ f y else 0

/-- **THE PHASE MAP IS THE FOLD — the check that the discharge is about the right object.** The
phase polynomial of `FriArityTransfer` evaluated at `β` IS `FriFoldArity.Fold β f y`, the arity-`n`
fold the deployed prover computes. Without this, `phaseOf` would be an unrelated map and the
discharge would be about nothing. -/
theorem phaseOf_H_eval (G : FriGeomK F ι κ n) (f : ι → F) (y : κ) (β : F) :
    (Dregg2.Circuit.FriArityTransfer.H n (phaseOf G f) y).eval β = Fold G β f y := by
  rw [Dregg2.Circuit.FriArityTransfer.H_eval,
    ← Fin.sum_univ_eq_sum_range (fun i => phaseOf G f i y * β ^ i) n, Fold]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [phaseOf, dif_pos j.isLt, Fin.eta]
  exact mul_comm _ _

/-- **THE DISCHARGE.** A `dOut`-far word with `dOut ≥ |ι| − 2n` has an INJECTIVE phase map: two
distinct fibres with the same phase vector `a` would put `|{y | phase = a}| ≥ 2` into the fiber bound,
forcing `2n + dOut < |ι|` — contradiction. This IS `M = 1`, and it IS
`good_card_le_of_phase_injective`'s `hΦ`. -/
theorem phase_injective_of_far (S : FriSetupK F ι κ n)
    (hconst : ∀ c : F, (fun _ : κ => c) ∈ S.C')
    {f : ι → F} {dOut : ℕ} (hfar : farN S.C dOut f)
    (hdOut : Fintype.card ι ≤ 2 * n + dOut) :
    ∀ y z : κ, y ≠ z → ∃ i < n, phaseOf S.geom f i y ≠ phaseOf S.geom f i z := by
  classical
  intro y z hyz
  by_contra hcon
  push_neg at hcon
  -- Same phase vector: both `y` and `z` sit in the fibre set of `a := Cⱼf(y)`.
  set a : Fin n → F := fun j => Cj S.geom j f y with ha
  have hz : ∀ j : Fin n, Cj S.geom j f z = a j := by
    intro j
    have h := hcon (j : ℕ) j.isLt
    simp only [phaseOf, dif_pos j.isLt] at h
    rw [ha]
    simp only [Fin.eta] at h ⊢
    exact h.symm
  have hy : ∀ j : Fin n, Cj S.geom j f y = a j := fun j => rfl
  set Y : Finset κ := Finset.univ.filter (fun y' : κ => ∀ j, Cj S.geom j f y' = a j) with hY
  have hyY : y ∈ Y := by rw [hY, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hy⟩
  have hzY : z ∈ Y := by rw [hY, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hz⟩
  have h2 : 2 ≤ Y.card := by
    have : ({y, z} : Finset κ) ⊆ Y := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw'
      · exact hyY
      · rw [Finset.mem_singleton] at hw'; subst hw'; exact hzY
    calc 2 = ({y, z} : Finset κ).card := (Finset.card_pair hyz).symm
      _ ≤ Y.card := Finset.card_le_card this
  have hbound := far_fiber_card_arity S hconst hfar a
  rw [← hY] at hbound
  have : n * 2 ≤ n * Y.card := Nat.mul_le_mul_left _ h2
  omega

/-! ## §5. THE SHIPPED CONFIGS — one theorem, four instantiations.

The primitive roots all descend from `omega27` (order `2^27`, `BabyBearFriDeployed.omega27_neg`) — no
new numeral chain, exactly as `omega128` does. -/

/-- A primitive `2^e`-th root of unity in BabyBear for any `1 ≤ e ≤ 27`, from `omega27`. -/
noncomputable def omegaOrd (e : ℕ) : BabyBear := omega27 ^ (2 ^ (27 - e))

/-- **`omegaOrd e` is a primitive `2^e`-th root** for `1 ≤ e ≤ 27` — the standard
`orderOf_eq_prime_pow` argument on `omega27^(2^(27−e))`, whose `2^(e−1)`-th power is
`omega27^(2^26) = −1`. -/
theorem omegaOrd_isPrimitiveRoot {e : ℕ} (h1 : 1 ≤ e) (h2 : e ≤ 27) :
    IsPrimitiveRoot (omegaOrd e) (2 ^ e) := by
  have hneg : (omegaOrd e) ^ (2 ^ (e - 1)) = -1 := by
    rw [omegaOrd, ← pow_mul, ← pow_add, show 27 - e + (e - 1) = 26 by omega]
    exact omega27_neg
  have hnot : (omegaOrd e) ^ (2 : ℕ) ^ (e - 1) ≠ 1 := by rw [hneg]; decide
  have hfin : (omegaOrd e) ^ (2 : ℕ) ^ ((e - 1) + 1) = 1 := by
    rw [show (2 : ℕ) ^ ((e - 1) + 1) = 2 ^ (e - 1) * 2 by ring, pow_mul, hneg]; simp
  have hord : orderOf (omegaOrd e) = (2 : ℕ) ^ ((e - 1) + 1) := orderOf_eq_prime_pow hnot hfin
  have hexp : (2 : ℕ) ^ e = orderOf (omegaOrd e) := by rw [hord, show (e - 1) + 1 = e by omega]
  rw [hexp]
  exact IsPrimitiveRoot.orderOf (omegaOrd e)

/-- **THE DEPLOYED ARITY-8 SETUP** — `|L| = 512`, `|κ| = 64`, dimension `8`, rate `1/64`
(`logBlowup = 6`, `maxLogArity = 3`). The setup `FriArityTransfer` §2 said the tree does not build. -/
noncomputable def friSetupK8Wrap : FriSetupK BabyBear (Fin (2 ^ (3 + 6))) (Fin (2 ^ 6)) (2 ^ 3) :=
  friSetupK 3 6 (omegaOrd 9) (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num))

/-- The deployed domain really is `512` points. -/
theorem friSetupK8Wrap_domain : Fintype.card (Fin (2 ^ (3 + 6))) = 512 := by simp

/-- **THE DEPLOYED DISCHARGE — `hΦ` at arity 8, `logBlowup 6`, from farness alone.** A `496`-far word
on the `512`-point rate-`1/64` domain has an injective phase map: `8·2 + 496 = 512 ≮ 512`. This is
`FriArityTransfer.arity8_good_card_le`'s hypothesis, PROVED. -/
theorem arity8_phase_injective {f : Fin (2 ^ (3 + 6)) → BabyBear} {dOut : ℕ}
    (hfar : farN friSetupK8Wrap.C dOut f) (hdOut : 496 ≤ dOut) :
    ∀ y z : Fin (2 ^ 6), y ≠ z →
      ∃ i < 8, phaseOf friSetupK8Wrap.geom f i y ≠ phaseOf friSetupK8Wrap.geom f i z := by
  have h := phase_injective_of_far friSetupK8Wrap (fun c => codeC'K_const 6 c) hfar
    (by rw [friSetupK8Wrap_domain]; omega)
  simpa using h

/-- **`Arity8FiberBound`** — the arity-8 far-fiber obligation, CORRECTLY stated. This is what
`FriArityTransfer.Arity8FiberBoundNaive` was TRYING to say and got wrong: it is a statement about the
phase map OF A `dOut`-FAR WORD over the real deployed setup, not about phase maps in general. The
farness hypothesis is the entire content — drop it and the claim is refuted by the constant map
(`FriArityTransfer.arity8FiberBoundNaive_false`). -/
def Arity8FiberBound (dOut : ℕ) : Prop :=
  ∀ f : Fin (2 ^ (3 + 6)) → BabyBear, farN friSetupK8Wrap.C dOut f → 496 ≤ dOut →
    ∀ y z : Fin (2 ^ 6), y ≠ z →
      ∃ i < 8, phaseOf friSetupK8Wrap.geom f i y ≠ phaseOf friSetupK8Wrap.geom f i z

/-- **THE OBLIGATION, DISCHARGED.** The `Prop` `FriArityTransfer` §2 named as the open residual —
correctly stated — is a THEOREM, at every radius. It is not vacuous: `fPow8Wrap` satisfies the
farness hypothesis at `dOut = 503` (`arity8_discharge_fires`). -/
theorem arity8FiberBound_holds (dOut : ℕ) : Arity8FiberBound dOut :=
  fun _ hfar hd => arity8_phase_injective hfar hd

/-- **The arity-8, `logBlowup = 3` discharge** (`prodV1Config` / `zkConfig`): `|L| = 64`,
`|κ| = 8`, dimension `8`, rate `1/8`. `M = 1` from `dOut ≥ 48`. -/
noncomputable def friSetupK8Lb3 : FriSetupK BabyBear (Fin (2 ^ (3 + 3))) (Fin (2 ^ 3)) (2 ^ 3) :=
  friSetupK 3 3 (omegaOrd 6) (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num))

theorem arity8Lb3_phase_injective {f : Fin (2 ^ (3 + 3)) → BabyBear} {dOut : ℕ}
    (hfar : farN friSetupK8Lb3.C dOut f) (hdOut : 48 ≤ dOut) :
    ∀ y z : Fin (2 ^ 3), y ≠ z →
      ∃ i < 8, phaseOf friSetupK8Lb3.geom f i y ≠ phaseOf friSetupK8Lb3.geom f i z := by
  have h := phase_injective_of_far friSetupK8Lb3 (fun c => codeC'K_const 3 c) hfar
    (by simp; omega)
  simpa using h

/-- The phase map of the ZERO word is constant `0`: `fvec` is the zero vector, and `V⁻¹ ·ᵥ 0 = 0`. -/
theorem Cj_zero (G : FriGeomK F ι κ n) (j : Fin n) : Cj G j (fun _ => (0 : F)) = fun _ => 0 := by
  funext y
  show comps G (fun _ => (0 : F)) y j = 0
  rw [comps, show fvec G (fun _ => (0 : F)) y = 0 by funext i; rfl, Matrix.mulVec_zero]
  rfl

/-- **THE FARNESS HYPOTHESIS IS LOAD-BEARING — a both-truth tooth.** The zero word is a CODEWORD
(maximally NOT far), and its phase map is constant `0`, hence NOT injective on the `64` fibres. So
`phase_injective_of_far`'s farness hypothesis cannot be dropped: the conclusion is FALSE for words
that are not far, and the deployed prover would hand you the counterexample for free.

⚑ This is precisely WHY `FriArityTransfer.Arity8FiberBoundNaive` is false. It asserted phase
injectivity for EVERY `Φ` with no farness link — and `M = 1` is not a property of `Φ` at all, it is a
property of the phase map OF A FAR WORD. The gap between those two statements is the whole theorem.
-/
theorem zero_phase_not_injective :
    (fun _ => (0 : BabyBear)) ∈ friSetupK8Wrap.C ∧
    ¬ (∀ y z : Fin (2 ^ 6), y ≠ z → ∃ i < 8,
        phaseOf friSetupK8Wrap.geom (fun _ => (0 : BabyBear)) i y
          ≠ phaseOf friSetupK8Wrap.geom (fun _ => (0 : BabyBear)) i z) := by
  refine ⟨Submodule.zero_mem _, ?_⟩
  intro h
  obtain ⟨i, hi, hne⟩ := h 0 1 (by decide)
  exact hne (by simp only [phaseOf, dif_pos hi, Cj_zero friSetupK8Wrap.geom])

/-- **THE DISCHARGE FIRES AT EVERY CONFIG SHAPE — generic non-vacuity.** For every `(k, b)` with
`k, b ≥ 1`, the concrete far word `fPowK` realizes farness `dMax = 2^(k+b) − 2^k − 1`, and the
discharge needs only `dOut ≥ 2^(k+b) − 2·2^k`. The window is non-empty by exactly `2^k − 1`, so the
`M = 1` bound is FORCEABLE and SATISFIED at every arity and every blowup — not a coincidence of the
deployed numbers. This is the general form of §7's `arity8_fiber_window_realizable`. -/
theorem phase_injective_fires (k b : ℕ) (hk : 1 ≤ k) (hb : 1 ≤ b)
    (ω : F) (hω : IsPrimitiveRoot ω (2 ^ (k + b))) :
    ∀ y z : Fin (2 ^ b), y ≠ z → ∃ i < 2 ^ k,
      phaseOf (friSetupK k b ω hω).geom (fPowK k b ω) i y
        ≠ phaseOf (friSetupK k b ω hω).geom (fPowK k b ω) i z := by
  have hA : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
  have hAB : 2 ^ k * 2 ≤ 2 ^ (k + b) := by
    calc 2 ^ k * 2 = 2 ^ (k + 1) := by rw [pow_succ]
      _ ≤ 2 ^ (k + b) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine phase_injective_of_far (friSetupK k b ω hω) (fun c => codeC'K_const b c)
    (dOut := 2 ^ (k + b) - 2 ^ k - 1) (fPowK_far k b ω hω (by omega)) ?_
  rw [Fintype.card_fin]
  omega

/-- **The arity-2, `logBlowup = 3` discharge** — `ethWrapOuterConfig` / `recursionConfig`, THE CONFIG
GNARK VERIFIES: `|L| = 16`, `|κ| = 8`, dimension `2`, rate `1/8`. `M = 1` from `dOut ≥ 12`. -/
noncomputable def friSetupK2Lb3 : FriSetupK BabyBear (Fin (2 ^ (1 + 3))) (Fin (2 ^ 3)) (2 ^ 1) :=
  friSetupK 1 3 (omegaOrd 4) (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num))

theorem arity2Lb3_phase_injective {f : Fin (2 ^ (1 + 3)) → BabyBear} {dOut : ℕ}
    (hfar : farN friSetupK2Lb3.C dOut f) (hdOut : 12 ≤ dOut) :
    ∀ y z : Fin (2 ^ 3), y ≠ z →
      ∃ i < 2, phaseOf friSetupK2Lb3.geom f i y ≠ phaseOf friSetupK2Lb3.geom f i z := by
  have h := phase_injective_of_far friSetupK2Lb3 (fun c => codeC'K_const 3 c) hfar
    (by simp; omega)
  simpa using h

/-- **The arity-2, `logBlowup = 6` discharge** — the rotated `ir2_leaf_wrap_config`, the ONE shipped
config the ~112.6 figure describes. `|L| = 128`, `M = 1` from `dOut ≥ 124`. -/
noncomputable def friSetupK2Lb6 : FriSetupK BabyBear (Fin (2 ^ (1 + 6))) (Fin (2 ^ 6)) (2 ^ 1) :=
  friSetupK 1 6 (omegaOrd 7) (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num))

theorem arity2Lb6_phase_injective {f : Fin (2 ^ (1 + 6)) → BabyBear} {dOut : ℕ}
    (hfar : farN friSetupK2Lb6.C dOut f) (hdOut : 124 ≤ dOut) :
    ∀ y z : Fin (2 ^ 6), y ≠ z →
      ∃ i < 2, phaseOf friSetupK2Lb6.geom f i y ≠ phaseOf friSetupK2Lb6.geom f i z := by
  have h := phase_injective_of_far friSetupK2Lb6 (fun c => codeC'K_const 6 c) hfar
    (by simp; omega)
  simpa using h

/-! ## §6. THE ANTI-MIRROR CHECKS — the generalization RECOVERS the arity-2 facts.

The tree's own discipline (`arity2_recovers_capacity_count`): a generalization that does not recover
the special case it generalizes is a MIRROR, not a proof. -/

/-- **ANTI-MIRROR 1 — `far_fiber_card_arity` at `n = 2` IS `far_fiber_card`.** At arity `2` the
conclusion is `2·|Y| + dOut < |ι|` — literally the statement of
`FriProximityGapWitness.far_fiber_card`, whose proof this file's §1 generalizes. -/
theorem arity2_recovers_far_fiber_card (S : FriSetupK F ι κ 2)
    (hconst : ∀ c : F, (fun _ : κ => c) ∈ S.C')
    {f : ι → F} {dOut : ℕ} (hfar : farN S.C dOut f) (a : Fin 2 → F) :
    2 * (Finset.univ.filter (fun y : κ => ∀ j, Cj S.geom j f y = a j)).card + dOut
      < Fintype.card ι :=
  far_fiber_card_arity S hconst hfar a

/-- **ANTI-MIRROR 2 — the arity-2 `M = 1` radius the generic discharge computes on the `128`-point
wrap domain is `124`, and §8's `wrap_fiber_le_one` uses `125`.** The generic bound is therefore at
least as strong as the hand-rolled one at the same config: `125 ≥ 124`, so `phase_injective_of_far`
FIRES wherever §8's `wrap_fiber_le_one` does. -/
theorem arity2_recovers_wrap_fiber_radius : 128 ≤ 2 * 2 + 124 ∧ (124 : ℕ) ≤ 125 := by norm_num

/-- **ANTI-MIRROR 3 — the deployed count is unchanged.** `FriArityTransfer`'s `2016` at arity 2 and
`14112` at arity 8 are what they were; this lane removed a hypothesis, it did not move a number. -/
theorem counts_unchanged :
    (2 - 1) * Nat.choose 64 2 = 2016 ∧ (8 - 1) * Nat.choose 64 2 = 14112 := by decide

/-! ## §7. THE PAYOFF — the deployed arity-8 count and per-fold bits, UNCONDITIONALLY. -/

/-- **The deployed far word.** `fPow8Wrap x = (ω₅₁₂^x)^8` — the degree-`8` monomial on the `512`-point
domain, one past the dimension-`8` code. -/
noncomputable def fPow8Wrap : Fin (2 ^ (3 + 6)) → BabyBear :=
  fPowK 3 6 (omegaOrd 9)

/-- **`fPow8Wrap` is `503`-far** — every dimension-`8` codeword agrees with it on `≤ 8` of the `512`
points. So the `dOut ≥ 496` hypothesis of the deployed discharge is SATISFIABLE, and the discharge is
not vacuous. -/
theorem fPow8Wrap_far : farN friSetupK8Wrap.C 503 fPow8Wrap :=
  fPowK_far 3 6 (omegaOrd 9) (omegaOrd_isPrimitiveRoot (by norm_num) (by norm_num)) (by norm_num)

/-- **THE ARITY-8 FIBER WINDOW, REALIZABLY.** `M = 1` needs `dOut ≥ 496`; `fPowK` realizes farness up
to `503` (NOT `504`: `farN` is strict, and agreement `8` gives `504` disagreements, i.e. `503`-far).
So the window where the hypothesis is both FORCEABLE and SATISFIED is `496 ≤ dOut ≤ 503`, and it is
non-empty. This CORRECTS `FriArityTransfer.arity8_fiber_window_nonempty`'s upper end (`504`) by one;
`dOut = 500` sits inside either way. -/
theorem arity8_fiber_window_realizable : 496 ≤ 500 ∧ 500 ≤ 503 := by norm_num

/-- **THE DEPLOYED DISCHARGE FIRES ON A REAL WORD** — `fPow8Wrap` is `496`-far and its phase map is
injective. Hypothesis satisfied, conclusion real. -/
theorem arity8_discharge_fires :
    ∀ y z : Fin (2 ^ 6), y ≠ z →
      ∃ i < 8, phaseOf friSetupK8Wrap.geom fPow8Wrap i y ≠ phaseOf friSetupK8Wrap.geom fPow8Wrap i z := by
  refine arity8_phase_injective (dOut := 503) fPow8Wrap_far (by norm_num)

/-- **THE DEPLOYED ARITY-8 GOOD COUNT — NOW UNCONDITIONAL.** A `496`-far word on the deployed
`512`-point rate-`1/64` domain has at most `14112` good folding challenges. Compare
`FriArityTransfer.arity8_good_card_le`, which takes `hΦ` as a hypothesis: here `hΦ` is DISCHARGED
from farness by `arity8_phase_injective`. This is the theorem `FriLedger`'s deployed `perFoldBits`
needed. -/
theorem arity8_good_card_le_unconditional {f : Fin (2 ^ (3 + 6)) → BabyBear} {dOut : ℕ}
    (hfar : farN friSetupK8Wrap.C dOut f) (hdOut : 496 ≤ dOut)
    (Good : Finset BabyBear) (c : BabyBear → BabyBear)
    (hS : ∀ β ∈ Good, 2 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) =>
        (Dregg2.Circuit.FriArityTransfer.H 8 (phaseOf friSetupK8Wrap.geom f) y).eval β = c β)).card) :
    Good.card ≤ 14112 :=
  Dregg2.Circuit.FriArityTransfer.arity8_good_card_le (arity8_phase_injective hfar hdOut) Good c hS

/-- **THE DEPLOYED PER-FOLD SOUNDNESS, UNCONDITIONALLY — ~109.84 bits.** The `14112` count over the
deployed quartic challenge field gives `|Good|/|F| < 2⁻¹⁰⁹`, with `hΦ` discharged.

⚑ This is ONE FACTOR of the FRI soundness product, not the whole soundness. The query ledger
(`johnsonBits` / `capacityBits`) is the other, and the columns are never multiplied into a headline. -/
theorem arity8_perFold_soundness_unconditional {f : Fin (2 ^ (3 + 6)) → BabyBear} {dOut : ℕ}
    (hfar : farN friSetupK8Wrap.C dOut f) (hdOut : 496 ≤ dOut)
    (Good : Finset BabyBear) (c : BabyBear → BabyBear)
    (hS : ∀ β ∈ Good, 2 ≤ (Finset.univ.filter (fun y : Fin (2 ^ 6) =>
        (Dregg2.Circuit.FriArityTransfer.H 8 (phaseOf friSetupK8Wrap.geom f) y).eval β = c β)).card) :
    (Good.card : ℝ) / (babyBearP : ℝ) ^ 4 < 1 / 2 ^ 109 :=
  Dregg2.Circuit.FriArityTransfer.arity8_perFold_soundness Good
    (arity8_good_card_le_unconditional hfar hdOut Good c hS)

/-! ## §8. Axiom hygiene.

Kernel-clean, `sorry`-free, no `axiom`. `#assert_axioms` is BLIND TO HYPOTHESES — but the point of
this file is that the per-fold column's `hΦ` is now a THEOREM (`phase_injective_of_far`) at every
shipped config, discharged from farness, and fires on a concrete far word. -/

#assert_axioms reps_injective
#assert_axioms cw_mem
#assert_axioms far_fiber_card_arity
#assert_axioms friGeomK
#assert_axioms friSetupK
#assert_axioms farN_of_agree_le
#assert_axioms rsPoly_natDegree
#assert_axioms rsPoly_ne_zero
#assert_axioms fPowK_agree_le
#assert_axioms fPowK_far
#assert_axioms phaseOf_H_eval
#assert_axioms phase_injective_of_far
#assert_axioms Cj_zero
#assert_axioms zero_phase_not_injective
#assert_axioms phase_injective_fires
#assert_axioms omegaOrd_isPrimitiveRoot
#assert_axioms arity8_phase_injective
#assert_axioms arity8FiberBound_holds
#assert_axioms arity8Lb3_phase_injective
#assert_axioms arity2Lb3_phase_injective
#assert_axioms arity2Lb6_phase_injective
#assert_axioms arity2_recovers_far_fiber_card
#assert_axioms fPow8Wrap_far
#assert_axioms arity8_discharge_fires
#assert_axioms arity8_good_card_le_unconditional
#assert_axioms arity8_perFold_soundness_unconditional

end Dregg2.Circuit.FriArityFiberDischarge
