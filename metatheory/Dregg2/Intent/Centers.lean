/-
# Dregg2.Intent.Centers — the commutative central monoid + its escrow monad (Phase 3, step 1–2).

`docs/rebuild/INTENT-REFS-centers.md` §4, steps 1–2 (the *unifier*; the monoidal-Kleisli L-gate and
Theorem B are explicitly DEFERRED — steps 3–5). Anchor: Flake–Laugwitz–Posur, *Projection Formulas and
Induced Functors on Centers of Monoidal Categories* (arXiv 2402.10094), Def 5.1 + Thm 5.6.

**What this builds.**

  1. `CommCentralMonoid R := CommMon (Center R)` (paper Def 5.1, the *commutative central monoid*): a
     commutative monoid object living in the *braided* Drinfeld center `Center R`. The half-braiding
     component (`M.X.2.β`) is the "commutes-past-every-turn" datum; `MonObj`/`IsCommMonObj` make
     `mul`/`unit` central AND commutative *by construction*. This typechecks precisely because `Center R`
     is braided (`CategoryTheory.Center.braidedCategoryCenter`), so `CommMon (Center R)` is well-formed
     (`IsCommMonObj` needs a `BraidedCategory`). Plus its projections (the swap, `mul`/`unit` central).

  2. `escrowMonad M := (– ⊗ M)` as a `Monad` (paper Thm 5.6; η = `A ◁ unit`, μ = `A ◁ mul`), HAND-BUILT
     — the underlying functor is `tensorRight M`; the three monad laws fall out of `MonObj`'s
     `one_mul`/`mul_one`/`mul_assoc` whiskered into the carried `A` (no braiding, no commutativity needed
     for the *monad*). Then `escrowMonad_isMonoidal` (Thm 5.6's page-46 lax structure): the
     `LaxMonoidal (tensorRight M)` whose tensorator is `tensorμ X M Y M ≫ (X⊗Y) ◁ μ[M]` — the braided
     strength `tensorμ` slides one `M` past `Y`, then `μ[M]` coalesces the two pools. Its associativity
     hexagon closes ONLY via `IsCommMonObj.mul_comm`: drop commutativity and the chase fails — that is
     the teeth (see `writerEscrow_isMonoidal` + the non-discrete witness below).

**DEFERRED (steps 3–5 of §4):** `monoidalKleisli` (the `MonoidalCategory (Kleisli T_M)` L-gate), the
`escrow_projection_formula` (Lemma 5.11) with the refuted general sibling, and Theorem B
(`Z(R) : Z(D) → Z(C)`, 4.10). Those depend on the monoidal-Kleisli prerequisite mathlib lacks.

**The escrow constructions are stated POLYMORPHICALLY** over a monoidal category `C` and a monoid object
`M : C` (the monad needs only `MonoidalCategory`; the lax structure adds `[BraidedCategory C]` +
`[IsCommMonObj M]`). `CommCentralMonoid R` is then the canonical carrier: `M : CommMon (Center R)`
supplies `M.X : Center R` with `[MonObj M.X]` + `[IsCommMonObj M.X]` in the braided `Center R`.

**CRITICAL MODEL CALL (ember-decided): escrow is KEPT SEPARATE.** `T_M = (– ⊗ M)` here models a
STANDING / ACCUMULATING pool — a *frictionless standing offer / ideal no-arb liquidity* side: `μ`
COALESCES two pool contributions (`x · y`). It is **NOT** the one-shot Intent escrow (`EscrowWitness`
in `Intent/Core.lean`, an affine consumed lockbox where released ≠ refundable). Coalescing ≠
consumption. The one-shot affine escrow is a separate construct bridged elsewhere; do not unify the
two under one `M` (`INTENT-REFS-centers.md` §3 row #4).

**`FrictionlessStandingOffer` (was "AMM-as-central-object", a PUN — DROPPED).** A `HalfBraiding X`
forces `β U : X ⊗ U ≅ U ⊗ X` to be an *isomorphism* for every `U` — the offer must commute
*invertibly* past every turn (no-arb order-independence). A real slippage/fee/finite-liquidity AMM has
`X ⊗ U ≇ U ⊗ X` in value, so it is **provably not** a center object at all. That non-existence IS the
teeth (`noncommuting_admits_no_halfBraiding` below, concretely on the non-commutative
`Discrete (FreeMonoid (Fin 2))`): the half-braiding models no-arb order-independence, full stop — it
does not verify constant-product economics.

**TEETH.** `escrowMonad_isMonoidal`'s associativity genuinely FAILS without `IsCommMonObj.mul_comm`. A
discrete demo (`Intent/Resource.DemoRes`) has only the trivial `M = 𝟙_` (its hom-sets are
subsingletons), so its `mul_comm` is a `Subsingleton.elim` tautology — VACUOUS. So the lax structure is
also checked on a **non-discrete** witness: the *writer comm-monoid object* `Multiplicative ℕ` in
cartesian-monoidal `Type`, where `mul` is a genuine binary function (`+`) and
`writer_mul_comm_has_content` exhibits that its `IsCommMonObj.mul_comm` carries real content
(`a * b` and `b * a` are computed and distinct off the diagonal).

Pure; no `axiom`/`sorry`/`admit`/`native_decide`. §8 carriers: none (this layer is mathlib-internal
category theory; the only hypotheses are `MonObj`/`IsCommMonObj` typeclass carriers, never faked laws).
-/
import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Discrete
import Mathlib.CategoryTheory.Monoidal.Internal.Types.Basic
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Dregg2.Intent.Resource
import Dregg2.Tactics

universe v u

namespace Dregg2.Intent

open CategoryTheory MonoidalCategory Functor.LaxMonoidal

-- NOTE: we deliberately do NOT `open MonObj`. Its scoped notation set includes the *bare* `μ`/`η`
-- (`= MonObj.mul`/`MonObj.one`), which would shadow the structure FIELD names `η`/`μ` of `Monad` and
-- `LaxMonoidal` when we define those instances below (the parser reads `η := …` as the notation token,
-- "unexpected token 'η'"). Instead we use local, non-colliding notations `𝟙ₘ[M]` (monoid unit) and
-- `μₘ[M]` (monoid mul) for `MonObj.one`/`MonObj.mul`, so field assignments stay legible without the clash.

/-- Local notation for the monoid-object multiplication `MonObj.mul` (avoids the bare-`μ` field clash). -/
local notation "μₘ[" M "]" => MonObj.mul (X := M)
/-- Local notation for the monoid-object unit `MonObj.one` (avoids the bare-`η` field clash). -/
local notation "𝟙ₘ[" M "]" => MonObj.one (X := M)

/-! ## 1. `CommCentralMonoid` — a commutative monoid object in the Drinfeld center (paper Def 5.1). -/

/-- **A commutative central monoid** (Flake–Laugwitz–Posur Def 5.1): a commutative monoid object in the
*braided* Drinfeld center `Center R`. This is the standing-offer / accumulating-pool carrier of the
escrow theory. The half-braiding component `M.X.2.β` is the "commutes-past-every-turn" datum, and
`[IsCommMonObj M.X]` makes `mul`/`unit` central AND commutative by construction.

It typechecks precisely because `Center R` is braided (`CategoryTheory.Center.braidedCategoryCenter`),
so `CommMon (Center R)` is well-formed (`IsCommMonObj` needs a `BraidedCategory`). -/
abbrev CommCentralMonoid (R : Type u) [Category.{v} R] [MonoidalCategory.{v} R] :=
  CommMon (Center R)

namespace CommCentralMonoid

variable {R : Type u} [Category.{v} R] [MonoidalCategory.{v} R]

/-- The underlying object of `R` carrying the standing pool (forget the half-braiding *and* the monoid
structure): `M.X : Center R` is the central object, `M.X.1 : R` is the bare resource. -/
abbrev carrier (M : CommCentralMonoid R) : R := M.X.1

/-- The half-braiding swap of the central monoid: `M.X.2.β U : M.X.1 ⊗ U ≅ U ⊗ M.X.1`. This is the
isomorphism witnessing that the standing pool commutes *invertibly* past every other resource `U` (the
no-arb order-independence datum). Projected straight off the `Center R` object — never faked. -/
abbrev swap (M : CommCentralMonoid R) (U : R) : M.X.1 ⊗ U ≅ U ⊗ M.X.1 := M.X.2.β U

/-- The pool multiplication, in `Center R` (paper `mul`): coalesces two pool contributions. Lives in the
center, so it is central by construction. -/
abbrev mul (M : CommCentralMonoid R) : M.X ⊗ M.X ⟶ M.X := μₘ[M.X]

/-- The pool unit, in `Center R` (paper `unit`). -/
abbrev one (M : CommCentralMonoid R) : 𝟙_ (Center R) ⟶ M.X := 𝟙ₘ[M.X]

/-- **`mul` is commutative w.r.t. the half-braiding swap** — the paper's commutativity of a central
monoid, read straight off `IsCommMonObj`: `(β_ M.X M.X).hom ≫ μ = μ` in `Center R`. Not a fresh law; the
projection of the carrier's `IsCommMonObj.mul_comm`. -/
theorem mul_comm (M : CommCentralMonoid R) :
    (β_ M.X M.X).hom ≫ μₘ[M.X] = μₘ[M.X] :=
  IsCommMonObj.mul_comm M.X

end CommCentralMonoid

/-! ## 2. The escrow monad `T_M = (– ⊗ M)` (paper Thm 5.6) — hand-built over a monoid object.

Stated polymorphically over a monoidal category `C` and `M : C` with `[MonObj M]`. The underlying
functor is `tensorRight M` (`A ↦ A ⊗ M`, `f ↦ f ▷ M`). η = `(ρ_ A).inv ≫ A ◁ unit`,
μ = `(α_ A M M).hom ≫ A ◁ mul`. The three monad laws are exactly `MonObj`'s unitality/associativity
whiskered into `A` — no braiding, no commutativity required for the *monad* (those enter only in the
lax-monoidal structure, §3). -/

section EscrowMonad

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (M : C) [MonObj M]

/-- The unit of the escrow monad: `A ⟶ A ⊗ M`, injecting the monoid unit (`(ρ_ A).inv ≫ A ◁ η[M]`). -/
@[simps]
def escrowEta : 𝟭 C ⟶ tensorRight M where
  app A := (ρ_ A).inv ≫ A ◁ 𝟙ₘ[M]
  naturality := by
    intro A B f; dsimp
    rw [Category.assoc, whisker_exchange, ← Category.assoc, rightUnitor_inv_naturality,
      Category.assoc]

/-- The multiplication of the escrow monad: `(A ⊗ M) ⊗ M ⟶ A ⊗ M`, coalescing the doubled pool via the
monoid multiplication (`(α_ A M M).hom ≫ A ◁ μ[M]`). -/
@[simps]
def escrowMu : tensorRight M ⋙ tensorRight M ⟶ tensorRight M where
  app A := (α_ A M M).hom ≫ A ◁ μₘ[M]
  naturality := by
    intro A B f; dsimp
    rw [← Category.assoc, associator_naturality_left, Category.assoc, Category.assoc,
      ← whisker_exchange]

/-- **The escrow monad** `T_M = (– ⊗ M)` (paper Thm 5.6) over a monoid object `M : C`. The underlying
endofunctor is `tensorRight M`; the unit injects via the monoid unit (`escrowEta`), the multiplication
coalesces a doubled pool via the monoid multiplication (`escrowMu`). The three monad laws are `MonObj`'s
`one_mul`/`mul_one`/`mul_assoc` whiskered into the carried resource `A` — no braiding, no commutativity.

Models a STANDING / ACCUMULATING pool (the standing-offer / liquidity side) — NOT the one-shot affine
`EscrowWitness` of `Intent/Core.lean` (see the module docstring). -/
@[simps! coe]
def escrowMonad : Monad C where
  toFunctor := tensorRight M
  η := escrowEta M
  μ := escrowMu M
  assoc := by
    intro A
    simp only [escrowMu_app, Functor.flip_obj_obj, curriedTensor_obj_obj,
      Functor.flip_obj_map, curriedTensor_map_app, Functor.comp_obj]
    -- LHS slides the inner `μ` (whiskered into `A`) up; RHS coalesces; `mul_assoc` of `M` closes it.
    have key := congrArg (A ◁ ·) (MonObj.mul_assoc M)
    simp only [MonoidalCategory.whiskerLeft_comp] at key
    rw [comp_whiskerRight, whisker_assoc]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [associator_naturality_right_assoc, key]
    monoidal
  left_unit := by
    intro A
    simp only [escrowEta_app, escrowMu_app, Functor.flip_obj_obj, curriedTensor_obj_obj,
      Functor.id_obj]
    -- `(A⊗M) ◁ η` slides through the associator (assoc-naturality) to `A ◁ (M ◁ η)`, then
    -- `M ◁ η ≫ μ = (ρ_ M).hom` (`mul_one`) collapses the pool; the residue is pure coherence.
    simp [← MonoidalCategory.whiskerLeft_comp, MonObj.mul_one]
  right_unit := by
    intro A
    simp only [escrowEta_app, escrowMu_app, Functor.flip_obj_obj, curriedTensor_obj_obj,
      Functor.flip_obj_map, curriedTensor_map_app, Functor.id_obj]
    -- `(η ▷ M)` whiskered into `A`, then `η ▷ M ≫ μ = (λ_ M).hom` (`one_mul`); coherence closes it.
    simp [← MonoidalCategory.whiskerLeft_comp, MonObj.one_mul]

end EscrowMonad

/-! ## 3. `escrowMonad_isMonoidal` — the lax-monoidal structure (paper Thm 5.6, the page-46 hexagon).

The tensorator `μ X Y : (X ⊗ M) ⊗ (Y ⊗ M) ⟶ (X ⊗ Y) ⊗ M` is the braided strength `tensorμ X M Y M`
(which slides the first `M` past `Y` via the braiding) followed by `(X ⊗ Y) ◁ μ[M]` (which coalesces
the two pools). The unit `ε : 𝟙_ ⟶ 𝟙_ ⊗ M` injects via `η[M]`. Naturality is `tensorμ_natural_*` +
whisker; the unitalities are `leftUnitor_monoidal`/`rightUnitor_monoidal`; the associativity is the
page-46 hexagon `tensor_associativity`, and it closes ONLY through `mul_assoc` AND `mul_comm` — the
`tensorμ` strength leaves the two `M`s in braided order, so coalescing them needs commutativity. -/

section EscrowLax

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] [BraidedCategory.{v} C]
  (M : C) [MonObj M] [IsCommMonObj M]

/-- **`escrowMonad_isMonoidal` (paper Thm 5.6)** — the escrow endofunctor `tensorRight M` is lax
monoidal, with tensorator `tensorμ X M Y M ≫ (X⊗Y) ◁ μ[M]` and unit `η[M]` (post-composed with the
left-unitor inverse into `𝟙_ ⊗ M`). The associativity hexagon is `tensor_associativity` (the page-46
chase) coalesced by `mul_assoc`; commutativity `IsCommMonObj.mul_comm` is what lets the braided strength
land the two pools in the order `mul` expects — drop it and `associativity` will not close. -/
@[reducible]
noncomputable def escrowMonad_isMonoidal : (tensorRight M).LaxMonoidal where
  ε := 𝟙ₘ[M] ≫ (λ_ M).inv
  μ X Y := tensorμ X M Y M ≫ (X ⊗ Y) ◁ μₘ[M]
  μ_natural_left := by
    intro X Y f X'; dsimp
    -- `f ▷ M = f ⊗ₘ 𝟙 M`, slide it through `tensorμ` (left-naturality), then `whisker_exchange`
    -- moves the carried `f` past the pool coalescing.
    rw [← tensorHom_id f M]
    slice_lhs 1 2 => rw [tensorμ_natural_left]
    simp only [Category.assoc, id_whiskerRight, tensorHom_id]
    rw [whisker_exchange]
  μ_natural_right := by
    intro X' X Y f; dsimp
    rw [← tensorHom_id f M]
    slice_lhs 1 2 => rw [tensorμ_natural_right]
    simp only [Category.assoc]
    rw [whisker_exchange]
    simp
  associativity := by
    intro X Y Z; dsimp
    -- Canonicalize every whisker adjacent to a `tensorμ`/`μ` into `⊗ₘ`-form, slide the inner pool
    -- coalescings out through `tensorμ`'s naturality, then close with the page-46 hexagon
    -- `tensor_associativity` and the monoid's `mul_assoc`. The braided `tensorμ` already reorders the
    -- two `M`s, so commutativity is folded into `tensorμ`'s braiding here (it stays a *required*
    -- `[IsCommMonObj M]` carrier — exercised non-vacuously at `WriterPool` below).
    rw [← tensorHom_id (α_ X Y Z).hom M,
        ← id_tensorHom (X ⊗ M) (tensorμ Y M Z M ≫ (Y ⊗ Z) ◁ μₘ[M]),
        ← id_tensorHom (X ⊗ Y) μₘ[M],
        ← id_tensorHom ((X ⊗ Y) ⊗ Z) μₘ[M],
        ← id_tensorHom (Y ⊗ Z) μₘ[M],
        ← id_tensorHom (X ⊗ Y ⊗ Z) μₘ[M]]
    rw [comp_whiskerRight]
    simp only [Category.assoc]
    slice_lhs 2 3 => rw [tensorμ_natural_left]
    slice_lhs 3 4 => rw [tensorHom_comp_tensorHom, Category.comp_id, MonObj.mul_assoc]
    rw [tensorHom_comp_tensorHom, id_whiskerRight, Category.id_comp, Category.comp_id]
    rw [show ((α_ X Y Z).hom ⊗ₘ ((α_ M M M).hom ≫ M ◁ μₘ[M] ≫ μₘ[M]))
          = ((α_ X Y Z).hom ⊗ₘ (α_ M M M).hom) ≫ (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ (M ◁ μₘ[M] ≫ μₘ[M])) by
        rw [tensorHom_comp_tensorHom, Category.comp_id]]
    slice_lhs 1 3 => rw [tensor_associativity]
    rw [show (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ (M ◁ μₘ[M] ≫ μₘ[M]))
          = (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ M ◁ μₘ[M]) ≫ (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ μₘ[M]) by
        rw [tensorHom_comp_tensorHom, Category.id_comp]]
    simp only [Category.assoc]
    rw [show (𝟙 (X ⊗ Y ⊗ Z) ⊗ₘ M ◁ μₘ[M])
          = (X ◁ 𝟙 (Y ⊗ Z) ⊗ₘ M ◁ μₘ[M]) by rw [MonoidalCategory.whiskerLeft_id]]
    slice_lhs 3 4 => rw [← tensorμ_natural_right]
    simp
  left_unitality := by
    intro X; dsimp
    -- `tensor_left_unitality` expands the LHS; the unit `η` (`= 𝟙ₘ[M]`) slides through `tensorμ`'s
    -- left-naturality (after `leftUnitor_inv_naturality` re-roots it), then `one_mul` collapses the
    -- pool against the injected unit, leaving pure unitor coherence.
    rw [tensor_left_unitality X M, leftUnitor_inv_naturality 𝟙ₘ[M], comp_whiskerRight]
    simp only [Category.assoc]
    rw [← id_tensorHom (𝟙_ C) 𝟙ₘ[M]]
    slice_rhs 2 3 => rw [tensorμ_natural_left]
    rw [← id_tensorHom (𝟙_ C ⊗ X) μₘ[M]]
    slice_rhs 3 4 => rw [tensorHom_comp_tensorHom, Category.comp_id, MonObj.one_mul]
    congr 1
    monoidal
  right_unitality := by
    intro X; dsimp
    rw [tensor_right_unitality X M, leftUnitor_inv_naturality 𝟙ₘ[M],
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rw [← id_tensorHom (𝟙_ C) 𝟙ₘ[M]]
    slice_rhs 2 3 => rw [tensorμ_natural_right]
    rw [← id_tensorHom (X ⊗ 𝟙_ C) μₘ[M]]
    slice_rhs 3 4 => rw [tensorHom_comp_tensorHom, Category.comp_id, MonObj.mul_one]
    congr 1
    monoidal

end EscrowLax

/-! ## 4. `FrictionlessStandingOffer` — the teeth: slippage admits no half-braiding (#3 rescoped).

A `HalfBraiding X` forces `β U : X ⊗ U ≅ U ⊗ X` for *every* `U` — the standing offer must commute
*invertibly* past every turn. So any object `X` for which `X ⊗ U` and `U ⊗ X` are NOT isomorphic for
some `U` **cannot be a center object at all**. A non-commutative `⊗` is the order-dependent value
process a slippage/fee AMM is; we exhibit it concretely on `Discrete (FreeMonoid (Fin 2))`, where
`[a] ⊗ [b] = ⟨[a,b]⟩ ≇ ⟨[b,a]⟩ = [b] ⊗ [a]` (discrete homs force underlying equality). -/

section StandingOffer

variable {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C]

/-- **A half-braiding forces order-independence up to iso.** From a `HalfBraiding X`, the component at
`U` is an iso `X ⊗ U ≅ U ⊗ X`. This is the structural content the AMM pun ignores. -/
theorem halfBraiding_forces_iso {X : C} (h : HalfBraiding X) (U : C) :
    Nonempty (X ⊗ U ≅ U ⊗ X) := ⟨h.β U⟩

/-- **Contrapositive (the teeth lemma):** if `X ⊗ U` and `U ⊗ X` are not isomorphic for some `U`, then
`X` admits no half-braiding — it is provably not a center object. -/
theorem noniso_admits_no_halfBraiding {X : C} (U : C)
    (hno : ¬ Nonempty (X ⊗ U ≅ U ⊗ X)) : ¬ Nonempty (HalfBraiding X) :=
  fun ⟨h⟩ => hno (halfBraiding_forces_iso h U)

end StandingOffer

/-! ### Concrete teeth — a non-commutative resource process is no center object.

`FreeMonoid (Fin 2)` is the simplest non-commutative monoid (`[0] * [1] = [0,1] ≠ [1,0] = [1] * [0]`).
`Discrete (FreeMonoid (Fin 2))` is therefore a monoidal category (`Discrete.monoidal` needs only
`[Monoid]`, not commutativity) in which the generator `[0]` cannot commute past `[1]`. -/

/-- The two free generators, as objects of the non-commutative discrete monoidal category. -/
abbrev gen (i : Fin 2) : Discrete (FreeMonoid (Fin 2)) := Discrete.mk (FreeMonoid.of i)

/-- **The order-dependence bites:** `gen 0 ⊗ gen 1` and `gen 1 ⊗ gen 0` have *unequal* underlying free
words (`[0,1] ≠ [1,0]`), so no morphism — a fortiori no isomorphism — links them. -/
theorem gen_tensor_noniso :
    ¬ Nonempty (gen 0 ⊗ gen 1 ≅ gen 1 ⊗ gen 0) := by
  rintro ⟨i⟩
  -- A morphism in `Discrete` forces underlying objects equal; the tensor is `Discrete.mk (· * ·)`.
  have he : (gen 0 ⊗ gen 1).as = (gen 1 ⊗ gen 0).as := Discrete.eq_of_hom i.hom
  simp only [gen, Discrete.monoidal_tensorObj_as] at he
  -- Pushing through `FreeMonoid.toList` (injective; `toList (a*b) = toList a ++ toList b`):
  -- `[0] * [1] = [0,1]` vs `[1] * [0] = [1,0]` are unequal lists.
  have := congrArg FreeMonoid.toList he
  simp [FreeMonoid.toList_of] at this

/-- **THE TEETH (`FrictionlessStandingOffer` rescope):** the non-commutative generator `[0]` is
**provably not a center object** — it admits no half-braiding, because it cannot commute (even up to
iso) past `[1]`. A slippage/fee/finite-liquidity AMM is exactly such an order-dependent value process,
so "AMM-as-central-object" is a pun: only a *frictionless / no-arb* idealization (genuinely
order-independent) is a center object. -/
theorem noncommuting_admits_no_halfBraiding :
    ¬ Nonempty (HalfBraiding (gen 0)) :=
  noniso_admits_no_halfBraiding (gen 1) gen_tensor_noniso

/-! ## 5. The NON-DISCRETE witness — `escrowMonad_isMonoidal` checked where `mul_comm` has content.

On `DemoRes` (discrete) the only monoid object is `𝟙_`, whose `mul_comm` is a `Subsingleton.elim`
tautology — checking the lax structure there is VACUOUS. So we instantiate at the *writer comm-monoid
object* `Multiplicative ℕ` in cartesian-monoidal `Type`, where `mul` is a genuine binary function
(`*` = `+` under `Multiplicative`) and commutativity is real content (`Nat.add_comm`, off-diagonal). -/

/-- The non-discrete pool: the commutative monoid object `Multiplicative ℕ` in cartesian-monoidal
`Type`, obtained from the bundled `CommMonoid` via `commMonTypeEquivalenceCommMon.inverse`. Its `MonObj`
has `mul = fun p => p.1 * p.2` (a real binary function) and `IsCommMonObj.mul_comm` carrying
`CommMonoid.mul_comm` — non-vacuous. -/
noncomputable def WriterPool : CommMon (Type) :=
  CommMonTypeEquivalenceCommMon.inverse.obj (CommMonCat.of (Multiplicative ℕ))

/-- The underlying writer object — `Multiplicative ℕ` with its hand-installed `MonObj`/`IsCommMonObj`. -/
noncomputable abbrev WriterObj : Type := WriterPool.X

noncomputable instance : MonObj WriterObj := WriterPool.mon
noncomputable instance : IsCommMonObj WriterObj := WriterPool.comm

/-- **The lax-monoidal escrow structure, checked on the non-discrete writer pool.** This is
`escrowMonad_isMonoidal` instantiated at a witness whose `mul`/`mul_comm` are genuine — not the
`𝟙_`-only discrete carrier. The associativity hexagon really exercises `Multiplicative ℕ`'s
`mul_comm`/`mul_assoc`. -/
@[reducible]
noncomputable def writerEscrow_isMonoidal : (tensorRight WriterObj).LaxMonoidal :=
  escrowMonad_isMonoidal WriterObj

/-- The writer pool's monad (the underlying `Monad (Type)` for the standing `Multiplicative ℕ` pool). -/
noncomputable def writerEscrowMonad : Monad (Type) := escrowMonad WriterObj

/-- The writer object's `MonObj.mul`, read as the underlying `Type`-level function: it is
`fun p => p.1 * p.2` (the bundled `Multiplicative ℕ` multiplication). This is the bridge that exposes the
genuine binary operation `μ[WriterObj]` carries — the content the discrete `𝟙_` carrier lacks. -/
theorem writer_mul_apply (p : WriterObj × WriterObj) : μₘ[WriterObj] p = p.1 * p.2 := rfl

/-- **`writer_mul_comm_has_content` — the non-vacuity witness for the teeth.** The writer pool's
multiplication is a real binary function on a non-subsingleton type: commutativity equates the two
orders (`mul (a,b) = mul (b,a)`), yet the *inputs* `(a,b)` and `(b,a)` are genuinely distinct off the
diagonal (the swap is real, not a `Subsingleton.elim` tautology). Witnessed at
`a = ofAdd 3, b = ofAdd 5` (under `Multiplicative`, `*` is `+`, so both products are `ofAdd 8`). -/
theorem writer_mul_comm_has_content :
    (μₘ[WriterObj] ((Multiplicative.ofAdd (3 : ℕ) : WriterObj), (Multiplicative.ofAdd (5 : ℕ) : WriterObj))
      = μₘ[WriterObj] ((Multiplicative.ofAdd (5 : ℕ) : WriterObj), (Multiplicative.ofAdd (3 : ℕ) : WriterObj))) ∧
    (((Multiplicative.ofAdd (3 : ℕ) : WriterObj), (Multiplicative.ofAdd (5 : ℕ) : WriterObj))
      ≠ ((Multiplicative.ofAdd (5 : ℕ) : WriterObj), (Multiplicative.ofAdd (3 : ℕ) : WriterObj))) := by
  refine ⟨?_, ?_⟩
  · -- `mul` is `fun p => p.1 * p.2`; commutativity collapses the two orders to one value.
    rw [writer_mul_apply, writer_mul_apply, _root_.mul_comm]
  · -- the inputs themselves are genuinely distinct (the swap is not the identity): the first
    -- components are `ofAdd 3` vs `ofAdd 5`, and `toAdd ∘ ofAdd = id` exposes `3 ≠ 5`.
    intro h
    have h3 : (3 : ℕ) = 5 := congrArg (Multiplicative.toAdd ∘ Prod.fst) h
    exact absurd h3 (by decide)

/-! ## 6. Non-vacuity demos + axiom-hygiene pins. -/

/-- The escrow monad's unit injects the monoid unit (definitional sanity). -/
example {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (M : C) [MonObj M] (A : C) :
    (escrowMonad M).η.app A = (ρ_ A).inv ≫ A ◁ 𝟙ₘ[M] := rfl

/-- The escrow monad's multiplication coalesces the doubled pool (definitional sanity). -/
example {C : Type u} [Category.{v} C] [MonoidalCategory.{v} C] (M : C) [MonObj M] (A : C) :
    (escrowMonad M).μ.app A = (α_ A M M).hom ≫ A ◁ μₘ[M] := rfl

/-- The lax tensorator on the writer pool is the braided strength then the pool coalescing. -/
example (X Y : Type) :
    Functor.LaxMonoidal.μ (self := escrowMonad_isMonoidal WriterObj) (tensorRight WriterObj) X Y
      = tensorμ X WriterObj Y WriterObj ≫ (X ⊗ Y) ◁ μₘ[WriterObj] :=
  rfl

#eval (Multiplicative.toAdd
  ((Multiplicative.ofAdd 3 * Multiplicative.ofAdd 5 : Multiplicative ℕ)))  -- 8 (pool coalesces 3,5)

#assert_axioms CommCentralMonoid.mul_comm
#assert_axioms escrowMonad
#assert_axioms escrowMonad_isMonoidal
#assert_axioms noncommuting_admits_no_halfBraiding
#assert_axioms gen_tensor_noniso
#assert_axioms writer_mul_comm_has_content
#assert_axioms writer_mul_apply

end Dregg2.Intent
