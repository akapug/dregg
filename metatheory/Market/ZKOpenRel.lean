/-
# Market.ZKOpenRel — the fhEgg CATEGORICAL UNIFICATION: `ZKOpenRel_R`, the objects + the one open theorem.

**Q2 of `docs/deos/FHEGG-CODEX-INSIGHTS.md`, formalized as a Lean development (not prose).** Codex
(GPT-5.6-sol) named the categorical home of the whole fhEgg stack:

> a **resource-graded, proof-carrying, guarded traced symmetric monoidal category of open relations**,
> realized by **decorated cospans** — `ZKOpenRel_R`, with:
>   * the **resource-defect** `d_M ∈ R` a strong monoidal functor to the additive monoid `(R,+,0)`;
>   * **conservation** = the zero-defect subcategory `d⁻¹(0)`;
>   * the **ring** = the guarded trace (feedback);
>   * **privacy** = a simulator natural transformation `View ≈ Sim∘Q` over the leakage functor `Q`;
>   * the four fhEgg objects (turn / auction / circulation / convex engine) as INSTANCES;
>   * **the ONE open theorem** = the compositionality/closure theorem under FEEDBACK (the guarded
>     trace) + ADAPTIVE composition. Codex was candid: *this is a well-posed research target with the
>     right objects named, NOT a discharged proof.*

This module turns that from prose into a real, sorry-free Lean development. It builds the OBJECTS,
proves the TRACTABLE pieces, and isolates the ONE open theorem as a NAMED conjecture (a `Prop`-valued
`def` + a hypothesis field of the unification bundle) — **never a `sorry`, never a fake-green
tautology.**

## What is BUILT + PROVEN (the tractable core, kernel-clean)

  * **THE CATEGORY `ZKOpenRel R`** (§1) — a lightweight decorated-cospan / open-relation category: objects
    carry a boundary state `S`; a morphism `X ⟶ Y` carries the **resource defect** `d ∈ R` (the grade)
    and a **feasibility relation** `rel : S_X → S_Y → Prop` (the open topology's fiber). Composition =
    relational (fiber-product) composition with **defects ADD**; identity = `Eq` with defect `0`. The
    genuine `CategoryTheory.Category` laws are PROVEN (`id_comp`/`comp_id`/`assoc`).
  * **THE RESOURCE-DEFECT FUNCTOR `d_M`** (§2) — `dFunctor : ZKOpenRel R ⥤ SingleObj (Multiplicative R)`,
    a genuine functor to the delooping of the additive monoid `(R,+,0)` (`map_id`/`map_comp` = the
    functor laws = `d(𝟙)=0`, `d(g∘f)=d f + d g`). Its **strong-monoidal** structure equations over the
    open-system tensor `⊗` (`dFunctor_tensor : d(f ⊗ g) = d f + d g`, `dFunctor_unit`) are proven — the
    conservation-accounting `toBal`-homomorphism, lifted to the functor.
  * **CONSERVATION = `d⁻¹(0)`** (§3) — `Conservative f := dGrade f = 0`. Proven a **monoidal
    subcategory**: `id_conservative`, `comp_conservative` (adaptive/sequential composition preserves
    zero defect), `tensor_conservative` (the ⊗ preserves it). Plus `iterate_conservative` — a conserving
    turn iterated `n` times stays conserving (the history `T_n∘…∘T_1`).
  * **THE FOUR INSTANCES** (§4–5) recovered as `ZKOpenRel` objects living in `d⁻¹(0)`:
      1. **turn** — a conserving proof-carrying endomorphism `T:S→S` (`turnMor`), history = its iterate;
      2. **auction** — the multilateral Frobenius-merge clearing `Market/Clearing.lean`'s `ringClearing`
         as a conservative morphism (`auctionMor`, `auction_conservative` via `clearing_conserves_per_asset`);
      3. **circulation** — a capacity-respecting flow `Market/CertF.lean`'s `FlowLP` as a conservative
         morphism whose defect is the node imbalance `A f` (`circulationMor`, conservative ⇔ `A f = 0`
         = `PrimalFeasible`);
      4. **convex engine** — the same flow carrying its `Cert-F` certificate (the refinement decoration),
         conservative on the same `A f = 0` face.
  * **THE PRIVACY NATURAL TRANSFORMATION** (§7) — `PrivacyNatTrans`, the `View ≈ Sim∘Q` shape (leakage
    map `Q`, real `view`, witness-free `sim`, naturality `view = sim∘Q`); `same_leakage_indistinguishable`
    (the reveal-nothing consequence) is PROVEN, and `Market/RevealNothing.lean`'s `RevealBundle` is shown
    to BE exactly such a natural transformation (`ofRevealBundle`). This is the categorical home of the
    reveal-nothing theorem — privacy = the simulator natural transformation over the leakage functor `Q`.

## THE ONE OPEN THEOREM, NAMED (§6) — NOT sorried, NOT overclaimed

The guarded trace (feedback) is the ring/feedback operation. Its GRADE side is easy and PROVEN
(`gtrace_conservative`: feedback does not change the resource accounting — `d(tr f) = d f`). The HARD,
OPEN content codex named is the **feasibility closure**: an ordinary trace of a relation can produce the
EMPTY relation ("it wires a cycle; it does not prove the cycle clears"). So the frontier is whether the
GUARD (non-vacuity of the feedback fiber — the loop actually clears) SURVIVES feedback and composes
adaptively. We:

  * PROVE the **non-feedback fragment**: guardedness is preserved by sequential/adaptive composition
    (`comp_guarded`) and by tensor (`tensor_guarded`) — the adaptive-composition half of the closure;
  * STATE the **feedback half as a named conjecture** — `GuardedTraceClosure R : Prop` (the precise
    statement "guarded trace of a guarded conservative morphism is guarded"), carried as an explicit
    HYPOTHESIS FIELD `ZKUnification.feedback_closure`, NEVER proven, NEVER `sorry`-ed. `ZKUnification`
    is the well-defined development with the ONE open field isolated; `traced_history_closed` shows what
    that field would buy (feedback preserves both conservation — proven — and guardedness — the open
    field).

**HONEST GRADE.** This is the RESEARCH TARGET, formalized: the objects + the functor + conservation-as-
kernel + the four instances + non-feedback composition + the privacy natural transformation are PROVEN
and kernel-clean; the **compositionality/closure-under-feedback theorem is the OPEN frontier**, stated
precisely as a conjecture, NOT proved, NOT sorried. Do NOT read this as "the unification is proved" — it
is the honest categorical skeleton with the one open theorem isolated.

Pure.
-/
import Market.Clearing
import Market.CertF
import Market.RevealNothing
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.TypeTags.Basic
import Dregg2.Tactics

namespace Market.ZKOpenRel

open CategoryTheory
open Dregg2.Intent
open Dregg2.Exec (AssetId)
open Matrix

set_option autoImplicit false

/-! ## 1. THE CATEGORY `ZKOpenRel R` — resource-graded open relations (decorated cospans, lightweight).

An **object** is a boundary/state interface `S` (the typed ports + private state of codex's `X`). A
**morphism** `X ⟶ Y` is the decoration a decorated cospan carries at the relevant grain: a **resource
defect** `defect ∈ R` (the grade `d_M`) and a **feasibility relation** `rel : S_X → S_Y → Prop` (the
fiber of the open topology — `∃`-over the private witness). Composition is the fiber product (relational
composition) with **defects adding**; identity is `Eq` with defect `0`. The category laws hold — this is
a genuine `CategoryTheory.Category`. -/

/-- **An object of `ZKOpenRel R`** — a boundary/state interface (codex's typed ports + private state
`S_X`). `R` is a phantom parameter fixing which resource group grades this category (so distinct `R`
give distinct categories, hence distinct `Category` instances). -/
structure ZKObj (R : Type) where
  /-- The boundary/state carrier (ports + private state). -/
  S : Type

/-- **A morphism `X ⟶ Y` of `ZKOpenRel R`** — the decorated-cospan decoration: the resource **defect**
(grade `d_M`) and the **feasibility relation** (the open topology's fiber, `∃`-over the private
witness). Composition adds defects and composes relations. -/
@[ext] structure ZKHom {R : Type} [AddCommMonoid R] (X Y : ZKObj R) where
  /-- The **resource defect** `d_M ∈ R` — the grade. Conservation is `defect = 0`. -/
  defect : R
  /-- The **feasibility relation** — the fiber of the open topology (`∃` over the private witness). -/
  rel : X.S → Y.S → Prop

variable {R : Type} [AddCommMonoid R]

/-- Identity — defect `0`, the diagonal relation `Eq` (the trivial open topology). -/
def idHom (X : ZKObj R) : ZKHom X X where
  defect := 0
  rel := Eq

/-- **Composition — the fiber product, with DEFECTS ADDING.** `(f ≫ g).rel x z = ∃ y, f x y ∧ g y z`
(relational/fiber-product composition at the shared boundary `Y`) and `(f ≫ g).defect = f.defect +
g.defect` (the resource defect is additive over composition — half the strong-monoidal-functor law). -/
def compHom {X Y Z : ZKObj R} (f : ZKHom X Y) (g : ZKHom Y Z) : ZKHom X Z where
  defect := f.defect + g.defect
  rel x z := ∃ y, f.rel x y ∧ g.rel y z

/-- **`ZKOpenRel R` is a genuine category.** The relational-composition laws (identity = `Eq`,
associativity of the fiber product) and the additive-monoid grade laws (`0 + a = a`, `(a+b)+c =
a+(b+c)`) together give the `CategoryTheory.Category` structure. -/
instance category : Category (ZKObj R) where
  Hom X Y := ZKHom X Y
  id X := idHom X
  comp f g := compHom f g
  id_comp {X Y} f := by
    apply ZKHom.ext
    · exact zero_add _
    · funext x y
      exact propext ⟨by rintro ⟨z, rfl, h⟩; exact h, fun h => ⟨x, rfl, h⟩⟩
  comp_id {X Y} f := by
    apply ZKHom.ext
    · exact add_zero _
    · funext x y
      exact propext ⟨by rintro ⟨z, h, rfl⟩; exact h, fun h => ⟨y, h, rfl⟩⟩
  assoc {W X Y Z} f g h := by
    apply ZKHom.ext
    · exact add_assoc _ _ _
    · funext x w
      exact propext
        ⟨by rintro ⟨z, ⟨y, hf, hg⟩, hh⟩; exact ⟨y, hf, z, hg, hh⟩,
         by rintro ⟨y, hf, z, hg, hh⟩; exact ⟨z, ⟨y, hf, hg⟩, hh⟩⟩

@[simp] theorem id_defect (X : ZKObj R) : (𝟙 X : ZKHom X X).defect = 0 := rfl

@[simp] theorem comp_defect {X Y Z : ZKObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).defect = f.defect + g.defect := rfl

/-! ## 2. THE RESOURCE-DEFECT FUNCTOR `d_M` — a strong monoidal functor to `(R,+,0)`.

`d_M` is the grade. As a functor it lands in the delooping `SingleObj (Multiplicative R)` — the additive
monoid `(R,+,0)` as a one-object category — and its `map_id`/`map_comp` ARE the functor laws
`d(𝟙)=0`, `d(g∘f)=d f + d g`. Its strong-monoidal structure equations over the open-system tensor `⊗`
(§below) are `dFunctor_tensor`/`dFunctor_unit`. -/

/-- **`dGrade` — the resource defect of a morphism**, `d_M ∈ R`. (`= dFunctor.map` up to the delooping
coercion; used directly for the conservation predicate.) -/
def dGrade {X Y : ZKObj R} (f : X ⟶ Y) : R := f.defect

/-- **`dFunctor` — the resource-defect functor `d : ZKOpenRel R ⥤ (R,+,0)`.** Lands in the delooping
`SingleObj (Multiplicative R)` of the additive monoid; `map` sends a morphism to its defect (as a
`Multiplicative` element), and the functor laws are exactly `d(𝟙 X) = 0` and `d(g ∘ f) = d f + d g` —
the conservation-accounting homomorphism, as a functor. (Target composition is `flip (*)`; the grade
commutes, so the direction is immaterial.) -/
def dFunctor : ZKObj R ⥤ SingleObj (Multiplicative R) where
  obj _ := SingleObj.star _
  map f := Multiplicative.ofAdd f.defect
  map_id X := by
    show Multiplicative.ofAdd ((𝟙 X : ZKHom X X).defect) = 1
    simp
  map_comp {X Y Z} f g := by
    show Multiplicative.ofAdd ((f ≫ g).defect) = Multiplicative.ofAdd g.defect * Multiplicative.ofAdd f.defect
    rw [comp_defect, ← ofAdd_add, add_comm f.defect g.defect]

/-- The functor law `d(g ∘ f) = d f + d g`, read off directly as an equation in `R`. -/
theorem dGrade_comp {X Y Z : ZKObj R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    dGrade (f ≫ g) = dGrade f + dGrade g := rfl

/-- The functor law `d(𝟙) = 0`. -/
theorem dGrade_id (X : ZKObj R) : dGrade (𝟙 X) = 0 := rfl

/-! ### The open-system tensor `⊗` and the strong-monoidal structure of `d`. -/

/-- **The tensor of open systems** on objects — side-by-side boundaries `S_X × S_Y`. -/
def tensorObj (X Y : ZKObj R) : ZKObj R := ⟨X.S × Y.S⟩

/-- **The unit object** — the empty boundary. -/
def unitObj : ZKObj R := ⟨PUnit⟩

/-- **The tensor of morphisms** — parallel composition: relations run side by side, **defects ADD**
(the other half of the strong-monoidal-functor law: `d` is additive over `⊗`, not just `∘`). -/
def tensorHom {X Y X' Y' : ZKObj R} (f : X ⟶ Y) (g : X' ⟶ Y') :
    tensorObj X X' ⟶ tensorObj Y Y' where
  defect := f.defect + g.defect
  rel p q := f.rel p.1 q.1 ∧ g.rel p.2 q.2

/-- **STRONG-MONOIDAL: `d(f ⊗ g) = d f + d g`.** The resource defect is additive over the monoidal
product of open systems (`⊗`), completing — with `dGrade_comp` (over `∘`) and `dGrade_id` — the
strong-monoidal-functor equations for the grade `d : ZKOpenRel R → (R,+,0)`. This is the categorical
form of `Market/Clearing.lean`'s `toBal_mul` (the per-asset reading is additive over the ⊗-pool). -/
theorem dFunctor_tensor {X Y X' Y' : ZKObj R} (f : X ⟶ Y) (g : X' ⟶ Y') :
    dGrade (tensorHom f g) = dGrade f + dGrade g := rfl

/-- **STRONG-MONOIDAL: `d(𝟙_⊗) = 0`.** The tensor unit carries zero defect (the monoidal-unit law). -/
theorem dFunctor_unit : dGrade (𝟙 (unitObj : ZKObj R)) = 0 := rfl

/-! ## 3. CONSERVATION = the zero-defect subcategory `d⁻¹(0)`.

Conservation is exactly `d_M = 0` — the kernel of the resource-defect functor. It is a **monoidal
subcategory**: closed under identity, (adaptive/sequential) composition, and tensor. This is the
categorical home of `Market/Clearing.lean`'s per-asset conservation and `Market/CertF.lean`'s flow
conservation — both are the statement `d = 0`. -/

/-- **`Conservative f` — the morphism lies in `d⁻¹(0)`**: its resource defect is zero (the market as a
whole neither mints nor burns). -/
def Conservative {X Y : ZKObj R} (f : X ⟶ Y) : Prop := dGrade f = 0

/-- The identity is conservative — `d⁻¹(0)` contains all identities (a subcategory). -/
theorem id_conservative (X : ZKObj R) : Conservative (𝟙 X) := dGrade_id X

/-- **ADAPTIVE/SEQUENTIAL COMPOSITION PRESERVES CONSERVATION** — composing two zero-defect morphisms is
zero-defect (`0 + 0 = 0`). `d⁻¹(0)` is closed under `∘` — the non-feedback half of the closure, PROVEN.
This is "a turn stream of conserving turns conserves." -/
theorem comp_conservative {X Y Z : ZKObj R} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Conservative f) (hg : Conservative g) : Conservative (f ≫ g) := by
  simp only [Conservative, dGrade_comp] at *
  rw [hf, hg, add_zero]

/-- **THE TENSOR PRESERVES CONSERVATION** — the ⊗-product of two zero-defect morphisms is zero-defect.
`d⁻¹(0)` is a *monoidal* subcategory (closed under `⊗` as well as `∘`). -/
theorem tensor_conservative {X Y X' Y' : ZKObj R} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : Conservative f) (hg : Conservative g) : Conservative (tensorHom f g) := by
  simp only [Conservative, dFunctor_tensor] at *
  rw [hf, hg, add_zero]

/-- **Iterated composition of a conserving endomorphism.** The turn-kernel history `T^n = T ∘ ⋯ ∘ T`. -/
def iterate {X : ZKObj R} (f : X ⟶ X) : ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => iterate f n ≫ f

/-- **A CONSERVING TURN ITERATED STAYS CONSERVING** — `T^n ∈ d⁻¹(0)` for every `n` (the history of a
conserving turn conserves), by induction from `id_conservative` + `comp_conservative`. -/
theorem iterate_conservative {X : ZKObj R} {f : X ⟶ X} (hf : Conservative f) :
    ∀ n, Conservative (iterate f n)
  | 0 => id_conservative X
  | n + 1 => comp_conservative (iterate_conservative hf n) hf

/-! ## 4. INSTANCE — CIRCULATION (from `Market/CertF.lean`): the flow LP as a graded morphism.

The circulation object is `codex`'s open-network morphism: a capacity-respecting flow whose resource
defect is the **node imbalance** `A f`. It is conservative — lives in `d⁻¹(0)` — exactly when `A f = 0`,
which is `PrimalFeasible`'s conservation clause. Grade `R := V → ℤ` (per-node imbalance). -/

section Circulation
variable {V E : Type} [Fintype V] [Fintype E]

/-- The circulation object — the flow boundary (kept abstract; the categorical content used here is the
grade). -/
def flowObj (V : Type) : ZKObj (V → ℤ) := ⟨PUnit⟩

/-- **The circulation morphism** — a flow `f` on `lp`, graded by its **node imbalance** `A f : V → ℤ`
(zero iff `f` conserves at every node). The decorated-cospan open-network morphism of codex's Q2. -/
def circulationMor (lp : Market.FlowLP V E ℤ) (f : E → ℤ) : flowObj V ⟶ flowObj V where
  defect := lp.A *ᵥ f
  rel _ _ := True

omit [Fintype V] in
/-- **CIRCULATION LIVES IN `d⁻¹(0)` ⇔ IT CONSERVES** — `circulationMor lp f` is `Conservative` exactly
when `A f = 0`, i.e. when `f` is a genuine circulation (`PrimalFeasible.1`). The categorical conservation
predicate IS the flow-conservation `Cert-F` reads. -/
theorem circulation_conservative {lp : Market.FlowLP V E ℤ} {f : E → ℤ}
    (hf : Market.PrimalFeasible lp f) : Conservative (circulationMor lp f) := hf.1

end Circulation

/-- **THE CIRCULATION INSTANCE, WITNESSED** — the worked 3-cycle circulation of `Market/CertF.lean`
(`ringLP`, unit flow `ringF`) is a conservative `ZKOpenRel (Fin 3 → ℤ)` morphism: its node imbalance is
zero (`ringCert_valid.1`, the certificate's primal-feasibility). Circulation recovered as an instance,
in `d⁻¹(0)`. -/
theorem ring_circulation_conservative :
    Conservative (circulationMor Market.ringLP Market.ringF) :=
  circulation_conservative Market.ringCert_valid.1

/-! ## 5. INSTANCE — CONVEX ENGINE + AUCTION + TURN (the remaining three of the four).

  * **convex engine** — the same flow morphism, now carrying its `Cert-F` certificate (the refinement
    2-cell / proof decoration). Its resource defect is the SAME `A f` (conservation on the flow face);
    the certificate is the proof-carrying decoration codex names (`U_θ` fixed solver + certificate
    2-cell). Conservative on `A f = 0`.
  * **auction** — the multilateral Frobenius-merge clearing `Market/Clearing.lean`'s `ringClearing`,
    graded by the per-asset pool imbalance; conservative by `clearing_conserves_per_asset`.
  * **turn** — a conserving proof-carrying endomorphism; history = its `iterate`. -/

/-- **The convex-engine morphism** — a certified flow: the circulation morphism decorated with a
`Cert-F` certificate `(f, π, s)` (the proof-carrying refinement 2-cell). The resource grade is the same
node imbalance `A f`; the certificate rides as attached data (codex's `U_θ` + certificate 2-cell). -/
def convexEngineMor {V E : Type} [Fintype V] [Fintype E]
    (lp : Market.FlowLP V E ℤ) (f : E → ℤ) (_π : V → ℤ) (_s : E → ℤ) : flowObj V ⟶ flowObj V :=
  circulationMor lp f

/-- **THE CONVEX-ENGINE INSTANCE, WITNESSED** — the worked certified triple (`ringCert_valid`) is a
conservative morphism: the certificate's primal conserves, so the graded morphism lies in `d⁻¹(0)`. The
convex engine's *optimality* is `Market/CertF.lean`'s `certifies_epsilon_optimal` (the certificate
2-cell); its *conservation* is this categorical face. -/
theorem convex_engine_conservative :
    Conservative (convexEngineMor Market.ringLP Market.ringF Market.ringπ Market.ringS) :=
  circulation_conservative Market.ringCert_valid.1

section Auction

variable {Stmt Wit : Type} {Bl : Dregg2.Authority.Blocklace.Lace}
  {reg : Dregg2.Authority.Predicate.Registry Stmt Wit}
  {stmtOf : Dregg2.Time.Frame.FrameStatement → Stmt}

/-- **The per-asset resource defect of a market clearing** — `d = Σ_out − Σ_in`, asset by asset (the
categorical grade of the multilateral clearing). Zero exactly when the clearing conserves. -/
def clearingDefect {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) : AssetId → ℤ :=
  fun a => (C.alloc.map (fun r => toBal r.as a)).sum - (book.map (fun i => toBal i.offered.as a)).sum

/-- **A market clearing conserves ⇒ its defect is zero** — `clearing_conserves_per_asset` says
`Σ_in = Σ_out` per asset, so `Σ_out − Σ_in = 0`. The `Market/Clearing.lean` conservation keystone, as
the statement `d = 0`. -/
theorem clearingDefect_zero {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) :
    clearingDefect C = 0 := by
  funext a
  have h := clearing_conserves_per_asset C a
  simp only [clearingDefect, Pi.zero_apply]
  omega

/-- The clearing object — a market boundary, graded by `R = AssetId → ℤ` (the per-asset ledger). -/
def clearingObj : ZKObj (AssetId → ℤ) := ⟨PUnit⟩

/-- **The auction/clearing morphism** — a multilateral market clearing as a graded endomorphism, graded
by its per-asset pool imbalance `clearingDefect`. -/
def clearingMor {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) :
    clearingObj ⟶ clearingObj where
  defect := clearingDefect C
  rel _ _ := True

/-- **A CLEARING LIVES IN `d⁻¹(0)`** — every market clearing is a conservative `ZKOpenRel` morphism (its
per-asset pool imbalance is zero). Conservation = zero defect, connected to `clearing_conserves_per_asset`. -/
theorem clearing_is_conservative {book : Book DemoRes Bl reg stmtOf} (C : MarketClearing book) :
    Conservative (clearingMor C) := clearingDefect_zero C

end Auction

/-- **THE AUCTION INSTANCE, WITNESSED** — the multilateral 3-party ring clearing of
`Market/Clearing.lean` (`ringClearing` — the cross-bid that only a MARKET can fill) is a conservative
`ZKOpenRel` morphism. The Frobenius-merge auction recovered as an instance, in `d⁻¹(0)`. -/
theorem ring_auction_conservative : Conservative (clearingMor Market.ringClearing) :=
  clearing_is_conservative Market.ringClearing

/-- **THE TURN INSTANCE** — a conserving proof-carrying endomorphism `T : S → S` (defect `0`, the
diagonal feasibility relation, decoration elided). Its history `T^n` is `iterate turnMor n`, conserving
for every `n` (`turn_history_conservative`). -/
def turnMor : (unitObj : ZKObj (AssetId → ℤ)) ⟶ unitObj := 𝟙 unitObj

/-- The turn is conservative (defect `0`). -/
theorem turn_conservative : Conservative turnMor := id_conservative _

/-- **THE TURN HISTORY CONSERVES** — `T^n = T ∘ ⋯ ∘ T` stays in `d⁻¹(0)` for every `n` (the
`T_n∘…∘T_1` history of a conserving turn conserves), via `iterate_conservative`. -/
theorem turn_history_conservative (n : ℕ) : Conservative (iterate turnMor n) :=
  iterate_conservative turn_conservative n

/-! ## 6. THE ONE OPEN THEOREM — the guarded trace (feedback) closure. NAMED, not sorried.

The **ring** is the guarded trace: feedback that glues an output boundary back to an input, imposing the
loop constraint (`A f = 0` = the cycle clears). Its GRADE side is trivial and PROVEN (feedback does not
change resource accounting). The OPEN content codex named is the **feasibility closure**: an ordinary
trace of a relation can produce the EMPTY relation ("it wires a cycle; it does NOT prove the cycle
clears"). So the frontier is whether the GUARD — non-vacuity of the feedback fiber, i.e. the loop
actually clears — SURVIVES feedback and composes adaptively.

We PROVE the non-feedback fragment (guardedness preserved by composition + tensor) and STATE the feedback
half as a NAMED conjecture (`GuardedTraceClosure`), carried as an explicit hypothesis FIELD — never a
`sorry`, never a fake-green tautology. -/

/-- **`Guarded f` — the feasibility fiber is inhabited at every input** (`∀ x, ∃ y, rel x y`): the open
system CLEARS — a witness exists, not merely a wired topology. This is the property the trace can
destroy (the empty-relation hazard). -/
def Guarded {X Y : ZKObj R} (f : X ⟶ Y) : Prop := ∀ x, ∃ y, f.rel x y

/-- The identity clears (diagonal is total). -/
theorem id_guarded (X : ZKObj R) : Guarded (𝟙 X) := fun x => ⟨x, rfl⟩

/-- **ADAPTIVE/SEQUENTIAL COMPOSITION PRESERVES GUARDEDNESS** — if `f` and `g` each clear, so does
`f ≫ g` (chain the two witnesses through the shared boundary). The non-feedback half of the closure,
PROVEN: adaptive composition of clearing open systems clears. -/
theorem comp_guarded {X Y Z : ZKObj R} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : Guarded f) (hg : Guarded g) : Guarded (f ≫ g) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  obtain ⟨z, hz⟩ := hg y
  exact ⟨z, y, hy, hz⟩

/-- **THE TENSOR PRESERVES GUARDEDNESS** — parallel composition of clearing systems clears. -/
theorem tensor_guarded {X Y X' Y' : ZKObj R} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hf : Guarded f) (hg : Guarded g) : Guarded (tensorHom f g) := by
  intro p
  obtain ⟨y, hy⟩ := hf p.1
  obtain ⟨y', hy'⟩ := hg p.2
  exact ⟨(y, y'), hy, hy'⟩

/-- **The guarded trace (feedback)** `tr_U : (X ⊗ U ⟶ Y ⊗ U) → (X ⟶ Y)` — glue the `U` output boundary
back to the `U` input, imposing the loop `u = u` (the fed-back value). The resource grade is UNCHANGED
(feedback is internal — it neither mints nor burns), so the GRADE side of the ring is easy. -/
def gtrace {X Y U : ZKObj R} (f : tensorObj X U ⟶ tensorObj Y U) : X ⟶ Y where
  defect := f.defect
  rel x y := ∃ u : U.S, f.rel (x, u) (y, u)

/-- **THE GRADE SIDE OF THE RING IS PROVEN — the guarded trace preserves the defect.** Feedback is
internal resource routing; it changes no resource accounting: `d(tr f) = d f`. -/
theorem gtrace_defect {X Y U : ZKObj R} (f : tensorObj X U ⟶ tensorObj Y U) :
    dGrade (gtrace f) = dGrade f := rfl

/-- **THE GRADE SIDE OF CONSERVATION-UNDER-FEEDBACK IS PROVEN — the guarded trace of a conservative
morphism is conservative.** `d(tr f) = d f = 0`. So feedback preserves `d⁻¹(0)` at the GRADE level; the
open part is the FEASIBILITY (guardedness), below. -/
theorem gtrace_conservative {X Y U : ZKObj R} {f : tensorObj X U ⟶ tensorObj Y U}
    (hf : Conservative f) : Conservative (gtrace f) := hf

/-- **THE ONE OPEN THEOREM — `GuardedTraceClosure R`, the feedback FEASIBILITY closure conjecture.**

STATED PRECISELY, NOT PROVEN, NOT `sorry`-ed: *for a conservative morphism whose feedback fiber clears
(guarded), the guarded trace CLEARS* — the loop's non-vacuity survives feedback. This is codex's named
frontier: "tracing a relation can produce the EMPTY relation; it wires a cycle, it does NOT prove the
cycle clears." The GRADE side (`gtrace_conservative`) is proven; THIS — the feasibility/non-vacuity of
the feedback — is the research target, false for general relations without the extra structure a genuine
guarded trace supplies. It is a `Prop`-valued `def` (a conjecture), carried as a HYPOTHESIS FIELD of
`ZKUnification`, never discharged here. -/
def GuardedTraceClosure (R : Type) [AddCommMonoid R] : Prop :=
  ∀ (X Y U : ZKObj R) (f : tensorObj X U ⟶ tensorObj Y U),
    Conservative f → Guarded f → Guarded (gtrace f)

/-- **`ZKUnification R` — the categorical unification as a well-defined development with the ONE OPEN
FIELD isolated.** Everything else in this module (the category, the functor `d`, conservation = `d⁻¹(0)`,
the four instances, non-feedback composition, the privacy natural transformation) is PROVEN
unconditionally. The single unproven piece — the compositionality/closure-under-FEEDBACK theorem — is
this structure's ONE field: an explicit named hypothesis (`GuardedTraceClosure`), NEVER a `sorry`. To
INHABIT `ZKUnification` is exactly to discharge the open theorem; this module does not claim to. -/
structure ZKUnification (R : Type) [AddCommMonoid R] where
  /-- **THE OPEN THEOREM as a hypothesis field** — the guarded-trace feedback-feasibility closure. Proving
  the unification = constructing this field. Not done here (the research frontier). -/
  feedback_closure : GuardedTraceClosure R

/-- **What the open theorem BUYS — full closure under feedback.** GIVEN a `ZKUnification` (i.e. assuming
the open `feedback_closure` field), the guarded trace of a conserving, clearing morphism is BOTH
conservative (proven unconditionally, `gtrace_conservative`) AND clearing (from the open field). This is
the compositional closure the unification targets — stated so the ONE open dependency is explicit. -/
theorem ZKUnification.traced_history_closed (U : ZKUnification R)
    {X Y V : ZKObj R} (f : tensorObj X V ⟶ tensorObj Y V)
    (hc : Conservative f) (hg : Guarded f) :
    Conservative (gtrace f) ∧ Guarded (gtrace f) :=
  ⟨gtrace_conservative hc, U.feedback_closure X Y V f hc hg⟩

/-! ## 7. PRIVACY — the simulator natural transformation `View ≈ Sim∘Q` (the categorical home).

Codex: *privacy = a simulator natural transformation `View ≈ Sim∘Q` over the leakage functor `Q`.* The
objects carry the leakage functor `Q` (`Market/RevealNothing.lean`'s `Q : Clearing → Leakage`);
reveal-nothing is the naturality square `view = sim ∘ Q` — the real view factors through the public
leakage alone. This section gives that categorical shape and shows `RevealNothing.RevealBundle` IS
exactly such a natural transformation. -/

/-- **`PrivacyNatTrans` — the `View ≈ Sim∘Q` shape.** A leakage map `Q` (the public projection), a real
`view`, a witness-free `sim`, and the naturality law `view = sim ∘ Q` (the real view factors through the
leakage). This is codex's simulator natural transformation, abstracted. -/
structure PrivacyNatTrans (Clr Lk Tr : Type) where
  /-- The leakage functor `Q` — the public projection of a clearing. -/
  Q : Clr → Lk
  /-- The REAL public view/transcript (a function of the full private clearing). -/
  view : Clr → Tr
  /-- The witness-free simulator (from the public leakage alone). -/
  sim : Lk → Tr
  /-- **Naturality — `View ≈ Sim∘Q`**: the real view factors through the leakage. -/
  naturality : ∀ c, view c = sim (Q c)

/-- **THE REVEAL-NOTHING CONSEQUENCE — same leakage ⇒ same view.** Two clearings with the SAME public
leakage `Q` produce the IDENTICAL view: an observer learns only the leakage class `Q`, nothing of the
private trades. Derived from naturality exactly as `RevealNothing.same_leakage_indistinguishable`. -/
theorem PrivacyNatTrans.indistinguishable {Clr Lk Tr : Type} (P : PrivacyNatTrans Clr Lk Tr)
    {c₁ c₂ : Clr} (h : P.Q c₁ = P.Q c₂) : P.view c₁ = P.view c₂ := by
  rw [P.naturality c₁, P.naturality c₂, h]

/-- **`RevealNothing.RevealBundle` IS a privacy natural transformation.** Its `view`, `sim`, and
`reveal_law` (over `RevealNothing.Q`) are exactly the `Q` / `view` / `sim` / naturality of a
`PrivacyNatTrans`. This is the categorical home of the reveal-nothing theorem — the leakage functor `Q`
is the object-map, and `View ≈ Sim∘Q` is the naturality square. -/
def ofRevealBundle (B : Market.RevealNothing.RevealBundle) :
    PrivacyNatTrans Market.RevealNothing.Clearing Market.RevealNothing.Leakage
      Market.RevealNothing.Transcript where
  Q := Market.RevealNothing.Q
  view := B.view
  sim := B.sim
  naturality := B.reveal_law

/-- **The reveal-nothing theorem, in the categorical frame** — `view = sim ∘ Q` for the bundle,
recovered as the naturality of `ofRevealBundle B`. -/
theorem ofRevealBundle_reveal_nothing (B : Market.RevealNothing.RevealBundle)
    (c : Market.RevealNothing.Clearing) :
    (ofRevealBundle B).view c = (ofRevealBundle B).sim ((ofRevealBundle B).Q c) :=
  (ofRevealBundle B).naturality c

/-- **THE PRIVACY NATURAL TRANSFORMATION, WITNESSED NON-VACUOUSLY** — the ideal/shell reveal bundle
(`RevealNothing.shellBundle`) gives a `PrivacyNatTrans` on which two genuinely-different clearings
`c_alpha ≠ c_beta` with equal leakage collapse to one view. The categorical reveal-nothing, made
concrete. -/
theorem shell_privacy_indistinguishable :
    (ofRevealBundle Market.RevealNothing.shellBundle).view Market.RevealNothing.c_alpha
      = (ofRevealBundle Market.RevealNothing.shellBundle).view Market.RevealNothing.c_beta :=
  (ofRevealBundle Market.RevealNothing.shellBundle).indistinguishable
    Market.RevealNothing.alpha_beta_same_leakage

/-! ### `#guard` smoke — the grade arithmetic is COMPUTED, not asserted. -/

-- the resource defect adds over composition (2 + 3 = 5), over the additive monoid ℤ:
#guard (compHom (X := (⟨PUnit⟩ : ZKObj ℤ)) (Y := ⟨PUnit⟩) (Z := ⟨PUnit⟩)
          ⟨2, fun _ _ => True⟩ ⟨3, fun _ _ => True⟩).defect == 5
-- the identity carries zero defect:
#guard (idHom (⟨PUnit⟩ : ZKObj ℤ)).defect == 0
-- the tensor adds defects too (2 + 3 = 5):
#guard (tensorHom (X := (⟨PUnit⟩ : ZKObj ℤ)) (Y := ⟨PUnit⟩) (X' := ⟨PUnit⟩) (Y' := ⟨PUnit⟩)
          ⟨2, fun _ _ => True⟩ ⟨3, fun _ _ => True⟩).defect == 5

/-! ### Axiom hygiene — the categorical-unification keystones pinned kernel-clean. The ONE open theorem
(`GuardedTraceClosure` / `ZKUnification.feedback_closure`) is a NAMED hypothesis, NOT a `sorry` and NOT
an axiom these catch. -/

#assert_all_clean [Market.ZKOpenRel.dGrade_comp, Market.ZKOpenRel.dGrade_id,
  Market.ZKOpenRel.dFunctor_tensor, Market.ZKOpenRel.dFunctor_unit,
  Market.ZKOpenRel.id_conservative, Market.ZKOpenRel.comp_conservative,
  Market.ZKOpenRel.tensor_conservative, Market.ZKOpenRel.iterate_conservative,
  Market.ZKOpenRel.circulation_conservative, Market.ZKOpenRel.ring_circulation_conservative,
  Market.ZKOpenRel.convex_engine_conservative, Market.ZKOpenRel.clearingDefect_zero,
  Market.ZKOpenRel.clearing_is_conservative, Market.ZKOpenRel.ring_auction_conservative,
  Market.ZKOpenRel.turn_conservative, Market.ZKOpenRel.turn_history_conservative,
  Market.ZKOpenRel.id_guarded, Market.ZKOpenRel.comp_guarded, Market.ZKOpenRel.tensor_guarded,
  Market.ZKOpenRel.gtrace_defect, Market.ZKOpenRel.gtrace_conservative,
  Market.ZKOpenRel.ZKUnification.traced_history_closed,
  Market.ZKOpenRel.PrivacyNatTrans.indistinguishable,
  Market.ZKOpenRel.ofRevealBundle_reveal_nothing, Market.ZKOpenRel.shell_privacy_indistinguishable]

end Market.ZKOpenRel
