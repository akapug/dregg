/-
# Metatheory.Open.FinalCoalgebra — CLOSING the §3 OPEN: the final coalgebra exists.

`Metatheory.Categorical` §3 (`Coalgebra`) states the behaviour endofunctor
`F X = Obs × (Adm → X)` (a Moore/DFA shape), the category of `F`-coalgebras
(`Cell`/`CoalgHom`), and the terminal-coalgebra universal property (`IsFinalCell`).
It proves the *uniqueness* half of finality (`ana_unique`, `final_unique_roundtrip`)
**conditionally** on a final cell existing, but leaves OPEN the *existence*:

    ∃ νF : Cell Obs Adm, IsFinalCell νF

This module CLOSES that OPEN, constructively and `sorry`-free, by exhibiting the
classical **Moore-behaviour** final coalgebra: the carrier is `List Adm → Obs` (a state
is "what would I observe after each finite input word"), the structure map reads the
empty-word observation and shifts each successor by prepending its input letter, and the
anamorphism of any cell `c` sends a state `x` to the function `w ↦ c.obs (run x w)` where
`run` replays the word `w` through `c`'s transitions. Commutation and the *unique*-anamorphism
condition are both proved (uniqueness by induction on the input word), discharging
`IsFinalCell` for ARBITRARY `Obs Adm : Type u`.

No new axioms: `#assert_axioms nuF_exists` (and the keystone lemmas) pins the result to the
kernel's own primitives. We do NOT weaken `IsFinalCell`; this closes the repo's actual
`Metatheory.IsFinalCell` for the repo's actual `Metatheory.Cell`.
-/
import Metatheory.Categorical

namespace Metatheory.Open.FinalCoalgebra

open Metatheory

universe u

variable {Obs Adm : Type u}

/-! ## The carrier: Moore behaviours `List Adm → Obs`. -/

/-- **Replay a word through a cell.** `run c x w` advances state `x` along the input word
`w`, one admissible action at a time. This is the trajectory the anamorphism observes. -/
def run (c : Cell Obs Adm) : c.V → List Adm → c.V
  | x, []      => x
  | x, a :: w  => run c (c.next x a) w

@[simp] theorem run_nil (c : Cell Obs Adm) (x : c.V) : run c x [] = x := rfl

@[simp] theorem run_cons (c : Cell Obs Adm) (x : c.V) (a : Adm) (w : List Adm) :
    run c x (a :: w) = run c (c.next x a) w := rfl

/-- **The final cell `νF`.** Carrier `List Adm → Obs`; structure map reads the empty-word
observation and, for each action `a`, shifts to the behaviour `w ↦ b (a :: w)`. So
`νF.obs b = b []` and `νF.next b a = fun w => b (a :: w)`. -/
def nuF (Obs Adm : Type u) : Cell Obs Adm where
  V := List Adm → Obs
  str := fun b => (b [], fun a => fun w => b (a :: w))

@[simp] theorem nuF_obs (b : List Adm → Obs) : (nuF Obs Adm).obs b = b [] := rfl

@[simp] theorem nuF_next (b : List Adm → Obs) (a : Adm) :
    (nuF Obs Adm).next b a = (fun w => b (a :: w)) := rfl

/-! ## The anamorphism (unfold) into `νF`. -/

/-- **The anamorphism carrier map.** Each state `x` of `c` unfolds to the Moore behaviour
"what `c` observes after replaying the word `w`". -/
def anaMap (c : Cell Obs Adm) : c.V → (nuF Obs Adm).V :=
  fun x => fun w => c.obs (run c x w)

@[simp] theorem anaMap_nil (c : Cell Obs Adm) (x : c.V) :
    anaMap c x [] = c.obs x := rfl

/-- The defining shift law of the anamorphism: an extra leading action `a` on the word is
the same as taking one transition first. This is the computational core of commutation. -/
theorem anaMap_cons (c : Cell Obs Adm) (x : c.V) (a : Adm) (w : List Adm) :
    anaMap c x (a :: w) = anaMap c (c.next x a) w := rfl

/-- **The anamorphism is a coalgebra morphism** `c ⟶ νF`. -/
def anaHom (c : Cell Obs Adm) : CoalgHom c (nuF Obs Adm) where
  f := anaMap c
  commutes := by
    -- `Fmap (anaMap c) ∘ c.str = (nuF …).str ∘ anaMap c`, proved pointwise.
    funext x
    -- LHS = (c.obs x, fun a => anaMap c (c.next x a));  RHS = (anaMap c x [], fun a w => anaMap c x (a::w))
    -- Both components agree: first by `anaMap_nil`, second by `anaMap_cons` under `funext`.
    apply Prod.ext
    · -- observations
      rfl
    · -- successors
      funext a
      funext w
      -- `anaMap c (c.next x a) w = anaMap c x (a :: w)` is `(anaMap_cons …).symm`, but both are rfl.
      rfl

/-! ## Uniqueness of the anamorphism. -/

/-- **Any coalgebra morphism into `νF` is THE anamorphism.** Reading the two coalgebra-square
components off `g.commutes`, one gets, for every state `x`:
  * (head)  `g.f x [] = c.obs x`;
  * (shift) `g.f x (a :: w) = g.f (c.next x a) w`.
Induction on the word `w` (generalizing `x`) then forces `g.f x w = c.obs (run c x w)`. -/
theorem coalgHom_eq_anaMap (c : Cell Obs Adm) (g : CoalgHom c (nuF Obs Adm)) :
    g.f = anaMap c := by
  -- Extract the two component equations from the commuting square.
  -- g.commutes : Fmap g.f ∘ c.str = (nuF …).str ∘ g.f
  have hsq := g.commutes
  -- head: for all x, g.f x [] = c.obs x.
  have head : ∀ x : c.V, g.f x [] = c.obs x := by
    intro x
    have := congrFun hsq x
    -- LHS x = (c.obs x, fun a => g.f (c.next x a)); RHS x = (g.f x [], fun a w => g.f x (a::w))
    -- first components equal:
    have h1 := congrArg Prod.fst this
    -- `Prod.fst (Fmap g.f (c.str x)) = c.obs x`  and  `Prod.fst ((nuF).str (g.f x)) = g.f x []`
    simpa [Fmap, Cell.str, nuF, Cell.obs] using h1.symm
  -- shift: for all x a w, g.f x (a :: w) = g.f (c.next x a) w.
  have shift : ∀ (x : c.V) (a : Adm) (w : List Adm),
      g.f x (a :: w) = g.f (c.next x a) w := by
    intro x a w
    have := congrFun hsq x
    have h2 := congrArg Prod.snd this
    -- `h2 : (fun a => g.f (c.next x a)) = (fun a w => g.f x (a :: w))`
    -- evaluate at `a` then `w`.
    have h2a := congrFun h2 a
    have := congrFun h2a w
    -- `this : g.f (c.next x a) w = g.f x (a :: w)`
    simpa [Fmap, nuF, Cell.next] using this.symm
  -- Now `funext x; funext w` and induct on `w` generalizing `x`.
  funext x w
  induction w generalizing x with
  | nil => simpa using head x
  | cons a w ih =>
    -- g.f x (a :: w) = g.f (c.next x a) w = anaMap c (c.next x a) w = anaMap c x (a :: w)
    rw [shift x a w, ih (c.next x a)]
    rfl

/-! ## `νF` is final. -/

/-- **`nuF` satisfies the terminal-coalgebra universal property.** Existence of the unfold is
`anaHom`; uniqueness of carrier maps is `coalgHom_eq_anaMap` (any two go through the
anamorphism). This is the repo's `Metatheory.IsFinalCell`, unweakened. -/
theorem nuF_isFinal : IsFinalCell (nuF Obs Adm) where
  ana := fun c => ⟨anaHom c⟩
  uniq := fun {c} g h => by
    rw [coalgHom_eq_anaMap c g, coalgHom_eq_anaMap c h]

/-- **THE CLOSE.** The §3 OPEN, discharged: a terminal `F`-coalgebra exists for ARBITRARY
`Obs Adm : Type u`. The carrier is the Moore behaviours `List Adm → Obs`. This is precisely
`∃ νF : Cell Obs Adm, IsFinalCell νF` for the repo's actual `Cell`/`IsFinalCell`. -/
theorem nuF_exists : ∃ νF : Cell Obs Adm, IsFinalCell νF :=
  ⟨nuF Obs Adm, nuF_isFinal⟩

/-! ## Self-check: pin to the kernel (errors if any `sorry`/extra axiom leaked). -/

#assert_axioms nuF_exists
#assert_axioms nuF_isFinal
#assert_axioms coalgHom_eq_anaMap
#assert_axioms anaHom

end Metatheory.Open.FinalCoalgebra
