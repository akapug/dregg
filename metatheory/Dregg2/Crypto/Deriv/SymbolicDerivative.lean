/-
# Dregg2.Crypto.Deriv.SymbolicDerivative — Stage 3: the SYMBOLIC derivative + `step`/`steps` over `PredRE`.

The CONCRETE derivative `der a R` (Stage 0) reads one specific frame. Finiteness must be
alphabet-INDEPENDENT, so it is proven over the SYMBOLIC derivative: `derivative R : TTerm Pred PredRE`
branches on the leaf predicate `φ` (the `sym` arm becomes `Node φ (Leaf ε) (Leaf bot)`), and `step R`
= the LIST of all leaf-states reachable in one symbolic step. The reachable state space is
`steps R n` (iterate `step`, flatten), and Brzozowski finiteness bounds it up to `≅`.

This file ports ITP'25 `SymbolicDerivative.lean` to `PredRE` (lookaround arms dropped; the `Pred φ`
branch carries the bare predicate `φ` as the `TTerm` condition — no `?=` lookahead, which `PredRE`
lacks). The `step_*` collection lemmas fall straight out of the `TTerm` `leaves` laws.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.TTerm
import Dregg2.Crypto.Deriv.Core

namespace Dregg2.Crypto.Deriv

open List
open Dregg2.Exec.PredAlgebra (Pred)

namespace PredRE

/-- A placeholder branch predicate for the `cat` symbolic node (the split point). The condition is
NOT used for the finiteness COUNT — `step` reads `leaves`, which ignore conditions — so any total
`PredRE → Pred` choice keeps `step_cat` exactly the ITP'25 shape. `tt` (the always-branch) records
that the `cat` derivative's leaf SET is condition-independent. -/
def firstPred (_ : PredRE) : Pred := .tt

/-- **`derivative R`** — the SYMBOLIC derivative: a transition term branching on leaf predicates,
with regex residuals at the leaves. The `sym φ` arm branches on `φ` itself (no lookahead). ITP'25
`derivative` (`SymbolicDerivative.lean:16`), lookaround arms dropped, `PredRE` leaf. -/
@[simp] def derivative : PredRE → TTerm Pred PredRE
  | .ε        => TTerm.Leaf bot
  | .sym φ    => TTerm.Node φ (TTerm.Leaf .ε) (TTerm.Leaf bot)
  | .alt l r  => lift_binary PredRE.alt (derivative l) (derivative r)
  | .inter l r => lift_binary PredRE.inter (derivative l) (derivative r)
  | .star r   => lift_unary (fun x => PredRE.cat x (.star r)) (derivative r)
  | .neg r    => lift_unary PredRE.neg (derivative r)
  | .cat l r  =>
    TTerm.Node (firstPred l)
      (lift_binary PredRE.alt (lift_unary (fun x => PredRE.cat x r) (derivative l)) (derivative r))
      (lift_unary (fun x => PredRE.cat x r) (derivative l))

@[inherit_doc] prefix:max "𝜕 " => derivative

/-- **`step R`** — one symbolic step: the LIST of leaf-states (regex residuals) reachable from `R`. -/
@[simp] def step (r : PredRE) : List PredRE := leaves (𝜕 r)

@[simp] theorem step_neg (r : PredRE) : step (.neg r) = List.map PredRE.neg (step r) := by
  simp only [step, derivative, lift_unary, leaves_fmap]

@[simp] theorem step_star (r : PredRE) :
    step (.star r) = List.map (fun x => PredRE.cat x (.star r)) (step r) :=
  leaves_unary (fun x => PredRE.cat x (.star r)) (𝜕 r)

@[simp] theorem step_alt (r s : PredRE) :
    step (.alt r s) = List.productWith PredRE.alt (step r) (step s) :=
  leaves_binary PredRE.alt (𝜕 r) (𝜕 s)

@[simp] theorem step_inter (r s : PredRE) :
    step (.inter r s) = List.productWith PredRE.inter (step r) (step s) :=
  leaves_binary PredRE.inter (𝜕 r) (𝜕 s)

@[simp] theorem step_cat (r s : PredRE) :
    step (.cat r s) =
      List.productWith PredRE.alt (leaves (lift_unary (fun x => PredRE.cat x s) (𝜕 r))) (step s)
      ++ leaves (lift_unary (fun x => PredRE.cat x s) (𝜕 r)) := by
  simp only [step, derivative, leaves, leaves_binary, List.productWith, leaves_unary]

/-- **`steps R n`** — the state space after `n` symbolic steps (iterate `step`, flatten). -/
@[simp] def steps (r : PredRE) : Nat → List PredRE
  | 0 => [r]
  | Nat.succ n => (steps r n).map step |>.flatten

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.step_neg,
  Dregg2.Crypto.Deriv.PredRE.step_star,
  Dregg2.Crypto.Deriv.PredRE.step_alt,
  Dregg2.Crypto.Deriv.PredRE.step_inter,
  Dregg2.Crypto.Deriv.PredRE.step_cat
]
