/-
# Dregg2.Crypto.Deriv.Pieces — Stage 3: the `pieces` over-approximation + `pieces_refl`.

`pieces R : List PredRE` is the FINITE over-approximation of every derivative-state reachable from
`R` (ITP'25 `Pieces.lean`): a fixed list such that every `step`-reachable state is `≅` an `alt`-sum
of a non-empty SUBSET of `pieces R` (the closure `step_to_pieces`, which whence `finiteness`). This
file ports `pieces`, `topmost_not_union` (no derivative-piece is a top-level `alt` — the structural
invariant the closure rests on), and `pieces_refl` (`R` itself is `≅` an `alt`-sum of a subset of
`pieces R` — the n=0 base of finiteness). All using ONLY the `neSublists`/`neSubsets`/`toSum`
scaffolding already banked (no nodup block).

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Permute
import Dregg2.Crypto.Deriv.SymbolicDerivative

namespace Dregg2.Crypto.Deriv

open _root_.List
open Dregg2.Crypto.Deriv.Combinatorics
open Dregg2.Exec.PredAlgebra (Pred)

namespace PredRE

/-- **`pieces R`** — the finite over-approximation of `R`'s derivative pieces. ITP'25 `pieces`
(`Pieces.lean:16`), lookaround arms dropped, `PredRE` constructors. -/
def pieces : PredRE → List PredRE
  | .ε        => [.ε, bot]
  | .sym φ    => [.sym φ, .ε, bot]
  | .alt l r  => pieces l ++ pieces r
  | .inter l r => List.productWith PredRE.inter ⊕(pieces l) ⊕(pieces r)
  | .cat l r  => map (fun x => PredRE.cat x r) ⊕(pieces l) ++ pieces r
  | .star r   => .star r :: map (fun x => PredRE.cat x (.star r)) ⊕(pieces r)
  | .neg r    => map PredRE.neg ⊕(pieces r)

/-- **`topmost_not_union`** — no piece of any `pieces R` is a top-level `alt`. The structural
invariant that lets the closure peel `alt`s. ITP'25 `topmost_not_union`. -/
theorem topmost_not_union {r x y : PredRE} : ¬ ((PredRE.alt x y) ∈ pieces r) := fun h => by
  match r with
  | .ε => simp only [pieces, mem_cons, reduceCtorEq, not_mem_nil, or_self] at h
  | .sym _ => simp only [pieces, mem_cons, reduceCtorEq, not_mem_nil, or_self] at h
  | .alt l r =>
    match mem_append.mp h with
    | Or.inl h1 => exact topmost_not_union h1
    | Or.inr h1 => exact topmost_not_union h1
  | .inter l r =>
    simp only [pieces, List.productWith, List.product, mem_map, mem_flatMap,
      exists_exists_and_exists_and_eq_and] at h
    obtain ⟨a, b, c, d, e⟩ := h
    simp only [Function.uncurry_apply_pair, reduceCtorEq] at e
  | .cat l r =>
    simp only [pieces, mem_append, mem_map, reduceCtorEq, and_false, exists_false, false_or] at h
    exact topmost_not_union h
  | .star r => simp only [pieces, mem_cons, reduceCtorEq, mem_map, and_false, exists_false, or_self] at h
  | .neg r => simp only [pieces, mem_map, reduceCtorEq, and_false, exists_false] at h

/-- **`pieces_refl`** — `R` is `≅` an `alt`-sum of a non-empty subset of `pieces R`. The n=0 base
of finiteness (`steps R 0 = [R] ⊆[≅] ⊕(pieces R)`). ITP'25 `pieces_refl`. -/
theorem pieces_refl {r : PredRE} :
    ∃ xs, xs ∈ neSublists (pieces r) ∧ toSum xs ≅ r :=
  match r with
  | .ε     => ⟨[.ε], mem_of_mem_head? rfl, Sim.rfl⟩
  | .sym φ => ⟨[.sym φ], mem_of_mem_head? rfl, Sim.rfl⟩
  | .alt l r =>
    have ⟨i1, i2, i3⟩ := pieces_refl (r := l)
    have ⟨j1, j2, j3⟩ := pieces_refl (r := r)
    ⟨i1 ++ j1, neSublists_append i2 j2,
     Sim.trans (toSum_append (neSub_ne i2) (neSub_ne j2)) (Sim.altCong i3 j3)⟩
  | .inter l r =>
    have ⟨i1, i2, i3⟩ := pieces_refl (r := l)
    have ⟨j1, j2, j3⟩ := pieces_refl (r := r)
    ⟨[.inter (toSum i1) (toSum j1)],
     neSublists_singleton (by
        unfold pieces
        simp only [List.productWith, List.product, mem_map, mem_flatMap,
          exists_exists_and_exists_and_eq_and, Function.uncurry_apply_pair]
        refine ⟨toSum i1, ?_, toSum j1, ?_, rfl⟩
        · exact mem_map.mpr ⟨i1, neSubsets_characterization.mpr ⟨i1, i2, Perm.refl _⟩, rfl⟩
        · exact mem_map.mpr ⟨j1, neSubsets_characterization.mpr ⟨j1, j2, Perm.refl _⟩, rfl⟩),
     Sim.interCong i3 j3⟩
  | .star r => ⟨[.star r], mem_of_mem_head? rfl, Sim.rfl⟩
  | .neg r => by
    have ⟨i1, i2, i3⟩ := pieces_refl (r := r)
    refine ⟨[.neg (toSum i1)], neSublists_singleton ?_, Sim.negCong i3⟩
    unfold pieces
    exact mem_map.mpr ⟨toSum i1, mem_map.mpr ⟨i1, neSublist_neSubset i2, rfl⟩, rfl⟩
  | .cat l r =>
    have ⟨i1, i2, i3⟩ := pieces_refl (r := l)
    ⟨[.cat (toSum i1) r],
     neSublists_singleton (mem_append_left _ <|
        mem_map.mpr ⟨toSum i1, mem_map.mpr ⟨i1, neSublist_neSubset i2, rfl⟩, rfl⟩),
     Sim.catCong i3⟩

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.topmost_not_union,
  Dregg2.Crypto.Deriv.PredRE.pieces_refl
]
