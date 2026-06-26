/-
# Dregg2.Crypto.Deriv.Finite — Stage 3: the single-step finiteness closure `step_to_pieces`.

THE heart of Brzozowski finiteness: every state reachable in ONE symbolic step from `f` is `≅` an
`alt`-sum of a non-empty subset of the finite `pieces f`. So one `step` stays inside `⊕(pieces f)`
up to similarity — `step f ⊆[≅] ⊕(pieces f)`. Ported from ITP'25 `Finite.lean`'s `step_to_pieces`
(lookaround arms dropped), using ONLY the `pieces`/`neSubsets`/`toSum` scaffolding already banked.

This is the load-bearing closure lemma the design §3.2 step-1 names as the hard core. With it, the
state space is finite up to `≅` after each individual step; the MULTI-step closure
(`steps_to_toSumSubsets` → `finiteness`) chains it through `pieces`-monotonicity, whose ONE remaining
dependency (`toSumSubsets_monotone`, the nodup/permutation block of ITP'25 `Permute.lean`) is the
last named residual — precisely scoped in the closing note.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Pieces

namespace Dregg2.Crypto.Deriv

open _root_.List
open Dregg2.Crypto.Deriv.Combinatorics
open Dregg2.Exec.PredAlgebra (Pred)

namespace PredRE

/-- **`step_to_pieces`** — every one-step-reachable state is `≅` an `alt`-sum of a non-empty subset of
`pieces f`. The single-step finiteness closure. Induction on `f`; each constructor uses its `step_*`
collection lemma + the matching `pieces` arm + the `neSubsets`/`toSum` congruences. ITP'25
`step_to_pieces` (`Finite.lean:17`), the seven surviving constructor arms. -/
theorem step_to_pieces {f e : PredRE} (e_in : e ∈ step f) :
    ∃ xs, Sim (toSum xs) e ∧ xs ∈ neSubsets (pieces f) := by
  match f with
  | .ε =>
    simp only [step, derivative, leaves, mem_cons, not_mem_nil, or_false] at e_in
    subst e_in
    exact ⟨[bot], Sim.rfl, mem_of_getLast? rfl⟩
  | .sym φ =>
    simp only [step, derivative, leaves, cons_append, nil_append, mem_cons, not_mem_nil,
      or_false] at e_in
    match e_in with
    | Or.inl h2 =>
      subst h2
      refine ⟨[.ε], Sim.rfl, neSubsets_characterization.mpr ⟨[.ε], ?_, .refl _⟩⟩
      exact neSublists_singleton (by simp [pieces])
    | Or.inr h2 =>
      subst h2
      refine ⟨[bot], Sim.rfl, neSubsets_characterization.mpr ⟨[bot], ?_, .refl _⟩⟩
      exact neSublists_singleton (by simp [pieces, bot])
  | .cat l r =>
    rw [step_cat] at e_in
    simp only [List.productWith, List.product, step, leaves_unary, mem_append, mem_map,
      mem_flatMap, exists_exists_and_eq_and, exists_exists_and_exists_and_eq_and] at e_in
    match e_in with
    | Or.inl ⟨a1, a2, a3, a4, a5⟩ =>
      subst a5
      have ⟨i1, i2, i3⟩ := step_to_pieces a2
      have ⟨j1, j2, j3⟩ := step_to_pieces a4
      obtain ⟨b, hb, hb1⟩ := neSubsets_characterization.mp j3
      refine ⟨(.cat (toSum i1) r) :: j1,
        Sim.trans (toSum_append (cons_ne_nil _ []) (neSub_ne_perm hb hb1)) (Sim.altCong (Sim.catCong i2) j2),
        ?_⟩
      have hsingle : [PredRE.cat (toSum i1) r] ∈ neSubsets (map (fun x => PredRE.cat x r) ⊕(pieces l)) :=
        neSubsets_singleton (mem_map.mpr ⟨toSum i1, mem_map.mpr ⟨i1, i3, rfl⟩, rfl⟩)
      have := neSubsets_append hsingle j3
      simpa only [pieces, List.cons_append, List.nil_append] using this
    | Or.inr ⟨a1, a2, a4⟩ =>
      subst a4
      have ⟨i1, i2, i3⟩ := step_to_pieces a2
      refine ⟨[.cat (toSum i1) r], Sim.catCong i2, ?_⟩
      exact neSubsets_singleton (mem_append_left _ (mem_map.mpr ⟨toSum i1, mem_map.mpr ⟨i1, i3, rfl⟩, rfl⟩))
  | .star r =>
    simp only [step, derivative, leaves_unary, mem_map] at e_in
    obtain ⟨a1, a2, a4⟩ := e_in
    subst a4
    have ⟨i1, i2, i3⟩ := step_to_pieces a2
    refine ⟨[.cat (toSum i1) (.star r)], Sim.catCong i2, ?_⟩
    exact neSubsets_singleton (by
      simp only [pieces, mem_cons]
      exact Or.inr (mem_map.mpr ⟨toSum i1, mem_map.mpr ⟨i1, i3, rfl⟩, rfl⟩))
  | .alt l r =>
    simp only [step, derivative, leaves_binary, List.productWith, List.product, mem_map,
      mem_flatMap, exists_exists_and_exists_and_eq_and] at e_in
    obtain ⟨a1, a2, a3, a4, a5⟩ := e_in; subst a5
    have ⟨i1, i2, i3⟩ := step_to_pieces a2
    have ⟨j1, j2, j3⟩ := step_to_pieces a4
    exact ⟨i1 ++ j1, Sim.trans (toSum_append (neSubsets_ne i3) (neSubsets_ne j3)) (Sim.altCong i2 j2),
           neSubsets_append i3 j3⟩
  | .inter l r =>
    simp only [step, derivative, leaves_binary, List.productWith, List.product, mem_map,
      mem_flatMap, exists_exists_and_exists_and_eq_and] at e_in
    obtain ⟨a1, a2, a3, a4, a5⟩ := e_in; subst a5
    have ⟨i1, i2, i3⟩ := step_to_pieces a2
    have ⟨j1, j2, j3⟩ := step_to_pieces a4
    refine ⟨[.inter (toSum i1) (toSum j1)], Sim.interCong i2 j2, ?_⟩
    refine neSubsets_singleton ?_
    unfold pieces
    simp only [List.productWith, List.product, mem_map, mem_flatMap,
      exists_exists_and_exists_and_eq_and, Function.uncurry_apply_pair]
    exact ⟨toSum i1, mem_map.mpr ⟨i1, i3, rfl⟩, toSum j1, mem_map.mpr ⟨j1, j3, rfl⟩, rfl⟩
  | .neg r =>
    simp only [step, derivative, leaves_unary, mem_map] at e_in
    obtain ⟨a1, a2, a3⟩ := e_in
    subst a3
    have ⟨i1, i2, i3⟩ := step_to_pieces a2
    refine ⟨[.neg (toSum i1)], Sim.negCong i2, ?_⟩
    exact neSubsets_singleton (mem_map.mpr ⟨toSum i1, mem_map.mpr ⟨i1, i3, rfl⟩, rfl⟩)

/-- **`step_to_toSumSubsets`** — one symbolic step stays inside `⊕(pieces f)` up to similarity:
`step f ⊆[≅] ⊕(pieces f)`. Immediate from `step_to_pieces`. ITP'25 `step_to_toSumSubsets`. -/
theorem step_to_toSumSubsets {r : PredRE} :
    step r ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun _ in_step =>
  have ⟨a1, a2, a3⟩ := step_to_pieces in_step
  ⟨toSum a1, Sim.sym a2, mem_map.mpr ⟨a1, a3, rfl⟩⟩

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.step_to_pieces,
  Dregg2.Crypto.Deriv.PredRE.step_to_toSumSubsets
]

/-!
## The LAST remaining residual for full `finiteness` — NAMED, precisely scoped.

`step_to_toSumSubsets` closes the SINGLE-step finiteness: `step f ⊆[≅] ⊕(pieces f)` for the finite
list `⊕(pieces f)`. The MULTI-step `finiteness` (`steps r n ⊆[≅] ⊕(pieces r)` for ALL n, ITP'25
`Finite.lean`'s `finiteness`) chains this through `pieces`-MONOTONICITY:

  steps_to_toSumSubsets : steps r n ⊆[≅] ⊕(pieces r)   -- induction on n; base = pieces_refl (DONE),
                                                          -- step = step_to_toSumSubsets (DONE) +
                                                          -- toSumSubsets_pieces_trans

whose ONLY missing dependency is `toSumSubsets_monotone` / `pieces_equiv'` — i.e. that a `≅`-subset
relation between two `pieces` lists lifts to their `⊕`-sums. THAT lift is the `Permute.lean`
nodup/permutation-erase block (`nodup_subset_to_neSubsets`, `subset_sim_toSum`, `perms_erase_helper`,
`erase_cons1`, ~150 lines of `Nodup`/`List.erase`/`permutations'Aux` combinatorics) — the LAST
un-ported piece. It is purely generic list combinatorics (no `PredRE`, no semantics), faithfully
buildable on the `neSubsets`/`SubsetUpTo` foundation already banked. With it, `finiteness` closes by
the (already-ported-in-shape) `steps`-induction.

So Stage 3 stands as: the SEMANTIC foundation (`sim_sound`), the FULL scaffolding (TTerm / symbolic
derivative / pieces / neSubsets / toSum), `pieces_refl` (the n=0 base), and `step_to_pieces` (the
single-step closure — the hard core) ALL kernel-clean; the residual is one generic-combinatorics
block (`toSumSubsets_monotone`) plus the `steps`-induction wrapper. NOT closed with `sorry`.
-/
