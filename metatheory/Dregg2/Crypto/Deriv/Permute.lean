/-
# Dregg2.Crypto.Deriv.Permute — Stage 3 scaffolding: `toSum` / `neSubsets` / `toSumSubsets`.

The over-approximation `pieces R` (the named Stage-3 closure) is collected into a finite set of
candidate derivatives via `toSumSubsets ⊕(pieces R)` = the `alt`-sums of all NON-EMPTY SUBSETS of
`pieces R`. This file builds `toSum` (fold a list into an `alt`-sum, base = `bot`), `neSubsets` (the
non-empty subsets, via `neSublists` + mathlib `permutations'` — subsets up to ORDER, since `Sim` has
`alt`-commutativity), and `toSumSubsets ⊕`, with the append/singleton/extend lemmas the `pieces`
closure consumes.

Ported from ITP'25 `Permute.lean` (read-only blueprint) — the GENERIC `neSubsets` core + the two
`PredRE`-specific `toSum` similarity lemmas (`toSum_append`, `toSum_alt_cong`). The heavy
nodup/permutation-erase block (`nodup_subset_to_neSubsets`, `subset_sim_toSum`) — needed for the
`pieces`-MONOTONICITY half of `finiteness` — is the remaining named wall; this file banks everything
the `pieces`-REFLEXIVITY + single-step closure need.

`#assert_axioms`-clean, `sorry`-free.
-/
import Mathlib.Data.List.Permutation
import Dregg2.Crypto.Deriv.Combinatorics
import Dregg2.Crypto.Deriv.Similarity

namespace Dregg2.Crypto.Deriv

open List
open Dregg2.Crypto.Deriv.Combinatorics
open PredRE (Sim bot)

namespace PredRE

/-! ## `toSum` — fold a list of regexes into an `alt`-sum. -/

/-- **`toSum xs`** — `xs` folded by `alt`, base `bot` (ITP'25 `toSum`). -/
def toSum : List PredRE → PredRE
  | []  => bot
  | [a] => a
  | a::b::bs => .alt a (toSum (b::bs))

/-- **`neSubsets xs`** — non-empty subsets of `xs` (non-empty sublists, each up to permutation). -/
@[simp] def neSubsets (xs : List PredRE) : List (List PredRE) :=
  neSublists xs |>.map permutations' |>.flatten

/-- **`toSumSubsets ⊕xs`** — the `alt`-sums of all non-empty subsets of `xs`. -/
def toSumSubsets (xs : List PredRE) : List PredRE := xs |> neSubsets |>.map toSum

@[inherit_doc] prefix:max "⊕" => toSumSubsets

/-! ## `neSubsets` characterization + append/singleton/extend (generic, port of ITP'25 `Permute`). -/

@[simp] theorem neSubsets_characterization {xs ys : List PredRE} :
    xs ∈ neSubsets ys ↔ ∃ zs, zs ∈ neSublists ys ∧ xs ~ zs := by
  simp only [neSubsets, mem_flatten, mem_map, exists_exists_and_eq_and, mem_permutations']

theorem neSubsets_refl {xs : List PredRE} (ne : xs ≠ []) : xs ∈ neSubsets xs :=
  neSubsets_characterization.mpr ⟨xs, neSublists_unitality ne, Perm.refl xs⟩

theorem neSublist_neSubset {xs ys : List PredRE} (h : xs ∈ neSublists ys) : xs ∈ neSubsets ys :=
  neSubsets_characterization.mpr ⟨xs, h, Perm.refl _⟩

theorem neSubsets_append {x y xs ys : List PredRE}
    (hl : x ∈ neSubsets xs) (hr : y ∈ neSubsets ys) : x ++ y ∈ neSubsets (xs ++ ys) :=
  let ⟨as, as_sub, as_perm⟩ := neSubsets_characterization.mp hl
  let ⟨bs, bs_sub, bs_perm⟩ := neSubsets_characterization.mp hr
  neSubsets_characterization.mpr ⟨as ++ bs, neSublists_append as_sub bs_sub, Perm.append as_perm bs_perm⟩

theorem neSubsets_extend {x : PredRE} {xs ys : List PredRE} (h : xs ∈ neSubsets ys) :
    xs ∈ neSubsets (x::ys) :=
  let ⟨as, as_sub, as_perm⟩ := neSubsets_characterization.mp h
  neSubsets_characterization.mpr ⟨as, neSublists_extend as_sub, as_perm⟩

theorem neSubsets_singleton {x : PredRE} {xs : List PredRE} (h : x ∈ xs) : [x] ∈ neSubsets xs :=
  match xs with
  | [] => False.elim ((mem_nil_iff x).mp h)
  | _::_ =>
    match mem_cons.mp h with
    | Or.inl h1 => mem_of_mem_head? (by subst h1; rfl)
    | Or.inr h1 => neSubsets_extend (neSubsets_singleton h1)

theorem neSubsets_ne {xs ys : List PredRE} (h : xs ∈ neSubsets ys) : xs ≠ [] := fun xs_empty => by
  subst xs_empty
  obtain ⟨zs, zs_sub, zs_perm⟩ := neSubsets_characterization.mp h
  exact (neSub_ne zs_sub) (zs_perm.nil_eq.symm)

/-! ## `toSum` similarity lemmas (the two `PredRE`-specific ones the `pieces` closure consumes). -/

/-- **`toSum_append`** — `toSum (xs ++ ys) ≅ toSum xs ⋓ toSum ys` (for non-empty lists). ITP'25
`toSum_append`. The associativity congruence of `Sim` does the work. -/
theorem toSum_append {xs ys : List PredRE} (_ : xs ≠ []) (h1 : ys ≠ []) :
    toSum (xs ++ ys) ≅ .alt (toSum xs) (toSum ys) :=
  match xs with
  | x::[] => by
    cases ys with
    | nil => simp only [ne_eq, not_true_eq_false] at h1
    | cons _ _ => exact Sim.rfl
  | _::a::as => Sim.trans (Sim.altCong Sim.rfl (toSum_append (cons_ne_nil a as) h1)) (Sim.sym Sim.assoc)

/-- **`toSum_alt_cong`** — congruence: `toSum (x::xs) ≅ toSum (y::ys)` from `x ≅ y` and
`toSum xs ≅ toSum ys` (non-empty). ITP'25 `toSum_alt_cong`. -/
theorem toSum_alt_cong {x y : PredRE} {xs ys : List PredRE}
    (_ : xs ≠ []) (_ : ys ≠ []) (eqv : x ≅ y) (eqv_fs : toSum xs ≅ toSum ys) :
    toSum (x :: xs) ≅ toSum (y :: ys) :=
  match xs, ys with
  | _::_, _::_ => Sim.altCong eqv eqv_fs

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.neSubsets_characterization,
  Dregg2.Crypto.Deriv.PredRE.neSubsets_append,
  Dregg2.Crypto.Deriv.PredRE.neSubsets_singleton,
  Dregg2.Crypto.Deriv.PredRE.neSubsets_extend,
  Dregg2.Crypto.Deriv.PredRE.toSum_append,
  Dregg2.Crypto.Deriv.PredRE.toSum_alt_cong
]
