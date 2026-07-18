/-
# Dregg2.Crypto.Deriv.AciComplete — FRAGMENT COMPLETENESS of `normalize`, and the
# NON-COMMUTATIVITY of `alt` under `≅` as a machine-checked COROLLARY.

`AciNormal.lean` argues in PROSE that `Sim`'s three `alt` laws (`assoc`, `idem`, `dedup`) are the
identities of a **left regular band** (`x(yz)=(xy)z`, `xx=x`, `xyx=xy`) and hence that
`alt a b ≅ alt b a` is NOT derivable — the fact the whole "order-preserving first-occurrence dedup,
never sort" design rests on. That argument is a model-theoretic sketch about the FREE left regular
band; nothing in it was checked. This module replaces it with theorems.

## What is proved

1. **`sim_key`** — the *first-occurrence disjunct sequence* is a `Sim`-INVARIANT on the pure-`alt`
   fragment. Stated as: the partial canonical key `key : PredRE → Option (List PredRE)` is constant
   on `≅`-classes, for EVERY `R S : PredRE` (no side condition — outside the fragment `key` is
   `none` on both sides, which is how the star/cat blind spots are absorbed honestly).

2. **`sim_normalize_eq`** — FRAGMENT COMPLETENESS:
   `Sim R S → Frag R → normalize R = normalize S`, where `Frag R` says every leaf of `R`'s `alt`
   spine is a `reEq`-decidable non-`alt` leaf (`ε`, or `sym p` with `p` in `predBEq`'s fragment).
   `Frag S` is not assumed — it FOLLOWS (`sim_frag`).

3. **`normalize_alt_comm_ne` / `not_sim_alt_comm`** — the FALSIFIER: two concrete distinct leaves
   with `normalize (a ⋓ b) ≠ normalize (b ⋓ a)`, hence by (2) `¬ Sim (a ⋓ b) (b ⋓ a)`. `alt` is
   NOT commutative under `≅`, as a theorem. Any normalizer that SORTS disjuncts therefore has an
   obligation that is not merely unproved but UNPROVABLE.

## How the invariance goes through, generator by generator

The key is `ddf ∘ altList` gated by rigidity, and its one structural law is
`ddf_append : ddf (u ++ v) = mergeR (ddf u) (ddf v)` (`mergeR l m = l ++ m.filter (∉ l)`), which
makes `key` a HOMOMORPHISM into the order-preserving-union monoid (`key_alt`). Then:

* `assoc` — a NO-OP on `altList`: both sides flatten to the same list by `List.append_assoc`.
  (Handled at the list level, so no `mergeR`-associativity is ever needed.)
* `idem` — `mergeR l l = l`; `dedup` — `mergeR l (mergeR m l) = mergeR l m`. Both need only that
  each element `y` of `l` satisfies `reEq y y = true`, which is exactly what rigidity buys.
* `altCong` — free, by the homomorphism `key_alt`.
* `negCong`, `interCong`, `catCong` — both sides have a NON-`alt`, NON-rigid head, so `key` is
  `none` on both. This is where the missing `starCong` / right-`catCong` stop mattering: the
  fragment simply does not contain those leaves, and `key` says so rather than guessing.
* `rfl`/`sym`/`trans` — the closure, for free, because the invariant is an EQUALITY of keys.

## Scope, stated exactly (no laundering)

This is NOT full `PredRE` completeness and does not approach it. `Sim` is not a full congruence
(`altCong` can hold because two DISJUNCTS are similar-but-unequal, e.g.
`alt (star (alt a a)) b ≅ alt (star a) b`), and a non-recursive `normalize` cannot see through that
— recursing would be UNSOUND without `starCong` and a right `catCong`. Under `key` those terms are
`none`, i.e. explicitly OUT of the proven fragment; the residual is unchanged and is restated at the
bottom of this file. Leaves outside `predBEq`'s decidable fragment (`atom`, `symMemberOf`, …) are
likewise out — `rigidLeaf` is fail-closed on them, by the same one-sided-`reEq` discipline as
`AciNormal`.

`Similarity.lean` is NOT edited (its `#assert_not_depends_on` pins stand). `sorry`-free.
-/
import Dregg2.Crypto.Deriv.AciNormal

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

namespace PredRE

/-! ## Rigid leaves — the fragment's alphabet.

A leaf is RIGID when it is not an `alt` (so it is a genuine spine leaf) and `reEq` decides equality
on it (so first-occurrence deletion is exact, not fail-closed). `star`/`cat`/`inter`/`neg` leaves are
deliberately EXCLUDED: `Sim` can relate them to unequal terms through `altCong` + the missing
`starCong`, which is precisely the blind spot this fragment is carved to avoid. -/

/-- **`rigidLeaf R`** — `R` is a non-`alt` leaf on which `reEq` is a decision procedure. -/
def rigidLeaf : PredRE → Bool
  | .ε     => true
  | .sym p => predBEq p p
  | _      => false

/-- On a rigid leaf, `reEq` is REFLEXIVE — the half `reEq_sound` does not give, and the half the
deduplication laws need. -/
theorem reEq_refl_of_rigid {R : PredRE} (h : rigidLeaf R = true) : reEq R R = true := by
  cases R with
  | ε => rfl
  | sym p => simpa [reEq] using h
  | _ => simp [rigidLeaf] at h

/-! ## The order-preserving union monoid. -/

/-- `notMemR l y` — `y` has NO `reEq`-match in `l`. -/
def notMemR (l : List PredRE) (y : PredRE) : Bool := !(l.any (fun x => reEq x y))

/-- **`mergeR l m`** — order-preserving union: keep `l`, then append the elements of `m` that are
new. This is the multiplication of the free left regular band, written on lists. -/
def mergeR (l m : List PredRE) : List PredRE := l ++ m.filter (notMemR l)

/-- **`ddf l`** — first-occurrence deduplication, structurally recursive (the `dedupFirst` of
`AciNormal` is the same function; see `dedupFirst_eq_ddf`). -/
def ddf : List PredRE → List PredRE
  | []      => []
  | x :: xs => x :: (ddf xs).filter (fun y => !reEq x y)

theorem ddf_subset : ∀ {l : List PredRE} {y}, y ∈ ddf l → y ∈ l := by
  intro l
  induction l with
  | nil => intro y h; simp [ddf] at h
  | cons x xs ih =>
    intro y h
    rw [ddf] at h
    rcases List.mem_cons.mp h with h | h
    · exact h ▸ List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih (List.mem_of_mem_filter h))

/-- If every element of `m` already has a match in `l`, the merge adds nothing. -/
theorem filter_notMemR_nil {l m : List PredRE}
    (h : ∀ y ∈ m, ∃ x ∈ l, reEq x y = true) : m.filter (notMemR l) = [] := by
  induction m with
  | nil => rfl
  | cons y ys ih =>
    have hy : notMemR l y = false := by
      obtain ⟨x, hx, hxy⟩ := h y (List.mem_cons_self ..)
      simp only [notMemR, Bool.not_eq_false']
      exact List.any_eq_true.mpr ⟨x, hx, hxy⟩
    rw [List.filter_cons, hy]
    simpa using ih (fun z hz => h z (List.mem_cons_of_mem _ hz))

/-- `mergeR l l = l` for a list of rigid leaves — the `idem` law, on lists. -/
theorem mergeR_self {l : List PredRE} (hr : ∀ y ∈ l, reEq y y = true) : mergeR l l = l := by
  rw [mergeR, filter_notMemR_nil (fun y hy => ⟨y, hy, hr y hy⟩), List.append_nil]

/-- `mergeR l (mergeR m l) = mergeR l m` for a list of rigid leaves — the `dedup` law (`xyx = xy`),
on lists. This is the left-regular-band identity itself. -/
theorem mergeR_dedup {l m : List PredRE} (hr : ∀ y ∈ l, reEq y y = true) :
    mergeR l (mergeR m l) = mergeR l m := by
  have hnil : (l.filter (notMemR m)).filter (notMemR l) = [] :=
    filter_notMemR_nil (fun y hy =>
      ⟨y, List.mem_of_mem_filter hy, hr y (List.mem_of_mem_filter hy)⟩)
  simp only [mergeR, List.filter_append, hnil, List.append_nil]

/-- **`ddf_append`** — the homomorphism law: first-occurrence dedup of a concatenation is the
order-preserving union of the parts' dedups. The whole invariance argument rests on this. -/
theorem ddf_append (u v : List PredRE) : ddf (u ++ v) = mergeR (ddf u) (ddf v) := by
  induction u with
  | nil =>
    simp only [List.nil_append, ddf, mergeR]
    rw [List.filter_eq_self.mpr (fun y _ => by simp [notMemR])]
  | cons x u ih =>
    have hpred : (fun y => !reEq x y && notMemR (ddf u) y)
        = notMemR (x :: (ddf u).filter (fun y => !reEq x y)) := by
      funext y
      by_cases hxy : reEq x y = true
      · simp [notMemR, hxy]
      · have hxy' : reEq x y = false := by simpa using hxy
        have hiff : ((ddf u).filter (fun z => !reEq x z)).any (fun z => reEq z y)
            = (ddf u).any (fun z => reEq z y) := by
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h
            obtain ⟨z, hz, hzy⟩ := List.any_eq_true.mp h
            exact List.any_eq_true.mpr ⟨z, List.mem_of_mem_filter hz, hzy⟩
          · intro h
            obtain ⟨z, hz, hzy⟩ := List.any_eq_true.mp h
            have hzeq : z = y := reEq_sound hzy
            refine List.any_eq_true.mpr ⟨z, List.mem_filter.mpr ⟨hz, ?_⟩, hzy⟩
            simp [hzeq, hxy']
        simp [notMemR, hxy', hiff]
    calc ddf (x :: u ++ v)
        = x :: (mergeR (ddf u) (ddf v)).filter (fun y => !reEq x y) := by
          rw [List.cons_append, ddf, ih]
      _ = x :: ((ddf u).filter (fun y => !reEq x y)
              ++ ((ddf v).filter (notMemR (ddf u))).filter (fun y => !reEq x y)) := by
          rw [mergeR, List.filter_append]
      _ = mergeR (ddf (x :: u)) (ddf v) := by
          rw [ddf, mergeR, List.cons_append, List.filter_filter, hpred]

/-! ## `dedupFirst` IS `ddf` — the bridge to `AciNormal.normalize`. -/

theorem dropEq_subset {x : PredRE} : ∀ {l : List PredRE} {y}, y ∈ dropEq x l → y ∈ l := by
  intro l
  induction l with
  | nil => intro y h; simp [dropEq] at h
  | cons a as ih =>
    intro y h
    rw [dropEq] at h
    split at h
    · exact List.mem_cons_of_mem _ (ih h)
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

theorem reEq_false_of_mem_dropEq {x : PredRE} :
    ∀ {l : List PredRE} {y}, y ∈ dropEq x l → reEq x y = false := by
  intro l
  induction l with
  | nil => intro y h; simp [dropEq] at h
  | cons a as ih =>
    intro y h
    rw [dropEq] at h
    split at h
    · exact ih h
    · rename_i hxa
      rcases List.mem_cons.mp h with h | h
      · subst h; simpa using hxa
      · exact ih h

theorem dropEq_comm (x y : PredRE) (l : List PredRE) :
    dropEq x (dropEq y l) = dropEq y (dropEq x l) := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hx : reEq x a = true <;> by_cases hy : reEq y a = true <;>
      simp_all [dropEq]

theorem dedupFirst_subset : ∀ (n : Nat) (l : List PredRE), l.length ≤ n → ∀ {y},
    y ∈ dedupFirst l → y ∈ l := by
  intro n
  induction n with
  | zero =>
    intro l hl y hy
    cases l with
    | nil => simp [dedupFirst] at hy
    | cons a as => simp at hl
  | succ n ih =>
    intro l hl y hy
    cases l with
    | nil => simp [dedupFirst] at hy
    | cons a as =>
      rw [dedupFirst] at hy
      rcases List.mem_cons.mp hy with h | h
      · exact h ▸ List.mem_cons_self ..
      · have hlen : (dropEq a as).length ≤ n :=
          Nat.le_trans (dropEq_length_le a as) (by simpa using hl)
        exact List.mem_cons_of_mem _ (dropEq_subset (ih _ hlen h))

theorem dedupFirst_dropEq_aux : ∀ (n : Nat) (l : List PredRE), l.length ≤ n → ∀ x : PredRE,
    dedupFirst (dropEq x l) = (dedupFirst l).filter (fun y => !reEq x y) := by
  intro n
  induction n with
  | zero =>
    intro l hl x
    cases l with
    | nil => simp [dropEq, dedupFirst]
    | cons a as => simp at hl
  | succ n ih =>
    intro l hl x
    cases l with
    | nil => simp [dropEq, dedupFirst]
    | cons a as =>
      have hasn : as.length ≤ n := by simpa using hl
      have hdropn : (dropEq a as).length ≤ n := Nat.le_trans (dropEq_length_le a as) hasn
      by_cases hxa : reEq x a = true
      · have hxa' : x = a := reEq_sound hxa
        subst hxa'
        have hfilter : (dedupFirst (dropEq x as)).filter (fun y => !reEq x y)
            = dedupFirst (dropEq x as) := by
          apply List.filter_eq_self.mpr
          intro y hy
          have := reEq_false_of_mem_dropEq (dedupFirst_subset n _ hdropn hy)
          simp [this]
        rw [dropEq, if_pos hxa, dedupFirst, List.filter_cons, hxa]
        simpa using hfilter.symm
      · have hxa' : reEq x a = false := by simpa using hxa
        rw [dropEq, if_neg (by simp [hxa']), dedupFirst, dedupFirst,
          List.filter_cons, hxa']
        rw [dropEq_comm, ih (dropEq a as) hdropn x]
        simp

/-- **`dedupFirst_eq_ddf`** — `AciNormal`'s well-founded `dedupFirst` is the structurally recursive
`ddf`. Everything proved about `ddf` therefore lands on `normalize`. -/
theorem dedupFirst_eq_ddf : ∀ (n : Nat) (l : List PredRE), l.length ≤ n → dedupFirst l = ddf l := by
  intro n
  induction n with
  | zero =>
    intro l hl
    cases l with
    | nil => simp [dedupFirst, ddf]
    | cons a as => simp at hl
  | succ n ih =>
    intro l hl
    cases l with
    | nil => simp [dedupFirst, ddf]
    | cons a as =>
      have hasn : as.length ≤ n := by simpa using hl
      rw [dedupFirst, ddf, dedupFirst_dropEq_aux as.length as (Nat.le_refl _) a,
        ih as hasn]

theorem dedupFirst_eq_ddf' (l : List PredRE) : dedupFirst l = ddf l :=
  dedupFirst_eq_ddf l.length l (Nat.le_refl _)

/-! ## The canonical key, and its `Sim`-invariance. -/

/-- `allRigid l` — every element of `l` is a rigid leaf. -/
def allRigid (l : List PredRE) : Bool := l.all rigidLeaf

/-- **`key R`** — the first-occurrence disjunct SEQUENCE of `R`'s `alt` spine, when every leaf of
that spine is rigid; `none` otherwise. `none` is the honest answer for terms outside the fragment
(a `star`/`cat`/`inter`/`neg` leaf, or a leaf outside `predBEq`'s decidable fragment). -/
def key (R : PredRE) : Option (List PredRE) :=
  if allRigid (altList R) then some (ddf (altList R)) else none

/-- **`Frag R`** — `R` is in the PURE-`alt` FRAGMENT: it is built from `alt` over leaves that are
`reEq`-decidable and are not themselves `alt`. -/
def Frag (R : PredRE) : Prop := allRigid (altList R) = true

theorem key_eq_some_of_frag {R : PredRE} (h : Frag R) : key R = some (ddf (altList R)) :=
  if_pos h

theorem frag_of_key_some {R : PredRE} {l} (h : key R = some l) : Frag R := by
  unfold key at h
  split at h
  · assumption
  · exact absurd h (by simp)

theorem key_rigid {R : PredRE} {l : List PredRE} (h : key R = some l) :
    ∀ y ∈ l, reEq y y = true := by
  have hf : Frag R := frag_of_key_some h
  have hl : l = ddf (altList R) := by
    rw [key_eq_some_of_frag hf] at h; exact (Option.some.inj h).symm
  intro y hy
  subst hl
  have hmem : y ∈ altList R := ddf_subset hy
  exact reEq_refl_of_rigid (List.all_eq_true.mp hf y hmem)

theorem altList_alt (l r : PredRE) : altList (.alt l r) = altList l ++ altList r := rfl

/-- **`key_alt`** — `key` is a HOMOMORPHISM from `alt` to `mergeR`. This is what makes the
congruence case of the invariance free. -/
theorem key_alt (R S : PredRE) :
    key (.alt R S) = (key R).bind (fun l => (key S).bind (fun m => some (mergeR l m))) := by
  unfold key
  rw [altList_alt]
  have hall : allRigid (altList R ++ altList S) = (allRigid (altList R) && allRigid (altList S)) := by
    simp [allRigid, List.all_append]
  rw [hall, ddf_append]
  cases hR : allRigid (altList R) <;> cases hS : allRigid (altList S) <;> simp

/-- Non-`alt`, non-rigid heads are OUT of the fragment: `key = none`. This is the clause that
absorbs `negCong` / `interCong` / `catCong` — and, silently, the absent `starCong`. -/
theorem key_neg (R : PredRE) : key (.neg R) = none := by simp [key, altList, allRigid, rigidLeaf]
theorem key_inter (R S : PredRE) : key (.inter R S) = none := by
  simp [key, altList, allRigid, rigidLeaf]
theorem key_cat (R S : PredRE) : key (.cat R S) = none := by
  simp [key, altList, allRigid, rigidLeaf]

/-- **`sim_key`** — THE INVARIANCE THEOREM: the first-occurrence disjunct sequence is constant on
`≅`-classes. Induction on the `Sim` derivation; every generator is discharged above. Holds for ALL
of `PredRE` — outside the fragment both sides are `none`, which is a true statement about a
deliberately partial invariant, not a completeness claim. -/
theorem sim_key {R S : PredRE} (h : Sim R S) : key R = key S := by
  induction h with
  | @assoc R₁ R₂ R₃ =>
    simp only [key, altList_alt, List.append_assoc]
  | @dedup R₁ R₂ =>
    rw [key_alt, key_alt, key_alt]
    cases hR : key R₁ with
    | none => simp
    | some l =>
      cases hS : key R₂ with
      | none => simp
      | some m => simp [mergeR_dedup (key_rigid hR)]
  | @idem R =>
    rw [key_alt]
    cases hR : key R with
    | none => simp
    | some l => simp [mergeR_self (key_rigid hR)]
  | rfl => rfl
  | sym _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | negCong _ _ => rw [key_neg, key_neg]
  | altCong _ _ ih₁ ih₂ => rw [key_alt, key_alt, ih₁, ih₂]
  | interCong _ _ _ _ => rw [key_inter, key_inter]
  | catCong _ _ => rw [key_cat, key_cat]

/-- The fragment is `Sim`-CLOSED: it is not an assumption on the right-hand side, it is a
consequence. -/
theorem sim_frag {R S : PredRE} (h : Sim R S) (hR : Frag R) : Frag S :=
  frag_of_key_some ((sim_key h) ▸ key_eq_some_of_frag hR)

/-! ## FRAGMENT COMPLETENESS of `normalize`. -/

/-- Refold a non-empty disjunct list. -/
def foldList : List PredRE → PredRE
  | []      => .ε
  | x :: xs => foldAlt x xs

/-- `normalize` IS "flatten, `ddf`, refold" — the bridge from `AciNormal`'s definition to the
canonical key. -/
theorem normalize_eq_foldList (R : PredRE) : normalize R = foldList (ddf (altList R)) := by
  unfold normalize
  cases h : altList R with
  | nil => exact absurd h (altList_ne_nil R)
  | cons x xs =>
    rw [← dedupFirst_eq_ddf' (x :: xs), dedupFirst]
    rfl

/-- **`sim_normalize_eq`** — FRAGMENT COMPLETENESS. For terms of the pure-`alt` fragment (an `alt`
tree over `reEq`-decidable non-`alt` leaves), `normalize` is a COMPLETE invariant of `≅`: similar
terms have EQUAL normal forms. Together with `AciNormal.normalize_sim` (soundness) this makes
`reEq (normalize R) (normalize S)` a genuine decision procedure for `≅` ON THAT FRAGMENT. -/
theorem sim_normalize_eq {R S : PredRE} (h : Sim R S) (hR : Frag R) : normalize R = normalize S := by
  have hkey : some (ddf (altList R)) = some (ddf (altList S)) := by
    rw [← key_eq_some_of_frag hR, ← key_eq_some_of_frag (sim_frag h hR)]; exact sim_key h
  rw [normalize_eq_foldList, normalize_eq_foldList, Option.some.inj hkey]

/-- The `←` direction, for the record: equal normal forms always imply similarity (this needs no
fragment hypothesis — it is `normalize_sim` plus `sym`/`trans`). -/
theorem normalize_eq_sim {R S : PredRE} (h : normalize R = normalize S) : Sim R S :=
  Sim.trans (Sim.sym (normalize_sim R)) (h ▸ normalize_sim S)

/-! ## THE FALSIFIER — `alt` is NOT commutative under `≅`.

The prose claim of `AciNormal.lean` ("the free left regular band on two generators has `ab ≠ ba`,
so `alt a b ≅ alt b a` is not derivable") is now a COROLLARY of fragment completeness, checked
against the ACTUAL `Sim` rather than against a model of it. -/

section Falsifier

private def q7 : Pred := .symEq "k" 7
private def q9 : Pred := .symEq "k" 9
private def s7 : PredRE := .sym q7
private def s9 : PredRE := .sym q9

theorem frag_s7_s9 : Frag (.alt s7 s9) := by unfold Frag; decide
theorem frag_s9_s7 : Frag (.alt s9 s7) := by unfold Frag; decide

theorem normalize_s7_s9 : normalize (.alt s7 s9) = .alt s7 s9 := by
  rw [normalize_eq_foldList]
  simp [altList, ddf, foldList, foldAlt, reEq, predBEq, s7, s9, q7, q9]

theorem normalize_s9_s7 : normalize (.alt s9 s7) = .alt s9 s7 := by
  rw [normalize_eq_foldList]
  simp [altList, ddf, foldList, foldAlt, reEq, predBEq, s7, s9, q7, q9]

theorem s7_ne_s9 : s7 ≠ s9 := by
  intro h
  simp [s7, s9, q7, q9] at h

/-- The two orders have DIFFERENT normal forms — decided, not asserted. -/
theorem normalize_alt_comm_ne : normalize (.alt s7 s9) ≠ normalize (.alt s9 s7) := by
  rw [normalize_s7_s9, normalize_s9_s7]
  intro h
  injection h with h1 _
  exact s7_ne_s9 h1

/-- **`not_sim_alt_comm`** — THE THEOREM the whole design rests on: `alt` is NOT commutative under
`≅`. Contrapositive of fragment completeness against the computed disequality above. A normalizer
that SORTS the disjunct list would need exactly this similarity, and it does not exist. -/
theorem not_sim_alt_comm : ¬ Sim (.alt s7 s9) (.alt s9 s7) := by
  intro h
  exact normalize_alt_comm_ne (sim_normalize_eq h frag_s7_s9)

/-- NON-VACUITY of `sim_normalize_eq`: a POSITIVE instance. `(a ⋓ b) ⋓ a ≅ a ⋓ b` really holds (by
`assoc` + `dedup`), both sides really are in the fragment, and completeness really equates their
normal forms — so the theorem is not merely true because its hypothesis is unsatisfiable. -/
theorem sim_dedup_witness : Sim (.alt (.alt s7 s9) s7) (.alt s7 s9) :=
  Sim.trans Sim.assoc Sim.dedup

theorem normalize_dedup_witness :
    normalize (.alt (.alt s7 s9) s7) = normalize (.alt s7 s9) :=
  sim_normalize_eq sim_dedup_witness (by unfold Frag; decide)

/-- …and the general shape: on the fragment, two distinct-normal-form terms are NEVER similar. -/
theorem not_sim_of_normalize_ne {R S : PredRE} (hR : Frag R)
    (h : normalize R ≠ normalize S) : ¬ Sim R S :=
  fun hs => h (sim_normalize_eq hs hR)

end Falsifier

/-! ## `#guard`s — the fragment predicate and the key are what they claim to be. -/

section Guards

private def g7 : PredRE := .sym (.symEq "k" 7)
private def g9 : PredRE := .sym (.symEq "k" 9)
private def gAtom : PredRE := .sym (.atom (.fieldLeField "a" "b"))

/-- `PredRE` has no `DecidableEq`, so the guards compare keys through the one-sided `reEq`
(fail-closed: a `true` here is a real equality, by `reEq_sound`). -/
private def keyBEq : Option (List PredRE) → Option (List PredRE) → Bool
  | none,   none   => true
  | some l, some m => l.length == m.length && (l.zip m).all (fun p => reEq p.1 p.2)
  | _,      _      => false

-- IN the fragment: `alt` trees over `ε`/decidable `sym` leaves.
#guard allRigid (altList (.alt (.alt g7 g9) g7)) = true
#guard allRigid (altList (.alt g7 .ε)) = true
-- OUT of the fragment, fail-closed: a `star` leaf, and an `atom` leaf.
#guard allRigid (altList (.alt (.star g7) g9)) = false
#guard allRigid (altList (.alt gAtom g9)) = false
#guard (key (.alt (.star g7) g9)).isNone = true
#guard (key (.alt gAtom g9)).isNone = true

-- The key really is the ORDER-PRESERVING first-occurrence sequence, and it SEPARATES the two orders.
#guard keyBEq (key (.alt (.alt g7 g9) g7)) (some [g7, g9]) = true
#guard keyBEq (key (.alt g9 g7)) (some [g9, g7]) = true
#guard keyBEq (key (.alt g7 g9)) (key (.alt g9 g7)) = false
-- …while genuinely IDENTIFYING the ACI-redundant spellings.
#guard keyBEq (key (.alt (.alt g7 g9) g7)) (key (.alt g7 g9)) = true
#guard keyBEq (key (.alt g7 (.alt g9 g7))) (key (.alt g7 g9)) = true
#guard keyBEq (key (.alt g7 g7)) (key g7) = true

end Guards

end PredRE

/-! ## Axiom hygiene. -/

#assert_all_clean [
  PredRE.reEq_refl_of_rigid, PredRE.ddf_subset, PredRE.filter_notMemR_nil,
  PredRE.mergeR_self, PredRE.mergeR_dedup, PredRE.ddf_append,
  PredRE.dropEq_subset, PredRE.reEq_false_of_mem_dropEq, PredRE.dropEq_comm,
  PredRE.dedupFirst_subset, PredRE.dedupFirst_dropEq_aux, PredRE.dedupFirst_eq_ddf',
  PredRE.key_alt, PredRE.key_neg, PredRE.key_inter, PredRE.key_cat,
  PredRE.sim_key, PredRE.sim_frag,
  PredRE.normalize_eq_foldList, PredRE.sim_normalize_eq, PredRE.normalize_eq_sim,
  PredRE.sim_dedup_witness, PredRE.normalize_dedup_witness,
  PredRE.normalize_alt_comm_ne, PredRE.not_sim_alt_comm, PredRE.not_sim_of_normalize_ne
]

/-!
## THE RESIDUAL — what is still NOT proved (unchanged by this module, restated exactly).

`normalize_complete` on FULL `PredRE` — `∀ R S, Sim R S → normalize R = normalize S` — remains open,
and this module does not narrow it in the two places `AciNormal` named:

1. **Non-rigid leaves.** `key` is `none` on any spine containing a `star`/`cat`/`inter`/`neg` leaf,
   because `Sim` can relate two such leaves without them being EQUAL (`altCong` + `interCong` +
   `catCong`), and a non-recursive `normalize` cannot see it. Closing this needs `Sim` to become a
   FULL congruence (`starCong`, a right `catCong`) and `normalize` to recurse — an edit to
   `Similarity.lean` that must re-prove `sim_null`/`sim_der`/`sim_sound` for the new constructors and
   keep its `#assert_not_depends_on` pins passing. NOT attempted here.
2. **Fail-closed leaf equality.** `rigidLeaf` demands `predBEq p p = true`, so `atom`,
   `symMemberOf`, `digFieldEq`, … leaves are outside the fragment even though they are perfectly good
   non-`alt` leaves. This is the SAME one-sided-`reEq` boundary as `AciNormal`, and it widens exactly
   as far as `predBEq` does: a real `DecidableEq StateConstraint` (an edit to `Exec/Program.lean`)
   would extend `rigidLeaf`, and every theorem above transports unchanged — the invariance argument
   uses only `reEq_sound` plus reflexivity on the fragment.

What IS closed: the design question. The order-preserving first-occurrence normal form is a COMPLETE
invariant of `≅` on the pure-`alt` fragment (`sim_normalize_eq`), and the SORTED normal form is
UNREACHABLE (`not_sim_alt_comm`) — not merely unproved. The "months-scale `Permute`/`Pieces`"
estimate was priced against the sorting picture; the theorem above says that price bought nothing,
because the commutativity it needs is false.
-/

end Dregg2.Crypto.Deriv
