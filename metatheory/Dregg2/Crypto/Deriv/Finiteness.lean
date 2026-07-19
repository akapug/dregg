/-
# Dregg2.Crypto.Deriv.Finiteness — Stage 3 CAPSTONE: `der_finite` (Brzozowski finiteness).

The multi-step finiteness: the ENTIRE symbolic-derivative state space reachable from `r` — `steps r n`
for ALL `n` — is contained, UP TO SIMILARITY `≅`, in the FIXED finite list `⊕(pieces r)`. So `r` has
finitely many derivatives up to ACI-normalization — Brzozowski finiteness over `PredRE`.

Chains the single-step closure (`step_to_pieces`, banked) through `pieces`-MONOTONICITY
(`toSumSubsets_monotone`, banked) via the `pieces`-similarity/transitivity layer ported here
(`pieces_equiv'` / `pieces_trans'` / the `toSumSubsets_pieces_refl/_trans`), then the `steps`
induction. Ported from ITP'25 `Pieces.lean` + `Finite.lean` (read-only blueprint, lookaround arms
dropped, v4.30 mathlib API).

`#assert_axioms`-clean (subset {propext, Classical.choice, Quot.sound}), `sorry`-free.

THIS CLOSES Stage 3 (design §3.2 hard core #1, `der_finite`).
-/
import Dregg2.Crypto.Deriv.Finite
import Dregg2.Crypto.Deriv.Monotone

namespace Dregg2.Crypto.Deriv

open _root_.List
open Dregg2.Crypto.Deriv.Combinatorics
open Dregg2.Exec.PredAlgebra (Pred)
open PredRE (Sim bot)

namespace PredRE

/-! ## `pieces`-similarity (`pieces_equiv'`) — `≅`-equal regexes have `≅`-equal `pieces`. -/

theorem pieces_equiv' {f f' : PredRE} (eqv : Sim f f') :
    (pieces f =[ (· ≅ ·) ] pieces f') := by
  simp only [EqualityUpTo, SubsetUpTo, MemUpTo]
  induction eqv with
  | rfl => exact ⟨fun r hr => ⟨r, Sim.rfl, hr⟩, fun r hr => ⟨r, Sim.rfl, hr⟩⟩
  | sym _ ph => exact ⟨fun r hr => ph.2 r hr, fun r hr => ph.1 r hr⟩
  | trans _ _ ph qh =>
    exact ⟨fun e h1 =>
           have ⟨e1, e1_eq, e1_in⟩ := ph.1 e h1
           have ⟨e2, e2_eq, e2_in⟩ := qh.1 e1 e1_in
           ⟨e2, Sim.trans e1_eq e2_eq, e2_in⟩,
           fun e h1 =>
           have ⟨e1, e1_eq, e1_in⟩ := qh.2 e h1
           have ⟨e2, e2_eq, e2_in⟩ := ph.2 e1 e1_in
           ⟨e2, Sim.trans e1_eq e2_eq, e2_in⟩⟩
  | assoc =>
    refine ⟨fun e h1 => ?_, fun e h1 => ?_⟩
    · simp_all only [pieces, append_assoc, mem_append]; exact ⟨e, Sim.rfl, h1⟩
    · simp_all only [pieces, append_assoc, mem_append]; exact ⟨e, Sim.rfl, h1⟩
  | idem =>
    refine ⟨fun e h1 => ?_, fun e h1 => ?_⟩
    · simp only [pieces, mem_append, or_self] at h1; exact ⟨e, Sim.rfl, h1⟩
    · exact ⟨e, Sim.rfl, mem_append.mpr (Or.inl h1)⟩
  | dedup =>
    refine ⟨fun e h1 => ⟨e, Sim.rfl, ?_⟩, fun e h1 => ⟨e, Sim.rfl, ?_⟩⟩
    · simp only [pieces, mem_append] at h1 ⊢; tauto
    · simp only [pieces, mem_append] at h1 ⊢; tauto
  | negCong _ ih =>
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp_all only [pieces, mem_map]
      obtain ⟨zs, hz1, hz2⟩ := hx; subst hz2
      have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih.1 zs hz1
      exact ⟨.neg i1, Sim.negCong i2, i1, i3, rfl⟩
    · simp_all only [pieces, mem_map]
      obtain ⟨zs, hz1, hz2⟩ := hx; subst hz2
      have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih.2 _ hz1
      exact ⟨.neg i1, Sim.negCong i2, i1, i3, rfl⟩
  | altCong _ _ ph qh =>
    refine ⟨fun e h1 => ?_, fun e h1 => ?_⟩
    · simp_all only [pieces, mem_append]
      match h1 with
      | Or.inl h2 => have ⟨i1, i2, i3⟩ := ph.1 _ h2; exact ⟨i1, i2, Or.inl i3⟩
      | Or.inr h2 => have ⟨i1, i2, i3⟩ := qh.1 _ h2; exact ⟨i1, i2, Or.inr i3⟩
    · simp_all only [pieces, mem_append]
      match h1 with
      | Or.inl h2 => have ⟨i1, i2, i3⟩ := ph.2 _ h2; exact ⟨i1, i2, Or.inl i3⟩
      | Or.inr h2 => have ⟨i1, i2, i3⟩ := qh.2 _ h2; exact ⟨i1, i2, Or.inr i3⟩
  | @catCong R₁ R₂ S h ih =>
    refine ⟨fun e h1 => ?_, fun e h1 => ?_⟩
    · simp only [pieces, mem_append, mem_map] at h1
      match h1 with
      | Or.inl ⟨xs, g1, g2⟩ =>
        subst g2
        have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih.1 _ g1
        exact ⟨.cat i1 S, Sim.catCong i2,
          by simp only [pieces, mem_append, mem_map]; exact Or.inl ⟨i1, i3, rfl⟩⟩
      | Or.inr g => exact ⟨e, Sim.rfl, mem_append.mpr (Or.inr g)⟩
    · simp only [pieces, mem_append, mem_map] at h1
      match h1 with
      | Or.inl ⟨xs, g1, g2⟩ =>
        subst g2
        have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih.2 _ g1
        exact ⟨.cat i1 S, Sim.catCong i2,
          by simp only [pieces, mem_append, mem_map]; exact Or.inl ⟨i1, i3, rfl⟩⟩
      | Or.inr g => exact ⟨e, Sim.rfl, mem_append.mpr (Or.inr g)⟩
  | @catCongR S₁ S₂ R hsim ih =>
    -- `pieces (cat R Sᵢ) = map (·⬝Sᵢ) ⊕(pieces R) ++ pieces Sᵢ`. The `map` block: same `R`-piece,
    -- right factor transported by `catCongR hsim`. The trailing `pieces Sᵢ` block: `ih` directly.
    refine ⟨fun e h1 => ?_, fun e h1 => ?_⟩
    · simp only [pieces, mem_append, mem_map] at h1
      match h1 with
      | Or.inl ⟨xs, g1, g2⟩ =>
        subst g2
        exact ⟨.cat xs S₂, Sim.catCongR hsim,
          by simp only [pieces, mem_append, mem_map]; exact Or.inl ⟨xs, g1, rfl⟩⟩
      | Or.inr g =>
        have ⟨i1, i2, i3⟩ := ih.1 _ g
        exact ⟨i1, i2, mem_append.mpr (Or.inr i3)⟩
    · simp only [pieces, mem_append, mem_map] at h1
      match h1 with
      | Or.inl ⟨xs, g1, g2⟩ =>
        subst g2
        exact ⟨.cat xs S₁, Sim.catCongR (Sim.sym hsim),
          by simp only [pieces, mem_append, mem_map]; exact Or.inl ⟨xs, g1, rfl⟩⟩
      | Or.inr g =>
        have ⟨i1, i2, i3⟩ := ih.2 _ g
        exact ⟨i1, i2, mem_append.mpr (Or.inr i3)⟩
  | @starCong R₁ R₂ hsim ih =>
    -- `pieces (star R) = star R :: map (·⬝star R) ⊕(pieces R)`. Head → `starCong`. Map block →
    -- transport the `R`-piece by `ih`, and the `star R` right factor by `catCongR ∘ starCong`.
    refine ⟨fun e h1 => ?_, fun e h1 => ?_⟩
    · simp only [pieces, mem_cons, mem_map] at h1
      match h1 with
      | Or.inl heq =>
        subst heq
        exact ⟨.star R₂, Sim.starCong hsim, by simp only [pieces]; exact mem_cons_self ..⟩
      | Or.inr ⟨xs, g1, g2⟩ =>
        subst g2
        have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih.1 _ g1
        exact ⟨.cat i1 (.star R₂),
          Sim.trans (Sim.catCong i2) (Sim.catCongR (Sim.starCong hsim)),
          by simp only [pieces, mem_cons, mem_map]; exact Or.inr ⟨i1, i3, rfl⟩⟩
    · simp only [pieces, mem_cons, mem_map] at h1
      match h1 with
      | Or.inl heq =>
        subst heq
        exact ⟨.star R₁, Sim.starCong (Sim.sym hsim),
          by simp only [pieces]; exact mem_cons_self ..⟩
      | Or.inr ⟨xs, g1, g2⟩ =>
        subst g2
        have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih.2 _ g1
        exact ⟨.cat i1 (.star R₁),
          Sim.trans (Sim.catCong i2) (Sim.catCongR (Sim.starCong (Sim.sym hsim))),
          by simp only [pieces, mem_cons, mem_map]; exact Or.inr ⟨i1, i3, rfl⟩⟩
  | interCong _ _ ih1 ih2 =>
    refine ⟨fun e h1 => ?_, fun e h1 => ?_⟩
    · simp only [pieces, List.productWith, mem_map, Prod.exists, List.pair_mem_product,
        Function.uncurry_apply_pair] at h1
      have ⟨a, b, ⟨c, d⟩, he⟩ := h1; subst he
      have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih1.1 _ c
      have ⟨j1, j2, j3⟩ := toSumSubsets_monotone ih2.1 _ d
      exact ⟨.inter i1 j1, Sim.interCong i2 j2, by
        simp only [pieces, List.productWith, mem_map, Prod.exists, List.pair_mem_product,
          Function.uncurry_apply_pair]; exact ⟨i1, j1, ⟨i3, j3⟩, rfl⟩⟩
    · simp only [pieces, List.productWith, mem_map, Prod.exists, List.pair_mem_product,
        Function.uncurry_apply_pair] at h1
      have ⟨a, b, ⟨c, d⟩, he⟩ := h1; subst he
      have ⟨i1, i2, i3⟩ := toSumSubsets_monotone ih1.2 _ c
      have ⟨j1, j2, j3⟩ := toSumSubsets_monotone ih2.2 _ d
      exact ⟨.inter i1 j1, Sim.interCong i2 j2, by
        simp only [pieces, List.productWith, mem_map, Prod.exists, List.pair_mem_product,
          Function.uncurry_apply_pair]; exact ⟨i1, j1, ⟨i3, j3⟩, rfl⟩⟩

theorem pieces_sim {f f' : PredRE} (sim : Sim f f') : pieces f ⊆[ (· ≅ ·) ] pieces f' :=
  fun _ h => (pieces_equiv' sim).1 _ h

/-! ## `pieces_toSum` / `pieces_bot_eps` — structural helpers for `pieces_trans'`. -/

theorem pieces_toSum {e : PredRE} {xs : List PredRE} (ne : xs ≠ []) (h : e ∈ pieces (toSum xs)) :
    ∃ g ∈ xs, e ∈ pieces g :=
  match xs with
  | _::[] => exists_mem_cons_of [] h
  | e1::e2::es =>
    match mem_append.mp h with
    | Or.inl h1 => ⟨e1, mem_cons_self, h1⟩
    | Or.inr h1 =>
      have ⟨i1, i2, ih⟩ := pieces_toSum (cons_ne_nil e2 es) h1
      ⟨i1, mem_cons_of_mem e1 i2, ih⟩

theorem pieces_bot_eps {e f : PredRE} (h1 : e ∈ pieces f) (h2 : f = .ε ∨ f = bot) :
    e = .ε ∨ e = bot := by
  match h2 with
  | Or.inl g =>
    subst g; simp only [pieces, mem_cons, not_mem_nil, or_false] at h1; exact h1
  | Or.inr g =>
    subst g; simp only [bot, pieces, mem_cons, not_mem_nil, or_false] at h1
    exact or_self_right.mp (Or.symm h1)

/-! ## `pieces_trans'` — pieces-of-a-piece is `≅`-in pieces (the closure transitivity). -/

theorem pieces_trans' {e f g : PredRE} (h1 : e ∈ pieces f) (h2 : f ∈ pieces g) :
    e ∈[ (· ≅ ·) ] pieces g := by
  match g with
  | .ε =>
    simp_all only [pieces, mem_cons, not_mem_nil, or_false, MemUpTo]
    match pieces_bot_eps h1 h2 with
    | Or.inl g1 => subst g1; exact ⟨.ε, Sim.rfl, Or.inl rfl⟩
    | Or.inr g1 => subst g1; exact ⟨bot, Sim.rfl, Or.inr rfl⟩
  | .sym φ =>
    simp_all only [pieces, mem_cons, not_mem_nil, or_false, MemUpTo]
    match h2 with
    | Or.inl g => subst g
                  exact ⟨e, Sim.rfl, by simp only [pieces, mem_cons, not_mem_nil, or_false] at h1; exact h1⟩
    | Or.inr g =>
      match pieces_bot_eps h1 g with
      | Or.inl g1 => subst g1; exact ⟨.ε, Sim.rfl, Or.inr (Or.inl rfl)⟩
      | Or.inr g1 => subst g1; exact ⟨bot, Sim.rfl, Or.inr (Or.inr rfl)⟩
  | .alt g1 g2 =>
    simp_all only [pieces, mem_append, MemUpTo]
    match h2 with
    | Or.inl g => have ⟨i1, i2, i3⟩ := pieces_trans' h1 g; exact ⟨i1, i2, Or.inl i3⟩
    | Or.inr g => have ⟨i1, i2, i3⟩ := pieces_trans' h1 g; exact ⟨i1, i2, Or.inr i3⟩
  | .inter l r =>
    simp_all only [pieces, List.productWith, mem_map, Prod.exists, List.pair_mem_product,
      Function.uncurry_apply_pair, MemUpTo]
    obtain ⟨a, b, ⟨ha, hb⟩, eq⟩ := h2; subst eq
    simp only [pieces, List.productWith, mem_map, Prod.exists, List.pair_mem_product,
      Function.uncurry_apply_pair] at h1
    obtain ⟨c, d, ⟨hc, hd⟩, eq⟩ := h1; subst eq
    have ⟨zs, ne_zs, m1, m2⟩ := toSumSubsets_to_neSubset ha
    have ⟨as, ne_as, k1, k2⟩ := toSumSubsets_to_neSubset hc
    subst m1 k1
    have hl : as ⊆[ (· ≅ ·) ] pieces l := fun x hx =>
      have ⟨pi, pi_in, pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
      pieces_trans' pi_piece (m2 pi_in)
    have ⟨n1, n2, n3⟩ := toSumSubsets_monotone hl (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as, rfl⟩)
    have ⟨zs', ne_zs', m1', m2'⟩ := toSumSubsets_to_neSubset hb
    have ⟨as', ne_as', k1', k2'⟩ := toSumSubsets_to_neSubset hd
    subst m1' k1'
    have hr : as' ⊆[ (· ≅ ·) ] pieces r := fun x hx =>
      have ⟨pi, pi_in, pi_piece⟩ := pieces_toSum ne_zs' (k2' hx)
      pieces_trans' pi_piece (m2' pi_in)
    have ⟨p1, p2, p3⟩ := toSumSubsets_monotone hr (toSum as') (mem_map.mpr ⟨as', neSubsets_refl ne_as', rfl⟩)
    exact ⟨.inter n1 p1, Sim.interCong n2 p2, n1, p1, ⟨n3, p3⟩, rfl⟩
  | .cat l r =>
    simp_all only [MemUpTo, pieces, mem_append, mem_map]
    match h2 with
    | Or.inl ⟨a, ha, ha1⟩ =>
      subst ha1
      simp only [pieces, mem_append, mem_map] at h1
      match h1 with
      | Or.inl ⟨b, hb, hb1⟩ =>
        subst hb1
        have ⟨zs, ne_zs, m1, m2⟩ := toSumSubsets_to_neSubset ha
        have ⟨as, ne_as, k1, k2⟩ := toSumSubsets_to_neSubset hb
        subst m1 k1
        have hl : as ⊆[ (· ≅ ·) ] pieces l := fun x hx =>
          have ⟨pi, pi_in, pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
          pieces_trans' pi_piece (m2 pi_in)
        have ⟨n1, n2, n3⟩ := toSumSubsets_monotone hl (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as, rfl⟩)
        exact ⟨.cat n1 r, Sim.catCong n2, Or.inl ⟨n1, n3, rfl⟩⟩
      | Or.inr g => exact ⟨e, Sim.rfl, Or.inr g⟩
    | Or.inr g =>
      have ⟨i1, i2, ih⟩ := pieces_trans' h1 g
      exact ⟨i1, i2, Or.inr ih⟩
  | .neg g =>
    simp only [pieces, mem_map] at h2
    obtain ⟨a, ha, ha1⟩ := h2; subst ha1
    simp only [pieces, mem_map] at h1
    obtain ⟨b, bh, bh1⟩ := h1; subst bh1
    simp only [MemUpTo, pieces, mem_map]
    have ⟨zs, ne_zs, m1, m2⟩ := toSumSubsets_to_neSubset ha
    have ⟨as, ne_as, k1, k2⟩ := toSumSubsets_to_neSubset bh; subst m1 k1
    have hg : as ⊆[ (· ≅ ·) ] pieces g := fun x hx =>
      have ⟨pi, pi_in, pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
      pieces_trans' pi_piece (m2 pi_in)
    have ⟨n1, n2, n3⟩ := toSumSubsets_monotone hg (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as, rfl⟩)
    exact ⟨.neg n1, Sim.negCong n2, ⟨n1, n3, rfl⟩⟩
  | .star r =>
    simp only [pieces, mem_cons, mem_map] at h2
    match h2 with
    | Or.inl g =>
      subst g
      simp_all only [pieces, mem_cons, mem_map, true_or, MemUpTo]
      match h1 with
      | Or.inl g => subst g; exact ⟨.star r, Sim.rfl, Or.inl rfl⟩
      | Or.inr ⟨a, _, ha1⟩ => subst ha1; exact ⟨.cat a (.star r), Sim.rfl, h1⟩
    | Or.inr ⟨a, ha, ha1⟩ =>
      subst ha1
      simp_all only [pieces, mem_append, mem_map, mem_cons, MemUpTo]
      match h1 with
      | Or.inl ⟨b, hb, hb1⟩ =>
        subst hb1
        have ⟨zs, ne_zs, m1, m2⟩ := toSumSubsets_to_neSubset ha
        have ⟨as, ne_as, k1, k2⟩ := toSumSubsets_to_neSubset hb
        subst m1 k1
        have hr : as ⊆[ (· ≅ ·) ] pieces r := fun x hx =>
          have ⟨pi, pi_in, pi_piece⟩ := pieces_toSum ne_zs (k2 hx)
          pieces_trans' pi_piece (m2 pi_in)
        have ⟨n1, n2, n3⟩ := toSumSubsets_monotone hr (toSum as) (mem_map.mpr ⟨as, neSubsets_refl ne_as, rfl⟩)
        exact ⟨.cat n1 (.star r), Sim.catCong n2, Or.inr ⟨n1, n3, rfl⟩⟩
      | Or.inr g =>
        match g with
        | Or.inl g1 => subst g1; exact ⟨.star r, Sim.rfl, Or.inl rfl⟩
        | Or.inr ⟨a, _, ha1⟩ => subst ha1; exact ⟨.cat a (.star r), Sim.rfl, g⟩

/-! ## `toSumSubsets_pieces_refl/_trans` — the `⊕(pieces ·)` reflexive/transitive closure. -/

theorem toSumSubsets_pieces_refl {r : PredRE} : r ∈[ (· ≅ ·) ] ⊕(pieces r) :=
  have ⟨xs, xs_in, xs_eqv⟩ := pieces_refl (r := r)
  ⟨toSum xs, Sim.sym xs_eqv,
   mem_map.mpr ⟨xs, neSubsets_characterization.mpr ⟨xs, xs_in, Perm.refl _⟩, rfl⟩⟩

theorem toSumSubsets_pieces_trans {e f g : PredRE}
    (h1 : e ∈[ (· ≅ ·) ] ⊕(pieces f)) (h2 : f ∈[ (· ≅ ·) ] ⊕(pieces g)) :
    e ∈[ (· ≅ ·) ] ⊕(pieces g) := by
  simp_all only [MemUpTo, toSumSubsets, mem_map]
  obtain ⟨ff, f1, sub_ps_f, hbs, hbs1⟩ := h1
  obtain ⟨gg, g1, sub_ps_g, has, has1⟩ := h2
  subst has1 hbs1
  have sub : sub_ps_f ⊆[ (· ≅ ·) ] pieces g := fun x hx =>
    have ⟨i1, i2, i3⟩ := (pieces_sim g1) _ ((neSubset_to_sublist hbs) hx)
    have ⟨gi, hgi1, hgi2⟩ := pieces_toSum (neSubsets_ne has) i3
    have hh : pieces gi ⊆[ (· ≅ ·) ] pieces g := fun p hp =>
      pieces_trans' hp ((neSubset_to_sublist has) hgi1)
    have ⟨f1', f2', f3'⟩ := hh _ hgi2
    ⟨f1', Sim.trans i2 f2', f3'⟩
  have ⟨ys', nodup_ys', ne_ys', sub_ys', fs_ys'⟩ := toSumnodup_equiv (neSubsets_ne hbs) sub
  refine ⟨toSum ys', Sim.trans (Sim.trans f1 fs_ys') Sim.rfl,
    ys', nodup_subset_to_neSubsets ne_ys' sub_ys' nodup_ys', rfl⟩

/-! ## The capstone — `steps_to_toSumSubsets` + `der_finite`. -/

/-- **`steps_to_toSumSubsets`** — the full state space after ANY number of symbolic steps stays
inside `⊕(pieces r)` up to `≅`. Induction on `n`: base = `pieces_refl`; step = `step_to_toSumSubsets`
+ `toSumSubsets_pieces_trans`. ITP'25 `steps_to_toSumSubsets`. -/
theorem steps_to_toSumSubsets {r : PredRE} {n : Nat} :
    steps r n ⊆[ (· ≅ ·) ] ⊕(pieces r) := fun e1 h =>
  match n with
  | 0 => by
    simp only [steps, mem_cons, not_mem_nil, or_false] at h
    subst h
    exact toSumSubsets_pieces_refl
  | Nat.succ n => by
    simp only [steps, mem_flatten, mem_map, step, exists_exists_and_eq_and] at h
    obtain ⟨e2, e2_steps_n, e1_step_e2⟩ := h
    have ⟨q1, q1_eqv, ih⟩ := steps_to_toSumSubsets e2 e2_steps_n
    have ⟨xs, xs_eqv, hxs⟩ := step_to_toSumSubsets _ e1_step_e2
    exact toSumSubsets_pieces_trans ⟨xs, xs_eqv, hxs⟩ ⟨q1, q1_eqv, ih⟩

/-- **`der_finite`** — BRZOZOWSKI FINITENESS over `PredRE`: there is a FIXED finite list of regexes
(`⊕(pieces r)`) that contains, UP TO SIMILARITY `≅`, EVERY state reachable by iterating the symbolic
derivative from `r`, for ALL step counts `n`. So `r` has finitely many derivatives up to ACI
normalization — the derivative automaton has a finite state space, which is exactly what a DFA table
requires. Stage 3 closed. ITP'25 `finiteness`. -/
theorem der_finite {r : PredRE} :
    ∃ (xs : List PredRE), ∀ {n : Nat}, steps r n ⊆[ (· ≅ ·) ] xs :=
  ⟨⊕(pieces r), steps_to_toSumSubsets⟩

/-! ## Non-vacuity — the finite bound is real (the state space genuinely lands in it). -/

section Guards

private def p7 : Pred := Pred.symEq "k" 7

-- The reachable states of `(sym p7)*` after 1 step land in ⊕(pieces (sym p7)*), up to ≅.
example : steps (.star (.sym p7)) 1 ⊆[ (· ≅ ·) ] ⊕(pieces (.star (.sym p7))) :=
  steps_to_toSumSubsets

-- der_finite yields a CONCRETE finite witness list.
example : ∃ xs : List PredRE, ∀ {n}, steps (.sym p7) n ⊆[ (· ≅ ·) ] xs := der_finite

end Guards

end PredRE

end Dregg2.Crypto.Deriv

/-! ## Axiom hygiene — Stage 3 (`der_finite`) is kernel-clean. -/

#assert_all_clean [
  Dregg2.Crypto.Deriv.PredRE.pieces_equiv',
  Dregg2.Crypto.Deriv.PredRE.pieces_trans',
  Dregg2.Crypto.Deriv.PredRE.toSumSubsets_pieces_trans,
  Dregg2.Crypto.Deriv.PredRE.steps_to_toSumSubsets,
  Dregg2.Crypto.Deriv.PredRE.der_finite
]
