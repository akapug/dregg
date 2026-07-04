/-
# Dregg2.Crypto.Deriv.Correctness — Stage 1 of the derivative-matching faithfulness close.

`correctness : derives w R = true ↔ Matches w R` — the dregg-native re-instantiation of ERE≤'s
`correctness` (`Correctness.lean:375`), over `PredRE`/`Pred`/`List Value`. The reference is read as a
proof MAP only (no import): the per-constructor `derives_<ctor>` lemmas + the `starMetric` induction.
We keep the SEVEN constructors that survive dropping lookarounds (`Eps`/`Pred`/`Alt`/`Inter`/`Cat`/
`Star`/`Negation`) and the four `derives_Look*` lemmas vanish.

Because the carrier is plain `List Value` (no spans / no left context — we have no lookbehind), the
proofs are STRICTLY SIMPLER than ERE≤'s span-indexed originals: the `der`-step lemma is a single
clean structural unfold, and `derives_Cat`'s word-split is over `List.append` directly.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Core

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

namespace PredRE

/-! ## The bottom regex matches nothing — `derives_bot`. -/

/-- **`derives_bot`** — `bot = sym .ff` rejects every word (the leaf `.ff` never fires, so `der`
keeps returning `bot`, and `null bot = false`). ERE≤'s `derives_Bot` (`Correctness.lean:15`). -/
theorem derives_bot (w : List Value) : derives w bot = false := by
  induction w with
  | nil => rfl
  | cons a as ih =>
    -- der a bot = if leaf .ff a then ε else bot; leaf .ff a = false, so der a bot = bot.
    simp only [derives, der, leaf, Pred.eval, Bool.false_eq_true, if_false]
    exact ih

/-- **`Matches_bot`** — nothing matches `bot` denotationally (`leaf .ff a = false`). -/
theorem matches_bot (w : List Value) : ¬ Matches w bot := by
  intro h
  rw [Matches] at h
  obtain ⟨a, _, hfire⟩ := h
  simp only [leaf, Pred.eval, Bool.false_eq_true] at hfire

/-! ## `ε` matches exactly the empty word — `derives_eps`. -/

/-- **`derives_eps`** — `ε` derives `true` iff the word is empty (`der a ε = bot`, which rejects). -/
theorem derives_eps (w : List Value) : derives w (.ε) = true ↔ w = [] := by
  cases w with
  | nil => simp only [derives, null]
  | cons a as =>
    simp only [derives, der, reduceCtorEq, iff_false]
    -- der a ε = bot, and derives as bot = false.
    rw [derives_bot]; simp

/-- **`matches_eps`** — `Matches w ε ↔ w = []` (by definition). -/
theorem matches_eps (w : List Value) : Matches w (.ε) ↔ w = [] := by rw [Matches]

/-! ## The single-frame leaf — `derives_sym`. -/

/-- **`derives_sym`** — `sym φ` derives `true` iff the word is a singleton `[a]` whose frame fires
`φ`. ERE≤'s `derives_Pred` (`Correctness.lean:35`), re-proved with dregg's `leaf` (= `Pred.eval ∅`). -/
theorem derives_sym (w : List Value) (φ : Pred) :
    derives w (.sym φ) = true ↔ ∃ a, w = [a] ∧ leaf φ a = true := by
  cases w with
  | nil => simp only [derives, null, Bool.false_eq_true, false_iff]; rintro ⟨a, h, _⟩; cases h
  | cons a as =>
    simp only [derives, der]
    by_cases h : leaf φ a
    · simp only [h, if_true]
      rw [derives_eps]
      constructor
      · intro has; subst has; exact ⟨a, rfl, h⟩
      · rintro ⟨b, hb, _⟩; rw [List.cons_eq_cons] at hb; exact hb.2
    · simp only [h, if_false, Bool.false_eq_true]
      rw [derives_bot]
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨b, hb, hfire⟩
      rw [List.cons_eq_cons] at hb
      obtain ⟨rfl, _⟩ := hb
      exact h hfire

/-! ## Alternation / intersection / complement — the Boolean steps.

`der` distributes over `alt`/`inter`/`neg`, so `derives (a::as) (alt l r) = derives as (alt (der a l)
(der a r))`. The induction is over the word; the `der`-pushing is a single unfold. -/

/-- **`derives_alt`** — `derives w (alt l r) = derives w l || derives w r`. ERE≤'s `derives_Alt`. -/
theorem derives_alt (w : List Value) (l r : PredRE) :
    derives w (.alt l r) = (derives w l || derives w r) := by
  induction w generalizing l r with
  | nil => rfl
  | cons a as ih => simp only [derives, der]; exact ih (der a l) (der a r)

/-- **`derives_inter`** — `derives w (inter l r) = derives w l && derives w r`. -/
theorem derives_inter (w : List Value) (l r : PredRE) :
    derives w (.inter l r) = (derives w l && derives w r) := by
  induction w generalizing l r with
  | nil => rfl
  | cons a as ih => simp only [derives, der]; exact ih (der a l) (der a r)

/-- **`derives_neg`** — `derives w (neg r) = !(derives w r)`. ERE≤'s `derives_Negation`. The Boolean
ground (`!!b = b`) is dregg-native and already proven (`Pred.eval_not_not`). -/
theorem derives_neg (w : List Value) (r : PredRE) :
    derives w (.neg r) = !(derives w r) := by
  induction w generalizing r with
  | nil => rfl
  | cons a as ih => simp only [derives, der]; exact ih (der a r)

/-! ## Concatenation — the intricate `derives_cat` (the fiddly lemma ERE≤ has finished).

The semantic content of the Brzozowski `cat` arm: `der a (cat l r) = (cat (der a l) r) ⋓ der a r`
when `null l`, else `cat (der a l) r`. We prove the word-level characterization directly:
`derives w (cat l r) = true ↔ ∃ w₁ w₂, w₁ ++ w₂ = w ∧ derives w₁ l ∧ derives w₂ r`. -/

/-- **`derives_cat`** — the concatenation split, in the `Bool`/`derives` world. ERE≤'s `derives_Cat`
(`Correctness.lean:241`), re-proved over `List.append` (no span machinery). The induction is on the
word length; the `null l` case-split mirrors `der`'s. -/
theorem derives_cat (w : List Value) (l r : PredRE) :
    derives w (.cat l r) = true ↔
      ∃ w₁ w₂, w₁ ++ w₂ = w ∧ derives w₁ l = true ∧ derives w₂ r = true := by
  induction w generalizing l with
  | nil =>
    -- empty word: cat matches iff null l && null r, i.e. l and r both match [].
    simp only [derives, null, Bool.and_eq_true]
    constructor
    · rintro ⟨hl, hr⟩; exact ⟨[], [], rfl, hl, hr⟩
    · rintro ⟨w₁, w₂, hsplit, hl, hr⟩
      rw [List.append_eq_nil_iff] at hsplit
      obtain ⟨rfl, rfl⟩ := hsplit
      exact ⟨hl, hr⟩
  | cons a as ih =>
    simp only [derives, der]
    by_cases hnull : null l = true
    · -- der a (cat l r) = alt (cat (der a l) r) (der a r)
      rw [if_pos hnull, derives_alt, Bool.or_eq_true, ih (der a l)]
      constructor
      · rintro (⟨w₁, w₂, hsplit, hl, hr⟩ | hr)
        · -- prepend a to w₁
          refine ⟨a :: w₁, w₂, by simp [hsplit], ?_, hr⟩
          simp only [derives]; exact hl
        · -- l matches [] (null l), r matches a::as
          refine ⟨[], a :: as, rfl, ?_, hr⟩
          simp only [derives]; exact hnull
      · rintro ⟨w₁, w₂, hsplit, hl, hr⟩
        cases w₁ with
        | nil =>
          -- w₁ = [], so a::as = w₂; r matches a::as. This is the right disjunct.
          simp only [List.nil_append] at hsplit; subst hsplit
          exact Or.inr hr
        | cons b w₁' =>
          -- a = b, as = w₁' ++ w₂; the left disjunct via ih.
          rw [List.cons_append, List.cons_eq_cons] at hsplit
          obtain ⟨rfl, hsplit'⟩ := hsplit
          refine Or.inl ⟨w₁', w₂, hsplit', ?_, hr⟩
          simp only [derives] at hl; exact hl
    · -- null l = false: der a (cat l r) = cat (der a l) r
      rw [if_neg hnull, ih (der a l)]
      constructor
      · rintro ⟨w₁, w₂, hsplit, hl, hr⟩
        refine ⟨a :: w₁, w₂, by simp [hsplit], ?_, hr⟩
        simp only [derives]; exact hl
      · rintro ⟨w₁, w₂, hsplit, hl, hr⟩
        cases w₁ with
        | nil =>
          -- w₁ = [] means derives [] l = null l = true, contradicting hnull.
          simp only [derives] at hl
          rw [hl] at hnull; exact absurd rfl hnull
        | cons b w₁' =>
          rw [List.cons_append, List.cons_eq_cons] at hsplit
          obtain ⟨rfl, hsplit'⟩ := hsplit
          refine ⟨w₁', w₂, hsplit', ?_, hr⟩
          simp only [derives] at hl; exact hl

/-! ## Kleene star — `derives_star`.

ERE≤ proves `sp ⊢ r* ↔ ∃ m, sp ⊢ rᵐ` (`Correctness.lean:363`) via mp/mpr + a `contraction` lemma.
We re-prove the `Bool`-level analog over `List Value`. The two halves:

* `derives_star_mp` — a star-match decomposes into SOME finite power, by induction on word length
  (each `der`-step of `star r` is `cat (der a r) (star r)`, peeling one `r`).
* `derives_star_mpr` — a finite power `rᵐ` is a star-match, by the `contraction` `r ⬝ r* → r*`. -/

/-- `null (star r) = true` and `der a (star r) = cat (der a r) (star r)` — the two facts the star
proofs lean on; here just the unfolding of `derives` over `star` for a `cons` word. -/
theorem derives_star_cons (a : Value) (as : List Value) (r : PredRE) :
    derives (a :: as) (.star r) = derives as (.cat (der a r) (.star r)) := rfl

/-- **`derives_star_contraction`** — `r ⬝ r*` matching implies `r*` matching. ERE≤'s
`derives_Star_contraction` (`Correctness.lean:333`). The `der`-step of `star` IS the body of `cat
(der a r) (star r)`, so a contraction is a one-step unfold in reverse. -/
theorem derives_star_contraction (w : List Value) (r : PredRE) :
    derives w (.cat r (.star r)) = true → derives w (.star r) = true := by
  cases w with
  | nil => intro _; rfl
  | cons a as =>
    intro h
    rw [derives_cat] at h
    obtain ⟨w₁, w₂, hsplit, hl, hr⟩ := h
    cases w₁ with
    | nil =>
      -- r matched [], so the tail r* already carries the whole word a::as.
      simp only [List.nil_append] at hsplit; subst hsplit; exact hr
    | cons b w₁' =>
      -- a = b; der a (star r) = cat (der a r) (star r); rebuild via derives_cat.
      rw [List.cons_append, List.cons_eq_cons] at hsplit
      obtain ⟨rfl, hsplit'⟩ := hsplit
      rw [derives_star_cons, derives_cat]
      refine ⟨w₁', w₂, hsplit', ?_, hr⟩
      simp only [derives] at hl; exact hl

/-- **`derives_star_mpr`** — a finite power `repeatCat r m` matching implies `star r` matching.
ERE≤'s `derives_Star_mpr` (`Correctness.lean:347`). Induction on `m`, using contraction. -/
theorem derives_star_mpr (w : List Value) (r : PredRE) (m : Nat) :
    derives w (repeatCat r m) = true → derives w (.star r) = true := by
  induction m generalizing w with
  | zero =>
    -- repeatCat r 0 = ε, so w = []; star matches [].
    intro h; rw [repeatCat] at h; rw [(derives_eps w).mp h]; rfl
  | succ n ih =>
    intro h
    rw [repeatCat, derives_cat] at h
    obtain ⟨w₁, w₂, hsplit, hl, hr⟩ := h
    apply derives_star_contraction
    rw [derives_cat]
    exact ⟨w₁, w₂, hsplit, hl, ih w₂ hr⟩

/-- **`derives_star_mp`** — a `star r` match decomposes into SOME finite power. ERE≤'s
`derives_Star_mp` (`Correctness.lean:299`). Strong induction on word length: an empty word is `r⁰`;
a nonempty match peels one `r` (the head of `der a (star r) = cat (der a r) (star r)`), the rest is
`r^(m)` by induction, giving `r^(m+1)`. -/
theorem derives_star_mp (w : List Value) (r : PredRE) :
    derives w (.star r) = true → ∃ m, derives w (repeatCat r m) = true := by
  -- strong induction on |w|
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    cases w with
    | nil => intro _; exact ⟨0, by rw [repeatCat]; rfl⟩
    | cons a as =>
      intro h
      rw [derives_star_cons, derives_cat] at h
      obtain ⟨w₁, w₂, hsplit, hl, hr⟩ := h
      -- der a r matched w₁, star r matched w₂, with w₁ ++ w₂ = as.
      -- Repackage: r matched (a :: w₁) [one der-step], so by induction on w₂ (shorter), get a power.
      have hw₂len : w₂.length < n := by
        subst hlen
        have : w₁.length + w₂.length = as.length := by
          rw [← List.length_append, hsplit]
        simp only [List.length_cons]; omega
      obtain ⟨m, hm⟩ := ih w₂.length hw₂len w₂ rfl hr
      refine ⟨m + 1, ?_⟩
      rw [repeatCat, derives_cat]
      refine ⟨a :: w₁, w₂, by simp [hsplit], ?_, hm⟩
      simp only [derives]; exact hl

/-- **`derives_star`** — `derives w (star r) = true ↔ ∃ m, derives w (repeatCat r m) = true`.
ERE≤'s `derives_Star` (`Correctness.lean:363`). -/
theorem derives_star (w : List Value) (r : PredRE) :
    derives w (.star r) = true ↔ ∃ m, derives w (repeatCat r m) = true :=
  ⟨derives_star_mp w r, fun ⟨_, h⟩ => derives_star_mpr w r _ h⟩

/-! ## The main correctness theorem — `correctness : derives ↔ Matches`. -/

/-- **`correctness`** — the dregg-native re-instantiation of ERE≤'s `correctness`
(`Correctness.lean:375`): the symbolic-derivative matcher `derives` decides EXACTLY the denotational
matching relation `Matches`, over `PredRE`/`Pred`/`List Value`. Structural induction on `R` with the
`starMetric` termination metric; each constructor discharged by its `derives_<ctor>` lemma above. -/
theorem correctness (w : List Value) (R : PredRE) :
    derives w R = true ↔ Matches w R := by
  match R with
  | .ε => rw [Matches]; exact derives_eps w
  | .sym φ => rw [Matches]; exact derives_sym w φ
  | .alt l r =>
    have : starMetric l < starMetric (.alt l r) := starMetric_alt_l
    have : starMetric r < starMetric (.alt l r) := starMetric_alt_r
    rw [derives_alt, Bool.or_eq_true, Matches, correctness w l, correctness w r]
  | .inter l r =>
    have : starMetric l < starMetric (.inter l r) := starMetric_inter_l
    have : starMetric r < starMetric (.inter l r) := starMetric_inter_r
    rw [derives_inter, Bool.and_eq_true, Matches, correctness w l, correctness w r]
  | .neg r =>
    have : starMetric r < starMetric (.neg r) := starMetric_neg
    rw [derives_neg, Matches, ← correctness w r]
    cases derives w r <;> simp
  | .cat l r =>
    have : starMetric l < starMetric (.cat l r) := starMetric_cat_l
    have : starMetric r < starMetric (.cat l r) := starMetric_cat_r
    rw [derives_cat, Matches]
    constructor
    · rintro ⟨w₁, w₂, hsplit, hl, hr⟩
      exact ⟨w₁, w₂, hsplit, (correctness w₁ l).mp hl, (correctness w₂ r).mp hr⟩
    · rintro ⟨w₁, w₂, hsplit, hl, hr⟩
      exact ⟨w₁, w₂, hsplit, (correctness w₁ l).mpr hl, (correctness w₂ r).mpr hr⟩
  | .star r =>
    rw [derives_star, Matches]
    constructor
    · rintro ⟨m, hm⟩
      have : starMetric (repeatCat r m) < starMetric (.star r) := starMetric_repeatCat
      exact ⟨m, (correctness w (repeatCat r m)).mp hm⟩
    · rintro ⟨m, hm⟩
      have : starMetric (repeatCat r m) < starMetric (.star r) := starMetric_repeatCat
      exact ⟨m, (correctness w (repeatCat r m)).mpr hm⟩
termination_by starMetric R
decreasing_by all_goals assumption

end PredRE

/-! ## Axiom hygiene — the Stage 1 correctness tower is kernel-clean. -/

#assert_all_clean [
  PredRE.derives_bot, PredRE.matches_bot, PredRE.derives_eps, PredRE.derives_sym,
  PredRE.derives_alt, PredRE.derives_inter, PredRE.derives_neg, PredRE.derives_cat,
  PredRE.derives_star_contraction, PredRE.derives_star_mpr, PredRE.derives_star_mp,
  PredRE.derives_star, PredRE.correctness
]

end Dregg2.Crypto.Deriv
