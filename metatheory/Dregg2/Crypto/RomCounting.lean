/-
# `Dregg2.Crypto.RomCounting` — the COUNTING core for random-oracle probability.

A uniform random oracle `D → R` is a uniform element of the finite type `D → R`. Everything an
ROM argument needs about "the adversary has not queried `a`, so it does not know `H a`" is a
statement about counting functions, and this module proves it by counting them.

## What is built

  **§1 — CYLINDERS.** `cyl S σ` is the set of oracles agreeing with `σ` on the finite set `S` — the
  conditioning event "the oracle's values on `S` are already known". `cyl ∅ σ` is the whole space
  (`cyl_empty`), so the unconditioned experiment is the empty cylinder.

  **§2 — CONDITIONAL PROBABILITY.** `condProb C win` is the fraction of oracles in `C` that win: a
  real in `[0,1]` (`condProb_nonneg`, `condProb_le_one`), monotone in the win predicate ON `C`
  (`condProb_le_of_imp`), depending only on the values of `win` on `C` (`condProb_congr`), with
  both poles proved (`condProb_eq_zero`, `condProb_eq_one`). `condProb_cyl_empty` ties it back to
  `ProbCrypto.winProb`.

  **§3 — FRESH COORDINATES.** For `d ∉ S`, slicing `cyl S σ` by the oracle's value at `d` gives the
  cylinder over `insert d S` (`cyl_filter_eq`), the slices are equinumerous (`cyl_insert_card_eq`,
  by the bijection `H ↦ Function.update H d r'`), and there are `|R|` of them
  (`cyl_card_insert_mul`). Hence `condProb_split`: conditioning on a fresh point averages the
  conditional probabilities uniformly over `R` — lazy sampling as a finite counting fact, with no
  measure theory — and `condProb_fresh_eq`: a fresh point hits a fixed target with probability
  exactly `1 / |R|`.

## On `Nonempty R`

No lemma assumes it. Every statement about a fresh point takes both `σ : D → R` and a point of
`D`, and `σ d : R` already inhabits `R`; `Fintype.card R = 0` is therefore unreachable inside those
proofs. The lemmas that do not mention a point of `D` (`condProb_*` at a general `C`) hold at
`|R| = 0` as stated, since `0 / 0 = 0` in `ℝ`.

## Axiom hygiene

`#assert_all_clean` over the keystones; no `sorry`, no fresh `axiom`, no `native_decide`.
-/
import Dregg2.Crypto.ProbCrypto
import Dregg2.Tactics
import Mathlib.Tactic

open scoped BigOperators

namespace Dregg2.Crypto.RomCounting

set_option autoImplicit false
-- The `condProb` lemmas at a general `C : Finset (D → R)` do not use the finiteness of `D` or `R`;
-- the signatures carry the section's instances anyway, so that every lemma in this file applies to
-- a cylinder without instance juggling at the call site.
set_option linter.unusedSectionVars false

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-! ## §1 — Cylinders. -/

/-- **A CYLINDER.** The oracles that agree with the partial assignment `σ` on the finite set `S` —
the conditioning event "the oracle's values at `S` are already known to be `σ`". -/
def cyl (S : Finset D) (σ : D → R) : Finset (D → R) :=
  Finset.univ.filter (fun H => ∀ x ∈ S, H x = σ x)

/-- Membership in a cylinder is agreement with `σ` on `S`. -/
theorem mem_cyl {S : Finset D} {σ : D → R} {H : D → R} :
    H ∈ cyl S σ ↔ ∀ x ∈ S, H x = σ x := by
  simp [cyl]

/-- The empty cylinder is the whole space — the unconditioned experiment. -/
theorem cyl_empty (σ : D → R) : cyl (∅ : Finset D) σ = Finset.univ := by
  ext H; simp [mem_cyl]

/-- A cylinder is nonempty: the assignment `σ` itself agrees with `σ` everywhere. -/
theorem cyl_nonempty (S : Finset D) (σ : D → R) : (cyl S σ).Nonempty :=
  ⟨σ, mem_cyl.2 (fun _ _ => rfl)⟩

/-- A cylinder has positive cardinality — the denominator of `condProb` at a cylinder never
vanishes. -/
theorem cyl_card_pos (S : Finset D) (σ : D → R) : 0 < (cyl S σ).card :=
  Finset.card_pos.2 (cyl_nonempty S σ)

/-! ## §2 — Conditional probability inside a cylinder. -/

/-- **CONDITIONAL PROBABILITY** within a cylinder: the fraction of oracles in `C` that win. -/
noncomputable def condProb (C : Finset (D → R)) (win : (D → R) → Bool) : ℝ :=
  ((C.filter (fun H => win H = true)).card : ℝ) / (C.card : ℝ)

/-- `condProb` is non-negative. -/
theorem condProb_nonneg (C : Finset (D → R)) (win : (D → R) → Bool) : 0 ≤ condProb C win := by
  unfold condProb; positivity

/-- `condProb ≤ 1` — the winning oracles in `C` are a subset of `C` (and `C = ∅` gives `0/0 = 0`). -/
theorem condProb_le_one (C : Finset (D → R)) (win : (D → R) → Bool) : condProb C win ≤ 1 := by
  unfold condProb
  rcases Nat.eq_zero_or_pos C.card with h0 | h0
  · simp [h0]
  · rw [div_le_one (by exact_mod_cast h0)]
    exact_mod_cast Finset.card_filter_le _ _

/-- Only the values on `C` matter: two predicates agreeing on `C` have the same conditional
probability. -/
theorem condProb_congr {C : Finset (D → R)} {win win' : (D → R) → Bool}
    (h : ∀ H ∈ C, win H = win' H) : condProb C win = condProb C win' := by
  unfold condProb
  have hfil : C.filter (fun H => win H = true) = C.filter (fun H => win' H = true) :=
    Finset.filter_congr (fun H hH => by rw [h H hH])
  rw [hfil]

/-- `condProb` is monotone in the win predicate, ON the cylinder. -/
theorem condProb_le_of_imp {C : Finset (D → R)} {f g : (D → R) → Bool}
    (h : ∀ H ∈ C, f H = true → g H = true) : condProb C f ≤ condProb C g := by
  unfold condProb
  have hsub : (C.filter (fun H => f H = true)) ⊆ (C.filter (fun H => g H = true)) := by
    intro H hH
    simp only [Finset.mem_filter] at hH ⊢
    exact ⟨hH.1, h H hH.1 hH.2⟩
  gcongr

/-- A predicate false everywhere on `C` has conditional probability `0`. -/
theorem condProb_eq_zero {C : Finset (D → R)} {win : (D → R) → Bool}
    (h : ∀ H ∈ C, win H = false) : condProb C win = 0 := by
  unfold condProb
  have : C.filter (fun H => win H = true) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro H hH
    simp [h H hH]
  simp [this]

/-- A predicate true everywhere on a nonempty `C` has conditional probability `1`. -/
theorem condProb_eq_one {C : Finset (D → R)} {win : (D → R) → Bool}
    (h : ∀ H ∈ C, win H = true) (hne : C.Nonempty) : condProb C win = 1 := by
  unfold condProb
  rw [Finset.filter_true_of_mem h]
  exact div_self (by exact_mod_cast (Finset.card_pos.2 hne).ne')

/-- Conditioning on the whole space is the ordinary `winProb`. The tie-back to the existing
probability core. -/
theorem condProb_cyl_empty (σ : D → R) (win : (D → R) → Bool) :
    condProb (cyl (∅ : Finset D) σ) win = Dregg2.Crypto.ProbCrypto.winProb win := by
  rw [cyl_empty]
  unfold condProb Dregg2.Crypto.ProbCrypto.winProb
  rw [Finset.card_univ]

/-! ## §3 — Fresh coordinates: slicing, equinumerosity, and the split. -/

/-- **EXTENDING A CYLINDER AT A FRESH POINT.** Slicing `cyl S σ` by the oracle's value at a fresh
`d ∉ S` gives exactly the cylinder over `insert d S` with `σ` updated at `d`. -/
theorem cyl_filter_eq (S : Finset D) (σ : D → R) (d : D) (r : R) (hd : d ∉ S) :
    (cyl S σ).filter (fun H => H d = r) = cyl (insert d S) (Function.update σ d r) := by
  ext H
  simp only [Finset.mem_filter, mem_cyl, Finset.mem_insert]
  constructor
  · rintro ⟨hS, hdv⟩ x (rfl | hx)
    · simpa using hdv
    · have hxd : x ≠ d := by rintro rfl; exact hd hx
      rw [Function.update_of_ne hxd]
      exact hS x hx
  · intro h
    refine ⟨fun x hx => ?_, ?_⟩
    · have hxd : x ≠ d := by rintro rfl; exact hd hx
      have := h x (Or.inr hx)
      rwa [Function.update_of_ne hxd] at this
    · have := h d (Or.inl rfl)
      simpa using this

/-- **THE SLICES AT A FRESH POINT ARE EQUINUMEROUS.** For `d ∉ S`, every value `r` slices off the
same number of oracles — the bijection is `H ↦ Function.update H d r'`, with inverse
`K ↦ Function.update K d r`. -/
theorem cyl_insert_card_eq (S : Finset D) (σ : D → R) (d : D) (r r' : R) (hd : d ∉ S) :
    (cyl (insert d S) (Function.update σ d r)).card
      = (cyl (insert d S) (Function.update σ d r')).card := by
  -- On the cylinder over `insert d S` with `σ` updated at `d` to `r`, every oracle takes the value
  -- `r` at `d`; overwriting that single coordinate with `r'` lands in the `r'`-cylinder, and
  -- overwriting back recovers the original oracle.
  have key : ∀ (a b : R) (H : D → R), H ∈ cyl (insert d S) (Function.update σ d a) →
      Function.update H d b ∈ cyl (insert d S) (Function.update σ d b) := by
    intro a b H hH
    rw [mem_cyl] at hH ⊢
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hxS
    · simp
    · have hxd : x ≠ d := by rintro rfl; exact hd hxS
      rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
      have := hH x (Finset.mem_insert_of_mem hxS)
      rwa [Function.update_of_ne hxd] at this
  have pin : ∀ (a : R) (H : D → R), H ∈ cyl (insert d S) (Function.update σ d a) → H d = a := by
    intro a H hH
    have := (mem_cyl.1 hH) d (Finset.mem_insert_self d S)
    simpa using this
  refine Finset.card_bij' (fun H _ => Function.update H d r') (fun K _ => Function.update K d r)
    (fun H hH => key r r' H hH) (fun K hK => key r' r K hK) (fun H hH => ?_) (fun K hK => ?_)
  · show Function.update (Function.update H d r') d r = H
    rw [Function.update_idem, ← pin r H hH, Function.update_eq_self]
  · show Function.update (Function.update K d r) d r' = K
    rw [Function.update_idem, ← pin r' K hK, Function.update_eq_self]

/-- **THE FRESH POINT IS UNIFORM — as a counting identity.** For `d ∉ S`, the cylinder `cyl S σ`
splits into `|R|` equal slices, one per value at `d`. -/
theorem cyl_card_insert_mul (S : Finset D) (σ : D → R) (d : D) (r : R) (hd : d ∉ S) :
    (cyl (insert d S) (Function.update σ d r)).card * Fintype.card R = (cyl S σ).card := by
  have hfib : (cyl S σ).card
      = ∑ r' : R, ((cyl S σ).filter (fun H => H d = r')).card :=
    Finset.card_eq_sum_card_fiberwise (fun H _ => Finset.mem_univ (H d))
  rw [hfib]
  have hslice : ∀ r' : R, ((cyl S σ).filter (fun H => H d = r')).card
      = (cyl (insert d S) (Function.update σ d r)).card := by
    intro r'
    rw [cyl_filter_eq S σ d r' hd]
    exact (cyl_insert_card_eq S σ d r r' hd).symm
  rw [Finset.sum_congr rfl (fun r' _ => hslice r'), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm]

/-- **⚑ THE LAW OF TOTAL PROBABILITY OVER A FRESH COORDINATE.** Conditioning on a fresh point's
value averages the conditional probabilities uniformly over `R`. This is lazy sampling, as a finite
counting fact — no measure theory. -/
theorem condProb_split (S : Finset D) (σ : D → R) (d : D) (hd : d ∉ S)
    (win : (D → R) → Bool) :
    condProb (cyl S σ) win
      = (∑ r : R, condProb (cyl (insert d S) (Function.update σ d r)) win)
          / (Fintype.card R : ℝ) := by
  -- `σ d` inhabits `R`, so the reference slice below exists and `|R| > 0`.
  set c : ℕ := (cyl (insert d S) (Function.update σ d (σ d))).card with hc
  have hcpos : 0 < c := cyl_card_pos _ _
  have hslice_card : ∀ r : R, (cyl (insert d S) (Function.update σ d r)).card = c := by
    intro r; exact cyl_insert_card_eq S σ d r (σ d) hd
  have htot : c * Fintype.card R = (cyl S σ).card := cyl_card_insert_mul S σ d (σ d) hd
  have hRpos : 0 < Fintype.card R := Fintype.card_pos_iff.2 ⟨σ d⟩
  -- The winning oracles of `cyl S σ` fiber over the value at `d`, each fiber being the winning
  -- oracles of the corresponding slice.
  have hnum : ((cyl S σ).filter (fun H => win H = true)).card
      = ∑ r : R, ((cyl (insert d S) (Function.update σ d r)).filter (fun H => win H = true)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun H : D → R => H d) (t := (Finset.univ : Finset R))
      (fun H _ => Finset.mem_univ (H d))]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [Finset.filter_comm, cyl_filter_eq S σ d r hd]
  unfold condProb
  rw [hnum, ← htot]
  have hslice_eq : ∀ r : R,
      (((cyl (insert d S) (Function.update σ d r)).filter (fun H => win H = true)).card : ℝ)
        / ((cyl (insert d S) (Function.update σ d r)).card : ℝ)
      = (((cyl (insert d S) (Function.update σ d r)).filter (fun H => win H = true)).card : ℝ)
        / (c : ℝ) := by
    intro r; rw [hslice_card r]
  rw [Finset.sum_congr rfl (fun r _ => hslice_eq r), ← Finset.sum_div]
  push_cast
  rw [div_div]

/-- **⚑ A FRESH POINT HITS A FIXED TARGET WITH PROBABILITY EXACTLY `1/|R|`.** For `a ∉ S`, the
oracle's value at `a` is not pinned by the conditioning, so it hits any fixed `z` with probability
exactly `1/|R|`. What the adversary has not queried, it does not know. -/
theorem condProb_fresh_eq (S : Finset D) (σ : D → R) (a : D) (ha : a ∉ S) (z : R) :
    condProb (cyl S σ) (fun H => decide (H a = z)) = 1 / (Fintype.card R : ℝ) := by
  rw [condProb_split S σ a ha]
  have hpin : ∀ (r : R) (H : D → R), H ∈ cyl (insert a S) (Function.update σ a r) → H a = r := by
    intro r H hH
    have := (mem_cyl.1 hH) a (Finset.mem_insert_self a S)
    simpa using this
  have hval : ∀ r : R, condProb (cyl (insert a S) (Function.update σ a r))
      (fun H => decide (H a = z)) = if r = z then 1 else 0 := by
    intro r
    by_cases hrz : r = z
    · subst hrz
      rw [if_pos rfl]
      exact condProb_eq_one (fun H hH => by simp [hpin r H hH]) (cyl_nonempty _ _)
    · rw [if_neg hrz]
      exact condProb_eq_zero (fun H hH => by simp [hpin r H hH, hrz])
  rw [Finset.sum_congr rfl (fun r _ => hval r), Finset.sum_ite_eq' Finset.univ z (fun _ => (1 : ℝ)),
    if_pos (Finset.mem_univ z)]

#assert_all_clean [
  mem_cyl,
  cyl_empty,
  cyl_nonempty,
  cyl_card_pos,
  condProb_nonneg,
  condProb_le_one,
  condProb_congr,
  condProb_le_of_imp,
  condProb_eq_zero,
  condProb_eq_one,
  condProb_cyl_empty,
  cyl_filter_eq,
  cyl_insert_card_eq,
  cyl_card_insert_mul,
  condProb_split,
  condProb_fresh_eq
]

end Dregg2.Crypto.RomCounting
