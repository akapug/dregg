/-
# Dregg2.Crypto.Deriv.SymbolicIntervals — the SCALAR COMPARISON cover: `amount ≤ limit`,
two-sided ranges, and scalar enums plugged into the minterm tower.

`SymbolicMinterms.lean` closed the per-`R` minterm decision for the typed sym/dig pin classes, and
`SymbolicMintermsPlus.lean` exposed the plug-in seam (`predRE_emptiness_decidable_cover` /
`predRE_equivalence_decidable_cover`: any new `MintermCover` constructor becomes runnable decisions
with zero tower changes). Both headers PRICED the scalar leaves as "the LIA-witness frontier". This
module collects the part of that frontier that is NOT full LIA and closes it: the STATELESS
SINGLE-FIELD comparison atoms of `SimpleConstraint` —

  `fieldEquals f v` · `fieldGe f v` · `fieldLe f v` · `inRangeTwoSided f lo hi` ·
  `memberOf f set` · `SimpleConstraint.not` over these

(wrapped into leaves as `Pred.atom (.simple c)`, under `Pred.and`/`or`/`not` with `tt`/`ff`).
CRITICAL structural fact: every atom above constrains ONE field by thresholds — there is no
cross-field linear relation (`a·x + b·y ≤ c` does not occur) — so minterm witnesses FACTOR PER
FIELD and the feasibility question is INTERVAL feasibility, not LIA.

## The construction (the classic difference-bound / threshold-cell witness)

1. **Thresholds partition ℤ into cells.** For a field `f`, collect the constants mentioned by its
   atoms (`v` from `fieldEquals`/`Ge`/`Le`, `lo`/`hi` from `inRangeTwoSided`, the elements of
   `memberOf`'s set — `intervalAtoms?`). Every atom's truth at a present value `x` is a Boolean
   function of the comparison pair `(x ≤ t, t ≤ x)` per threshold `t` (`x = v ⟺ x ≤ v ∧ v ≤ x`
   etc.), so two present values with the same comparison PROFILE (`profileEq`) satisfy exactly the
   same atoms — as do two ABSENT reads (every atom fails closed on an absent/ill-typed field).
2. **One representative per cell.** `cellReps T = 0 :: T.flatMap (fun t => [t-1, t, t+1])` hits
   every inhabited profile (`exists_cellRep`): a value within distance 1 of a threshold IS a
   representative; otherwise the nearest threshold below (`maxBelow`, +1) or above (`minAbove`, −1)
   yields one on the same side of every threshold.
3. **The per-field product.** `scalarCands A` enumerates one record per choice of
   absent-or-representative per mentioned field (a `List.sections` product — the same shape as
   `atomCands`); the covering witness for a frame `a` is its cell-canonicalization
   (`restrictScalarFrame`, via `findRep`). `coverOfScalars` proves the `MintermCover` contract, and
   the generic §3 assembly of `SymbolicMintermsPlus` turns it into runnable `n`-free decisions
   (`predRE_emptiness_decidable_scalar` / `predRE_equivalence_decidable_scalar`; rigidity is free —
   `predBEq` already decides `atom` leaves by `DecidableEq StateConstraint`).

`memberOf` with a large set stays finite and covered: `|set|` thresholds ⇒ `3·|set| + 1`
representatives — the enum IS its own threshold list.

## Honest boundary — what is NOT covered (named, not faked)

* **REACTIVE atoms** (`immutable`/`writeOnce`/`monotonic`/`strictMono`/`fieldDelta`/
  `deltaBounded`) — they compare NEW against OLD state; a single-frame threshold cell cannot
  witness them. They need a TWO-FRAME delta cover (correlated `(old, new)` representatives) — the
  REACTIVE FRONTIER, the next constructor, not attempted here (`intervalAtoms?` fails closed).
* **Turn-context atoms** (`senderIs`/`balanceGe`/…) — constant-false in the ctx-less leaf reading;
  excluded wholesale rather than special-cased as constants.
* **Cross-field / structural** (`fieldLeField`, `fieldEqField`, `sumEquals`, `prefixOf`, …) — a
  relation BETWEEN fields (or a path shape) does not factor per field; `constraintIntervalAtoms?`
  answers `none`.
* **Mixed guards** (a scalar atom AND a sym/dig pin leaf in one regex) — need the PRODUCT of this
  cover with `coverOfAtoms` (mechanical: both factor per field; the joint constructor is priced,
  not hidden — mixed guards simply are not `scalarRE`, fail closed).
* **`allOf`/`anyOf` payloads holding scalar atoms** — compose `desugarRE` (proven
  language-preserving, `SymbolicMintermsPlus`) with these decisions; `predIntervalAtoms?` itself
  stays structural.

`#assert_all_clean` at the bottom; `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicMintermsPlus
import Mathlib.Data.List.Sections
import Mathlib.Data.List.Dedup

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (der null derives leaf bot derList derives_eq_null_derList
  predBEq RigidFull rigidRE)

/-! ## §1 The interval-atom vocabulary — thresholds of the stateless single-field comparisons. -/

/-- **`intervalAtoms? c`** — the per-field THRESHOLD list of a stateless single-field comparison
atom: `some pairs` when `c`'s truth on a frame is a Boolean function of the comparison profile of
each mentioned field's scalar read against the listed thresholds; `none` outside the class (the
reactive/context/cross-field atoms — the honest boundary in the header). -/
def intervalAtoms? : SimpleConstraint → Option (List (FieldName × Int))
  | .fieldEquals f v         => some [(f, v)]
  | .fieldGe f v             => some [(f, v)]
  | .fieldLe f v             => some [(f, v)]
  | .inRangeTwoSided f lo hi => some [(f, lo), (f, hi)]
  | .memberOf f set          => some (set.map (fun v => (f, v)))
  | .not c                   => intervalAtoms? c
  | _                        => none

/-- Lift to `StateConstraint`: only the `simple` embedding of the interval class. -/
def constraintIntervalAtoms? : StateConstraint → Option (List (FieldName × Int))
  | .simple c => intervalAtoms? c
  | _         => none

/-- **`predIntervalAtoms? φ`** — the threshold set of a scalar-comparison leaf: `atom (.simple c)`
for interval `c`, under `and`/`or`/`not` with `tt`/`ff`. `none` outside (fail closed). -/
def predIntervalAtoms? : Pred → Option (List (FieldName × Int))
  | .tt     => some []
  | .ff     => some []
  | .atom c => constraintIntervalAtoms? c
  | .and l r =>
      match predIntervalAtoms? l, predIntervalAtoms? r with
      | some A, some B => some (A ++ B)
      | _, _ => none
  | .or l r =>
      match predIntervalAtoms? l, predIntervalAtoms? r with
      | some A, some B => some (A ++ B)
      | _, _ => none
  | .not p  => predIntervalAtoms? p
  | _       => none

/-! ## §2 The comparison probe and the leaf-truth factoring. -/

/-- **`scalarProbe a f t`** — everything an interval atom can see of frame `a` at field `f`
relative to threshold `t`: `none` when the scalar read fails (absent/ill-typed — every atom then
fails closed), otherwise the comparison pair `(x ≤ t, t ≤ x)`. -/
def scalarProbe (a : Value) (f : FieldName) (t : Int) : Option (Bool × Bool) :=
  (a.scalar f).map (fun x => (decide (x ≤ t), decide (t ≤ x)))

private theorem bool_eq_of_iff {p q : Bool} (h : p = true ↔ q = true) : p = q := by
  cases p <;> cases q <;> simp_all

/-- Unpack probe agreement at one threshold: both reads absent, or both present with the same
comparison profile against `t`. -/
private theorem probe_agree {a b : Value} {f : FieldName} {t : Int}
    (h : scalarProbe a f t = scalarProbe b f t) :
    (a.scalar f = none ∧ b.scalar f = none) ∨
      (∃ x y, a.scalar f = some x ∧ b.scalar f = some y ∧ (x ≤ t ↔ y ≤ t) ∧ (t ≤ x ↔ t ≤ y)) := by
  simp only [scalarProbe] at h
  cases ha : a.scalar f with
  | none =>
      cases hb : b.scalar f with
      | none => exact Or.inl ⟨rfl, rfl⟩
      | some y => rw [ha, hb] at h; simp at h
  | some x =>
      cases hb : b.scalar f with
      | none => rw [ha, hb] at h; simp at h
      | some y =>
          rw [ha, hb] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          exact Or.inr ⟨x, y, rfl, rfl, decide_eq_decide.mp h.1, decide_eq_decide.mp h.2⟩

/-- `List.contains` congruence under pointwise `==`-agreement. -/
private theorem contains_congr {x y : Int} : ∀ {l : List Int},
    (∀ s ∈ l, ((x == s) = (y == s))) → l.contains x = l.contains y
  | [], _ => rfl
  | s :: rest, h => by
      simp only [List.contains_cons]
      rw [h s (by simp), contains_congr (fun s' hs' => h s' (List.mem_cons_of_mem _ hs'))]

/-- **`intervalAtoms?_reads`** — the interval-atom truth factoring: two frames agreeing on every
threshold probe get the same verdict (old state is irrelevant — the class is stateless). -/
theorem intervalAtoms?_reads : ∀ {c : SimpleConstraint} {A : List (FieldName × Int)},
    intervalAtoms? c = some A →
    ∀ {o a b : Value}, (∀ p ∈ A, scalarProbe a p.1 p.2 = scalarProbe b p.1 p.2) →
      evalSimple c o a = evalSimple c o b
  | .fieldEquals f v, A, h, o, a, b, hab => by
      simp only [intervalAtoms?, Option.some.injEq] at h
      subst h
      rcases probe_agree (hab (f, v) (by simp)) with ⟨ha, hb⟩ | ⟨x, y, ha, hb, h1, h2⟩
      · simp only [evalSimple, ha, hb]
      · simp only [evalSimple, ha, hb]
        apply bool_eq_of_iff
        simp only [beq_iff_eq, Option.some.injEq]
        omega
  | .fieldGe f v, A, h, o, a, b, hab => by
      simp only [intervalAtoms?, Option.some.injEq] at h
      subst h
      rcases probe_agree (hab (f, v) (by simp)) with ⟨ha, hb⟩ | ⟨x, y, ha, hb, h1, h2⟩
      · simp only [evalSimple, ha, hb]
      · simp only [evalSimple, ha, hb]
        apply bool_eq_of_iff
        show decide (v ≤ x) = true ↔ decide (v ≤ y) = true
        simp only [decide_eq_true_eq]
        omega
  | .fieldLe f v, A, h, o, a, b, hab => by
      simp only [intervalAtoms?, Option.some.injEq] at h
      subst h
      rcases probe_agree (hab (f, v) (by simp)) with ⟨ha, hb⟩ | ⟨x, y, ha, hb, h1, h2⟩
      · simp only [evalSimple, ha, hb]
      · simp only [evalSimple, ha, hb]
        apply bool_eq_of_iff
        show decide (x ≤ v) = true ↔ decide (y ≤ v) = true
        simp only [decide_eq_true_eq]
        omega
  | .inRangeTwoSided f lo hi, A, h, o, a, b, hab => by
      simp only [intervalAtoms?, Option.some.injEq] at h
      subst h
      rcases probe_agree (hab (f, lo) (by simp)) with ⟨ha, hb⟩ | ⟨x, y, ha, hb, hl1, hl2⟩
      · simp only [evalSimple, ha, hb]
      · rcases probe_agree (hab (f, hi) (by simp)) with ⟨ha', _⟩ | ⟨x', y', ha', hb', hh1, hh2⟩
        · rw [ha] at ha'; exact absurd ha' (by simp)
        · rw [ha] at ha'; rw [hb] at hb'
          injection ha' with hx
          injection hb' with hy
          subst hx; subst hy
          simp only [evalSimple, ha, hb]
          apply bool_eq_of_iff
          show (decide (lo ≤ x) && decide (x ≤ hi)) = true ↔
               (decide (lo ≤ y) && decide (y ≤ hi)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          omega
  | .memberOf f set, A, h, o, a, b, hab => by
      simp only [intervalAtoms?, Option.some.injEq] at h
      subst h
      cases set with
      | nil =>
          simp only [evalSimple]
          cases a.scalar f <;> cases b.scalar f <;> rfl
      | cons s rest =>
          rcases probe_agree (hab (f, s) (List.mem_map.mpr ⟨s, by simp, rfl⟩)) with
            ⟨ha, hb⟩ | ⟨x, y, ha, hb, -, -⟩
          · simp only [evalSimple, ha, hb]
          · simp only [evalSimple, ha, hb]
            apply contains_congr
            intro s' hs'
            rcases probe_agree (hab (f, s') (List.mem_map.mpr ⟨s', hs', rfl⟩)) with
              ⟨ha', _⟩ | ⟨x', y', ha', hb', h1, h2⟩
            · rw [ha] at ha'; exact absurd ha' (by simp)
            · rw [ha] at ha'; rw [hb] at hb'
              injection ha' with hx
              injection hb' with hy
              subst hx; subst hy
              apply bool_eq_of_iff
              simp only [beq_iff_eq]
              omega
  | .not c, A, h, o, a, b, hab => by
      simp only [intervalAtoms?] at h
      rw [evalSimple_not, evalSimple_not, intervalAtoms?_reads h hab]

/-- Lift to `StateConstraint` (only the `simple` arm is inhabited). -/
theorem constraintIntervalAtoms?_reads : ∀ {c : StateConstraint} {A : List (FieldName × Int)},
    constraintIntervalAtoms? c = some A →
    ∀ {o a b : Value}, (∀ p ∈ A, scalarProbe a p.1 p.2 = scalarProbe b p.1 p.2) →
      evalConstraint c o a = evalConstraint c o b
  | .simple sc, A, h, o, a, b, hab => by
      simp only [constraintIntervalAtoms?] at h
      simp only [evalConstraint]
      exact intervalAtoms?_reads h hab

/-- **`predIntervalAtoms?_reads`** — the leaf-truth factoring through threshold probes (the scalar
analogue of `predAtoms?_reads`): when `predIntervalAtoms? φ = some A`, two frames agreeing on every
probe of `A` get the same single-frame verdict from `φ`. -/
theorem predIntervalAtoms?_reads : ∀ (φ : Pred) {A : List (FieldName × Int)},
    predIntervalAtoms? φ = some A →
    ∀ {a b : Value}, (∀ p ∈ A, scalarProbe a p.1 p.2 = scalarProbe b p.1 p.2) →
      leaf φ a = leaf φ b
  | .tt, _, _, _, _, _ => rfl
  | .ff, _, _, _, _, _ => rfl
  | .atom c, A, h, a, b, hab => by
      simp only [predIntervalAtoms?] at h
      show Pred.eval (.atom c) (.record []) a = Pred.eval (.atom c) (.record []) b
      simp only [Pred.eval]
      exact constraintIntervalAtoms?_reads h hab
  | .and l r, A, h, a, b, hab => by
      simp only [predIntervalAtoms?] at h
      cases hl : predIntervalAtoms? l with
      | none => rw [hl] at h; exact absurd h (by simp)
      | some Al =>
        cases hr : predIntervalAtoms? r with
        | none => rw [hl, hr] at h; exact absurd h (by simp)
        | some Ar =>
          rw [hl, hr, Option.some.injEq] at h
          subst h
          have ihl := predIntervalAtoms?_reads l hl
            (fun p hp => hab p (List.mem_append.mpr (Or.inl hp)))
          have ihr := predIntervalAtoms?_reads r hr
            (fun p hp => hab p (List.mem_append.mpr (Or.inr hp)))
          simp only [PredRE.leaf, Pred.eval] at ihl ihr ⊢
          rw [ihl, ihr]
  | .or l r, A, h, a, b, hab => by
      simp only [predIntervalAtoms?] at h
      cases hl : predIntervalAtoms? l with
      | none => rw [hl] at h; exact absurd h (by simp)
      | some Al =>
        cases hr : predIntervalAtoms? r with
        | none => rw [hl, hr] at h; exact absurd h (by simp)
        | some Ar =>
          rw [hl, hr, Option.some.injEq] at h
          subst h
          have ihl := predIntervalAtoms?_reads l hl
            (fun p hp => hab p (List.mem_append.mpr (Or.inl hp)))
          have ihr := predIntervalAtoms?_reads r hr
            (fun p hp => hab p (List.mem_append.mpr (Or.inr hp)))
          simp only [PredRE.leaf, Pred.eval] at ihl ihr ⊢
          rw [ihl, ihr]
  | .not p, A, h, a, b, hab => by
      have ih := predIntervalAtoms?_reads p h hab
      simp only [PredRE.leaf, Pred.eval] at ih ⊢
      rw [ih]

/-! ## §3 Threshold cells and their representatives — the per-field witness enumeration. -/

/-- **`profileEq T r x`** — `r` and `x` fall on the same side of every threshold in `T` (both
comparisons agree per threshold). Same profile ⇒ same verdict from every atom over `T`. -/
def profileEq (T : List Int) (r x : Int) : Bool :=
  T.all (fun t => (decide (r ≤ t) == decide (x ≤ t)) && (decide (t ≤ r) == decide (t ≤ x)))

theorem profileEq_refl (T : List Int) (x : Int) : profileEq T x x = true := by
  simp [profileEq]

theorem profileEq_probe {T : List Int} {r x : Int} (h : profileEq T r x = true) {t : Int}
    (ht : t ∈ T) : ((r ≤ t) ↔ (x ≤ t)) ∧ ((t ≤ r) ↔ (t ≤ x)) := by
  rw [profileEq, List.all_eq_true] at h
  have := h t ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_decide] at this
  exact this

/-- **`cellReps T`** — one representative per threshold cell: each threshold, its two neighbors,
and a default (`0`, covering the no-threshold case). Every inhabited comparison profile is realized
by a member (`exists_cellRep`). -/
def cellReps (T : List Int) : List Int := 0 :: T.flatMap (fun t => [t - 1, t, t + 1])

theorem mem_cellReps_of_near {T : List Int} {t r : Int} (ht : t ∈ T)
    (h : r = t - 1 ∨ r = t ∨ r = t + 1) : r ∈ cellReps T := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨t, ht, ?_⟩)
  rcases h with rfl | rfl | rfl <;> simp

/-- The greatest element of `T` strictly below `x` (`none` if there is none). -/
def maxBelow (x : Int) : List Int → Option Int
  | [] => none
  | t :: ts =>
      match maxBelow x ts with
      | none => if t < x then some t else none
      | some m => if t < x ∧ m < t then some t else some m

/-- The least element of `T` strictly above `x` (`none` if there is none). -/
def minAbove (x : Int) : List Int → Option Int
  | [] => none
  | t :: ts =>
      match minAbove x ts with
      | none => if x < t then some t else none
      | some m => if x < t ∧ t < m then some t else some m

theorem maxBelow_none {x : Int} : ∀ {T : List Int}, maxBelow x T = none →
    ∀ t ∈ T, ¬ t < x := by
  intro T
  induction T with
  | nil => intro _ t ht; simp at ht
  | cons s ts ih =>
      intro h t ht
      simp only [maxBelow] at h
      cases hrec : maxBelow x ts with
      | none =>
          rw [hrec] at h
          by_cases hs : s < x
          · rw [if_pos hs] at h; exact absurd h (by simp)
          · rw [if_neg hs] at h
            rcases List.mem_cons.mp ht with rfl | ht'
            · exact hs
            · exact ih hrec t ht'
      | some m =>
          rw [hrec] at h
          split at h <;> exact absurd h (by simp)

theorem maxBelow_some {x : Int} : ∀ {T : List Int} {m : Int}, maxBelow x T = some m →
    m ∈ T ∧ m < x ∧ ∀ t ∈ T, t < x → t ≤ m := by
  intro T
  induction T with
  | nil => intro m h; simp [maxBelow] at h
  | cons s ts ih =>
      intro m h
      simp only [maxBelow] at h
      cases hrec : maxBelow x ts with
      | none =>
          rw [hrec] at h
          by_cases hs : s < x
          · rw [if_pos hs] at h
            injection h with h
            subst h
            refine ⟨by simp, hs, ?_⟩
            intro t ht htx
            rcases List.mem_cons.mp ht with rfl | ht'
            · omega
            · exact absurd htx (maxBelow_none hrec t ht')
          · rw [if_neg hs] at h; exact absurd h (by simp)
      | some m' =>
          rw [hrec] at h
          obtain ⟨hmT, hmx, hmax⟩ := ih hrec
          by_cases hc : s < x ∧ m' < s
          · rw [if_pos hc] at h
            injection h with h
            subst h
            refine ⟨by simp, hc.1, ?_⟩
            intro t ht htx
            rcases List.mem_cons.mp ht with rfl | ht'
            · omega
            · have := hmax t ht' htx; omega
          · rw [if_neg hc] at h
            injection h with h
            subst h
            refine ⟨List.mem_cons_of_mem _ hmT, hmx, ?_⟩
            intro t ht htx
            rcases List.mem_cons.mp ht with rfl | ht'
            · omega
            · exact hmax t ht' htx

theorem minAbove_none {x : Int} : ∀ {T : List Int}, minAbove x T = none →
    ∀ t ∈ T, ¬ x < t := by
  intro T
  induction T with
  | nil => intro _ t ht; simp at ht
  | cons s ts ih =>
      intro h t ht
      simp only [minAbove] at h
      cases hrec : minAbove x ts with
      | none =>
          rw [hrec] at h
          by_cases hs : x < s
          · rw [if_pos hs] at h; exact absurd h (by simp)
          · rw [if_neg hs] at h
            rcases List.mem_cons.mp ht with rfl | ht'
            · exact hs
            · exact ih hrec t ht'
      | some m =>
          rw [hrec] at h
          split at h <;> exact absurd h (by simp)

theorem minAbove_some {x : Int} : ∀ {T : List Int} {m : Int}, minAbove x T = some m →
    m ∈ T ∧ x < m ∧ ∀ t ∈ T, x < t → m ≤ t := by
  intro T
  induction T with
  | nil => intro m h; simp [minAbove] at h
  | cons s ts ih =>
      intro m h
      simp only [minAbove] at h
      cases hrec : minAbove x ts with
      | none =>
          rw [hrec] at h
          by_cases hs : x < s
          · rw [if_pos hs] at h
            injection h with h
            subst h
            refine ⟨by simp, hs, ?_⟩
            intro t ht htx
            rcases List.mem_cons.mp ht with rfl | ht'
            · omega
            · exact absurd htx (minAbove_none hrec t ht')
          · rw [if_neg hs] at h; exact absurd h (by simp)
      | some m' =>
          rw [hrec] at h
          obtain ⟨hmT, hmx, hmin⟩ := ih hrec
          by_cases hc : x < s ∧ s < m'
          · rw [if_pos hc] at h
            injection h with h
            subst h
            refine ⟨by simp, hc.1, ?_⟩
            intro t ht htx
            rcases List.mem_cons.mp ht with rfl | ht'
            · omega
            · have := hmin t ht' htx; omega
          · rw [if_neg hc] at h
            injection h with h
            subst h
            refine ⟨List.mem_cons_of_mem _ hmT, hmx, ?_⟩
            intro t ht htx
            rcases List.mem_cons.mp ht with rfl | ht'
            · omega
            · exact hmin t ht' htx

/-- **`exists_cellRep`** — the cell-cover fact: every integer's comparison profile against `T` is
realized by an enumerated representative. Near a threshold (distance ≤ 1) the value itself is
enumerated; otherwise the neighbor of the nearest threshold below/above is on the same side of
every threshold. -/
theorem exists_cellRep (T : List Int) (x : Int) :
    ∃ r ∈ cellReps T, profileEq T r x = true := by
  by_cases hnear : ∃ t ∈ T, t - 1 ≤ x ∧ x ≤ t + 1
  · obtain ⟨t, ht, h1, h2⟩ := hnear
    exact ⟨x, mem_cellReps_of_near ht (by omega), profileEq_refl T x⟩
  · push_neg at hnear
    cases hmb : maxBelow x T with
    | some m =>
        obtain ⟨hmT, hmx, hmax⟩ := maxBelow_some hmb
        refine ⟨m + 1, mem_cellReps_of_near hmT (by omega), ?_⟩
        rw [profileEq, List.all_eq_true]
        intro t ht
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_decide]
        have hn := hnear t ht
        by_cases htx : t < x
        · have h1 := hmax t ht htx
          omega
        · have hxt : x ≤ t := by omega
          have hfar : x < t - 1 := by
            by_cases hc : t - 1 ≤ x
            · have := hn hc; omega
            · omega
          omega
    | none =>
        have hno := maxBelow_none hmb
        cases hma : minAbove x T with
        | some m =>
            obtain ⟨hmT, hxm, hmin⟩ := minAbove_some hma
            refine ⟨m - 1, mem_cellReps_of_near hmT (by omega), ?_⟩
            rw [profileEq, List.all_eq_true]
            intro t ht
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_decide]
            have h1 := hno t ht
            have hn := hnear t ht
            have hxt : x < t := by
              by_cases hc : t - 1 ≤ x
              · have := hn hc; omega
              · omega
            have h2 := hmin t ht hxt
            omega
        | none =>
            refine ⟨0, by simp [cellReps], ?_⟩
            rw [profileEq, List.all_eq_true]
            intro t ht
            have h1 := hno t ht
            have h2 := minAbove_none hma t ht
            have hn := hnear t ht
            exfalso
            have hteq : t = x := by omega
            subst hteq
            have := hn (by omega)
            omega

/-- **`findRep T x`** — the computable cell canonicalization: the first enumerated representative
with `x`'s profile (total by `exists_cellRep`; the `0` default is never reached). -/
def findRep (T : List Int) (x : Int) : Int :=
  match (cellReps T).find? (fun r => profileEq T r x) with
  | some r => r
  | none => 0

theorem findRep_mem (T : List Int) (x : Int) : findRep T x ∈ cellReps T := by
  unfold findRep
  split
  · next r hf => exact List.mem_of_find?_eq_some hf
  · next hf =>
      obtain ⟨r, hr, hp⟩ := exists_cellRep T x
      exact absurd hp (by simpa using List.find?_eq_none.mp hf r hr)

theorem findRep_profileEq (T : List Int) (x : Int) : profileEq T (findRep T x) x = true := by
  unfold findRep
  split
  · next r hf => exact List.find?_some hf
  · next hf =>
      obtain ⟨r, hr, hp⟩ := exists_cellRep T x
      exact absurd hp (by simpa using List.find?_eq_none.mp hf r hr)

/-! ## §4 The per-field product frames and the assembled cover. -/

/-- The thresholds mentioned at field `f`. -/
def sThresholds (A : List (FieldName × Int)) (f : FieldName) : List Int :=
  (A.filter (fun p => p.1 == f)).map (·.2)

/-- The distinct mentioned fields. -/
def sFields (A : List (FieldName × Int)) : List FieldName := (A.map (·.1)).dedup

/-- The canonical per-field choice frame `a` induces: absent stays absent; a present value maps to
its cell representative. -/
def sChoice (A : List (FieldName × Int)) (a : Value) (f : FieldName) : Option Int :=
  (a.scalar f).map (fun x => findRep (sThresholds A f) x)

/-- The cell-canonicalization of frame `a`: per mentioned field, the representative of `a`'s cell
(dropped when absent). A finite record with the same probe behavior as `a`. -/
def restrictScalarFrame (A : List (FieldName × Int)) (a : Value) : Value :=
  .record ((sFields A).filterMap (fun f => (sChoice A a f).map (fun i => (f, Value.int i))))

/-- The candidate frames: one record per choice of absent-or-representative per mentioned field
(a `List.sections` product — the scalar twin of `atomCands`). -/
def scalarCands (A : List (FieldName × Int)) : List Value :=
  (((sFields A).map
      (fun f => (none :: (cellReps (sThresholds A f)).map some).map (fun o => (f, o)))).sections).map
    (fun ch => .record (ch.filterMap (fun p => p.2.map (fun i => (p.1, Value.int i)))))

/-- Field lookup on a choice-built scalar record: with distinct fields, reading `f` returns exactly
the choice at `f` (the `Value.int` twin of `field_ofChoices`). -/
theorem scalarField_ofChoices {g : FieldName → Option Int} :
    ∀ {fs : List FieldName}, fs.Nodup → ∀ {f : FieldName}, f ∈ fs →
      (Value.record (fs.filterMap
          (fun x => (g x).map (fun v => (x, Value.int v))))).field f
        = (g f).map Value.int := by
  intro fs
  induction fs with
  | nil => intro _ f hf; simp at hf
  | cons x xs ih =>
      intro hnd f hf
      obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
      by_cases hfx : f = x
      · subst hfx
        cases hgx : g f with
        | none =>
            rw [List.filterMap_cons_none (by rw [hgx]; rfl)]
            simp only [Option.map_none]
            rw [List.find?_eq_none.mpr, Option.map_none]
            intro p hp
            obtain ⟨y, hy, hpy⟩ := List.mem_filterMap.mp hp
            cases hgy : g y with
            | none => rw [hgy] at hpy; simp at hpy
            | some v =>
                rw [hgy] at hpy
                simp only [Option.map_some, Option.some.injEq] at hpy
                subst hpy
                simp only [Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq]
                intro hyf
                exact hx (hyf ▸ hy)
        | some v =>
            rw [List.filterMap_cons_some (by rw [hgx]; rfl)]
            simp only [Value.field]
            rw [List.find?_cons_of_pos (by simp)]
            rfl
      · have hf' : f ∈ xs := by
          rcases List.mem_cons.mp hf with h | h
          · exact absurd h hfx
          · exact h
        cases hgx : g x with
        | none =>
            rw [List.filterMap_cons_none (by rw [hgx]; rfl)]
            exact ih hnd' hf'
        | some v =>
            rw [List.filterMap_cons_some (by rw [hgx]; rfl)]
            have := ih hnd' hf'
            simp only [Value.field] at this ⊢
            rw [List.find?_cons_of_neg (by simpa using fun h => hfx h.symm)]
            exact this

/-- The scalar read of a choice-built record is exactly the choice. -/
theorem scalar_ofChoices {g : FieldName → Option Int} {fs : List FieldName} (hnd : fs.Nodup)
    {f : FieldName} (hf : f ∈ fs) :
    (Value.record (fs.filterMap
        (fun x => (g x).map (fun v => (x, Value.int v))))).scalar f = g f := by
  simp only [Value.scalar, scalarField_ofChoices hnd hf]
  cases g f <;> rfl

theorem restrictScalarFrame_scalar {A : List (FieldName × Int)} {a : Value} {f : FieldName}
    (hf : f ∈ sFields A) :
    (restrictScalarFrame A a).scalar f = sChoice A a f :=
  scalar_ofChoices (List.nodup_dedup _) hf

/-- **`scalarProbe_restrict`** — the canonicalization preserves every mentioned probe: on each
`(f, t) ∈ A`, `restrictScalarFrame A a` and `a` agree (absent stays absent; a present value's
representative shares its profile at `t`). -/
theorem scalarProbe_restrict {A : List (FieldName × Int)} {a : Value} {f : FieldName} {t : Int}
    (hft : (f, t) ∈ A) :
    scalarProbe (restrictScalarFrame A a) f t = scalarProbe a f t := by
  have hf : f ∈ sFields A :=
    List.mem_dedup.mpr (List.mem_map.mpr ⟨(f, t), hft, rfl⟩)
  have ht : t ∈ sThresholds A f := by
    simp only [sThresholds, List.mem_map, List.mem_filter]
    exact ⟨(f, t), ⟨hft, by simp⟩, rfl⟩
  simp only [scalarProbe, restrictScalarFrame_scalar hf, sChoice]
  cases ha : a.scalar f with
  | none => rfl
  | some x =>
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      have hp := profileEq_probe (findRep_profileEq (sThresholds A f) x) ht
      constructor <;> (rw [decide_eq_decide]; tauto)

/-- The canonicalization IS one of the enumerated candidates. -/
theorem restrictScalarFrame_mem_scalarCands (A : List (FieldName × Int)) (a : Value) :
    restrictScalarFrame A a ∈ scalarCands A := by
  apply List.mem_map.mpr
  refine ⟨(sFields A).map (fun f => (f, sChoice A a f)), ?_, ?_⟩
  · apply List.mem_sections.mpr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro f _
    simp only [List.mem_map]
    refine ⟨sChoice A a f, ?_, rfl⟩
    have hrep : sChoice A a f = none ∨
        ∃ x, sChoice A a f = some (findRep (sThresholds A f) x) := by
      unfold sChoice
      cases a.scalar f with
      | none => exact Or.inl rfl
      | some x => exact Or.inr ⟨x, rfl⟩
    rcases hrep with h | ⟨x, h⟩
    · rw [h]; exact List.mem_cons.mpr (Or.inl rfl)
    · rw [h]
      exact List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨_, findRep_mem _ _, rfl⟩))
  · simp only [List.filterMap_map]
    rfl

/-- **`coverOfScalars`** — the assembled `MintermCover` for scalar-comparison leaf lists: the
per-field product of cell representatives covers every inhabited minterm — the covering witness
for frame `a` is its cell-canonicalization. -/
def coverOfScalars (A : List (FieldName × Int)) (L : List Pred)
    (hL : ∀ φ ∈ L, ∃ Aφ, predIntervalAtoms? φ = some Aφ ∧ Aφ ⊆ A) : MintermCover L where
  cands := scalarCands A
  covers a := by
    refine ⟨restrictScalarFrame A a, restrictScalarFrame_mem_scalarCands A a, ?_⟩
    apply List.map_inj_left.mpr
    intro φ hφ
    obtain ⟨Aφ, hAφ, hsub⟩ := hL φ hφ
    exact predIntervalAtoms?_reads φ hAφ (fun p hp => scalarProbe_restrict (hsub hp))

/-! ## §5 The fragment check, rigidity, and the runnable decisions. -/

/-- Fold `predIntervalAtoms?` over a leaf list (fails closed on one uncovered leaf). -/
def scalarLeaves? : List Pred → Option (List (FieldName × Int))
  | [] => some []
  | φ :: rest =>
      match predIntervalAtoms? φ, scalarLeaves? rest with
      | some A, some B => some (A ++ B)
      | _, _ => none

theorem scalarLeaves?_spec : ∀ {l : List Pred} {A : List (FieldName × Int)},
    scalarLeaves? l = some A → ∀ φ ∈ l, ∃ Aφ, predIntervalAtoms? φ = some Aφ ∧ Aφ ⊆ A := by
  intro l
  induction l with
  | nil => intro A _ φ hφ; simp at hφ
  | cons ψ rest ih =>
      intro A h φ hφ
      simp only [scalarLeaves?] at h
      cases hψ : predIntervalAtoms? ψ with
      | none => rw [hψ] at h; exact absurd h (by simp)
      | some Aψ =>
        cases hrest : scalarLeaves? rest with
        | none => rw [hψ, hrest] at h; exact absurd h (by simp)
        | some B =>
          rw [hψ, hrest, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp hφ with rfl | hφ'
          · exact ⟨Aψ, hψ, fun x hx => List.mem_append.mpr (Or.inl hx)⟩
          · obtain ⟨Aφ, hA, hsub⟩ := ih hrest φ hφ'
            exact ⟨Aφ, hA, fun x hx => List.mem_append.mpr (Or.inr (hsub hx))⟩

theorem scalarLeaves?_isSome : ∀ {l : List Pred},
    (scalarLeaves? l).isSome = true ↔ ∀ φ ∈ l, (predIntervalAtoms? φ).isSome = true := by
  intro l
  induction l with
  | nil => simp [scalarLeaves?]
  | cons ψ rest ih =>
      simp only [scalarLeaves?]
      cases hψ : predIntervalAtoms? ψ with
      | none => simp [hψ]
      | some Aψ =>
        cases hrest : scalarLeaves? rest with
        | none =>
            rw [hrest] at ih
            simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at ih ⊢
            intro hall
            exact ih (fun φ hφ => hall φ (List.mem_cons.mpr (Or.inr hφ)))
        | some B =>
            rw [hrest] at ih
            simp only [Option.isSome_some, true_iff] at ih
            simp only [Option.isSome_some, true_iff]
            intro φ hφ
            rcases List.mem_cons.mp hφ with rfl | hφ'
            · rw [hψ]; rfl
            · exact ih φ hφ'

/-- **`scalarRE R`** — the computable fragment check: every leaf of `R` is a scalar-comparison
combination (the `IsSymbolic`/`dfeRE` analogue for the interval class). -/
def scalarRE (R : PredRE) : Bool := (scalarLeaves? (leavesOf R)).isSome

/-- Scalar-comparison leaves are `predBEq`-reflexive (`atom` leaves ride
`DecidableEq StateConstraint`) — rigidity is derivable on this fragment too. -/
theorem predBEq_refl_of_intervalAtoms : ∀ {φ : Pred}, (predIntervalAtoms? φ).isSome = true →
    predBEq φ φ = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .atom c, _ => by simp [predBEq]
  | .and l r, h => by
      simp only [predIntervalAtoms?] at h
      cases hl : predIntervalAtoms? l with
      | none => rw [hl] at h; simp at h
      | some Al =>
        cases hr : predIntervalAtoms? r with
        | none => rw [hl, hr] at h; simp at h
        | some Ar =>
          have ihl := predBEq_refl_of_intervalAtoms (φ := l) (by rw [hl]; rfl)
          have ihr := predBEq_refl_of_intervalAtoms (φ := r) (by rw [hr]; rfl)
          simp only [predBEq, Bool.and_eq_true]
          exact ⟨ihl, ihr⟩
  | .or l r, h => by
      simp only [predIntervalAtoms?] at h
      cases hl : predIntervalAtoms? l with
      | none => rw [hl] at h; simp at h
      | some Al =>
        cases hr : predIntervalAtoms? r with
        | none => rw [hl, hr] at h; simp at h
        | some Ar =>
          have ihl := predBEq_refl_of_intervalAtoms (φ := l) (by rw [hl]; rfl)
          have ihr := predBEq_refl_of_intervalAtoms (φ := r) (by rw [hr]; rfl)
          simp only [predBEq, Bool.and_eq_true]
          exact ⟨ihl, ihr⟩
  | .not p, h => by
      have ih := predBEq_refl_of_intervalAtoms (φ := p) h
      simpa [predBEq] using ih

theorem rigidRE_of_scalarRE {R : PredRE} (h : scalarRE R = true) : RigidFull R :=
  rigidRE_of_leaves fun φ hφ =>
    predBEq_refl_of_intervalAtoms ((scalarLeaves?_isSome.mp h) φ hφ)

/-- The scalar fragment is closed under `symDiff` — equivalence stays in the fragment. -/
theorem scalarRE_symDiff {R S : PredRE} (hR : scalarRE R = true) (hS : scalarRE S = true) :
    scalarRE (symDiff R S) = true := by
  simp only [scalarRE, scalarLeaves?_isSome] at *
  intro φ hφ
  simp only [symDiff, leavesOf, List.mem_append] at hφ
  rcases hφ with (h | h) | (h | h)
  · exact hR φ h
  · exact hS φ h
  · exact hR φ h
  · exact hS φ h

/-- **`predRE_emptiness_decidable_scalar`** — runnable unbounded emptiness for scalar-comparison
guards: the threshold-cell product cover through the generic assembly; every hypothesis
computable. -/
def predRE_emptiness_decidable_scalar (fuel : Nat) {R : PredRE} (h : scalarRE R = true) :
    Decidable (∃ w, derives w R = true) :=
  match hA : scalarLeaves? (leavesOf R) with
  | some A =>
      predRE_emptiness_decidable_cover
        (coverOfScalars A (leavesOf R) (scalarLeaves?_spec hA))
        fuel (symbolicOver_leavesOf R) (rigidRE_of_scalarRE h)
  | none => absurd h (by simp [scalarRE, hA])

/-- **`predRE_equivalence_decidable_scalar`** — runnable language equivalence for
scalar-comparison guards (the symmetric difference stays in the fragment). -/
def predRE_equivalence_decidable_scalar (fuel : Nat) {R S : PredRE}
    (hR : scalarRE R = true) (hS : scalarRE S = true) :
    Decidable (∀ w, derives w R = derives w S) :=
  match hA : scalarLeaves? (leavesOf (symDiff R S)) with
  | some A =>
      predRE_equivalence_decidable_cover
        (coverOfScalars A (leavesOf (symDiff R S)) (scalarLeaves?_spec hA))
        fuel (symbolicOver_leavesOf _) (rigidRE_of_scalarRE (scalarRE_symDiff hR hS))
  | none => absurd (scalarRE_symDiff hR hS) (by simp [scalarRE, hA])

/-! ## §6 The deliverable `#guard`s — REAL scalar guards KERNEL-DECIDED.

The classic builder questions, decided end to end: a spend cap is satisfiable; contradictory
bounds are EMPTY at every word length (`n`-free, through the saturating fixpoint); a refactored
bound is EQUIVALENT to its original spelling (a subsumed point, a range-vs-conjunction identity,
an enum-vs-disjunction identity); a two-field guard rides the per-field product cover. -/

section Guards

/-- The spend cap: `amount ≤ 100`. -/
def amountLe100 : PredRE := .sym (.atom (.simple (.fieldLe "amount" 100)))

/-- The floor: `amount ≥ 200`. -/
def amountGe200 : PredRE := .sym (.atom (.simple (.fieldGe "amount" 200)))

/-- Contradictory bounds: `amount ≤ 100 ∧ amount ≥ 200` — no frame satisfies both. -/
def amountContraRE : PredRE := .inter amountLe100 amountGe200

/-- The cap with a redundantly disjoined point INSIDE it: `amount ≤ 100 ∨ amount = 50` — the
"is my refactored bound equivalent?" spelling (the range subsumes the point). -/
def amountLeOr50RE : PredRE :=
  .alt amountLe100 (.sym (.atom (.simple (.fieldEquals "amount" 50))))

/-- The cap with a point OUTSIDE it: `amount ≤ 100 ∨ amount = 150` — genuinely different. -/
def amountLeOr150RE : PredRE :=
  .alt amountLe100 (.sym (.atom (.simple (.fieldEquals "amount" 150))))

/-- The over-cap violation guard: `¬(amount ≤ 100)` — `SimpleConstraint.not` inside the atom. -/
def overCapRE : PredRE := .sym (.atom (.simple (.not (.fieldLe "amount" 100))))

/-- The TWO-FIELD guard: `amount ≤ 100 ∧ fee ≥ 0` — the per-field product cover. -/
def feeGuardRE : PredRE :=
  .sym (.and (.atom (.simple (.fieldLe "amount" 100))) (.atom (.simple (.fieldGe "fee" 0))))

/-- The price band as ONE atom: `10 ≤ amount ≤ 20`. -/
def bandRE : PredRE := .sym (.atom (.simple (.inRangeTwoSided "amount" 10 20)))

/-- The same band as a conjunction of one-sided atoms. -/
def bandConjRE : PredRE :=
  .sym (.and (.atom (.simple (.fieldGe "amount" 10))) (.atom (.simple (.fieldLe "amount" 20))))

/-- The scalar enum: `state ∈ {1, 2}`. -/
def stateEnumRE : PredRE := .sym (.atom (.simple (.memberOf "state" [1, 2])))

/-- The same enum as an equality disjunction. -/
def stateDisjRE : PredRE :=
  .alt (.sym (.atom (.simple (.fieldEquals "state" 1))))
       (.sym (.atom (.simple (.fieldEquals "state" 2))))

-- Fragment membership + rigidity, kernel-checked (rigidity rides `DecidableEq StateConstraint`):
#guard scalarRE amountLe100 = true
#guard scalarRE amountContraRE = true
#guard scalarRE overCapRE = true
#guard scalarRE feeGuardRE = true
#guard rigidRE amountLe100 = true
-- ...and the honest scope boundary, fail-closed: REACTIVE atoms (new-vs-old) are NOT in this
-- fragment — the two-frame delta cover is the named next frontier, not a hidden failure mode.
#guard scalarRE (.sym (.atom (.simple (.monotonic "amount")))) = false
#guard scalarRE (.sym (.atom (.simple (.fieldDelta "amount" 5)))) = false
#guard scalarRE (.sym (.atom (.simple (.deltaBounded "amount" 3)))) = false
-- ...as are mixed scalar+pin guards (the product-of-covers constructor, priced in the header):
#guard scalarRE (.sym (.and (.atom (.simple (.fieldLe "amount" 100))) (.symEq "role" 3))) = false

-- THE END-TO-END DECISIONS, kernel-fired through `decide`:
-- the spend cap is NONEMPTY (a cell representative under the cap is found);
#guard @decide _ (predRE_emptiness_decidable_scalar 1024 (R := amountLe100) rfl)
-- contradictory bounds are EMPTY at ALL lengths (`n`-free: the saturated fixpoint proves no word
-- of ANY length threads `≤ 100` and `≥ 200` through one field);
#guard !(@decide _ (predRE_emptiness_decidable_scalar 1024 (R := amountContraRE) rfl))
-- the violation guard is NONEMPTY (the representative above the cap);
#guard @decide _ (predRE_emptiness_decidable_scalar 1024 (R := overCapRE) rfl)
-- the two-field guard is NONEMPTY through the per-field PRODUCT cover;
#guard @decide _ (predRE_emptiness_decidable_scalar 1024 (R := feeGuardRE) rfl)
-- EQUIVALENT: the cap and the cap-with-subsumed-point (the refactored-bound question);
#guard @decide _ (predRE_equivalence_decidable_scalar 1024
        (R := amountLe100) (S := amountLeOr50RE) rfl rfl)
-- NOT equivalent: the disjoined point OUTSIDE the cap genuinely widens the language;
#guard !(@decide _ (predRE_equivalence_decidable_scalar 1024
        (R := amountLe100) (S := amountLeOr150RE) rfl rfl))
-- EQUIVALENT: the two-sided band IS the conjunction of its one-sided bounds;
#guard @decide _ (predRE_equivalence_decidable_scalar 1024
        (R := bandRE) (S := bandConjRE) rfl rfl)
-- EQUIVALENT: the scalar enum IS its equality disjunction.
#guard @decide _ (predRE_equivalence_decidable_scalar 1024
        (R := stateEnumRE) (S := stateDisjRE) rfl rfl)

/-- The spend cap accepts some word — concluded through the running threshold-cell decision. -/
theorem amountLe_nonempty : ∃ w, derives w amountLe100 = true :=
  @of_decide_eq_true _ (predRE_emptiness_decidable_scalar 1024 (R := amountLe100) rfl) (by rfl)

/-- Contradictory bounds accept NO word of ANY length — the `n`-free negative verdict on the
scalar class (the whole point: not "none found up to n", but emptiness over the infinite
alphabet at every length). -/
theorem amountContra_empty : ¬ ∃ w, derives w amountContraRE = true :=
  @of_decide_eq_false _ (predRE_emptiness_decidable_scalar 1024 (R := amountContraRE) rfl) (by rfl)

/-- The over-cap violation guard is satisfiable (the negation atom has a witness cell). -/
theorem overCap_nonempty : ∃ w, derives w overCapRE = true :=
  @of_decide_eq_true _ (predRE_emptiness_decidable_scalar 1024 (R := overCapRE) rfl) (by rfl)

/-- The two-field policy guard accepts some word — through the per-field product cover. -/
theorem feeGuard_nonempty : ∃ w, derives w feeGuardRE = true :=
  @of_decide_eq_true _ (predRE_emptiness_decidable_scalar 1024 (R := feeGuardRE) rfl) (by rfl)

/-- `amount ≤ 100` ≡ `amount ≤ 100 ∨ amount = 50`: the range subsumes the interior point —
the refactored-bound identification, decided for ALL words. -/
theorem amountLe_equiv_or50 : ∀ w, derives w amountLe100 = derives w amountLeOr50RE :=
  @of_decide_eq_true _ (predRE_equivalence_decidable_scalar 1024
    (R := amountLe100) (S := amountLeOr50RE) rfl rfl) (by rfl)

/-- ...and the separation: disjoining a point OUTSIDE the cap genuinely changes the language. -/
theorem amountLe_not_equiv_or150 :
    ¬ ∀ w, derives w amountLe100 = derives w amountLeOr150RE :=
  @of_decide_eq_false _ (predRE_equivalence_decidable_scalar 1024
    (R := amountLe100) (S := amountLeOr150RE) rfl rfl) (by rfl)

/-- The two-sided band ≡ the conjunction of its one-sided bounds, decided. -/
theorem band_equiv_conj : ∀ w, derives w bandRE = derives w bandConjRE :=
  @of_decide_eq_true _ (predRE_equivalence_decidable_scalar 1024
    (R := bandRE) (S := bandConjRE) rfl rfl) (by rfl)

/-- The scalar enum ≡ its equality disjunction, decided. -/
theorem stateEnum_equiv_disj : ∀ w, derives w stateEnumRE = derives w stateDisjRE :=
  @of_decide_eq_true _ (predRE_equivalence_decidable_scalar 1024
    (R := stateEnumRE) (S := stateDisjRE) rfl rfl) (by rfl)

end Guards

/-! ## Axiom hygiene — the scalar cover is kernel-clean. -/

#assert_all_clean [
  intervalAtoms?_reads, constraintIntervalAtoms?_reads, predIntervalAtoms?_reads,
  profileEq_refl, profileEq_probe, exists_cellRep, findRep_mem, findRep_profileEq,
  maxBelow_none, maxBelow_some, minAbove_none, minAbove_some,
  scalarField_ofChoices, scalar_ofChoices, restrictScalarFrame_scalar,
  scalarProbe_restrict, restrictScalarFrame_mem_scalarCands, coverOfScalars,
  scalarLeaves?_spec, scalarLeaves?_isSome,
  predBEq_refl_of_intervalAtoms, rigidRE_of_scalarRE, scalarRE_symDiff,
  predRE_emptiness_decidable_scalar, predRE_equivalence_decidable_scalar,
  amountLe_nonempty, amountContra_empty, overCap_nonempty, feeGuard_nonempty,
  amountLe_equiv_or50, amountLe_not_equiv_or150, band_equiv_conj, stateEnum_equiv_disj
]

end Dregg2.Crypto.Deriv
