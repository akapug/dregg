/-
# Dregg2.Crypto.Segmentation — the alphabet-generic word-combinatorics core of parse-uniqueness.

`HandlebarsUniqueness.brace_split_unique` (over the 2-symbol `Tok` alphabet, delimiter `Tok.brace`)
and `HandlebarsGuardedUniqueness.split_unique` (generic in `c : Value`) are, on a full-closure read,
TOKEN-IDENTICAL inductions over the first list: the delimiter sits at the first position absent from
both prefixes, so the prefix — and hence the whole decomposition — is forced. NOTHING in either proof
touches `Tok`, `Value`, holes, guards, or rendering; the content is pure `List α` combinatorics.

This module LANDS that content once, alphabet-generically, so both uniqueness lemmas are visibly the
SAME theorem at two different `α`. It is deliberately LOW-LEVEL and SELF-CONTAINED — it imports only
Mathlib list basics and `Dregg2.Tactics`, and depends on nothing under `Handlebars*`. That is the
point: the delimiter-refactor can later have the two Handlebars uniqueness files DEPEND ON this file
(replacing their hand-rolled inductions with `Segmentation.split_unique_generic`) without any import
cycle. This lane only lands the generic and records the exact instantiation each existing lemma is; it
does NOT edit either Handlebars file (that wiring is the deferred refactor).

## What is proved (no `sorry`; `#assert_axioms`-clean)

  * `Absent c w` — `c` does not occur in `w` (generic over `{α : Type*}`; the delimiter-role guard).
  * `split_unique_generic c` — THE CORE: `x ++ c :: s = y ++ c :: t` with `x`, `y` both `Absent c`
    forces `x = y ∧ s = t`. Generic in `α` and `c`; the two existing lemmas are its instances (§3).
  * `spine_segment_unique` — the alternating-join / spine form: a chain of holes separated by
    single-symbol delimiters, each non-final hole `Absent` its following delimiter, is uniquely
    segmentable — equal output forces equal per-hole data. This is the alphabet-generic core of both
    `HandlebarsUniqueness.delim_render_injective_holes` and
    `HandlebarsGuardedUniqueness.spine_render_injective_aux`.
  * `absence_is_load_bearing` — the `Absent` hypotheses are NOT decorative: the bare split premise
    `x ++ c :: s = y ++ c :: t` is satisfiable with `x ≠ y`, so `split_unique_generic` is non-vacuous
    (its conclusion genuinely needs the absence guards). Plus concrete `#guard`s.
-/
import Mathlib.Data.List.Basic
import Dregg2.Tactics

namespace Dregg2.Crypto.Segmentation

universe u

variable {α : Type u}

/-! ## §1 `Absent` — the generic delimiter-role guard.

`c` does not occur in `w`. This is EXACTLY the shape of `HandlebarsUniqueness.NoBrace` (at `c :=
Tok.brace`) and `HandlebarsGuardedUniqueness.Absent` (at `α := Value`): same recursion, one `≠`
conjunct per element. No `DecidableEq` is needed to STATE it; a decidability instance is provided (§1a)
for alphabets that have one, so concrete `#guard`s / `decide` go through. -/

/-- **`Absent c w`** — the symbol `c` does not occur in `w` (a `c`-free word). A hole whose data is
`Absent c` cannot emit the delimiter `c`, so a following `c` marks an unambiguous boundary. -/
def Absent (c : α) : List α → Prop
  | []       => True
  | a :: rest => a ≠ c ∧ Absent c rest

/-! ### §1a Decidability (for alphabets with `DecidableEq`; the generic lemma below needs none). -/

instance decAbsent [DecidableEq α] (c : α) : (w : List α) → Decidable (Absent c w)
  | []       => isTrue trivial
  | a :: rest =>
      have _ : Decidable (Absent c rest) := decAbsent c rest
      inferInstanceAs (Decidable (a ≠ c ∧ Absent c rest))

/-! ## §2 The core — a `c`-free prefix before the first `c` is UNIQUE.

Induction on the first list `x`. `c` cannot occur inside a `c`-free prefix, so it falls at the same
index in both decompositions; the prefix, and thus the whole split, is forced. This is character for
character the induction `HandlebarsUniqueness.brace_split_unique` and
`HandlebarsGuardedUniqueness.split_unique` each hand-roll — nothing about the alphabet is used. -/

/-- **`split_unique_generic c`** — if `x ++ c :: s = y ++ c :: t` with `x`, `y` both `Absent c`, then
`x = y` and `s = t`. Generic in the alphabet `α` and the delimiter `c`. The two existing uniqueness
lemmas are exactly this at `⟨α, c⟩ = ⟨Tok, Tok.brace⟩` and `⟨Value, c⟩` respectively (§3). -/
theorem split_unique_generic (c : α) :
    ∀ (x y s t : List α), Absent c x → Absent c y →
      x ++ c :: s = y ++ c :: t → x = y ∧ s = t
  | [], [], s, t, _, _, h => ⟨rfl, by simpa using h⟩
  | [], _ :: _, _, _, _, hy, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1.symm hy.1
  | _ :: _, [], _, _, hx, _, h => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.1 hx.1
  | a :: x', b :: y', s, t, hx, hy, h => by
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨hab, htail⟩ := h
      obtain ⟨hxy, hst⟩ := split_unique_generic c x' y' s t hx.2 hy.2 htail
      exact ⟨by rw [hab, hxy], hst⟩

/-- The statement SHAPE both existing lemmas inhabit — a named `Prop` so the instance identity (§3)
reads as one equation. `split_unique_generic` proves `SplitUniqueAt c` for every `α` and `c`. -/
def SplitUniqueAt (c : α) : Prop :=
  ∀ (x y s t : List α), Absent c x → Absent c y →
    x ++ c :: s = y ++ c :: t → x = y ∧ s = t

theorem split_unique_generic_packaged (c : α) : SplitUniqueAt c :=
  split_unique_generic c

/-! ## §3 THE TWO EXISTING LEMMAS ARE INSTANCES (doc-noted; the wiring is a deferred refactor).

This file imports NOTHING under `Handlebars*` (import-cycle-free, so the refactor can later make those
files depend on THIS one), so the identities below are recorded as prose rather than machine-checked
here. ⚠ HONEST MECHANISM (tested against the real oleans): the existing guards are only
**propositionally** equivalent to `Segmentation.Absent`, NOT defeq — `NoBrace w = Segmentation.Absent
Tok.brace w` FAILS by `rfl` (they are distinct equation-compiler fixpoints). So `brace_split_unique`
does NOT typecheck at `SplitUniqueAt Tok.brace`, and the refactor is NOT a drop-in one-liner: it needs
an inductive `NoBrace ↔ Absent` bridge (or replacing the guard `def`s in the Handlebars files with
`Segmentation.Absent`). What IS exact is the instantiation SHAPE — the same generic proof at two
alphabets:

  * `Dregg2.Crypto.HandlebarsUniqueness.brace_split_unique` is the α := `Tok`, c := `Tok.brace` case
    (its `NoBrace w` is propositionally, not definitionally, `Segmentation.Absent Tok.brace w`).
  * `Dregg2.Crypto.HandlebarsGuardedUniqueness.split_unique` is the α := `Value` case, ∀ c
    (its `Absent c w` is propositionally, not definitionally, `Segmentation.Absent c w`).

The deferred refactor points both files at `split_unique_generic` via that guard-equivalence bridge. Both
render-injectivity lemmas — `HandlebarsUniqueness.delim_render_injective_holes` (over `Tok`) and
`HandlebarsGuardedUniqueness.spine_render_injective_aux` (over `Value`) — are in turn instances of the
generic spine form `spine_segment_unique` (§4), at the same two alphabets. -/

/-! ## §4 The alternating-join / spine form — unique segmentation of a delimiter-joined word.

A `Spine` is a chain of holes separated by single-symbol delimiters,
`hole id₀ · c₀ · hole id₁ · c₁ · … · hole idₙ`, rendered under a hole-assignment `d : Nat → List α`.
When every non-final hole's data is `Absent` its following delimiter (`Segmented`), the join is
uniquely segmentable: equal output forces equal per-hole data. This mirrors, alphabet-generically,
`HandlebarsUniqueness.delim_render_injective_holes` and
`HandlebarsGuardedUniqueness.spine_render_injective_aux` (which carry a `PredRE` guard whose only used
consequence is exactly this `Absent`-the-delimiter fact). -/

/-- A separated-delimiter spine over hole-ids: holes joined by single-symbol delimiters. -/
inductive Spine (α : Type u) where
  /-- The final hole. -/
  | last (id : Nat)
  /-- Hole `id`, then a single-symbol delimiter `c`, then the rest of the spine. -/
  | cons (id : Nat) (c : α) (rest : Spine α)

/-- The hole-ids named by the spine, in order. -/
def spineHoles : Spine α → List Nat
  | .last id      => [id]
  | .cons id _ rest => id :: spineHoles rest

/-- The spine rendered under a hole-assignment: hole data joined by the delimiters. -/
def spineRender (d : Nat → List α) : Spine α → List α
  | .last id      => d id
  | .cons id c rest => d id ++ c :: spineRender d rest

/-- **`Segmented d s`** — every non-final hole's data is `Absent` the delimiter that follows it. Under
this the spine is uniquely segmentable (a hole cannot bleed into its trailing delimiter). -/
def Segmented (d : Nat → List α) : Spine α → Prop
  | .last _       => True
  | .cons id c rest => Absent c (d id) ∧ Segmented d rest

/-- **`spine_segment_unique`** — the alternating-join uniqueness: for a `Segmented` spine, equal render
under `d` and `d'` forces `d id = d' id` on every named hole. Proof: strip the first hole via
`split_unique_generic` (its data is `Absent` the first delimiter, so it ends exactly there), recurse on
the tail. This is the alphabet-generic core of both Handlebars render-injectivity lemmas. -/
theorem spine_segment_unique :
    ∀ (s : Spine α) (d d' : Nat → List α),
      Segmented d s → Segmented d' s →
      spineRender d s = spineRender d' s →
      ∀ id ∈ spineHoles s, d id = d' id
  | .last id0, d, d', _, _, heq => by
      intro id hmem
      simp only [spineHoles, List.mem_singleton] at hmem
      subst hmem
      simpa only [spineRender] using heq
  | .cons id0 c0 rest, d, d', hseg, hseg', heq => by
      simp only [spineRender] at heq
      obtain ⟨habs0, hseg_rest⟩ := hseg
      obtain ⟨habs0', hseg_rest'⟩ := hseg'
      obtain ⟨hhead, htail⟩ :=
        split_unique_generic c0 (d id0) (d' id0)
          (spineRender d rest) (spineRender d' rest) habs0 habs0' heq
      have ih := spine_segment_unique rest d d' hseg_rest hseg_rest' htail
      intro id hmem
      simp only [spineHoles, List.mem_cons] at hmem
      rcases hmem with rfl | hin
      · exact hhead
      · exact ih id hin

/-! ## §5 Non-vacuity — the `Absent` guards are LOAD-BEARING, and concrete instances compute. -/

/-- **`absence_is_load_bearing`** — the bare split premise `x ++ c :: s = y ++ c :: t` is satisfiable
with `x ≠ y` (here `c = 0`: `[] ++ 0 :: [0] = [0,0] = [0] ++ 0 :: []`, yet `[] ≠ [0]`). So the
conclusion `x = y` of `split_unique_generic` genuinely REQUIRES the `Absent` hypotheses — the lemma is
not vacuous, and its guards do real work (`Absent 0 [0]` is false, which is exactly what forbids this
mis-split). -/
theorem absence_is_load_bearing :
    ∃ (x y s t : List Nat), x ++ (0 : Nat) :: s = y ++ (0 : Nat) :: t ∧ x ≠ y :=
  ⟨[], [0], [0], [], rfl, by decide⟩

/-- A positive instance: with both prefixes `Absent 0`, the split is forced. Demonstrates the lemma
firing on concrete data (delimiter `0`, brace-free prefixes `[1]`/`[1]`). -/
example :
    ([1] : List Nat) = [1] ∧ ([2] : List Nat) = [2] :=
  split_unique_generic 0 [1] [1] [2] [2] (by decide) (by decide) rfl

/-- Spine non-vacuity: `hole 0 · delim 9 · hole 1`, distinct assignments render distinctly. -/
def demoSpine : Spine Nat := .cons 0 9 (.last 1)

/-- The delimiter really separates: `[1] 9 [2]` vs `[1,1] 9 [2]` are different outputs, so
`spine_segment_unique` has content on this spine. -/
example : spineRender (fun i => if i = 0 then [1] else [2]) demoSpine
        ≠ spineRender (fun i => if i = 0 then [1,1] else [2]) demoSpine := by decide

-- The premise of `split_unique_generic` is inhabited (a delimiter-joined word decomposes):
#guard (([1] ++ (0 : Nat) :: [2]) == [1, 0, 2])
-- The demo spine renders as its hole data joined by the delimiter `9`:
#guard spineRender (fun i => if i = 0 then [1] else [2]) demoSpine == [1, 9, 2]
#guard spineRender (fun i => if i = 0 then [1, 1] else [2]) demoSpine == [1, 1, 9, 2]
-- `Absent` decides: brace-free prefix accepted, delimiter-bearing prefix rejected:
#guard decide (Absent (0 : Nat) [1, 2])
#guard ! decide (Absent (0 : Nat) [1, 0, 2])

/-! ## §6 Axiom hygiene. -/

#assert_axioms split_unique_generic
#assert_axioms split_unique_generic_packaged
#assert_axioms spine_segment_unique
#assert_axioms absence_is_load_bearing

end Dregg2.Crypto.Segmentation
