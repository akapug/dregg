/-
# Dregg2.Crypto.HandlebarsGuardedCompose — SCHEMA-IN-SCHEMA: composition IS guard refinement.

`HandlebarsGuarded.lean` demotes the hardcoded "no `{{`" ban to ONE guard among many: each hole
carries a `PredRE` guard (from the VERIFIED derivative matcher), and generation soundness
(`guarded_render_mem_language`) is now guard-parametric. Its §7 residual named the guard-parametric
`HandlebarsCompose`: nesting a guarded template inside another's hole, the inner language REFINING the
outer hole's guard via `PredRE.inter` — "the boolean-closed algebra is exactly what this needs." This
module DISCHARGES that residual.

## The key insight (HandlebarsGuarded §7, made precise)

A guarded template's language is REGULAR: it is a concatenation of literal-symbols and per-hole guard
leaves (that is exactly what `guardedToGrammar` composes). So it is itself expressible as a `PredRE` —
`templateRE T`. Nesting `T'` into hole `h` of `T` then means: the data landing in hole `h` must
satisfy BOTH the outer hole's guard `g_h` AND be a valid render of the inner template `T'`. The second
condition is "matches `templateRE T'`", so the composed hole's guard is precisely

    g_h  ⋒  templateRE T'      (`PredRE.inter g_h (templateRE T')`)

and composition = **boolean guard refinement**. The `inter`/`neg`-closed `PredRE` algebra
(`Deriv/Core.lean`) is the whole mechanism: `derives_inter` gives `Matches w (a ⋒ b) ↔ Matches w a ∧
Matches w b`, so the composed hole admits data iff it clears both guards.

## What is proven (sorry-free)

* `templateRE T` — a guarded template's language AS a `PredRE`: `segsRE` folds the segments into an
  ordered `cat`, a literal of length `n` becoming `anyN n` (any `n` frames — the SOUND, generate-side
  reading), a hole becoming its guard. `render_derives_templateRE` — the GENERATE direction: a
  guard-safe render always matches `templateRE` (the fact composition needs). The exact CONVERSE
  (literals pinned to their bytes) is named a residual (§Residuals).
* `guardedCompose T h T'` — replace hole `h`'s guard `g_h` with `g_h ⋒ templateRE T'`. Every other
  segment is untouched; `render` is unchanged (the guard, not the shape, moves).
* `guardedCompose_render_mem_language` — THE KEY THEOREM: rendering `T` with hole `h` filled by the
  inner render `render T' d'` lands in the COMPOSED template's induced language, PROVIDED the inner
  data is guard-safe for `T'` (`hInner`) and the OUTER guard admits the inner render (`hOuter`). The
  hole-`h` step is exactly `derives_inter`: the outer guard AND `render_derives_templateRE` both fire.
* `Demo` — an outer slot guarded against `{{` injection (`noDoubleBraceRE`) with an inner template
  nested in; the inner render (a lone interior `{`) clears BOTH the no-injection outer guard and the
  inner structural guard, so the composed hole's `inter` guard ACCEPTS it, while `#guard`s pin that the
  same `inter` guard REJECTS data violating EITHER guard (a `{{` breakout; a too-short word).
-/
import Dregg2.Crypto.HandlebarsGuarded
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsGuardedCompose

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.HandlebarsGuarded

/-! ## §1 `templateRE` — a guarded template's language AS a `PredRE`.

A guarded template's language is regular (a concatenation of literal-symbols and guard leaves), so it
is itself a `PredRE`. `anyN n` is "any `n` frames" (the literal-symbol run, SOUND for generation);
`segRE` maps a literal to `anyN` and a hole to its guard; `segsRE`/`templateRE` fold segments into an
ordered `cat`. -/

/-- **`anyN n`** — `PredRE.any` concatenated `n` times: matches any word of length exactly `n`. -/
def anyN : Nat → PredRE
  | 0     => .ε
  | n + 1 => .cat PredRE.any (anyN n)

/-- One segment's regular leaf: a literal of length `n` becomes `anyN n` (any `n` frames — the
generate-side reading), a hole becomes its guard. -/
def segRE : GSeg → PredRE
  | .lit text  => anyN text.length
  | .hole _ g  => g

/-- Fold a segment list into an ordered concatenation of segment-`PredRE`s. -/
def segsRE : List GSeg → PredRE
  | []          => .ε
  | seg :: rest => .cat (segRE seg) (segsRE rest)

/-- **`templateRE T`** — the whole guarded template's language as a single `PredRE`. -/
def templateRE (T : GuardedTemplate) : PredRE := segsRE T.segments

/-! ### The generate direction — a guard-safe render matches `templateRE`. -/

/-- A singleton always matches `PredRE.any` (`der a any = ε`, reusing `HandlebarsGuarded.der_any`). -/
theorem derives_singleton_any (a : Value) : derives [a] PredRE.any = true := by
  simp only [derives, der_any, null]

/-- **`derives_anyN`** — `anyN` of a word's length always accepts that word (any `n` frames). -/
theorem derives_anyN (w : List Value) : derives w (anyN w.length) = true := by
  induction w with
  | nil => rfl
  | cons a as ih =>
      show derives (a :: as) (.cat PredRE.any (anyN as.length)) = true
      apply (derives_cat _ _ _).mpr
      exact ⟨[a], as, rfl, derives_singleton_any a, ih⟩

/-- The body lemma: a guard-satisfied segment list renders into its `segsRE`. Each literal step is
`derives_anyN` (the render's bytes fill the any-run); each hole step is the hole's guard, supplied by
the safety hypothesis. Mirrors `HandlebarsGuarded.body_gLang`, at the `derives` level. -/
theorem segsRE_derives (d : Nat → List Value) :
    ∀ segs : List GSeg,
      (∀ id g, GSeg.hole id g ∈ segs → derives (d id) g = true) →
      derives (segs.flatMap (renderSeg d)) (segsRE segs) = true := by
  intro segs
  induction segs with
  | nil => intro _; rfl
  | cons seg rest ih =>
      intro h
      simp only [List.flatMap_cons, segsRE]
      apply (derives_cat _ _ _).mpr
      refine ⟨renderSeg d seg, rest.flatMap (renderSeg d), rfl, ?_, ?_⟩
      · cases seg with
        | lit text  => show derives text (anyN text.length) = true; exact derives_anyN text
        | hole id g => show derives (d id) g = true; exact h id g List.mem_cons_self
      · exact ih (fun id g hg => h id g (List.mem_cons_of_mem _ hg))

/-- **`render_derives_templateRE`** — THE GENERATE DIRECTION: a guard-safe render always matches the
template's `PredRE`. This is the fact the composition needs: the inner render clears `templateRE T'`. -/
theorem render_derives_templateRE (T' : GuardedTemplate) (d' : Nat → List Value)
    (hsafe : guardedSafe T' d') :
    derives (render T' d') (templateRE T') = true :=
  segsRE_derives d' T'.segments hsafe

/-! ## §2 `guardedCompose` — replace hole `h`'s guard with `g_h ⋒ templateRE T'`.

Composition = BOOLEAN GUARD REFINEMENT. Hole `h`'s guard `g_h` becomes `g_h ⋒ templateRE T'`, so the
slot admits exactly data that BOTH satisfies the outer guard AND is a valid inner render. Every other
segment (and the render shape) is untouched. -/

/-- Refine one segment: hole `h`'s guard `g` becomes `g ⋒ templateRE T'`; all else unchanged. -/
def composeSeg (h : Nat) (T' : GuardedTemplate) : GSeg → GSeg
  | .lit text  => .lit text
  | .hole id g => if id = h then .hole id (.inter g (templateRE T')) else .hole id g

/-- **`guardedCompose T h T'`** — `T` with hole `h`'s guard refined by `⋒ templateRE T'`. -/
def guardedCompose (T : GuardedTemplate) (h : Nat) (T' : GuardedTemplate) : GuardedTemplate :=
  ⟨T.segments.map (composeSeg h T')⟩

/-- Refining a guard never changes the rendered bytes (`renderSeg` reads id/text, not the guard). -/
theorem renderSeg_composeSeg (d : Nat → List Value) (h : Nat) (T' : GuardedTemplate) (seg : GSeg) :
    renderSeg d (composeSeg h T' seg) = renderSeg d seg := by
  cases seg with
  | lit text  => rfl
  | hole id g => simp only [composeSeg]; split <;> rfl

/-- **`render` is composition-invariant** — only the guard moves, not the shape. -/
theorem render_guardedCompose (T : GuardedTemplate) (h : Nat) (T' : GuardedTemplate)
    (d : Nat → List Value) :
    render (guardedCompose T h T') d = render T d := by
  show (T.segments.map (composeSeg h T')).flatMap (renderSeg d) = T.segments.flatMap (renderSeg d)
  induction T.segments with
  | nil => rfl
  | cons seg rest ih =>
      simp only [List.map_cons, List.flatMap_cons, renderSeg_composeSeg]
      rw [ih]

/-! ## §3 The fill assignment and the composed render. -/

/-- Fill assignment: hole `h` gets `inner`, every other hole `k` gets `d k`. -/
def fillH (d : Nat → List Value) (h : Nat) (inner : List Value) : Nat → List Value :=
  fun k => if k = h then inner else d k

/-- **`renderGuardedCompose T h T' d d'`** — render `T` with hole `h` filled by the inner render
`render T' d'`, and other holes by `d`. The NESTED render (over the composed template). -/
def renderGuardedCompose (T : GuardedTemplate) (h : Nat) (T' : GuardedTemplate)
    (d d' : Nat → List Value) : List Value :=
  render (guardedCompose T h T') (fillH d h (render T' d'))

/-- The nested render equals "render `T` with hole `h` filled by the inner render" — the guard-refined
composed template renders the same bytes as the outer template with the inner slot filled. -/
theorem renderGuardedCompose_eq (T : GuardedTemplate) (h : Nat) (T' : GuardedTemplate)
    (d d' : Nat → List Value) :
    renderGuardedCompose T h T' d d' = render T (fillH d h (render T' d')) :=
  render_guardedCompose T h T' (fillH d h (render T' d'))

/-! ## §4 THE KEY THEOREM — guarded compose soundness = the `inter` step.

The composed render is guard-safe for the composed template. The hole-`h` obligation is exactly
`derives_inter`: the refined guard `g_h ⋒ templateRE T'` accepts the inner render iff the outer guard
does (hypothesis `hOuter`) AND `templateRE T'` does (`render_derives_templateRE`, always). Every other
hole is untouched. Then `guarded_render_mem_language` lifts safety to language membership. -/

/-- **`guardedCompose_guardedSafe`** — under the fill assignment, the composed template is guard-safe.
The hole-`h` step is `derives_inter`: BOTH the outer guard (`hOuter`) and `templateRE T'`
(`render_derives_templateRE`) fire; surviving holes keep their data (`hRest`). -/
theorem guardedCompose_guardedSafe (T : GuardedTemplate) (h : Nat) (T' : GuardedTemplate)
    (d d' : Nat → List Value)
    (hInner : guardedSafe T' d')
    (hOuter : ∀ g, GSeg.hole h g ∈ T.segments → derives (render T' d') g = true)
    (hRest : ∀ id g, GSeg.hole id g ∈ T.segments → id ≠ h → derives (d id) g = true) :
    guardedSafe (guardedCompose T h T') (fillH d h (render T' d')) := by
  intro id2 g2 hmem
  have hmem2 : GSeg.hole id2 g2 ∈ T.segments.map (composeSeg h T') := hmem
  rw [List.mem_map] at hmem2
  obtain ⟨seg, hseg, heq⟩ := hmem2
  cases seg with
  | lit text =>
      simp only [composeSeg, reduceCtorEq] at heq
  | hole id g =>
      simp only [composeSeg] at heq
      by_cases hh : id = h
      · rw [if_pos hh, GSeg.hole.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hfill : fillH d h (render T' d') id = render T' d' := by simp [fillH, hh]
        rw [hfill, derives_inter, Bool.and_eq_true]
        refine ⟨hOuter g ?_, render_derives_templateRE T' d' hInner⟩
        exact hh ▸ hseg
      · rw [if_neg hh, GSeg.hole.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        have hfill : fillH d h (render T' d') id = d id := by simp [fillH, hh]
        rw [hfill]
        exact hRest id g hseg hh

/-- **`guardedCompose_render_mem_language`** — THE KEY THEOREM: rendering `T` with hole `h` filled by
the inner render `render T' d'` lands in the COMPOSED template's induced language. Provided the inner
data is guard-safe for `T'` and the outer hole-`h` guard admits the inner render, the composed render
is generation-sound for `guardedCompose T h T'`. Composition = guard refinement via `PredRE.inter`. -/
theorem guardedCompose_render_mem_language (T : GuardedTemplate) (h : Nat) (T' : GuardedTemplate)
    (d d' : Nat → List Value)
    (hInner : guardedSafe T' d')
    (hOuter : ∀ g, GSeg.hole h g ∈ T.segments → derives (render T' d') g = true)
    (hRest : ∀ id g, GSeg.hole id g ∈ T.segments → id ≠ h → derives (d id) g = true) :
    renderGuardedCompose T h T' d d' ∈ (guardedToGrammar (guardedCompose T h T')).language :=
  guarded_render_mem_language (guardedCompose T h T') (fillH d h (render T' d'))
    (guardedCompose_guardedSafe T h T' d d' hInner hOuter hRest)

/-! ## §5 Axiom hygiene. -/

#assert_axioms render_derives_templateRE
#assert_axioms guardedCompose_guardedSafe
#assert_axioms guardedCompose_render_mem_language

/-! ## §6 Non-vacuity — schema-in-schema, guarded against `{{` injection.

The outer slot is guarded by `noDoubleBraceRE` (no `{{`); an inner guarded template is nested in. The
inner render carries a LONE interior `{` — which clears BOTH the no-injection outer guard AND the
inner structural guard — so the composed hole's `inter` guard ACCEPTS it. The `#guard`s pin that the
SAME `inter` guard REJECTS data violating EITHER guard. -/

namespace Demo

/-- Inner template `"(" ++ {{1 : anything}} ++ ")"` — a bracketed slot whose guard is `star any`
(permits the lone interior `{`). Its `templateRE` structurally demands `≥ 2` frames. -/
def innerT : GuardedTemplate :=
  ⟨[ GSeg.lit [dataVal], GSeg.hole 1 (.star PredRE.any), GSeg.lit [dataVal] ]⟩

/-- Outer template `"[" ++ {{0 : no `{{`}} ++ "]"` — a bracketed slot guarded against `{{` injection.
Hole `0` is the composition point. -/
def outerT : GuardedTemplate :=
  ⟨[ GSeg.lit [dataVal], GSeg.hole 0 noDoubleBraceRE, GSeg.lit [dataVal] ]⟩

/-- Inner fill: hole `1` gets a single interior brace (SAFE — a lone `{`, not a `{{` breakout). -/
def dInner : Nat → List Value
  | 1 => [braceVal]
  | _ => []

/-- Outer non-composition data: none (hole `0` is the composition point). -/
def dOuter : Nat → List Value := fun _ => []

/-- The inner data is guard-safe for `innerT` (hole `1`'s `star any` accepts the lone brace). -/
theorem demo_hInner : guardedSafe innerT dInner := by
  intro id g hmem
  simp only [innerT, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
             GSeg.hole.injEq] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact derives_star_any (dInner 1)

/-- The OUTER guard admits the inner render: `render innerT dInner = [data,{,data]` has a lone brace,
so it clears `noDoubleBraceRE`. Routed through the `Tok` bridge (`NoDoubleBrace` over the finite `Tok`
alphabet is `decide`-able), not a raw `decide` on the `String`-field matcher. -/
theorem demo_hOuter : ∀ g, GSeg.hole 0 g ∈ outerT.segments → derives (render innerT dInner) g = true := by
  intro g hmem
  have hg : g = noDoubleBraceRE := by
    simp only [outerT, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
               GSeg.hole.injEq] at hmem
    tauto
  subst hg
  have hr : render innerT dInner = [dataVal, braceVal, dataVal] := rfl
  rw [hr]
  exact (noDoubleBraceRE_iff [Handlebars.Tok.data, Handlebars.Tok.brace, Handlebars.Tok.data]).mpr
    (by decide)

/-- The surviving outer holes are trivially safe (only hole `0` exists, and it is the compose point). -/
theorem demo_hRest : ∀ id g, GSeg.hole id g ∈ outerT.segments → id ≠ 0 → derives (dOuter id) g = true := by
  intro id g hmem hne
  simp only [outerT, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
             GSeg.hole.injEq] at hmem
  obtain ⟨rfl, _⟩ := hmem
  exact absurd rfl hne

/-- **Non-vacuity of the key theorem** — the concrete NESTED render (`"[" ++ "(x{y)" ++ "]"`) lands in
the COMPOSED template's language, carrying the schema-in-schema witness. The composed hole's guard is
`noDoubleBraceRE ⋒ templateRE innerT` — the boolean refinement of both. -/
theorem demo_composed_mem_language :
    renderGuardedCompose outerT 0 innerT dOuter dInner
      ∈ (guardedToGrammar (guardedCompose outerT 0 innerT)).language :=
  guardedCompose_render_mem_language outerT 0 innerT dOuter dInner
    demo_hInner demo_hOuter demo_hRest

-- The composed bytes: outer `[`, then inner `(`, `x`, `{`, `y`, `)`, then outer `]` — 5 frames.
theorem demo_composed_bytes :
    renderGuardedCompose outerT 0 innerT dOuter dInner
      = [dataVal, dataVal, braceVal, dataVal, dataVal] := rfl

-- The composed hole's `inter` guard ACCEPTS the inner render (clears BOTH guards)...
#guard derives [dataVal, braceVal, dataVal] (.inter noDoubleBraceRE (templateRE innerT)) = true
-- ...REJECTS a `{{` breakout (violates the OUTER guard, though it clears the inner structure)...
#guard derives [braceVal, braceVal] (.inter noDoubleBraceRE (templateRE innerT)) = false
-- ...and REJECTS a too-short word (violates the INNER guard `templateRE`, though `{` clears the outer).
#guard derives [braceVal] (.inter noDoubleBraceRE (templateRE innerT)) = false

#assert_axioms demo_composed_mem_language

end Demo

/-! ## §7 RESIDUALS — named follow-ons (stated, not `sorry`-ed).

  -- RESIDUAL (templateRE_matches, the exact CONVERSE): `render_derives_templateRE` is the GENERATE
  -- direction (a guard-safe render matches `templateRE`), which is what composition needs. The full
  -- iff `Matches w (templateRE T) ↔ w ∈ (guardedToGrammar T).language` requires literals to pin their
  -- EXACT bytes, not just their length — i.e. `segRE (.lit text)` recognizing exactly `text`, which
  -- needs a `PredRE` deciding value-equality frame-by-frame (a `sym` leaf per literal `Value`). With
  -- `anyN` the recognizer is a SOUND over-approximation (any `n` frames); the exact converse is the
  -- delimiter-guarded uniqueness slice, the honest home of `HandlebarsGuarded` §7's `guarded_uniqueness`.

  -- RESIDUAL (nested materialized witness): the guard-parametric twin of `HandlebarsWitness` — the
  -- composed render EMITS its generation certificate carrying, per hole, the matcher run for the
  -- REFINED guard (`derives (render T' d') (g_h ⋒ templateRE T')`), the inner certificate nesting
  -- under the `inter`. `HandlebarsCompose.lean` §9 records the CFG-side analogue (`nested_replay`).

  -- RESIDUAL (multi-hole / iterated composition): `guardedCompose` refines ONE hole `h`. Iterating it
  -- (`guardedCompose (guardedCompose T h₁ T₁) h₂ T₂`) composes a whole tree of schemas; the key
  -- theorem chains because each step only refines guards and preserves the render shape
  -- (`render_guardedCompose`). The tree-shaped soundness is a fold over these single-hole steps.
-/

end Dregg2.Crypto.HandlebarsGuardedCompose
