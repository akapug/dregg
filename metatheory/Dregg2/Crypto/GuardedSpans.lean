/-
# Dregg2.Crypto.GuardedSpans — the SPAN FACTORIZATION the guarded-grammar circuit discharges.

`docs/DESIGN-guarded-grammar-circuit.md` splits a guarded-template attestation across the composed
substrate: the **skeleton** circuit walks the segment sequence (one step per segment), each **hole
span** is attested by a cheap DFA/regular leaf proof of its OWN guard (`derives span guard = true`,
the verified matcher), each **literal span** is pinned to the template's text, and the fold stitches
the spans back into one word by offset continuity. For that split to be sound AND complete, one
statement must hold at the semantics: *membership in the induced guarded language is EXACTLY
"the word decomposes into per-segment spans, each span leaf-attested".*

This file proves that statement — `mem_language_iff_spans` — for arbitrary guarded templates:

    u ∈ (guardedToGrammar T).language  ↔  ∃ spans, SpanOk T.segments spans ∧ spans.flatten = u

`SpanOk` is precisely the conjunction of per-span obligations the circuit stack discharges:
* a `lit` segment's span **equals the template text** (the skeleton circuit's literal pin);
* a `hole` segment's span **satisfies its own guard, decided by the verified matcher `derives`**
  (the DFA-leaf proof's statement; `correctness` converts to the denotational `Matches`);
* `spans.flatten = u` (the fold's span-continuity: adjacent spans abut, offsets cover the word).

So the composed proof's obligations, jointly, are equivalent to language membership — nothing is
lost by proving per-span (completeness, `gLang_spans`) and nothing extra is admitted
(soundness, `spans_compose`).

Non-vacuity: the `HandlebarsGuarded.Demo` template (two DIFFERENT guards, one hole holding a
double brace) is decomposed concretely; its render's membership is re-derived through the span
route, and a bad span list (hole data violating its guard) is shown `¬ SpanOk`.

Axiom hygiene: `#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. New file; imports
read-only.
-/
import Dregg2.Crypto.HandlebarsGuarded
import Dregg2.Tactics

namespace Dregg2.Crypto.GuardedSpans

open Dregg2.Exec
open Dregg2.Crypto
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.HandlebarsGuarded

/-! ## §1 `SpanOk` — the per-span obligations, one per segment. -/

/-- **`SpanOk segs spans`** — a span list matches a segment list pointwise: a literal segment's
span IS the literal text; a hole segment's span SATISFIES its own guard, decided by the verified
matcher. This is the conjunction of the per-leaf circuit obligations (literal pin / DFA-leaf
guard proof), stated at the semantics. -/
def SpanOk : List GSeg → List (List Value) → Prop
  | [], [] => True
  | .lit text :: segs, s :: spans => s = text ∧ SpanOk segs spans
  | .hole _ g :: segs, s :: spans => derives s g = true ∧ SpanOk segs spans
  | _, _ => False

/-! ## §2 Soundness — attested spans concatenate into the language. -/

/-- **`spans_compose`** — SOUNDNESS of the span split: if every span meets its segment's
obligation, the concatenation is in the induced language. This is what makes the composed proof
(skeleton + leaf proofs + fold continuity) imply membership. -/
theorem spans_compose :
    ∀ (segs : List GSeg) (spans : List (List Value)),
      SpanOk segs spans → gLang (segs.map segLeaf) spans.flatten := by
  intro segs
  induction segs with
  | nil =>
      intro spans h
      cases spans with
      | nil => rfl
      | cons s ss => exact absurd h (by simp [SpanOk])
  | cons seg rest ih =>
      intro spans h
      cases spans with
      | nil => cases seg <;> exact absurd h (by simp [SpanOk])
      | cons s ss =>
          cases seg with
          | lit text =>
              obtain ⟨rfl, hrest⟩ := h
              exact ⟨s, ss.flatten, (List.flatten_cons ..).symm, rfl, ih ss hrest⟩
          | hole id g =>
              obtain ⟨hd, hrest⟩ := h
              exact ⟨s, ss.flatten, (List.flatten_cons ..).symm,
                     (correctness s g).mp hd, ih ss hrest⟩

/-! ## §3 Completeness — every language member decomposes into attested spans. -/

/-- **`gLang_spans`** — COMPLETENESS of the span split: every word of the induced language HAS a
per-segment span decomposition meeting the obligations. So the circuit's span-shaped statement
loses no members: whatever is in the language can be attested span-wise. -/
theorem gLang_spans :
    ∀ (segs : List GSeg) (u : List Value),
      gLang (segs.map segLeaf) u → ∃ spans, SpanOk segs spans ∧ spans.flatten = u := by
  intro segs
  induction segs with
  | nil =>
      intro u h
      exact ⟨[], trivial, h.symm⟩
  | cons seg rest ih =>
      intro u h
      obtain ⟨a, b, hab, hleaf, hrest⟩ := h
      obtain ⟨spans, hok, hfl⟩ := ih b hrest
      cases seg with
      | lit text =>
          exact ⟨a :: spans, ⟨hleaf, hok⟩, by simp [hfl, hab]⟩
      | hole id g =>
          exact ⟨a :: spans, ⟨(correctness a g).mpr hleaf, hok⟩, by simp [hfl, hab]⟩

/-! ## §4 THE FACTORIZATION — membership ⇔ span decomposition. -/

/-- **`mem_language_iff_spans`** — THE statement the composed circuit discharges: membership in
the guarded template's induced language is EXACTLY the existence of a per-segment span
decomposition where each literal span is pinned and each hole span is guard-attested by the
verified matcher. The composed proof obligations (skeleton walk + literal pins + DFA-leaf guard
proofs + fold span-continuity) are therefore sound AND complete for language membership. -/
theorem mem_language_iff_spans (T : GuardedTemplate) (u : List Value) :
    u ∈ (guardedToGrammar T).language ↔
      ∃ spans, SpanOk T.segments spans ∧ spans.flatten = u := by
  constructor
  · exact gLang_spans T.segments u
  · rintro ⟨spans, hok, rfl⟩
    exact spans_compose T.segments spans hok

/-! ## §5 Non-vacuity — the Demo template decomposed, and a bad span list rejected. -/

/-- The Demo template's honest span list: literal, hole-0 data (lone interior brace), literal,
hole-1 data (a DOUBLE brace, admitted by its permissive `star any` guard). -/
def demoSpans : List (List Value) :=
  [[dataVal], Demo.demoD 0, [dataVal], Demo.demoD 1]

/-- Each demo span meets its segment's obligation — the hole-0 span through the strict
`noDoubleBraceRE` guard, the hole-1 span through the permissive `star any` guard. -/
theorem demoSpans_ok : SpanOk Demo.demoT.segments demoSpans :=
  ⟨rfl, (noDoubleBraceRE_iff _).mpr (by decide), rfl, derives_star_any _, trivial⟩

/-- The demo render's membership, RE-DERIVED through the span factorization (agreeing with
`Demo.demo_mem_language`, which reaches it through `guarded_render_mem_language`). -/
theorem demo_mem_via_spans :
    render Demo.demoT Demo.demoD ∈ (guardedToGrammar Demo.demoT).language :=
  (mem_language_iff_spans Demo.demoT _).mpr ⟨demoSpans, demoSpans_ok, rfl⟩

/-- A TAMPERED span list — hole 0's span holds a double brace, violating its strict guard — is
REJECTED by `SpanOk`: the obligation bites. -/
theorem demoSpans_bad_rejected :
    ¬ SpanOk Demo.demoT.segments [[dataVal], [braceVal, braceVal], [dataVal], Demo.demoD 1] := by
  rintro ⟨-, hbad, -⟩
  have : derives [braceVal, braceVal] noDoubleBraceRE = false := by decide
  rw [this] at hbad
  exact absurd hbad (by decide)

/-! ## §6 Axiom hygiene. -/

#assert_axioms spans_compose
#assert_axioms gLang_spans
#assert_axioms mem_language_iff_spans
#assert_axioms demo_mem_via_spans

end Dregg2.Crypto.GuardedSpans
