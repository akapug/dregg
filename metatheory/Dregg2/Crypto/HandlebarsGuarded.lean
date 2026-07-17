/-
# Dregg2.Crypto.HandlebarsGuarded — holes carry GUARDS, not a hardcoded brace-ban.

`Crypto/Handlebars.lean` proves generation soundness for handlebars templates, but it hardcodes an
ARBITRARY content restriction where a PARAMETER belongs: `Handlebars.safe` demands `NoDoubleBrace`
of EVERY hole (and `HandlebarsUniqueness` forbids `{` entirely). That "no `{{`" law is a pure
artifact of the impoverished 2-symbol alphabet `Tok = {brace, data}` — with only those two symbols
the only structural question a hole can answer is "does it contain a delimiter?", so the guard is
frozen for the whole family.

This module DEMOTES `NoDoubleBrace` to ONE guard among many. A hole carries a **guard** — a `PredRE`
from the VERIFIED derivative matcher (`Crypto/Deriv/Core.lean` + `Correctness.lean`), the template
author's CHOICE — and injection-freedom / well-formedness fall out of the guards' STRUCTURE, decided
by the matcher, not a global ban.

## The alphabet (assessed honestly)

`Tok`'s two symbols cannot express a real guard: a guard that distinguishes a delimiter from content
needs to name MORE than "brace vs everything". So the guard alphabet here is `Dregg2.Exec.Value` —
dregg's own universal value type, exactly the alphabet `PredRE`'s `sym φ` leaf reads (`Pred.eval φ ∅
a`). `Value` is unboundedly rich (arbitrary `Pred` leaves, boolean-closed regex via `inter`/`neg`),
so a guard can express any regular in-slot policy the matcher decides — of which "no `{{`" is a
single, recoverable instance (§Degenerate). The committed `Tok`-family embeds into `Value` via
`tokVal`, and `noDoubleBraceRE` bridges the two (`noDoubleBraceRE_iff`).

Because the alphabet is INFINITE, the induced object is NOT a finite mathlib `ContextFreeGrammar`
(that needs a rule per terminal symbol); each hole is a **regular leaf** — the DFA/regex side of the
`regex ⊗ CFG` substrate in `docs/DESIGN-composed-attestation-architecture.md` — whose language is
`{ w | Matches w guard }`, decided cheaply by `derives`. `guardedToGrammar` composes those leaves.

## What is proven (sorry-free)

* `guarded_render_mem_language` — GENERATION SOUNDNESS, now guard-parametric: if every hole's data
  satisfies ITS OWN guard (`guardedSafe`, via the verified matcher), the render lands in the induced
  language. The per-hole step is `correctness` for the guard.
* `noDoubleBraceRE_iff` — the DEGENERATE instance: `NoDoubleBrace` IS the particular guard
  `noDoubleBraceRE = neg (any* ⬝ {{ ⬝ any*)`. `derives (w.map tokVal) noDoubleBraceRE ↔
  Handlebars.NoDoubleBrace w`, so the committed family is exactly "every guard = noDoubleBraceRE"
  (`guardedSafe_noDoubleBrace_iff`). The generalization SUBSUMES the hardcoded version.
* `Demo` — TWO different guards on two holes; a hole holding `{{` renders into the language because
  its `star any` guard permits it (the brace-ban is GONE), while the strict guard rejects the same
  data. `#guard`s pin the split.
-/
import Dregg2.Crypto.Handlebars
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsGuarded

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE

/-! ## §1 The guarded template — segments carry `(id, guard)`. -/

/-- A guarded template **segment**: fixed literal `Value`s, or a hole carrying its own `guard`
(a `PredRE` over `Value`) — the template author's choice of in-slot policy. -/
inductive GSeg where
  | lit  (text : List Value)
  | hole (id : Nat) (guard : PredRE)
  deriving Repr

/-- **`GuardedTemplate`** — a list of guarded segments. -/
structure GuardedTemplate where
  segments : List GSeg

/-- Render one segment under a hole assignment. -/
def renderSeg (d : Nat → List Value) : GSeg → List Value
  | .lit text => text
  | .hole id _ => d id

/-- **`render T d`** — instantiate `T` with per-hole data and concatenate (the GENERATE direction). -/
def render (T : GuardedTemplate) (d : Nat → List Value) : List Value :=
  T.segments.flatMap (renderSeg d)

/-- **`guardedSafe T d`** — every hole's data satisfies ITS OWN guard, decided by the VERIFIED
matcher `derives`. This replaces `Handlebars.safe`'s hardcoded `NoDoubleBrace`. -/
def guardedSafe (T : GuardedTemplate) (d : Nat → List Value) : Prop :=
  ∀ id g, GSeg.hole id g ∈ T.segments → derives (d id) g = true

/-! ## §2 The induced grammar — a composition of regular leaves. -/

/-- A composition **leaf**: a fixed literal word, or a regular guard whose language is the guard's. -/
inductive Leaf where
  | fixed   (w : List Value)
  | guarded (g : PredRE)

/-- The leaf's language. The guarded leaf is exactly the guard's denotational language `Matches`,
which by `correctness` equals `{ w | derives w g = true }` — the verified regular leaf. -/
def Leaf.lang : Leaf → List Value → Prop
  | .fixed w,   u => u = w
  | .guarded g, u => Matches u g

/-- The induced language: the ordered concatenation of the leaves' languages. -/
def gLang : List Leaf → List Value → Prop
  | [],      u => u = []
  | l :: ls, u => ∃ a b, a ++ b = u ∧ l.lang a ∧ gLang ls b

/-- **`GuardedGrammar`** — the composed sequence of leaves. NOT a finite `ContextFreeGrammar`: the
`Value` alphabet is infinite, so each guard is a regular leaf (regex/DFA side of the `⊗` substrate),
not a set of per-terminal productions. -/
structure GuardedGrammar where
  leaves : List Leaf

/-- The grammar's language. -/
def GuardedGrammar.language (G : GuardedGrammar) : Set (List Value) :=
  { u | gLang G.leaves u }

/-- One segment's leaf: a literal becomes a fixed leaf, a hole becomes its guard's regular leaf. -/
def segLeaf : GSeg → Leaf
  | .lit text => .fixed text
  | .hole _ g => .guarded g

/-- **`guardedToGrammar T`** — the template as its induced composition grammar. -/
def guardedToGrammar (T : GuardedTemplate) : GuardedGrammar :=
  ⟨T.segments.map segLeaf⟩

/-! ## §3 THE KEY THEOREM — generation soundness, guard-parametric. -/

/-- The body lemma: a segment list whose holes are guard-satisfied renders into the composed
language. The hole step converts the matcher fact `derives (d id) g = true` into `Matches` via the
VERIFIED `correctness` — the per-hole derivation is now the guard's, not a hardcoded `NoDoubleBrace`. -/
theorem body_gLang (d : Nat → List Value) :
    ∀ segs : List GSeg,
      (∀ id g, GSeg.hole id g ∈ segs → derives (d id) g = true) →
      gLang (segs.map segLeaf) (segs.flatMap (renderSeg d)) := by
  intro segs
  induction segs with
  | nil => intro _; exact rfl
  | cons seg rest ih =>
      intro h
      simp only [List.map_cons, List.flatMap_cons]
      refine ⟨renderSeg d seg, rest.flatMap (renderSeg d), rfl, ?_, ?_⟩
      · cases seg with
        | lit text => exact rfl
        | hole id g =>
            exact (correctness (d id) g).mp (h id g (by simp))
      · exact ih (fun id g hg => h id g (List.mem_cons_of_mem _ hg))

/-- **`guarded_render_mem_language`** — GENERATION SOUNDNESS: rendering `T` with per-hole data that
each satisfies its OWN guard always produces a member of the induced language. The brace-ban is gone;
the guard is a PARAMETER, decided by the verified matcher. -/
theorem guarded_render_mem_language (T : GuardedTemplate) (d : Nat → List Value)
    (hsafe : guardedSafe T d) :
    render T d ∈ (guardedToGrammar T).language := by
  show gLang (T.segments.map segLeaf) (render T d)
  exact body_gLang d T.segments hsafe

/-! ## §4 The degenerate instance — `NoDoubleBrace` IS a particular guard.

`Tok` embeds into `Value` by tagging one field `"t"`; `braceP` fires on the brace tag. `noDoubleBraceRE`
is `neg (any* ⬝ brace ⬝ brace ⬝ any*)` — "no two adjacent braces". We prove it decides exactly
`Handlebars.NoDoubleBrace` on the embedded word. -/

/-- The embedded `brace` value (field `"t"` tagged `0`). -/
def braceVal : Value := .record [("t", .sym 0)]
/-- The embedded `data` value (field `"t"` tagged `1`). -/
def dataVal : Value := .record [("t", .sym 1)]
/-- The leaf predicate that fires exactly on `braceVal`. -/
def braceP : Pred := .symEq "t" 0
/-- `Tok` embeds into `Value`. -/
def tokVal : Handlebars.Tok → Value
  | .brace => braceVal
  | .data  => dataVal

-- `Pred.eval` reduces only via its equation lemmas (not kernel whnf — `decide`/`rfl` stall on the
-- `String` field-name compare), so these leaf facts are discharged by `simp only` over the readers.
theorem leaf_braceP_brace : leaf braceP braceVal = true := by
  simp [leaf, braceP, Pred.eval, Value.symField, Value.field, braceVal, List.find?]
theorem leaf_braceP_data  : leaf braceP dataVal = false := by
  simp [leaf, braceP, Pred.eval, Value.symField, Value.field, dataVal, List.find?]

/-- Within the embedded image, the brace-predicate fires only on the `brace` token. -/
theorem tok_of_leaf : ∀ {t : Handlebars.Tok}, leaf braceP (tokVal t) = true → t = Handlebars.Tok.brace
  | .brace, _ => rfl
  | .data,  h => by rw [show tokVal Handlebars.Tok.data = dataVal from rfl, leaf_braceP_data] at h
                    exact absurd h (by decide)

/-- `any* ⬝ brace ⬝ brace ⬝ any*` — the "contains adjacent braces" regex. -/
def BB : PredRE :=
  .cat (.star PredRE.any) (.cat (.sym braceP) (.cat (.sym braceP) (.star PredRE.any)))

/-- **`noDoubleBraceRE`** — the "no `{{`" guard = `neg (any* ⬝ {{ ⬝ any*)`. A SINGLE guard; the
committed `Handlebars` family is the instance where EVERY hole uses it. -/
def noDoubleBraceRE : PredRE := .neg BB

/-- `der a any = ε` (the top leaf fires on every frame). -/
theorem der_any (a : Value) : der a PredRE.any = PredRE.ε := rfl

/-- `star any` matches every word — the derivative peels a fired leaf each step. -/
theorem derives_star_any (w : List Value) : derives w (.star PredRE.any) = true := by
  induction w with
  | nil => rfl
  | cons a as ih =>
      have hstep : derives (a :: as) (.star PredRE.any)
                 = derives as (.cat PredRE.ε (.star PredRE.any)) := by
        show derives as (.cat (der a PredRE.any) (.star PredRE.any))
           = derives as (.cat PredRE.ε (.star PredRE.any))
        rw [der_any]
      rw [hstep]
      exact (derives_cat as PredRE.ε (.star PredRE.any)).mpr ⟨[], as, rfl, rfl, ih⟩

/-- `u` has two adjacent frames both firing `braceP`. -/
def hasAdjB (u : List Value) : Prop :=
  ∃ p b1 b2 s, u = p ++ b1 :: b2 :: s ∧ leaf braceP b1 = true ∧ leaf braceP b2 = true

/-- **`derives_BB`** — the matcher decides `BB` exactly as "contains adjacent braces". -/
theorem derives_BB (u : List Value) : derives u BB = true ↔ hasAdjB u := by
  unfold BB
  rw [derives_cat]
  constructor
  · rintro ⟨w1, w2, hsplit, _, h2⟩
    rw [derives_cat] at h2
    obtain ⟨x1, x2, hs2, hb1, hrest⟩ := h2
    rw [derives_sym] at hb1
    obtain ⟨b1, rfl, hlb1⟩ := hb1
    rw [derives_cat] at hrest
    obtain ⟨y1, y2, hs3, hb2, _⟩ := hrest
    rw [derives_sym] at hb2
    obtain ⟨b2, rfl, hlb2⟩ := hb2
    -- hs3 : [b2] ++ y2 = x2 ; hs2 : [b1] ++ x2 = w2 ; hsplit : w1 ++ w2 = u
    subst hs3; subst hs2
    exact ⟨w1, b1, b2, y2, hsplit.symm, hlb1, hlb2⟩
  · rintro ⟨p, b1, b2, s, hu, hlb1, hlb2⟩
    refine ⟨p, b1 :: b2 :: s, hu.symm, derives_star_any p, ?_⟩
    rw [derives_cat]
    refine ⟨[b1], b2 :: s, rfl, ?_, ?_⟩
    · rw [derives_sym]; exact ⟨b1, rfl, hlb1⟩
    · rw [derives_cat]
      refine ⟨[b2], s, rfl, ?_, derives_star_any s⟩
      rw [derives_sym]; exact ⟨b2, rfl, hlb2⟩

/-- The matcher decides `noDoubleBraceRE` as "no adjacent braces". -/
theorem noDoubleBraceRE_via_matcher (u : List Value) :
    derives u noDoubleBraceRE = true ↔ ¬ hasAdjB u := by
  simp only [noDoubleBraceRE, derives_neg]
  rw [← derives_BB]
  cases derives u BB <;> simp

/-! ### The Tok bridge — `hasAdjB (w.map tokVal) ↔ Handlebars.NoDoubleBrace w`. -/

/-- `Tok`-level adjacent braces. -/
def hasAdjBTok (w : List Handlebars.Tok) : Prop :=
  ∃ p s, w = p ++ Handlebars.Tok.brace :: Handlebars.Tok.brace :: s

/-- Decompose a mapped list at a `cons`. -/
theorem map_eq_cons {α β} {f : α → β} :
    ∀ {l : List α} {b : β} {B : List β}, l.map f = b :: B →
      ∃ c l', l = c :: l' ∧ f c = b ∧ l'.map f = B
  | [], _, _, h => by simp at h
  | c :: l', b, B, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      exact ⟨c, l', rfl, h.1, h.2⟩

/-- Decompose a mapped list at an `append`. -/
theorem map_eq_append {α β} {f : α → β} :
    ∀ {A : List β} {l : List α} {B : List β}, l.map f = A ++ B →
      ∃ la lb, l = la ++ lb ∧ la.map f = A ∧ lb.map f = B
  | [], l, B, h => ⟨[], l, rfl, rfl, by simpa using h⟩
  | a :: A', l, B, h => by
      obtain ⟨c, l', rfl, hfc, hrest⟩ := map_eq_cons (by simpa using h)
      obtain ⟨la, lb, rfl, hla, hlb⟩ := map_eq_append hrest
      exact ⟨c :: la, lb, rfl, by simp [List.map_cons, hfc, hla], hlb⟩

theorem hasAdjB_map (w : List Handlebars.Tok) :
    hasAdjB (w.map tokVal) ↔ hasAdjBTok w := by
  constructor
  · rintro ⟨p, b1, b2, s, hmap, h1, h2⟩
    obtain ⟨wp, w', rfl, _, hw'⟩ := map_eq_append hmap
    obtain ⟨t1, w'', rfl, ht1, hw''⟩ := map_eq_cons hw'
    obtain ⟨t2, w''', rfl, ht2, _⟩ := map_eq_cons hw''
    have e1 : t1 = Handlebars.Tok.brace := tok_of_leaf (by rw [ht1]; exact h1)
    have e2 : t2 = Handlebars.Tok.brace := tok_of_leaf (by rw [ht2]; exact h2)
    exact ⟨wp, w''', by rw [e1, e2]⟩
  · rintro ⟨p, s, rfl⟩
    exact ⟨p.map tokVal, tokVal .brace, tokVal .brace, s.map tokVal,
      by simp [List.map_append, List.map_cons], leaf_braceP_brace, leaf_braceP_brace⟩

/-- `hasAdjBTok (a :: b :: rest)` peels the head pair. -/
theorem hasAdjBTok_cons2 (a b : Handlebars.Tok) (rest : List Handlebars.Tok) :
    hasAdjBTok (a :: b :: rest) ↔
      (a = Handlebars.Tok.brace ∧ b = Handlebars.Tok.brace) ∨ hasAdjBTok (b :: rest) := by
  constructor
  · rintro ⟨p, s, hp⟩
    cases p with
    | nil =>
        simp only [List.nil_append, List.cons.injEq] at hp
        exact Or.inl ⟨hp.1, hp.2.1⟩
    | cons x p' =>
        rw [List.cons_append, List.cons.injEq] at hp
        obtain ⟨rfl, hp'⟩ := hp
        exact Or.inr ⟨p', s, hp'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨p, s, hp⟩)
    · exact ⟨[], rest, rfl⟩
    · exact ⟨a :: p, s, by rw [List.cons_append, ← hp]⟩

/-- **`noDoubleBrace_iff`** — `Handlebars.NoDoubleBrace` is exactly "no adjacent braces". -/
theorem noDoubleBrace_iff (w : List Handlebars.Tok) :
    Handlebars.NoDoubleBrace w ↔ ¬ hasAdjBTok w := by
  induction w with
  | nil =>
      simp only [Handlebars.NoDoubleBrace, true_iff]
      rintro ⟨p, s, h⟩
      have hl := congrArg List.length h
      simp only [List.length_cons, List.length_append, List.length_nil] at hl
      omega
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp only [Handlebars.NoDoubleBrace, true_iff]
          rintro ⟨p, s, h⟩
          have hl := congrArg List.length h
          simp only [List.length_cons, List.length_append, List.length_nil] at hl
          omega
      | cons b rest' =>
          show (¬ (a = Handlebars.Tok.brace ∧ b = Handlebars.Tok.brace)
                 ∧ Handlebars.NoDoubleBrace (b :: rest'))
             ↔ ¬ hasAdjBTok (a :: b :: rest')
          rw [ih, hasAdjBTok_cons2]
          tauto

/-- **`noDoubleBraceRE_iff`** — THE degenerate lemma: the matcher-decided guard `noDoubleBraceRE`
decides EXACTLY `Handlebars.NoDoubleBrace` on the embedded word. The hardcoded "no `{{`" is one
`PredRE` guard; the guarded framework SUBSUMES the committed family. -/
theorem noDoubleBraceRE_iff (w : List Handlebars.Tok) :
    derives (w.map tokVal) noDoubleBraceRE = true ↔ Handlebars.NoDoubleBrace w := by
  rw [noDoubleBraceRE_via_matcher, hasAdjB_map, noDoubleBrace_iff]

/-- **`guardedSafe_noDoubleBrace_iff`** — when every hole's guard is `noDoubleBraceRE`, `guardedSafe`
on the embedded data is exactly `Handlebars`' per-hole `NoDoubleBrace` safety. So the committed
`Handlebars` family IS the instance "every guard = noDoubleBraceRE". -/
theorem guardedSafe_noDoubleBrace_iff (T : GuardedTemplate)
    (hall : ∀ id g, GSeg.hole id g ∈ T.segments → g = noDoubleBraceRE)
    (dt : Nat → List Handlebars.Tok) :
    guardedSafe T (fun id => (dt id).map tokVal) ↔
      ∀ id g, GSeg.hole id g ∈ T.segments → Handlebars.NoDoubleBrace (dt id) := by
  constructor
  · intro h id g hmem
    have hd := h id g hmem
    rw [hall id g hmem] at hd
    exact (noDoubleBraceRE_iff (dt id)).mp hd
  · intro h id g hmem
    rw [hall id g hmem]
    exact (noDoubleBraceRE_iff (dt id)).mpr (h id g hmem)

/-! ## §5 Non-vacuity — TWO different guards; a hole may now hold `{{`. -/

namespace Demo

/-- Template `[data] {{hole0 : no `{{`}} [data] {{hole1 : anything}}`. Hole 1's guard is `star any`,
which permits a DOUBLE brace — impossible under the committed `Handlebars.safe`. -/
def demoT : GuardedTemplate :=
  ⟨[ GSeg.lit [dataVal],
     GSeg.hole 0 noDoubleBraceRE,
     GSeg.lit [dataVal],
     GSeg.hole 1 (.star PredRE.any) ]⟩

/-- Hole 0 gets a lone interior brace (obeys "no `{{`"); hole 1 gets a DOUBLE brace (its `star any`
guard permits it — the brace-ban is gone). -/
def demoD : Nat → List Value
  | 0 => [Handlebars.Tok.data, Handlebars.Tok.brace, Handlebars.Tok.data].map tokVal
  | 1 => [braceVal, braceVal]
  | _ => []

/-- Each hole's data satisfies its OWN guard, via the verified matcher. Hole 0's obligation goes
through the `noDoubleBraceRE_iff` bridge (`NoDoubleBrace` over the finite `Tok` is `decide`-able);
hole 1's `star any` accepts the double brace by `derives_star_any`. -/
theorem demoD_guardedSafe : guardedSafe demoT demoD := by
  intro id g hmem
  simp only [demoT, List.mem_cons, List.not_mem_nil, or_false, GSeg.hole.injEq,
             reduceCtorEq, false_or] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (noDoubleBraceRE_iff _).mpr (by decide)
  · exact derives_star_any _

/-- **Non-vacuity** — the concrete render (with a `{{`-bearing hole) lands in the induced language. -/
theorem demo_mem_language :
    render demoT demoD ∈ (guardedToGrammar demoT).language :=
  guarded_render_mem_language demoT demoD demoD_guardedSafe

-- The SAME data (`[{, {]`) is REJECTED by the strict guard yet ACCEPTED by the permissive one:
-- the brace-ban is now the template author's choice, not a global law.
#guard derives [braceVal, braceVal] (PredRE.star PredRE.any) = true   -- permissive: `{{` OK
#guard derives [braceVal, braceVal] noDoubleBraceRE = false           -- strict: rejects `{{`
#guard derives [dataVal, braceVal, dataVal] noDoubleBraceRE = true    -- strict: lone `{` fine

end Demo

/-! ## §6 Axiom hygiene. -/

#assert_axioms guarded_render_mem_language
#assert_axioms noDoubleBraceRE_iff
#assert_axioms guardedSafe_noDoubleBrace_iff
#assert_axioms Demo.demo_mem_language

/-! ## §7 RESIDUALS — named follow-ons (stated, not `sorry`-ed).

The guarded framework generalizes each member of the committed proof-producing-templater family; these
are the guard-parametric versions of the three landed theorems, named for a later slice:

  -- RESIDUAL (guarded_witness): the guard-parametric `HandlebarsWitness` — render EMITS its generation
  -- certificate carrying, per hole, the matcher run `derives (d id) (guard id)` (the leftmost pushdown
  -- witness of §3 packaged as data), so the certificate names WHICH guard admitted each slot.

  -- RESIDUAL (guarded_compose): the guard-parametric `HandlebarsCompose` — nesting a guarded template
  -- inside another's hole, the inner guard REFINING the outer (`inter`), proofs NESTing under
  -- composition. The `PredRE` `inter`/`neg` closure is exactly the algebra this needs.

  -- RESIDUAL (guarded_uniqueness): the guard-parametric `HandlebarsUniqueness` — for a DELIMITER-guarded
  -- class (guards whose languages are prefix-free / separated by a distinctive frame), the inverse
  -- `∈ language → ∃! per-hole data` holds. General guards are ambiguous (e.g. two `star any` holes
  -- abutting), so this needs the guard-structure side-condition, not a global ban — the honest home of
  -- the old `NoBrace`. `noDoubleBraceRE` is the coarsest such guard.

  -- RESIDUAL (junction breakout): as in `Handlebars` §9, per-hole guards are IN-SLOT; a guard ending in
  -- a frame that abuts a literal can still form a cross-junction structure. `∈ language` captures
  -- in-slot confinement (the structural injection question); a byte-level cross-junction guarantee needs
  -- junction-aware guards or literals that never abut a hole's boundary frame.
-/

end Dregg2.Crypto.HandlebarsGuarded
