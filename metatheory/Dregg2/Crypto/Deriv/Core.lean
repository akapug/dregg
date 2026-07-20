/-
# Dregg2.Crypto.Deriv.Core — Stage 0 of the derivative-matching faithfulness close.

A Brzozowski/Antimirov SYMBOLIC DERIVATIVE matcher built directly over dregg's own `Pred`
algebra (`Exec/PredAlgebra.lean`), in dregg's own Lean. NO import of any external regex
artifact (the Zhuchko–Veanes–Ebner ERE≤ formalization at `~/dev/_research/extended-regexes`
and the ITP'25 `finiteness-derivatives` repo are read PURELY as proof blueprints — never a code
dependency). This is the design in `docs/deos/DERIVATIVE-MATCHING-DESIGN.md`, Stage 0.

`PredRE` is **ERE≤'s `RE α` MINUS the four lookarounds**, with dregg's `Pred` as the `sym` leaf.
Dropping lookarounds is a strict simplification: nullability is location-INDEPENDENT, `der` needs no
height-bounded subtype and no `existsMatch` mutual recursion, and the termination metric collapses
from a 4-tuple to nothing more than structural list recursion (for `derives`) / `star_metric` (for
`Matches`).

The alphabet remains `σ := Value`, so the derivative/finiteness tower does not fork, but it now
has TWO conservative symbol forms.  An ordinary record is still a single NEW frame and is evaluated
exactly as before with `old = ∅`.  `transitionSymbol old new` is a reserved record envelope for one
real transition; a `sym φ` leaf decodes it and evaluates `Pred.eval φ old new`.  Thus stateless
users retain their old language definitionally, while reactive leaves can use the same derivative
and finite-cover machinery over genuine `(old,new)` points.

`#guard`s pin non-vacuity in BOTH polarities (`der`/`derives`/`Matches` admit AND reject real words),
the dregg discipline mirroring `PredAlgebra.lean:489-508`.
-/
import Mathlib.Data.Prod.Lex
import Dregg2.Exec.PredAlgebra
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

/-! ## `PredRE` — regex over `Pred` (ERE≤'s `RE α` minus lookarounds). -/

/-- **`PredRE`** — a regular expression whose `sym` leaf carries a whole dregg `Pred`. This is
ERE≤'s `RE α` (`Definitions.lean:14`) with the four lookaround constructors dropped, and `Pred`
in place of the abstract atom `α`. `inter` is native intersection (the FilterTree product) and
`neg` is native complement (the missing deny-filter), both first-class derivative constructors. -/
inductive PredRE where
  /-- The empty word (matches `[]` only). -/
  | ε
  /-- One frame satisfying `φ` (ERE≤'s `Pred φ`). -/
  | sym   (φ : Pred)
  /-- Alternation `⋓`. -/
  | alt   (l r : PredRE)
  /-- Intersection `⋒` (native product — the FilterTree's `&`). -/
  | inter (l r : PredRE)
  /-- Concatenation `⬝`. -/
  | cat   (l r : PredRE)
  /-- Kleene star `*`. -/
  | star  (r : PredRE)
  /-- Complement `~` (native deny-filter). -/
  | neg   (r : PredRE)
  deriving Repr

namespace PredRE

/-- The bottom regex (matches nothing): `sym .ff`. The leaf predicate is dregg's `Pred.ff`. -/
abbrev bot : PredRE := .sym .ff

/-- The "any single frame" regex: `sym .tt`. -/
abbrev any : PredRE := .sym .tt

/-! ## The leaf decision — ordinary frames plus a reserved transition envelope. -/

/-- Reserved first field of a transition symbol.  It is deliberately not an authoring field: the
outer record is an alphabet envelope, while its tail is the actual NEW record. -/
def transitionTagField : FieldName := "\u0000dregg.transition"

/-- Reserved second field carrying the OLD record of a transition symbol. -/
def transitionOldField : FieldName := "\u0000dregg.old"

/-- **`transitionSymbol old new`** — encode a real record transition in the existing `Value`
alphabet.  For the record substrate (the supported policy carrier), the NEW record's fields remain
at the outer level after a two-field reserved prefix; this keeps the representation a point whose
coordinates are `(field × frame-slot)` without changing `PredRE`, `der`, or any fixpoint type.
Non-record NEW values have no policy-visible fields and are therefore represented by an empty NEW
record, consistently with every record predicate failing closed on them. -/
def transitionSymbol (old : Value) : Value → Value
  | .record fs => .record ((transitionTagField, .sym 0) :: (transitionOldField, old) :: fs)
  | _          => .record [(transitionTagField, .sym 0), (transitionOldField, old)]

/-- Decode the OLD frame.  Ordinary symbols take the legacy empty-old path; only the exact reserved
two-field prefix is recognized as a transition. -/
def symbolOld : Value → Value
  | .record ((tag, .sym 0) :: (oldKey, old) :: _fs) =>
      if tag == transitionTagField && oldKey == transitionOldField
      then old
      else .record []
  | _ => .record []

/-- Decode an alphabet symbol to the `(old,new)` pair seen by `Pred.eval`.  The NEW component is
definitionally the symbol itself; the reserved prefix is merely extra record data and therefore
invisible to every ordinary authored field.  This also keeps all established stateless covers
definitionally unchanged. -/
def symbolFrames (a : Value) : Value × Value := (symbolOld a, a)

@[simp] theorem symbolFrames_transitionSymbol (old : Value) (fs : List (FieldName × Value)) :
    symbolFrames (transitionSymbol old (.record fs)) =
      (old, transitionSymbol old (.record fs)) := by
  simp [transitionSymbol, symbolFrames, symbolOld, transitionTagField, transitionOldField]

@[simp] theorem symbolFrames_record_nil :
    symbolFrames (.record []) = (.record [], .record []) := rfl

@[simp] theorem symbolFrames_record_single (p : FieldName × Value) :
    symbolFrames (.record [p]) = (.record [], .record [p]) := by
  rcases p with ⟨k, v⟩
  cases v with
  | int i => rfl
  | dig d => rfl
  | sym s => cases s <;> rfl
  | record fs => rfl

/-- **`leaf φ a`** — evaluate an ordinary NEW frame or a decoded transition symbol. -/
@[simp] def leaf (φ : Pred) (a : Value) : Bool :=
  φ.eval (symbolOld a) a

/-! ## Nullability — does the regex match the empty word `[]`?

Location-INDEPENDENT (we have no lookarounds), so a plain `PredRE → Bool`. Direct re-instantiation
of ERE≤'s `null` (`Derives.lean:27`) minus the location argument and the four lookaround arms. -/

/-- **`null R`** — `true` iff `R` matches the empty word. -/
@[simp] def null : PredRE → Bool
  | .ε        => true
  | .sym _    => false
  | .alt l r  => null l || null r
  | .inter l r => null l && null r
  | .cat l r  => null l && null r
  | .star _   => true
  | .neg r    => !(null r)

/-! ## The symbol derivative — `der a R`.

Direct re-instantiation of ERE≤'s `der` (`Derives.lean:65`), with the `sym` leaf decided by `leaf`
instead of `denote`, and NO height-bounded subtype (no lookaround ⇒ no `existsMatch` mutual
recursion ⇒ no well-foundedness trick). Plain structural recursion on `PredRE`. -/

/-- **`der a R`** — the Brzozowski derivative of `R` w.r.t. reading the frame `a`. -/
@[simp] def der (a : Value) : PredRE → PredRE
  | .ε        => bot                                  -- ε has no derivative → ∅
  | .sym φ    => if leaf φ a then .ε else bot         -- the leaf: Pred.eval, old = ∅
  | .alt l r  => .alt (der a l) (der a r)
  | .inter l r => .inter (der a l) (der a r)          -- native intersection
  | .neg r    => .neg (der a r)                       -- native complement
  | .cat l r  => if null l
                 then .alt (.cat (der a l) r) (der a r)
                 else .cat (der a l) r
  | .star r   => .cat (der a r) (.star r)

/-- **`derives w R`** — iterate `der` along the word `w`, then check `null`. Terminates trivially
on the list (structural recursion, no metric). ERE≤'s `derives` (`Derives.lean:107`) over a span. -/
@[simp] def derives : List Value → PredRE → Bool
  | [],      R => null R
  | a :: as, R => derives as (der a R)

/-! ## The denotational matching relation — `Matches w R` (the spec side).

Re-instantiation of ERE≤'s `models`/`⊫` (`Models.lean`) for `PredRE` over `List Value`. Because we
have no lookarounds, this is the CLASSICAL regex denotation (simpler than `Models.lean`'s
span-indexed one): no left context is needed. `star` is the finite-iteration union, encoded (like
ERE≤) via bounded repetition `repeatCat`.

Termination uses the `star_metric : Nat ×ₗ Nat` (star-height, size) lexicographic metric — exactly
ERE≤'s `star_metric` (`Metrics.lean:46`), minus the lookaround arms. -/

/-- **`repeatCat R n`** — `R` concatenated with itself `n` times (`ε` for `0`). ERE≤'s
`repeat_cat` (`Definitions.lean:59`); used to encode `star` as `⋃ₙ Rⁿ`. -/
@[simp] def repeatCat (R : PredRE) : Nat → PredRE
  | 0          => .ε
  | Nat.succ n => .cat R (repeatCat R n)

/-- **`starHeight R`** — the nesting depth of `star`. The first component of `star_metric`. -/
@[simp] def starHeight : PredRE → Nat
  | .ε        => 0
  | .sym _    => 0
  | .alt l r  => max (starHeight l) (starHeight r)
  | .inter l r => max (starHeight l) (starHeight r)
  | .cat l r  => max (starHeight l) (starHeight r)
  | .star r   => 1 + starHeight r
  | .neg r    => starHeight r

/-- **`size R`** — constructor count (the second component of `star_metric`). ERE≤'s `sizeOf_RE`. -/
@[simp] def size : PredRE → Nat
  | .ε        => 0
  | .sym _    => 0
  | .alt l r  => 1 + size l + size r
  | .inter l r => 1 + size l + size r
  | .cat l r  => 1 + size l + size r
  | .star r   => 1 + size r
  | .neg r    => 1 + size r

/-- **`starMetric R`** — `(starHeight, size)` lexicographic. The metric that makes `Matches`
well-founded: `star` strictly drops the height (so unfolding `star → cat (der) (star)` and the
`repeatCat` encoding both terminate), every other constructor strictly drops the size. ERE≤'s
`star_metric` (`Metrics.lean:46`), lookaround arms dropped. -/
@[simp] def starMetric (R : PredRE) : Nat ×ₗ Nat := toLex (starHeight R, size R)

instance : WellFoundedRelation (Nat ×ₗ Nat) where
  rel := (· < ·)
  wf  := WellFounded.prod_lex WellFoundedRelation.wf WellFoundedRelation.wf

/-! ### `starMetric` decrease lemmas (the metric arms of ERE≤'s `Metrics.lean`, lookaround-free).

Each is a strict `<` in the `Nat ×ₗ Nat` lex order, proven exactly as ERE≤ proves them (`Metrics.lean:
225-319`) for the seven constructors we keep. They are the `decreasing_by` obligations of `Matches`. -/

/-- The lex `<` on `Nat ×ₗ Nat`: a strict drop in the FIRST coordinate, OR equal first +
strict drop in the second. The two `Prod.Lex` constructors, packaged as the only shape we need. -/
private theorem lex_lt {a b c d : Nat} (h : a < c ∨ (a = c ∧ b < d)) :
    (toLex (a, b)) < (toLex (c, d)) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h
  · subst h1; exact Prod.Lex.right _ h2

theorem starMetric_alt_l : starMetric l < starMetric (.alt l r) := by
  refine lex_lt ?_; simp only [starHeight, size]; omega

theorem starMetric_alt_r : starMetric r < starMetric (.alt l r) := by
  refine lex_lt ?_; simp only [starHeight, size]; omega

theorem starMetric_inter_l : starMetric l < starMetric (.inter l r) := by
  refine lex_lt ?_; simp only [starHeight, size]; omega

theorem starMetric_inter_r : starMetric r < starMetric (.inter l r) := by
  refine lex_lt ?_; simp only [starHeight, size]; omega

theorem starMetric_cat_l : starMetric l < starMetric (.cat l r) := by
  refine lex_lt ?_; simp only [starHeight, size]; omega

theorem starMetric_cat_r : starMetric r < starMetric (.cat l r) := by
  refine lex_lt ?_; simp only [starHeight, size]; omega

theorem starMetric_neg : starMetric r < starMetric (.neg r) := by
  refine lex_lt (Or.inr ⟨rfl, ?_⟩); simp only [size]; omega

theorem starMetric_star : starMetric r < starMetric (.star r) := by
  refine lex_lt (Or.inl ?_); simp only [starHeight]; omega

/-- `repeatCat R m`'s star-height never exceeds `R`'s — so `repeatCat R m` is strictly below
`star R` in the metric (the height drops by one). ERE≤'s `star_metric_repeat_first`. -/
theorem starHeight_repeatCat (R : PredRE) (m : Nat) : starHeight (repeatCat R m) ≤ starHeight R := by
  induction m with
  | zero => simp only [repeatCat, starHeight]; omega
  | succ n ih => simp only [repeatCat, starHeight]; omega

theorem starMetric_repeatCat : starMetric (repeatCat R m) < starMetric (.star R) := by
  refine lex_lt (Or.inl ?_); simp only [starHeight]
  have := starHeight_repeatCat R m; omega

/-! ## `Matches w R` — the classical denotational matching relation (the spec). -/

/-- **`Matches w R`** — `Prop`-valued: does word `w` match `R`? The classical regex language
denotation over `List Value`, re-instantiated from ERE≤'s `models` (`Models.lean:17`) with the
span machinery and lookarounds removed:

* `ε` matches `[]`;
* `sym φ` matches the singleton `[a]` with `leaf φ a`;
* `cat l r` splits `w = w₁ ++ w₂`;
* `alt`/`inter`/`neg` are language ∪/∩/complement;
* `star r` is `∃ m, Matches w (repeatCat r m)` (the finite-iteration union).

Termination by `starMetric` (ERE≤'s `star_metric`). -/
def Matches : List Value → PredRE → Prop
  | w, .ε        => w = []
  | w, .sym φ    => ∃ a, w = [a] ∧ leaf φ a = true
  | w, .alt l r  =>
      have : starMetric l < starMetric (.alt l r) := starMetric_alt_l (l := l) (r := r)
      have : starMetric r < starMetric (.alt l r) := starMetric_alt_r (l := l) (r := r)
      Matches w l ∨ Matches w r
  | w, .inter l r =>
      have : starMetric l < starMetric (.inter l r) := starMetric_inter_l (l := l) (r := r)
      have : starMetric r < starMetric (.inter l r) := starMetric_inter_r (l := l) (r := r)
      Matches w l ∧ Matches w r
  | w, .cat l r  =>
      have : starMetric l < starMetric (.cat l r) := starMetric_cat_l (l := l) (r := r)
      have : starMetric r < starMetric (.cat l r) := starMetric_cat_r (l := l) (r := r)
      ∃ w₁ w₂, w₁ ++ w₂ = w ∧ Matches w₁ l ∧ Matches w₂ r
  | w, .neg r    =>
      have : starMetric r < starMetric (.neg r) := starMetric_neg (r := r)
      ¬ Matches w r
  | w, .star r   =>
      ∃ m,
        have : starMetric (repeatCat r m) < starMetric (.star r) := starMetric_repeatCat (R := r) (m := m)
        Matches w (repeatCat r m)
termination_by _ R => starMetric R
decreasing_by all_goals assumption

/-! ## Non-vacuity `#guard`s — `der`/`derives` admit AND reject real words, both polarities.

The dregg discipline (mirroring `PredAlgebra.lean:489-508`): every load-bearing decision is pinned
true AND false on concrete witnesses so it cannot be vacuously satisfied. Here the witnesses are
real `Value` frames and real `Pred` leaves. -/

section Guards

/-- A frame whose field `"k"` is the symbol `7`. -/
private def frameK7 : Value := .record [("k", .sym 7)]
/-- A frame whose field `"k"` is the symbol `9`. -/
private def frameK9 : Value := .record [("k", .sym 9)]

/-- The leaf predicate "`k` is the symbol `7`". -/
private def isK7 : Pred := .symEq "k" 7

-- The leaf admits the matching frame and rejects the other (both polarities).
#guard PredRE.leaf isK7 frameK7 = true
#guard PredRE.leaf isK7 frameK9 = false

-- `sym isK7` matches the singleton `[k7]` and nothing else.
#guard PredRE.derives [frameK7] (.sym isK7) = true          -- admits
#guard PredRE.derives [frameK9] (.sym isK7) = false         -- rejects (wrong frame)
#guard PredRE.derives [] (.sym isK7) = false                -- rejects (empty word ≠ singleton)
#guard PredRE.derives [frameK7, frameK7] (.sym isK7) = false -- rejects (too long)

-- `ε` matches exactly the empty word.
#guard PredRE.derives [] (PredRE.ε) = true
#guard PredRE.derives [frameK7] (PredRE.ε) = false

-- Concatenation: `sym isK7 ⬝ sym isK7` matches exactly `[k7, k7]`.
#guard PredRE.derives [frameK7, frameK7] (.cat (.sym isK7) (.sym isK7)) = true
#guard PredRE.derives [frameK7] (.cat (.sym isK7) (.sym isK7)) = false
#guard PredRE.derives [frameK7, frameK9] (.cat (.sym isK7) (.sym isK7)) = false

-- Star: `(sym isK7)*` matches any run of k7-frames, including the empty word.
#guard PredRE.derives [] (.star (.sym isK7)) = true
#guard PredRE.derives [frameK7, frameK7, frameK7] (.star (.sym isK7)) = true
#guard PredRE.derives [frameK7, frameK9] (.star (.sym isK7)) = false

-- Alternation: `sym isK7 ⋓ ε` matches `[]` and `[k7]` but not `[k9]`.
#guard PredRE.derives [] (.alt (.sym isK7) PredRE.ε) = true
#guard PredRE.derives [frameK7] (.alt (.sym isK7) PredRE.ε) = true
#guard PredRE.derives [frameK9] (.alt (.sym isK7) PredRE.ε) = false

-- Intersection: `(sym tt) ⋒ (sym isK7)` = matches singleton iff it's k7 (the FilterTree product).
#guard PredRE.derives [frameK7] (.inter PredRE.any (.sym isK7)) = true
#guard PredRE.derives [frameK9] (.inter PredRE.any (.sym isK7)) = false

-- Complement (the NEW deny-filter): `~ (sym isK7)` matches everything that is NOT a single k7 —
-- including the empty word and a k9 singleton, but NOT a k7 singleton.
#guard PredRE.derives [frameK7] (.neg (.sym isK7)) = false   -- the one thing it denies
#guard PredRE.derives [frameK9] (.neg (.sym isK7)) = true    -- a different frame: admitted
#guard PredRE.derives [] (.neg (.sym isK7)) = true           -- empty word: admitted (≠ singleton)

-- Deny-namespace pattern: `any ⋒ ~(sym isK7)` = "one frame, but not a k7" — the capability-secure
-- deny-filter that was inexpressible in the FilterTree (`compiler.rs` had no `Not`).
#guard PredRE.derives [frameK9] (.inter PredRE.any (.neg (.sym isK7))) = true
#guard PredRE.derives [frameK7] (.inter PredRE.any (.neg (.sym isK7))) = false

end Guards

end PredRE

/-! ## Axiom hygiene — the Stage 0 metric lemmas are kernel-clean. -/

#assert_all_clean [
  PredRE.symbolFrames_transitionSymbol,
  PredRE.starMetric_alt_l, PredRE.starMetric_alt_r,
  PredRE.starMetric_inter_l, PredRE.starMetric_inter_r,
  PredRE.starMetric_cat_l, PredRE.starMetric_cat_r,
  PredRE.starMetric_neg, PredRE.starMetric_star,
  PredRE.starHeight_repeatCat, PredRE.starMetric_repeatCat
]

end Dregg2.Crypto.Deriv
