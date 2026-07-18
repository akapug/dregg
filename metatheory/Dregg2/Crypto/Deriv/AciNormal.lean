/-
# Dregg2.Crypto.Deriv.AciNormal — a COMPUTABLE, SOUND ACI normalizer for `≅` (ingredient (a),
# first slice).

The unbounded-emptiness rung of `SymbolicEmptiness.lean` needs a DECIDABLE `≅`. This module lands the
bounded first slice: a **computable normalizer** `normalize : PredRE → PredRE` together with its
**soundness** `normalize_sim : Sim (normalize R) R`. Completeness (`R ≅ S → normalize R = normalize S`)
is NOT proved here and is named precisely at the bottom.

## What `Sim` actually is (measured, and it changes the design)

`Sim` gives `alt` associativity (`assoc`), idempotence (`idem`) and right-deduplication
(`dedup : R₁ ⋓ (R₂ ⋓ R₁) ≅ R₁ ⋓ R₂`). Written multiplicatively those three are `x(yz) = (xy)z`,
`xx = x`, `xyx = xy` — the defining identities of a **left regular band**. Two consequences that
directly constrain any normalizer, and that the "sort the disjuncts into a canonical order" plan does
not survive:

1. **`alt` is NOT commutative under `≅`.** The free left regular band on two generators has
   `ab ≠ ba`. Restricted to pure-`alt` terms over distinct leaves, `Sim` is exactly the
   left-regular-band congruence, so `alt a b ≅ alt b a` is not derivable. A normalizer may therefore
   **not sort** the disjunct list: any reordering step would be an unprovable obligation. The
   canonical form of a left-regular-band word is instead the **order-preserving first-occurrence**
   sequence — read the spine left to right, keep the first occurrence of each disjunct, delete every
   later duplicate. That is what `normalize` computes, and it is why `normalize_sim` goes through.

   ⚑ This is now a THEOREM, not a model argument: `AciComplete.not_sim_alt_comm`
   (`¬ Sim (.alt s7 s9) (.alt s9 s7)` for concrete distinct leaves) proves the sorted normal form is
   UNREACHABLE against the ACTUAL `Sim`, derived from the key-invariance `AciComplete.sim_key` through
   fragment completeness against a decided disequality — not against a free-LRB model *of* `Sim`. So
   the design choice above is machine-checked necessary, not merely argued.

2. **`Sim` is not a full congruence.** There is no `starCong`, and `catCong` rewrites the LEFT factor
   only. So `normalize` CANNOT recurse under `star` (nor under the right factor of `cat`) and still
   be sound. This slice normalizes the TOP-LEVEL `alt` spine only; disjuncts are left untouched.

Both points are findings of this slice, not assumptions carried into it.

## Equality: computable, CONSERVATIVE, and stated plainly

`PredRE` has **no computable `DecidableEq`** — `Pred`'s `atom` carries a `StateConstraint`
(`ClearanceGraph` / `Label` / `BoundBranch` payloads), and `deriving instance DecidableEq for Pred`
FAILS (verified, not assumed). `Monotone.lean` supplies a `noncomputable`
`Classical.typeDecidableEq PredRE`; using that here would make `normalize` noncomputable and the word
"normalizer" a lie.

So this module carries its own **computable, one-sided** test `reEq : PredRE → PredRE → Bool` with
`reEq_sound : reEq R S = true → R = S`. It is deliberately **FAIL-CLOSED**: on leaf `Pred`s outside
the decidable fragment (`tt`, `ff`, `symEq`, `digEq`) it answers `false` rather than guessing. It may
therefore MISS a duplicate (under-dedup, a completeness loss) but can never claim one that is not
there (which would be an unsoundness — deleting a genuinely different disjunct). Soundness of
`normalize` depends only on the `→` direction, so `normalize_sim` holds for ALL of `PredRE`; it is
the dedup POWER that degrades outside the fragment. The fragment widens by extending `predBEq` alone.

`sorry`-free; `#assert_all_clean` at the bottom.
-/
import Dregg2.Crypto.Deriv.Similarity

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

namespace PredRE

/-! ## A computable, one-sided equality test.

`predBEq`/`reEq` never return `true` on distinct terms. They DO return `false` on some equal terms
(any `Pred` outside the `tt`/`ff`/`symEq`/`digEq` fragment) — the honest cost of `Pred` having no
derivable `DecidableEq`. -/

/-- **`predBEq`** — computable equality on the decidable fragment of `Pred`; `false` elsewhere. -/
def predBEq : Pred → Pred → Bool
  | .tt,        .tt        => true
  | .ff,        .ff        => true
  | .symEq f s, .symEq g t => f == g && s == t
  | .digEq f s, .digEq g t => f == g && s == t
  | _,          _          => false

/-- **`predBEq_sound`** — the ONE direction that matters: a `true` answer is a real equality. -/
theorem predBEq_sound : ∀ {p q : Pred}, predBEq p q = true → p = q := by
  intro p q h
  unfold predBEq at h
  split at h
  · rfl
  · rfl
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  · simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1, h.2]
  · exact absurd h (by simp)

/-- **`reEq`** — the structural lift of `predBEq` to `PredRE`. Computable; one-sided. -/
def reEq : PredRE → PredRE → Bool
  | .ε,         .ε         => true
  | .sym p,     .sym q     => predBEq p q
  | .alt a b,   .alt c d   => reEq a c && reEq b d
  | .inter a b, .inter c d => reEq a c && reEq b d
  | .cat a b,   .cat c d   => reEq a c && reEq b d
  | .star a,    .star b    => reEq a b
  | .neg a,     .neg b     => reEq a b
  | _,          _          => false

/-- **`reEq_sound`** — `reEq` never lies in the affirmative. This is what licenses deleting a
disjunct: `reEq x y = true` means `x` and `y` are the SAME regex, so `idem`/`dedup` apply. -/
theorem reEq_sound : ∀ {R S : PredRE}, reEq R S = true → R = S := by
  intro R
  induction R with
  | ε => intro S h; cases S <;> first | rfl | (simp [reEq] at h)
  | sym p =>
    intro S h; cases S <;> first
      | (simp only [reEq] at h; exact congrArg _ (predBEq_sound h))
      | (simp [reEq] at h)
  | alt a b iha ihb =>
    intro S h; cases S <;> first
      | (simp only [reEq, Bool.and_eq_true] at h; rw [iha h.1, ihb h.2])
      | (simp [reEq] at h)
  | inter a b iha ihb =>
    intro S h; cases S <;> first
      | (simp only [reEq, Bool.and_eq_true] at h; rw [iha h.1, ihb h.2])
      | (simp [reEq] at h)
  | cat a b iha ihb =>
    intro S h; cases S <;> first
      | (simp only [reEq, Bool.and_eq_true] at h; rw [iha h.1, ihb h.2])
      | (simp [reEq] at h)
  | star a iha =>
    intro S h; cases S <;> first
      | (simp only [reEq] at h; rw [iha h])
      | (simp [reEq] at h)
  | neg a iha =>
    intro S h; cases S <;> first
      | (simp only [reEq] at h; rw [iha h])
      | (simp [reEq] at h)

/-! ## The `alt` spine: flatten, fold, dedup. -/

/-- **`altList R`** — the disjunct list of `R`'s `alt` spine, fully flattened (both sides; `assoc`
makes the nesting irrelevant). Every non-`alt` constructor is a LEAF of the spine — in particular
`star`/`cat`/`inter`/`neg` bodies are not entered, matching `Sim`'s congruence coverage. -/
def altList : PredRE → List PredRE
  | .alt l r => altList l ++ altList r
  | R        => [R]

/-- The spine is never empty. -/
theorem altList_ne_nil (R : PredRE) : altList R ≠ [] := by
  induction R with
  | alt l r ihl _ => simp only [altList]; intro h; exact ihl (List.append_eq_nil_iff.mp h).1
  | _ => simp [altList]

/-- **`foldAlt h l`** — rebuild an `alt` spine by folding LEFT from the head `h`. Left folding is
what makes the deduplication proof go through: the accumulator carries the whole prefix, which is the
side the left-regular-band identity `x·u·x = x·u` needs. -/
def foldAlt : PredRE → List PredRE → PredRE
  | h, []      => h
  | h, y :: ys => foldAlt (.alt h y) ys

theorem foldAlt_append (xs : List PredRE) (h : PredRE) (ys : List PredRE) :
    foldAlt h (xs ++ ys) = foldAlt (foldAlt h xs) ys := by
  induction xs generalizing h with
  | nil => rfl
  | cons a as ih => simpa [foldAlt] using ih (.alt h a)

/-- `foldAlt` is a `Sim`-congruence in its head. -/
theorem foldAlt_cong {h h' : PredRE} (hs : Sim h h') : ∀ l, Sim (foldAlt h l) (foldAlt h' l) := by
  intro l; induction l generalizing h h' with
  | nil => exact hs
  | cons y ys ih => exact ih (Sim.altCong hs Sim.rfl)

/-- **`dropEq x l`** — delete every `reEq`-occurrence of `x` from `l` (order preserved). -/
def dropEq (x : PredRE) : List PredRE → List PredRE
  | []      => []
  | y :: ys => if reEq x y then dropEq x ys else y :: dropEq x ys

theorem dropEq_length_le (x : PredRE) (l : List PredRE) : (dropEq x l).length ≤ l.length := by
  induction l with
  | nil => simp [dropEq]
  | cons y ys ih =>
    rw [dropEq]
    split
    · exact Nat.le_succ_of_le ih
    · simpa using ih

/-- **`dedupFirst l`** — keep the FIRST occurrence of each disjunct, delete every later
`reEq`-equal one. Order is PRESERVED (see the module header: `Sim` has no commutativity to license
a sort). -/
def dedupFirst : List PredRE → List PredRE
  | []      => []
  | x :: xs => x :: dedupFirst (dropEq x xs)
termination_by l => l.length
decreasing_by exact Nat.lt_succ_of_le (dropEq_length_le _ _)

/-- **`normalize R`** — the ACI normal form of `R`'s top-level `alt` spine: flatten, drop later
duplicates, refold. The `[]` branch is unreachable (`altList_ne_nil`) and returns `R`, keeping the
function total without an arbitrary `bot`. -/
def normalize (R : PredRE) : PredRE :=
  match altList R with
  | []      => R
  | x :: xs => foldAlt x (dedupFirst (dropEq x xs))

/-! ## SOUNDNESS — `Sim (normalize R) R`.

The chain: refolding the flattened spine is `assoc` (`foldAlt_altList`), and dropping later
duplicates is the left-regular-band deletion argument (`foldAlt_dropEq`, engine `absorb_step`). -/

/-- Folding the flattened spine back up recovers the original, under a prefix `h`. -/
theorem foldAlt_altList (R : PredRE) : ∀ h, Sim (foldAlt h (altList R)) (.alt h R) := by
  induction R with
  | alt l r ihl ihr =>
    intro h
    rw [altList, foldAlt_append]
    exact Sim.trans (foldAlt_cong (ihl h) (altList r)) (Sim.trans (ihr (.alt h l)) Sim.assoc)
  | _ => intro h; exact Sim.rfl

/-- The head-free form: if the spine of `R` is `x :: xs`, folding it recovers `R`. -/
theorem foldAlt_altList_head (R : PredRE) :
    ∀ x xs, altList R = x :: xs → Sim (foldAlt x xs) R := by
  induction R with
  | alt l r ihl _ =>
    intro x xs heq
    rw [altList] at heq
    cases hl : altList l with
    | nil => exact absurd hl (altList_ne_nil l)
    | cons y ys =>
      rw [hl] at heq
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      rw [foldAlt_append]
      exact Sim.trans (foldAlt_cong (ihl y ys hl) (altList r)) (foldAlt_altList r l)
  | _ =>
    intro x xs heq
    simp only [altList, List.cons.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact Sim.rfl

/-- **`absorb_step`** — the left-regular-band engine. If the prefix `h` already ABSORBS `x`
(`h ⋓ x ≅ h`), then so does `h ⋓ a`, for ANY `a`. Multiplicatively: from `hx = h` derive
`hax = (hx)ax = h(xax) = h(xa) = (hx)a = ha`; the middle step is exactly `Sim.dedup`. -/
theorem absorb_step {h x : PredRE} (hx : Sim (.alt h x) h) (a : PredRE) :
    Sim (.alt (.alt h a) x) (.alt h a) :=
  Sim.trans (Sim.altCong (Sim.altCong (Sim.sym hx) Sim.rfl) Sim.rfl)
    (Sim.trans (Sim.altCong Sim.assoc Sim.rfl)
      (Sim.trans Sim.assoc
        (Sim.trans (Sim.altCong Sim.rfl Sim.assoc)
          (Sim.trans (Sim.altCong Sim.rfl Sim.dedup)
            (Sim.trans (Sim.sym Sim.assoc) (Sim.altCong hx Sim.rfl))))))

/-- **`foldAlt_dropEq`** — deleting every later occurrence of `x` from the spine tail is
`Sim`-neutral, provided the prefix `h` already absorbs `x`. Induction on the tail, with
`absorb_step` carrying the absorption hypothesis past each surviving disjunct. -/
theorem foldAlt_dropEq (x : PredRE) :
    ∀ (ys : List PredRE) (h : PredRE), Sim (.alt h x) h →
      Sim (foldAlt h (dropEq x ys)) (foldAlt h ys) := by
  intro ys
  induction ys with
  | nil => intro h _; exact Sim.rfl
  | cons a as ih =>
    intro h hx
    rw [dropEq]
    split
    · rename_i hxa
      have hax : x = a := reEq_sound hxa
      subst hax
      exact Sim.trans (ih h hx) (foldAlt_cong (Sim.sym hx) as)
    · exact ih (.alt h a) (absorb_step hx a)

/-- The `dedupFirst` pass is `Sim`-neutral (fuel-indexed form; the usable form is below). -/
theorem foldAlt_dedupFirst_aux : ∀ (n : Nat) (l : List PredRE), l.length ≤ n → ∀ h : PredRE,
    Sim (foldAlt h (dedupFirst l)) (foldAlt h l) := by
  intro n
  induction n with
  | zero =>
    intro l hl h
    cases l with
    | nil => rw [dedupFirst]; exact Sim.rfl
    | cons x xs => simp at hl
  | succ n ih =>
    intro l hl h
    cases l with
    | nil => rw [dedupFirst]; exact Sim.rfl
    | cons x xs =>
      rw [dedupFirst]
      show Sim (foldAlt (.alt h x) (dedupFirst (dropEq x xs))) (foldAlt (.alt h x) xs)
      refine Sim.trans (ih (dropEq x xs) ?_ (.alt h x)) (foldAlt_dropEq x xs (.alt h x) ?_)
      · exact Nat.le_trans (dropEq_length_le x xs) (by simpa using hl)
      · exact Sim.trans Sim.assoc (Sim.altCong Sim.rfl Sim.idem)

/-- **`foldAlt_dedupFirst`** — the whole `dedupFirst` pass is `Sim`-neutral. -/
theorem foldAlt_dedupFirst (l : List PredRE) (h : PredRE) :
    Sim (foldAlt h (dedupFirst l)) (foldAlt h l) :=
  foldAlt_dedupFirst_aux l.length l (Nat.le_refl _) h

/-- **`normalize_sim`** — THE DELIVERABLE: the normal form is similar to the original. This is what
makes `normalize` usable as a `≅`-decision substrate: any decision made on `normalize R` transports
back to `R` through every `≅`-invariant already proved (`sim_null`, `sim_der`, `sim_sound`). -/
theorem normalize_sim (R : PredRE) : Sim (normalize R) R := by
  unfold normalize
  split
  · exact Sim.rfl
  · rename_i x xs heq
    refine Sim.trans (foldAlt_dedupFirst (dropEq x xs) x) ?_
    refine Sim.trans (foldAlt_dropEq x xs x Sim.idem) ?_
    exact foldAlt_altList_head R x xs heq

/-- Language-soundness, transported: normalizing never changes what the matcher accepts. -/
theorem normalize_derives (R : PredRE) (w : List Value) : derives w (normalize R) = derives w R :=
  sim_derives_syntactic (normalize_sim R) w

/-! ## `#guard`s — `normalize` really collapses ACI redundancy, and really does not over-collapse. -/

section Guards

private def p7 : Pred := .symEq "k" 7
private def p9 : Pred := .symEq "k" 9
private def r7 : PredRE := .sym p7
private def r9 : PredRE := .sym p9
private def f7 : Value := .record [("k", .sym 7)]
private def f5 : Value := .record [("k", .sym 5)]

-- The flagship: `(r7 ⋓ r9) ⋓ r7` — an ACI-redundant, left-nested spine — collapses to `r7 ⋓ r9`.
#guard reEq (normalize (.alt (.alt r7 r9) r7)) (.alt r7 r9) = true
-- …and it genuinely CHANGED the term (the normalizer is not the identity here).
#guard reEq (normalize (.alt (.alt r7 r9) r7)) (.alt (.alt r7 r9) r7) = false

-- Pure idempotence: `r7 ⋓ r7 ↦ r7`.
#guard reEq (normalize (.alt r7 r7)) r7 = true

-- A duplicate PAST a survivor and WITH a tail after it — the `absorb_step` case, not just `dedup`:
-- `r7 ⋓ (r9 ⋓ (r7 ⋓ ε))` ↦ the left-refolded `(r7 ⋓ r9) ⋓ ε`.
#guard reEq (normalize (.alt r7 (.alt r9 (.alt r7 .ε)))) (.alt (.alt r7 r9) .ε) = true

-- ORDER IS PRESERVED (no sort — `Sim` has no commutativity): the two orders normalize DIFFERENTLY.
#guard reEq (normalize (.alt r7 r9)) (.alt r7 r9) = true
#guard reEq (normalize (.alt r9 r7)) (.alt r7 r9) = false

-- NOT over-collapsing: distinct disjuncts survive, and a non-`alt` term is untouched.
#guard reEq (normalize (.alt r7 r9)) r7 = false
#guard reEq (normalize (.star r7)) (.star r7) = true
#guard reEq (normalize (.cat r7 r9)) (.cat r7 r9) = true

-- The verdict is preserved on concrete words, in BOTH polarities (`normalize_derives`).
#guard derives [f7] (normalize (.alt (.alt r7 r9) r7)) = true
#guard derives [f7] (.alt (.alt r7 r9) r7) = true
#guard derives [f5] (normalize (.alt (.alt r7 r9) r7)) = false
#guard derives [f5] (.alt (.alt r7 r9) r7) = false

-- The FAIL-CLOSED edge, PINNED rather than hidden: an `atom` leaf is outside `predBEq`'s fragment,
-- so a duplicate of it is NOT detected. `normalize` stays SOUND; it just fails to dedup.
private def atomLeaf : PredRE := .sym (.atom (.fieldLeField "a" "b"))
#guard reEq atomLeaf atomLeaf = false
#guard reEq (normalize (.alt atomLeaf atomLeaf)) (.alt atomLeaf atomLeaf) = false

end Guards

end PredRE

/-! ## Axiom hygiene. -/

#assert_all_clean [
  PredRE.predBEq_sound, PredRE.reEq_sound,
  PredRE.altList_ne_nil, PredRE.dropEq_length_le,
  PredRE.foldAlt_append, PredRE.foldAlt_cong,
  PredRE.foldAlt_altList, PredRE.foldAlt_altList_head,
  PredRE.absorb_step, PredRE.foldAlt_dropEq, PredRE.foldAlt_dedupFirst,
  PredRE.normalize_sim, PredRE.normalize_derives
]

/-!
## THE RESIDUAL — completeness, stated precisely and NOT proved.

    `normalize_complete : ∀ R S, Sim R S → normalize R = normalize S`

This is the half that turns the normalizer into a DECISION procedure
(`decide (R ≅ S) := reEq (normalize R) (normalize S)`); soundness alone gives only the `←` direction
(`normalize R = normalize S → R ≅ S`, immediate from `normalize_sim` plus `sym`/`trans`). Completeness
is NOT proved here and nothing above approximates it. What it needs, exactly:

1. **An invariance argument over the `Sim` GENERATORS, then closure under `sym`/`trans`.** `Sim` is an
   inductively generated equivalence, so `Sim R S` offers no direct handle on spines; the route is to
   show `normalize` is unchanged by each of `assoc`, `dedup`, `idem` and each congruence, which
   exhibits `normalize` as a function on the quotient. For the pure-`alt` fragment this is the
   free-left-regular-band canonical-form theorem: `assoc` does not change `altList`, `idem` and
   `dedup` are absorbed by first-occurrence deletion. It is finite and self-contained.

2. **Congruence closure of the normal form, which the present `Sim` CANNOT supply.** `altCong` lets
   `Sim R S` hold because two DISJUNCTS are similar without being equal (e.g.
   `alt (star (alt a a)) b ≅ alt (star a) b`). A `normalize` that does not recurse into disjuncts is
   therefore not complete on full `PredRE`. But recursing is UNSOUND under the present `Sim`: there
   is no `starCong` and `catCong` covers the left factor only. So full completeness is blocked on a
   PRIOR change — either `Sim` gains `starCong` and a right `catCong` (an edit to `Similarity.lean`,
   which must keep its `#assert_not_depends_on` pins passing and must re-prove `sim_der`/`sim_sound`
   for the new constructors), or completeness is stated only for the pure-`alt` fragment.

3. **A decidable leaf equality.** `predBEq` is fail-closed outside `tt`/`ff`/`symEq`/`digEq`, so even
   on the pure-`alt` fragment completeness fails for `atom` leaves. Closing this needs a real
   `DecidableEq StateConstraint` (currently NOT derivable — `ClearanceGraph`/`Label`/`BoundBranch`
   carry no instance), which is mechanical but edits `Exec/Program.lean`.

**Is the chosen normal form reachable?** Yes — and that is the good news of this slice. Because the
form is the ORDER-PRESERVING first-occurrence sequence (the free-left-regular-band canonical form),
fragment completeness is a finite invariance theorem, not a permutation-combinatorics problem. A
canonical form obtained by SORTING would not have been reachable at all: it needs `alt`
commutativity, which `Sim` does not have and which is FALSE in the free left regular band on two
generators. The design's "months-scale `Permute`/`Pieces`" estimate is priced against the sorting
picture; this normal form does not need it.
-/

end Dregg2.Crypto.Deriv
