/-
# Dregg2.Crypto.Deriv.Similarity — Stage 3 foundation: the ACI similarity over `PredRE`,
# proven LANGUAGE-SOUND.

Brzozowski finiteness holds only UP TO SIMILARITY `≅` — the associativity / commutative-dedup /
idempotence (ACI) congruence on `alt`, which is what collapses the syntactically-infinite set of
derivatives to a finite quotient. The ITP'25 `finiteness-derivatives` proof (`Similarity.lean`)
defines exactly this `Sim` relation and quotients the state space by it.

This module ports `Sim` to `PredRE` AND proves the fact that licenses the quotient at all:
**similarity is LANGUAGE-SOUND** — `R ≅ S → (Matches w R ↔ Matches w S)` for every word `w`. Without
this, "finite up to `≅`" would be a quotient by a relation that does not respect the matched
language, and the finiteness would be vacuous/unsound (the `feedback-dont-launder-vacuity` discipline:
prove the quotient relation is the RIGHT one). With it, every `≅`-class is a genuine language class,
so a finite set of `≅`-classes IS a finite set of recognized languages.

This is the load-bearing SEMANTIC half of Stage 3. The remaining half — the COMBINATORIAL counting
(`pieces`/`neSubsets`/`toSum`: that `der a R` is `≅` a sum over a non-empty subset of the finite
`pieces R`) — is named as the precise wall in the module note at the bottom and in the report; it is
purely syntactic (no semantics) and is the ~2000-line `Permute`/`Pieces` development the design §3.3
rates months-scale.

It also carries the **DER-CONGRUENCE** `sim_der : R ≅ S → der a R ≅ der a S` (and its supporting
`sim_null : R ≅ S → null R = null S`, plus the word-iterated `sim_derList`). This is what makes `der`
WELL-DEFINED ON THE `≅`-QUOTIENT — the bounded ingredient (c) of `SymbolicEmptiness.lean`'s
unbounded-emptiness rung. It does NOT close that rung: the pigeonhole/counting step and a decidable
`≅` remain open there.

The der-congruence half is **SEMANTICS-FREE**: `sim_null`, `sim_der` and `sim_derList` are proved by
induction on the `Sim` derivation from the defining clauses of `null`/`der` alone, and `sim_null` is
placed BEFORE the language-soundness section precisely so that independence is enforced by
declaration order rather than merely asserted. Consequently `sim_derives_syntactic` is a genuinely
independent route to the verdict-invariance that `sim_derives` gets denotationally. `sim_derives`
itself is unchanged and still denotational — the two are separate routes, not one rewritten.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Correctness

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra

namespace PredRE

/-! ## The similarity relation `≅` — the ACI congruence on `alt` (+ structural congruences). -/

/-- **`Sim`** — similarity: associativity, right-deduplication and idempotence of `alt`, plus the
reflexive/symmetric/transitive closure and the structural congruences. EXACTLY the ITP'25
`Sim` (`Similarity.lean:21`), re-instantiated over `PredRE` (lookaround congruences dropped, `inter`
congruence kept since `PredRE` has native `inter`). -/
inductive Sim : PredRE → PredRE → Prop where
  /-- Associativity of `alt`. -/
  | assoc     : Sim (.alt (.alt R₁ R₂) R₃) (.alt R₁ (.alt R₂ R₃))
  /-- Right deduplication: `R₁ ⋓ R₂ ⋓ R₁ ≅ R₁ ⋓ R₂` (the `⋓` right-associated, matching ITP'25). -/
  | dedup     : Sim (.alt R₁ (.alt R₂ R₁)) (.alt R₁ R₂)
  /-- Idempotence: `R ⋓ R ≅ R`. -/
  | idem      : Sim (.alt R R) R
  /-- Reflexivity. -/
  | rfl       : Sim R R
  /-- Symmetry. -/
  | sym       : Sim R₁ R₂ → Sim R₂ R₁
  /-- Transitivity. -/
  | trans     : Sim R R₁ → Sim R₁ R₂ → Sim R R₂
  /-- Complement congruence. -/
  | negCong   : Sim R₁ R₂ → Sim (.neg R₁) (.neg R₂)
  /-- Alternation congruence. -/
  | altCong   : Sim R₁ R₂ → Sim S₁ S₂ → Sim (.alt R₁ S₁) (.alt R₂ S₂)
  /-- Intersection congruence. -/
  | interCong : Sim R₁ R₂ → Sim S₁ S₂ → Sim (.inter R₁ S₁) (.inter R₂ S₂)
  /-- Concatenation congruence (left only — the derivative only ever rewrites the left of a `cat`). -/
  | catCong   : Sim R₁ R₂ → Sim (.cat R₁ S) (.cat R₂ S)

@[inherit_doc] infix:37 " ≅ " => Sim

/-- **`sim_null`** — `≅`-invariance of nullability, PROVED SYNTACTICALLY: induction on the `Sim`
derivation, discharging each case with `null`'s own defining clauses and Boolean algebra. NO appeal
to `Matches` / `correctness` / `sim_sound` / `sim_derives` — this lemma does not touch the
denotational tower at all.

Why it goes through: `null` is a homomorphism from the syntax into `Bool` (`alt ↦ ||`, `inter ↦ &&`,
`cat ↦ &&`, `neg ↦ !`, `ε`/`star ↦ true`, `sym ↦ false`), and every `Sim` law is a law that `||`
satisfies in `Bool` — `assoc` is `Bool.or_assoc`, `idem` is `b || b = b`, `dedup` is
`a || (b || a) = a || b`. So each case closes by case-splitting the finitely many `Bool`s. The
congruences transport their IHs through the corresponding Boolean operation; `catCong` only rewrites
the LEFT factor of a `cat`, and `null (cat l r) = null l && null r` is congruent in its left argument,
so it transports too. -/
theorem sim_null {R S : PredRE} (h : R ≅ S) : null R = null S := by
  induction h with
  | @assoc R₁ R₂ R₃ =>
    simp only [null]; cases null R₁ <;> cases null R₂ <;> cases null R₃ <;> rfl
  | @dedup R₁ R₂ =>
    simp only [null]; cases null R₁ <;> cases null R₂ <;> rfl
  | @idem R => simp only [null]; cases null R <;> rfl
  | rfl => exact Eq.refl _
  | sym _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | negCong _ ih => simp only [null, ih]
  | altCong _ _ ihR ihS => simp only [null, ihR, ihS]
  | interCong _ _ ihR ihS => simp only [null, ihR, ihS]
  | @catCong R₁ R₂ S _ ih => simp only [null, ih]

/-! ## Language-soundness of `≅` — the fact that licenses the quotient.

`R ≅ S → ∀ w, Matches w R ↔ Matches w S`. Proven by induction on the `Sim` derivation; each ACI law
is a Boolean identity on the matched language (alt = ∪, so associativity/dedup/idempotence are the
∪-laws), and each congruence transports its premise's language-equality through the matching
denotation. This is the dregg-native analog of the (implicit) soundness ERE≤ relies on; we prove it
EXPLICITLY because it is the non-vacuity witness for the whole "up to `≅`" quotient. -/

/-- A `cons` word matches `alt l r` iff it matches one of the disjuncts — the language-level `∪`.
(`Matches` for `alt` is literally `∨`, so this is by definition; stated for readability.) -/
private theorem matches_alt (w : List Value) (l r : PredRE) :
    Matches w (.alt l r) ↔ (Matches w l ∨ Matches w r) := by rw [Matches]

private theorem matches_inter (w : List Value) (l r : PredRE) :
    Matches w (.inter l r) ↔ (Matches w l ∧ Matches w r) := by rw [Matches]

private theorem matches_neg (w : List Value) (r : PredRE) :
    Matches w (.neg r) ↔ ¬ Matches w r := by rw [Matches]

private theorem matches_cat (w : List Value) (l r : PredRE) :
    Matches w (.cat l r) ↔ ∃ w₁ w₂, w₁ ++ w₂ = w ∧ Matches w₁ l ∧ Matches w₂ r := by rw [Matches]

/-- **`sim_sound`** — similarity is LANGUAGE-SOUND: similar regexes match exactly the same words.
THE theorem that makes "finite up to `≅`" a finiteness of recognized LANGUAGES, not just of syntax
trees. Induction on the `Sim` derivation. -/
theorem sim_sound {R S : PredRE} (h : R ≅ S) : ∀ w, Matches w R ↔ Matches w S := by
  induction h with
  | @assoc R₁ R₂ R₃ =>
    intro w
    simp only [matches_alt]; tauto
  | @dedup R₁ R₂ =>
    intro w
    simp only [matches_alt]; tauto
  | @idem R =>
    intro w; simp only [matches_alt]; tauto
  | rfl => intro w; exact Iff.rfl
  | sym _ ih => intro w; exact (ih w).symm
  | trans _ _ ih₁ ih₂ => intro w; exact (ih₁ w).trans (ih₂ w)
  | negCong _ ih =>
    intro w; rw [matches_neg, matches_neg, ih w]
  | altCong _ _ ihR ihS =>
    intro w; rw [matches_alt, matches_alt, ihR w, ihS w]
  | interCong _ _ ihR ihS =>
    intro w; rw [matches_inter, matches_inter, ihR w, ihS w]
  | @catCong R₁ R₂ S _ ih =>
    intro w
    rw [matches_cat, matches_cat]
    constructor
    · rintro ⟨w₁, w₂, hsplit, hl, hr⟩; exact ⟨w₁, w₂, hsplit, (ih w₁).mp hl, hr⟩
    · rintro ⟨w₁, w₂, hsplit, hl, hr⟩; exact ⟨w₁, w₂, hsplit, (ih w₁).mpr hl, hr⟩

/-- **`sim_derives`** — the same soundness, transported to the EXECUTABLE matcher via Stage 1's
`correctness`: similar regexes give the same `derives` verdict on every word. So normalizing a
derivative by ACL-similarity never changes what the matcher accepts. -/
theorem sim_derives {R S : PredRE} (h : R ≅ S) (w : List Value) :
    derives w R = derives w S := by
  have := sim_sound h w
  rw [Bool.eq_iff_iff, correctness w R, correctness w S]; exact this

/-! ## DER-CONGRUENCE — `≅` is preserved by the derivative.

`Sim` as defined above is a congruence for the SYNTAX constructors, but nothing in its definition
says the DERIVATIVE respects it. That is the ingredient every route to the `n`-free emptiness
decision needs: to search the `≅`-quotient state space one must know `der` is well-defined ON the
quotient, i.e. `R ≅ S → der a R ≅ der a S`.

The proof is structural induction on the `Sim` derivation. Every ACI law's `der`-image is an
instance of the SAME law (`der` distributes over `alt` verbatim), and every congruence transports
its IH. The one case with content is `catCong`: `der a (cat l r)` branches on `null l`, so the
congruence only goes through once we know `≅` preserves NULLABILITY — hence `sim_null` first. -/

/-- **`sim_der`** — THE der-congruence: similarity is preserved by the Brzozowski derivative, so
`der` descends to the `≅`-quotient. Structural induction on the `Sim` derivation; the `catCong`
case is the interesting one — it splits on the shared `null` value supplied by `sim_null`. -/
theorem sim_der {R S : PredRE} (h : R ≅ S) (a : Value) : der a R ≅ der a S := by
  induction h with
  | assoc => exact Sim.assoc
  | dedup => exact Sim.dedup
  | idem => exact Sim.idem
  | rfl => exact Sim.rfl
  | sym _ ih => exact Sim.sym ih
  | trans _ _ ih₁ ih₂ => exact Sim.trans ih₁ ih₂
  | negCong _ ih => exact Sim.negCong ih
  | altCong _ _ ihR ihS => exact Sim.altCong ihR ihS
  | interCong _ _ ihR ihS => exact Sim.interCong ihR ihS
  | @catCong R₁ R₂ S hsim ih =>
    -- `der a (cat Rᵢ S)` branches on `null Rᵢ`; `sim_null hsim` says the two branches agree.
    have hnull : null R₁ = null R₂ := sim_null hsim
    simp only [der, hnull]
    cases hn : null R₂ with
    | false => simpa using Sim.catCong ih
    | true => simpa using Sim.altCong (Sim.catCong ih) Sim.rfl

/-! ## Iterating the der-congruence along a whole word. -/

/-- **`derList w R`** — the derivative iterated along the word `w` (the state `derives` reaches
before its final `null` check). Exposed so the SYNTACTIC congruence below can be stated on the
regex itself, not only on the Boolean verdict. -/
@[simp] def derList : List Value → PredRE → PredRE
  | [],      R => R
  | a :: as, R => derList as (der a R)

/-- `derives` is `null ∘ derList` — the two agree by construction. -/
theorem derives_eq_null_derList (w : List Value) (R : PredRE) :
    derives w R = null (derList w R) := by
  induction w generalizing R with
  | nil => rfl
  | cons a as ih => simpa only [derives, derList] using ih (der a R)

/-- **`sim_derList`** — the der-congruence iterated: similar regexes stay similar after reading any
word. This is `sim_der` folded along `w`. -/
theorem sim_derList {R S : PredRE} (h : R ≅ S) (w : List Value) :
    derList w R ≅ derList w S := by
  induction w generalizing R S with
  | nil => exact h
  | cons a as ih => exact ih (sim_der h a)

/-- **`sim_derives_syntactic`** — `sim_derives` re-derived through the DERIVATIVE route: iterate
`sim_der` along the word, then apply `sim_null` at the end.

This route IS semantics-free, and the name is now earned. Its three ingredients — `sim_der`,
`sim_derList`, `sim_null` — are each proved by induction on the `Sim` derivation using only the
defining clauses of `null` and `der`; none of them mentions `Matches`, `correctness`, `sim_sound` or
`sim_derives`. The independence is pinned STRUCTURALLY, not just by inspection: `sim_null` is
declared ABOVE the language-soundness section in this file, so it typechecks in an environment where
`sim_sound`/`sim_derives` do not yet exist and therefore cannot appeal to them. Moving it back below
would be the mutation that detects a regression.

MEASURED, not asserted — and REPRODUCIBLY: walk the transitive constant-closure of each theorem's
proof term in the BUILT environment (`ConstantInfo.value?` with `allowOpaque := true`, which is
required for theorems; a probe that omits it, or that runs before `lake build Dregg2`, reads the
STALE olean and can report the opposite). Under that method, the closures of `sim_null`, `sim_der`,
`sim_derList` and `sim_derives_syntactic` contain NO occurrence of `Matches`, `correctness`,
`sim_sound` or `denote` — `sim_null`'s is `Sim.rec` + `null` + `Bool` operations + `Eq` plumbing and
nothing else — whereas the denotational `sim_derives` DOES close over the full `Matches`/`correctness`
block (roughly an order of magnitude larger). That gap is the independence. Exact constant COUNTS are
deliberately not quoted here: they drift with mathlib and with the probe's treatment of opaque
definitions, so a stale figure would read as precision it does not have; re-run the probe rather than
trusting a number in a comment.

Scope, precisely: this does NOT retroactively make `sim_derives` syntactic — that theorem is
unchanged and still goes through `sim_sound` → `correctness` → `Matches`, and it remains the
LANGUAGE-level statement (it is what licenses the `≅`-quotient as a quotient of recognized
languages). What is new is that a SECOND and genuinely independent route to the same *verdict*
equation now exists: the derivative route needs no denotational semantics at all. The two routes
agreeing is a TWO-GATES-PROVABLY-AGREE property of this file, not extra strength in either one. -/
theorem sim_derives_syntactic {R S : PredRE} (h : R ≅ S) (w : List Value) :
    derives w R = derives w S := by
  rw [derives_eq_null_derList, derives_eq_null_derList]
  exact sim_null (sim_derList h w)

/-! ## Non-vacuity — `≅` is a NON-trivial congruence (relates distinct syntax, separates languages).

The dregg discipline: pin the quotient relation is neither empty nor universal. -/

section Guards

private def fr7 : Value := .record [("k", .sym 7)]
private def p7 : Pred := .symEq "k" 7

-- `≅` relates SYNTACTICALLY DISTINCT trees (idempotence): `(sym p7) ⋓ (sym p7) ≅ sym p7`.
example : (PredRE.alt (.sym p7) (.sym p7)) ≅ (.sym p7) := Sim.idem

-- …and that relation is language-sound: both accept exactly `[fr7]`.
example : derives [fr7] (PredRE.alt (.sym p7) (.sym p7)) = derives [fr7] (.sym p7) :=
  sim_derives Sim.idem [fr7]

-- `≅` does NOT relate everything: `sym p7` and `ε` recognize different languages, so (by
-- contrapositive of sim_sound) they are NOT similar — witnessed by a separating word.
example : ¬ Matches [fr7] (PredRE.ε) := by
  rw [matches_eps]; exact fun h => by cases h
example : Matches [fr7] (.sym p7) := by
  rw [Matches]; exact ⟨fr7, rfl, by simp only [leaf, p7, fr7, Pred.eval]; decide⟩

-- DER-CONGRUENCE, on a concrete pair: the `catCong` case with a NULLABLE left factor (so the
-- `null`-guarded branch of `der` is the one actually exercised).
example : (PredRE.cat (.alt (.star (.sym p7)) (.star (.sym p7))) (.sym p7))
        ≅ (PredRE.cat (.star (.sym p7)) (.sym p7)) := Sim.catCong Sim.idem

example : PredRE.der fr7 (.cat (.alt (.star (.sym p7)) (.star (.sym p7))) (.sym p7))
        ≅ PredRE.der fr7 (.cat (.star (.sym p7)) (.sym p7)) :=
  sim_der (Sim.catCong Sim.idem) fr7

-- …and the two agree on a concrete word, decided by the executable matcher (both `true`).
#guard PredRE.derives [fr7, fr7] (.cat (.alt (.star (.sym p7)) (.star (.sym p7))) (.sym p7)) = true
#guard PredRE.derives [fr7, fr7] (.cat (.star (.sym p7)) (.sym p7)) = true
-- …and reject the same word (both `false`) — the invariance is not vacuously "everything accepts".
#guard PredRE.derives [] (.cat (.alt (.star (.sym p7)) (.star (.sym p7))) (.sym p7)) = false
#guard PredRE.derives [] (.cat (.star (.sym p7)) (.sym p7)) = false

-- `null` invariance, on a pair whose two sides are syntactically distinct.
#guard PredRE.null (.alt (.star (PredRE.sym p7)) (.star (.sym p7))) = true
#guard PredRE.null (.star (PredRE.sym p7)) = true

end Guards

end PredRE

/-! ## Axiom hygiene. -/

#assert_all_clean [
  PredRE.sim_sound, PredRE.sim_derives,
  PredRE.sim_null, PredRE.sim_der,
  PredRE.derives_eq_null_derList, PredRE.sim_derList, PredRE.sim_derives_syntactic
]

/-!
## Stage 3 (`der_finite`) — NOW CLOSED (this note records how `sim_sound` fits the closed proof).

`sim_sound` here is the SEMANTIC foundation of "finite up to `≅`": it proves the quotient relation
respects the matched language, so a finite set of `≅`-classes is a finite set of recognized
languages (non-vacuous). The COMBINATORIAL finiteness COUNT — once named here as the remaining wall —
is now BUILT AND PROVEN kernel-clean across the `Deriv.{Combinatorics,TTerm,Permute,
SymbolicDerivative,Pieces,Finite,Monotone,Finiteness}` modules:

  * `Deriv.Finiteness.der_finite` : `∃ xs, ∀ {n}, steps r n ⊆[≅] xs` — the whole symbolic-derivative
    state space fits, up to `≅`, in the fixed finite `⊕(pieces r)` (depends only on
    `{propext, Classical.choice, Quot.sound}`).
  * the closure heart `Deriv.Finite.step_to_pieces` and the lift `Deriv.Monotone.toSumSubsets_monotone`
    + the `pieces`-similarity layer (`Deriv.Finiteness.pieces_equiv'`/`pieces_trans'`) are the ported
    ITP'25 tower (`step_to_pieces` / `Permute` nodup block / `pieces_equiv'`), over dregg's `Pred`.

So `sim_sound` (this module) is the language-soundness that makes that finite ≅-quotient a finite set
of recognized LANGUAGES. Stage 3 is closed; nothing here is a wall.

This is the design §3.3 "hard core #1 — months, not days," and it is NOT reduced by owning the
carrier (only the licensing/toolchain costs were). It is faithfully buildable (the structure
transfers; the leaf changes), but it is a multi-file syntactic-combinatorics port, not a
before-lunch close. It is named here so the next session opens the `pieces`/`Permute` port directly,
with the semantic foundation (`sim_sound`) already banked.
-/

end Dregg2.Crypto.Deriv
