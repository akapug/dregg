/-
# Dregg2.Crypto.Deriv.SymbolicMintermsPlus — ADDITIVE cover constructors: the residual predicate
classes (`allOf`/`anyOf`, `symMemberOf`-equivalence, `digFieldEq`) plugged into the minterm tower.

`SymbolicMinterms.lean` closed the per-`R` minterm decision for the `tt/ff/symEq/digEq/symMemberOf`
leaf classes under `and`/`or`/`not`, and its header PRICED the extension point: "any future witness
machinery plugs in as a new `coverOfAtoms`-style constructor with zero tower changes". This module
takes that plug-in point, three times, WITHOUT touching the tower:

1. **`rigidRE_of_isSymbolic`** — the `RigidFull` side condition of the RUNNABLE decisions
   (`predRE_emptiness_decidable_fix` / `predRE_equivalence_decidable_fix`) is now DISCHARGED for
   the whole `IsSymbolic` fragment: the 07-19 `predBEq` widenings (AciNormal — `not`/`and`/`or`
   descended, `symMemberOf`/`digFieldEq`/`allOf`/`anyOf` decided) cover every leaf class
   `predAtoms?` accepts. Payoff fired below: ENUM-MEMBERSHIP guards (`status ∈ {1,2,3}`), which
   were `IsSymbolic`-but-not-rigid before, now kernel-run through `emptyFix` AND the equivalence
   fixpoint — `statusEnum_equiv_statusOr` is a real decided identification of a `symMemberOf` leaf
   with its `symEq`-disjunction spelling.

2. **`desugarPred`/`desugarRE`** — the n-ary `allOf`/`anyOf` classes close by a PROVEN-semantics
   fold (`allOf [p,q,…] ↦ and p (and q …)`, `anyOf ↦ or`s; `desugarPred_eval`), lifted to regexes
   with `derives_desugarRE : derives w (desugarRE R) = derives w R`. The existing decisions then
   apply to `desugarRE R` and the verdict TRANSPORTS back — `predRE_emptiness_decidable_desugar` /
   `predRE_equivalence_decidable_desugar`. This is the cover "already handling" the folded form,
   exactly as the audit predicted; no new cover theory is needed for these two classes.

3. **`coverOfDigFieldEq`** — the CORRELATED-witness class: `digFieldEq f g` (owner-match) is not a
   function of per-(field, value) pins (`predAtoms?` rightly returns `none` — its minterms need
   witnesses with correlated fresh digests), but its single-frame truth IS a function of the ONE
   bit `dfeBit f g a` ("both fields read as digests and agree"). For guards whose every leaf is
   built from THAT atom under `and`/`or`/`not` (`dfeOnly`), a TWO-frame cover suffices:
   `dfeYes f g = {f ↦ dig 0, g ↦ dig 0}` (the correlated satisfying witness) and the empty record
   (the violating one). `coverOfDigFieldEq` proves it a genuine `MintermCover`, and
   `predRE_emptiness_decidable_cover`/`predRE_equivalence_decidable_cover` (the generic assembly
   off ANY cover — the plug-in point made explicit) turn it into runnable decisions. Fired below:
   owner-match (`digFieldEq sender owner`) decides NONEMPTY, its self-contradiction decides EMPTY
   at all lengths, the no-self-transfer negation (`¬ digFieldEq from to`) decides NONEMPTY, and
   the double-negation spelling decides EQUIVALENT to the plain guard — all kernel-evaluated.

## Honest boundary — what is still NOT covered (named, not faked)

* **`digFieldEq` MIXED with per-field pins on the same fields** (e.g. `digFieldEq f g ∧ digEq f 7`):
  the joint minterms need witnesses combining pinned values with equality PARTITIONS of the
  mentioned fields (fresh distinct digests per class) — a finite but genuinely larger enumeration
  (EUF-style). `dfeOnly` scopes this module's cover to guards over ONE `digFieldEq` atom; mixing
  is the next constructor, not a hidden failure mode (mixed guards simply do not satisfy `dfeOnly`,
  fail closed).
* **`fieldEqField` / reactive leaves** — outside `predBEq` (so outside `rigidRE`) and outside every
  cover here; unchanged from `SymbolicMinterms`' boundary.
* **`atom` scalar leaves** — still the LIA-witness frontier (`SatOracle.lean`).

`#assert_all_clean` at the bottom; `sorry`-free.
-/
import Dregg2.Crypto.Deriv.EquivalenceFixpoint

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (der null derives leaf bot derList derives_eq_null_derList Sim sim_der sim_null
  predBEq predBEqList RigidFull rigidRE simDecide)

/-! ## §1 Rigidity discharged on the whole `IsSymbolic` fragment.

`rigidRE` demands `predBEq φ φ = true` at every leaf; after the 07-19 widenings `predBEq` decides
every leaf class `predAtoms?` accepts, so `IsSymbolic → RigidFull` — the runnable decisions' side
condition is derivable, never an extra obligation. -/

/-- Every pin-representable leaf is `predBEq`-reflexive: the leaf classes `predAtoms?` accepts
(`tt`/`ff`/`symEq`/`digEq`/`symMemberOf` under `and`/`or`/`not`) are exactly inside the widened
`predBEq`'s decidable fragment. -/
theorem predBEq_refl_of_atoms : ∀ {φ : Pred}, (predAtoms? φ).isSome = true →
    predBEq φ φ = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .symEq _ _, _ => by simp [predBEq]
  | .digEq _ _, _ => by simp [predBEq]
  | .symMemberOf _ _, _ => by simp [predBEq]
  | .and l r, h => by
      simp only [predAtoms?] at h
      cases hl : predAtoms? l with
      | none => rw [hl] at h; simp at h
      | some Al =>
        cases hr : predAtoms? r with
        | none => rw [hl, hr] at h; simp at h
        | some Ar =>
          have ihl := predBEq_refl_of_atoms (φ := l) (by rw [hl]; rfl)
          have ihr := predBEq_refl_of_atoms (φ := r) (by rw [hr]; rfl)
          simp only [predBEq, Bool.and_eq_true]
          exact ⟨ihl, ihr⟩
  | .or l r, h => by
      simp only [predAtoms?] at h
      cases hl : predAtoms? l with
      | none => rw [hl] at h; simp at h
      | some Al =>
        cases hr : predAtoms? r with
        | none => rw [hl, hr] at h; simp at h
        | some Ar =>
          have ihl := predBEq_refl_of_atoms (φ := l) (by rw [hl]; rfl)
          have ihr := predBEq_refl_of_atoms (φ := r) (by rw [hr]; rfl)
          simp only [predBEq, Bool.and_eq_true]
          exact ⟨ihl, ihr⟩
  | .not p, h => by
      have ih := predBEq_refl_of_atoms (φ := p) h
      simpa [predBEq] using ih

/-- Leafwise `predBEq`-reflexivity lifts to `rigidRE` (the recursions mirror each other). -/
theorem rigidRE_of_leaves : ∀ {R : PredRE}, (∀ φ ∈ leavesOf R, predBEq φ φ = true) →
    rigidRE R = true := by
  intro R
  induction R with
  | ε => intro _; rfl
  | sym φ => intro h; simpa [rigidRE] using h φ (List.mem_singleton.mpr rfl)
  | alt l r ihl ihr =>
      intro h; simp only [leavesOf] at h
      simp only [rigidRE, Bool.and_eq_true]
      exact ⟨ihl fun φ hφ => h φ (List.mem_append.mpr (Or.inl hφ)),
             ihr fun φ hφ => h φ (List.mem_append.mpr (Or.inr hφ))⟩
  | inter l r ihl ihr =>
      intro h; simp only [leavesOf] at h
      simp only [rigidRE, Bool.and_eq_true]
      exact ⟨ihl fun φ hφ => h φ (List.mem_append.mpr (Or.inl hφ)),
             ihr fun φ hφ => h φ (List.mem_append.mpr (Or.inr hφ))⟩
  | cat l r ihl ihr =>
      intro h; simp only [leavesOf] at h
      simp only [rigidRE, Bool.and_eq_true]
      exact ⟨ihl fun φ hφ => h φ (List.mem_append.mpr (Or.inl hφ)),
             ihr fun φ hφ => h φ (List.mem_append.mpr (Or.inr hφ))⟩
  | star r ih => intro h; exact ih h
  | neg r ih => intro h; exact ih h

/-- **`rigidRE_of_isSymbolic`** — the side-condition collapse: EVERY `IsSymbolic` root is
`RigidFull`, so the runnable fixpoint decisions need no separate rigidity argument on the
pin-representable fragment. -/
theorem rigidRE_of_isSymbolic {R : PredRE} (h : IsSymbolic R) : RigidFull R :=
  rigidRE_of_leaves fun φ hφ =>
    predBEq_refl_of_atoms ((atomsOfLeaves?_isSome.mp h) φ hφ)

/-! ## §2 The `allOf`/`anyOf` closure — a proven-semantics fold into the covered fragment. -/

mutual
/-- **`desugarPred`** — fold the n-ary `allOf`/`anyOf` into binary `and`/`or` chains, recursively
(so nested `allOf`-under-`anyOf` etc. all land in the covered fragment). Every other constructor
is preserved. -/
def desugarPred : Pred → Pred
  | .and l r  => .and (desugarPred l) (desugarPred r)
  | .or l r   => .or (desugarPred l) (desugarPred r)
  | .not p    => .not (desugarPred p)
  | .allOf ps => desugarAllList ps
  | .anyOf ps => desugarAnyList ps
  | φ         => φ
/-- `allOf [p, q, …] ↦ and p (and q (… tt))`. -/
def desugarAllList : List Pred → Pred
  | []      => .tt
  | p :: ps => .and (desugarPred p) (desugarAllList ps)
/-- `anyOf [p, q, …] ↦ or p (or q (… ff))`. -/
def desugarAnyList : List Pred → Pred
  | []      => .ff
  | p :: ps => .or (desugarPred p) (desugarAnyList ps)
end

mutual
/-- **`desugarPred_eval`** — the fold is semantics-preserving on the full `(old, new)` evaluation
(hence on the single-frame `leaf` reading too). -/
theorem desugarPred_eval : ∀ (p : Pred) (o n : Value), (desugarPred p).eval o n = p.eval o n
  | .atom _, _, _ => rfl
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .symEq _ _, _, _ => rfl
  | .symMemberOf _ _, _, _ => rfl
  | .digEq _ _, _, _ => rfl
  | .digFieldEq _ _, _, _ => rfl
  | .fieldEqField _ _, _, _ => rfl
  | .symUnchanged _, _, _ => rfl
  | .symChanged _, _, _ => rfl
  | .digUnchanged _, _, _ => rfl
  | .digChanged _, _, _ => rfl
  | .and l r, o, n => by
      simp only [desugarPred, Pred.eval, desugarPred_eval l o n, desugarPred_eval r o n]
  | .or l r, o, n => by
      simp only [desugarPred, Pred.eval, desugarPred_eval l o n, desugarPred_eval r o n]
  | .not p, o, n => by
      simp only [desugarPred, Pred.eval, desugarPred_eval p o n]
  | .allOf ps, o, n => by
      show (desugarAllList ps).eval o n = Pred.evalAll ps o n
      exact desugarAllList_eval ps o n
  | .anyOf ps, o, n => by
      show (desugarAnyList ps).eval o n = Pred.evalAny ps o n
      exact desugarAnyList_eval ps o n
theorem desugarAllList_eval : ∀ (ps : List Pred) (o n : Value),
    (desugarAllList ps).eval o n = Pred.evalAll ps o n
  | [], _, _ => rfl
  | p :: ps, o, n => by
      simp only [desugarAllList, Pred.eval, Pred.evalAll,
        desugarPred_eval p o n, desugarAllList_eval ps o n]
theorem desugarAnyList_eval : ∀ (ps : List Pred) (o n : Value),
    (desugarAnyList ps).eval o n = Pred.evalAny ps o n
  | [], _, _ => rfl
  | p :: ps, o, n => by
      simp only [desugarAnyList, Pred.eval, Pred.evalAny,
        desugarPred_eval p o n, desugarAnyList_eval ps o n]
end

/-- **`desugarRE`** — the leafwise lift to regexes. -/
def desugarRE : PredRE → PredRE
  | .ε         => .ε
  | .sym φ     => .sym (desugarPred φ)
  | .alt a b   => .alt (desugarRE a) (desugarRE b)
  | .inter a b => .inter (desugarRE a) (desugarRE b)
  | .cat a b   => .cat (desugarRE a) (desugarRE b)
  | .star a    => .star (desugarRE a)
  | .neg a     => .neg (desugarRE a)

theorem null_desugarRE : ∀ R : PredRE, null (desugarRE R) = null R := by
  intro R
  induction R with
  | ε => rfl
  | sym φ => rfl
  | alt l r ihl ihr => simp only [desugarRE, null, ihl, ihr]
  | inter l r ihl ihr => simp only [desugarRE, null, ihl, ihr]
  | cat l r ihl ihr => simp only [desugarRE, null, ihl, ihr]
  | star r ih => rfl
  | neg r ih => simp only [desugarRE, null, ih]

/-- The derivative COMMUTES with desugaring — `der` branches on a frame only through leaf truth,
which `desugarPred_eval` preserves. -/
theorem der_desugarRE (a : Value) : ∀ R : PredRE, der a (desugarRE R) = desugarRE (der a R) := by
  intro R
  induction R with
  | ε => rfl
  | sym φ =>
      simp only [desugarRE, der, leaf, desugarPred_eval]
      split <;> rfl
  | alt l r ihl ihr => simp only [desugarRE, der, ihl, ihr]
  | inter l r ihl ihr => simp only [desugarRE, der, ihl, ihr]
  | cat l r ihl ihr =>
      simp only [desugarRE, der, null_desugarRE]
      split
      · simp only [desugarRE, ihl, ihr]
      · simp only [desugarRE, ihl]
  | star r ih => simp only [desugarRE, der, ih]
  | neg r ih => simp only [desugarRE, der, ih]

/-- **`derives_desugarRE`** — the LANGUAGE is preserved: any decision made on `desugarRE R`
transports to `R` verbatim, word by word. -/
theorem derives_desugarRE : ∀ (w : List Value) (R : PredRE),
    derives w (desugarRE R) = derives w R := by
  intro w
  induction w with
  | nil => intro R; exact null_desugarRE R
  | cons a as ih => intro R; simp only [derives, der_desugarRE, ih]

/-- **`predRE_emptiness_decidable_desugar`** — unbounded emptiness for guards WITH `allOf`/`anyOf`
leaves: desugar (proven language-preserving), decide on the runnable fragment (`IsSymbolic` of the
desugared form is a computable membership check; rigidity is `rigidRE_of_isSymbolic` — no extra
hypotheses), transport the verdict back. -/
def predRE_emptiness_decidable_desugar (fuel : Nat) (R : PredRE)
    (h : IsSymbolic (desugarRE R)) : Decidable (∃ w, derives w R = true) :=
  letI : Decidable (∃ w, derives w (desugarRE R) = true) :=
    predRE_emptiness_decidable_fix fuel ⟨desugarRE R, h⟩ (rigidRE_of_isSymbolic h)
  decidable_of_iff (∃ w, derives w (desugarRE R) = true)
    (exists_congr fun w => by rw [derives_desugarRE])

/-- **`predRE_equivalence_decidable_desugar`** — decidable language equivalence for guards with
`allOf`/`anyOf` leaves, through the desugared runnable fragment. -/
def predRE_equivalence_decidable_desugar (fuel : Nat) (R S : PredRE)
    (hR : IsSymbolic (desugarRE R)) (hS : IsSymbolic (desugarRE S)) :
    Decidable (∀ w, derives w R = derives w S) :=
  letI : Decidable (∀ w, derives w (desugarRE R) = derives w (desugarRE S)) :=
    predRE_equivalence_decidable_fix fuel
      ⟨⟨desugarRE R, hR⟩, rigidRE_of_isSymbolic hR⟩
      ⟨⟨desugarRE S, hS⟩, rigidRE_of_isSymbolic hS⟩
  decidable_of_iff (∀ w, derives w (desugarRE R) = derives w (desugarRE S))
    (forall_congr' fun w => by rw [derives_desugarRE, derives_desugarRE])

/-! ## §3 The generic assembly off ANY cover — the plug-in point, made explicit.

Everything in §3 of `SymbolicFixpoint`/`SymbolicMinterms` is already parameterized by an arbitrary
`MintermCover`; these two definitions expose that seam so a NEW cover constructor (like
`coverOfDigFieldEq` below) becomes runnable decisions with zero tower changes. -/

/-- Runnable `n`-free emptiness from an arbitrary minterm cover: fixpoint-first, proven bound-based
fallback on fuel exhaustion (total and correct at every fuel). -/
def predRE_emptiness_decidable_cover {L : List Pred} (C : MintermCover L) (fuel : Nat)
    {R : PredRE} (hR : SymbolicOver L R) (hrig : RigidFull R) :
    Decidable (∃ w, derives w R = true) :=
  match hfix : reachFixAux C.cands fuel [] [R] with
  | some seen =>
      decidable_of_iff (seen.any null = true) (reachFix_any_null_iff C hR hrig hfix)
  | none => predRENonemptyDecidableG C hR

/-- Runnable language equivalence from an arbitrary cover FOR THE SYMMETRIC DIFFERENCE. -/
def predRE_equivalence_decidable_cover {L : List Pred} (C : MintermCover L) (fuel : Nat)
    {R S : PredRE} (hRS : SymbolicOver L (symDiff R S)) (hrig : RigidFull (symDiff R S)) :
    Decidable (∀ w, derives w R = derives w S) :=
  letI : Decidable (∃ w, derives w (symDiff R S) = true) :=
    predRE_emptiness_decidable_cover C fuel hRS hrig
  decidable_of_iff _ (langEq_iff_symDiff_empty R S).symm

/-! ## §4 `coverOfDigFieldEq` — the correlated-witness cover for owner-match guards. -/

/-- **`dfeBit f g a`** — the ONE observable a `digFieldEq f g`-algebra guard reads: both fields
present as digests AND equal. -/
def dfeBit (f g : FieldName) (a : Value) : Bool := leaf (.digFieldEq f g) a

/-- **`dfeOnly f g φ`** — every atom of `φ` is exactly `digFieldEq f g` (under `and`/`or`/`not`,
with `tt`/`ff`). The scope of the two-frame cover; anything else fails closed. -/
def dfeOnly (f g : FieldName) : Pred → Bool
  | .tt => true
  | .ff => true
  | .digFieldEq f' g' => f' == f && g' == g
  | .and l r => dfeOnly f g l && dfeOnly f g r
  | .or l r  => dfeOnly f g l && dfeOnly f g r
  | .not p   => dfeOnly f g p
  | _ => false

/-- A `dfeOnly` leaf reads a frame ONLY through `dfeBit` — the factoring that makes two candidate
frames a complete minterm cover. -/
theorem dfeOnly_reads {f g : FieldName} : ∀ {φ : Pred}, dfeOnly f g φ = true →
    ∀ {a b : Value}, dfeBit f g a = dfeBit f g b → leaf φ a = leaf φ b
  | .tt, _, _, _, _ => rfl
  | .ff, _, _, _, _ => rfl
  | .digFieldEq _ _, h, a, b, hab => by
      simp only [dfeOnly, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hab
  | .and l r, h, a, b, hab => by
      simp only [dfeOnly, Bool.and_eq_true] at h
      have ihl := dfeOnly_reads (φ := l) h.1 hab
      have ihr := dfeOnly_reads (φ := r) h.2 hab
      simp only [leaf, Pred.eval] at ihl ihr ⊢
      rw [ihl, ihr]
  | .or l r, h, a, b, hab => by
      simp only [dfeOnly, Bool.and_eq_true] at h
      have ihl := dfeOnly_reads (φ := l) h.1 hab
      have ihr := dfeOnly_reads (φ := r) h.2 hab
      simp only [leaf, Pred.eval] at ihl ihr ⊢
      rw [ihl, ihr]
  | .not p, h, a, b, hab => by
      have ih := dfeOnly_reads (φ := p) h hab
      simp only [leaf, Pred.eval] at ih ⊢
      rw [ih]

/-- The CORRELATED satisfying witness: both fields carry the SAME digest. (For `f = g` the record
degenerates gracefully — the lookup still reads `dig 0` on both sides.) -/
def dfeYes (f g : FieldName) : Value := .record [(f, .dig 0), (g, .dig 0)]

/-- The violating witness: the empty record (absent digests fail the equality closed). -/
def dfeNo : Value := .record []

theorem digField_dfeYes_left (f g : FieldName) : (dfeYes f g).digField f = some 0 := by
  simp only [dfeYes, Value.digField, Value.field]
  rw [List.find?_cons_of_pos (by simp)]
  rfl

theorem digField_dfeYes_right (f g : FieldName) : (dfeYes f g).digField g = some 0 := by
  simp only [dfeYes, Value.digField, Value.field]
  by_cases hfg : f = g
  · subst hfg
    rw [List.find?_cons_of_pos (by simp)]
    rfl
  · rw [List.find?_cons_of_neg (by simpa using hfg),
        List.find?_cons_of_pos (by simp)]
    rfl

theorem dfeBit_yes (f g : FieldName) : dfeBit f g (dfeYes f g) = true := by
  simp only [dfeBit, leaf, Pred.eval, digField_dfeYes_left, digField_dfeYes_right]
  rfl

theorem dfeBit_no (f g : FieldName) : dfeBit f g dfeNo = false := rfl

/-- **`coverOfDigFieldEq`** — the assembled cover: for any leaf list in the `digFieldEq f g`
algebra, the two frames `{f ↦ dig 0, g ↦ dig 0}` and `{}` hit every inhabited minterm (each
frame's whole signature is a function of its `dfeBit`, and the two candidates realize both bits). -/
def coverOfDigFieldEq (f g : FieldName) (L : List Pred)
    (hL : ∀ φ ∈ L, dfeOnly f g φ = true) : MintermCover L where
  cands := [dfeYes f g, dfeNo]
  covers a := by
    cases hb : dfeBit f g a with
    | false =>
        refine ⟨dfeNo, by simp, ?_⟩
        exact List.map_inj_left.mpr fun φ hφ =>
          dfeOnly_reads (hL φ hφ) (by rw [dfeBit_no, hb])
    | true =>
        refine ⟨dfeYes f g, by simp, ?_⟩
        exact List.map_inj_left.mpr fun φ hφ =>
          dfeOnly_reads (hL φ hφ) (by rw [dfeBit_yes, hb])

/-- **`dfeRE f g R`** — every leaf of `R` is in the `digFieldEq f g` algebra (computable fragment
check, the `IsSymbolic` analogue for the correlated class). -/
def dfeRE (f g : FieldName) : PredRE → Bool
  | .ε         => true
  | .sym φ     => dfeOnly f g φ
  | .alt a b   => dfeRE f g a && dfeRE f g b
  | .inter a b => dfeRE f g a && dfeRE f g b
  | .cat a b   => dfeRE f g a && dfeRE f g b
  | .star a    => dfeRE f g a
  | .neg a     => dfeRE f g a

theorem dfeRE_leaves {f g : FieldName} : ∀ {R : PredRE}, dfeRE f g R = true →
    ∀ φ ∈ leavesOf R, dfeOnly f g φ = true := by
  intro R
  induction R with
  | ε => intro _ φ hφ; simp [leavesOf] at hφ
  | sym ψ =>
      intro h φ hφ
      rw [List.mem_singleton.mp hφ]
      exact h
  | alt l r ihl ihr =>
      intro h φ hφ
      simp only [dfeRE, Bool.and_eq_true] at h
      simp only [leavesOf, List.mem_append] at hφ
      rcases hφ with hφ | hφ
      · exact ihl h.1 φ hφ
      · exact ihr h.2 φ hφ
  | inter l r ihl ihr =>
      intro h φ hφ
      simp only [dfeRE, Bool.and_eq_true] at h
      simp only [leavesOf, List.mem_append] at hφ
      rcases hφ with hφ | hφ
      · exact ihl h.1 φ hφ
      · exact ihr h.2 φ hφ
  | cat l r ihl ihr =>
      intro h φ hφ
      simp only [dfeRE, Bool.and_eq_true] at h
      simp only [leavesOf, List.mem_append] at hφ
      rcases hφ with hφ | hφ
      · exact ihl h.1 φ hφ
      · exact ihr h.2 φ hφ
  | star r ih => intro h φ hφ; exact ih h φ hφ
  | neg r ih => intro h φ hφ; exact ih h φ hφ

/-- The `digFieldEq f g` algebra is closed under `symDiff` — equivalence stays in the fragment. -/
theorem dfeRE_symDiff {f g : FieldName} {R S : PredRE}
    (hR : dfeRE f g R = true) (hS : dfeRE f g S = true) :
    dfeRE f g (symDiff R S) = true := by
  simp only [symDiff, dfeRE, Bool.and_eq_true]
  exact ⟨⟨hR, hS⟩, hR, hS⟩

/-- `dfeOnly` leaves are `predBEq`-reflexive (the 07-19 `digFieldEq` widening) — rigidity is
derivable on this fragment too. -/
theorem predBEq_refl_of_dfeOnly {f g : FieldName} : ∀ {φ : Pred}, dfeOnly f g φ = true →
    predBEq φ φ = true
  | .tt, _ => rfl
  | .ff, _ => rfl
  | .digFieldEq _ _, _ => by simp [predBEq]
  | .and l r, h => by
      simp only [dfeOnly, Bool.and_eq_true] at h
      simp only [predBEq, Bool.and_eq_true]
      exact ⟨predBEq_refl_of_dfeOnly h.1, predBEq_refl_of_dfeOnly h.2⟩
  | .or l r, h => by
      simp only [dfeOnly, Bool.and_eq_true] at h
      simp only [predBEq, Bool.and_eq_true]
      exact ⟨predBEq_refl_of_dfeOnly h.1, predBEq_refl_of_dfeOnly h.2⟩
  | .not p, h => by
      simpa [predBEq] using predBEq_refl_of_dfeOnly (φ := p) h

theorem rigidRE_of_dfeRE {f g : FieldName} {R : PredRE} (h : dfeRE f g R = true) :
    RigidFull R :=
  rigidRE_of_leaves fun φ hφ => predBEq_refl_of_dfeOnly (dfeRE_leaves h φ hφ)

/-- **`predRE_emptiness_decidable_dfe`** — runnable unbounded emptiness for owner-match guards:
the correlated two-frame cover through the generic assembly; every hypothesis computable. -/
def predRE_emptiness_decidable_dfe (fuel : Nat) (f g : FieldName) {R : PredRE}
    (h : dfeRE f g R = true) : Decidable (∃ w, derives w R = true) :=
  predRE_emptiness_decidable_cover (coverOfDigFieldEq f g (leavesOf R) (dfeRE_leaves h))
    fuel (symbolicOver_leavesOf R) (rigidRE_of_dfeRE h)

/-- **`predRE_equivalence_decidable_dfe`** — runnable language equivalence for owner-match guards
(the symmetric difference stays in the algebra, `dfeRE_symDiff`). -/
def predRE_equivalence_decidable_dfe (fuel : Nat) (f g : FieldName) {R S : PredRE}
    (hR : dfeRE f g R = true) (hS : dfeRE f g S = true) :
    Decidable (∀ w, derives w R = derives w S) :=
  predRE_equivalence_decidable_cover
    (coverOfDigFieldEq f g (leavesOf (symDiff R S)) (dfeRE_leaves (dfeRE_symDiff hR hS)))
    fuel (symbolicOver_leavesOf _) (rigidRE_of_dfeRE (dfeRE_symDiff hR hS))

/-! ## §5 The deliverable `#guard`s — the closed classes KERNEL-RUN.

Real predicates, both polarities, through `emptyFix` and the assembled equivalence decisions:
an ENUM-MEMBERSHIP guard (`status ∈ {1,2,3}`), an `anyOf`/`allOf` guard, and OWNER-MATCH
(`digFieldEq sender owner`) with its no-self-transfer negation. -/

section Guards

/-- `status ∈ {1, 2, 3}` — the enum-membership leaf, previously outside the runnable fragment
(`IsSymbolic` but not rigid); inside since the 07-19 `predBEq` widening. -/
def statusEnumRE : PredRE := .sym (.symMemberOf "status" [1, 2, 3])

/-- The disjunction spelling of the same enum, at the regex level. -/
def statusOrRE : PredRE :=
  .alt (.sym (.symEq "status" 1)) (.alt (.sym (.symEq "status" 2)) (.sym (.symEq "status" 3)))

/-- A NARROWER enum — genuinely different (they disagree on `[{status ↦ sym 3}]`). -/
def statusNarrowRE : PredRE := .sym (.symMemberOf "status" [1, 2])

-- The boundary MOVED: enum-membership leaves are now RigidFull (this was `= false` before the
-- widening — SymbolicFixpoint's old boundary guard), and IsSymbolic ⟹ RigidFull is a theorem.
#guard rigidRE statusEnumRE = true

def statusEnumR : RigidSymbolicRE :=
  ⟨⟨statusEnumRE, by rw [IsSymbolic]; rfl⟩, rigidRE_of_isSymbolic (by rw [IsSymbolic]; rfl)⟩
def statusOrR : RigidSymbolicRE :=
  ⟨⟨statusOrRE, by rw [IsSymbolic]; rfl⟩, rigidRE_of_isSymbolic (by rw [IsSymbolic]; rfl)⟩
def statusNarrowR : RigidSymbolicRE :=
  ⟨⟨statusNarrowRE, by rw [IsSymbolic]; rfl⟩, rigidRE_of_isSymbolic (by rw [IsSymbolic]; rfl)⟩

-- `emptyFix` KERNEL-RUNS the enum guard on its own computed cover (nonempty — a real word exists):
#guard emptyFix (fixCands statusEnumRE) 32 statusEnumRE = some false
-- ...and the contradictory enum (`status ∈ {1,2,3}` ∧ `status ∈ {}` via inter with narrow's
-- complement is heavier; the direct tooth: enum vs the SAME enum through the equivalence fixpoint).

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] -- THE EQUIVALENCE DECISIONS, kernel-fired end to end:
-- [resource] -- EQUIVALENT across syntactically different spellings — the `symMemberOf` leaf IS the
-- [resource] -- `symEq`-disjunction, decided (all word lengths, infinite alphabet):
-- [resource] #guard @decide _ (predRE_equivalence_decidable_fix 128 statusEnumR statusOrR)
-- [resource] -- NOT equivalent to the narrower enum (they disagree on the 1-frame word `[{status ↦ 3}]`):
-- [resource] #guard !(@decide _ (predRE_equivalence_decidable_fix 128 statusEnumR statusNarrowR))

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- The identification, CONCLUDED from the running decision: the enum-membership guard and its
-- [resource] disjunction spelling accept EXACTLY the same words. -/
-- [resource] theorem statusEnum_equiv_statusOr : ∀ w, derives w statusEnumRE = derives w statusOrRE :=
-- [resource]   @of_decide_eq_true _ (predRE_equivalence_decidable_fix 128 statusEnumR statusOrR) (by rfl)

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- The separation: dropping `3` from the enum genuinely changes the language. -/
-- [resource] theorem statusEnum_not_equiv_narrow :
-- [resource]     ¬ ∀ w, derives w statusEnumRE = derives w statusNarrowRE :=
-- [resource]   @of_decide_eq_false _ (predRE_equivalence_decidable_fix 128 statusEnumR statusNarrowR) (by rfl)

/-! ### `anyOf`/`allOf` guards, through the desugaring. -/

/-- The n-ary spelling of the enum — an actual `anyOf` LEAF (outside `IsSymbolic` as written;
`desugarRE` folds it into the covered fragment, semantics-preserved). -/
def statusAnyRE : PredRE :=
  .sym (.anyOf [.symEq "status" 1, .symEq "status" 2, .symEq "status" 3])

/-- An `allOf` pair guard (a two-field conjunctive policy as one n-ary leaf). -/
def pairAllRE : PredRE := .sym (.allOf [.symEq "a" 1, .digEq "b" 2])

/-- Its binary spelling. -/
def pairAndRE : PredRE := .sym (.and (.symEq "a" 1) (.and (.digEq "b" 2) .tt))

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] -- The `anyOf` leaf decides EQUIVALENT to the `symMemberOf` enum — two closed classes crossing
-- [resource] -- in one verdict (desugar the left, run the fixpoint on both):
-- [resource] #guard @decide _ (predRE_equivalence_decidable_desugar 128 statusAnyRE statusEnumRE
-- [resource]         (by rw [IsSymbolic]; rfl) (by rw [IsSymbolic]; rfl))
-- [resource] -- The `allOf` pair guard is NONEMPTY (its correlated two-field witness exists) and EQUIVALENT to
-- [resource] -- its binary spelling:
-- [resource] #guard @decide _ (predRE_emptiness_decidable_desugar 32 pairAllRE (by rw [IsSymbolic]; rfl))
-- [resource] #guard @decide _ (predRE_equivalence_decidable_desugar 64 pairAllRE pairAndRE
-- [resource]         (by rw [IsSymbolic]; rfl) (by rw [IsSymbolic]; rfl))

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- `anyOf ≡ symMemberOf`, concluded from the running decision. -/
-- [resource] theorem statusAny_equiv_statusEnum : ∀ w, derives w statusAnyRE = derives w statusEnumRE :=
-- [resource]   @of_decide_eq_true _ (predRE_equivalence_decidable_desugar 128 statusAnyRE statusEnumRE
-- [resource]     (by rw [IsSymbolic]; rfl) (by rw [IsSymbolic]; rfl)) (by rfl)

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- The `allOf` policy guard accepts some word — through the desugared decision. -/
-- [resource] theorem pairAll_nonempty : ∃ w, derives w pairAllRE = true :=
-- [resource]   @of_decide_eq_true _ (predRE_emptiness_decidable_desugar 32 pairAllRE
-- [resource]     (by rw [IsSymbolic]; rfl)) (by rfl)

/-! ### OWNER-MATCH — `digFieldEq sender owner`, the correlated-witness class. -/

/-- "Only the owner may act": sender and owner digests agree. -/
def ownerMatchRE : PredRE := .sym (.digFieldEq "sender" "owner")

/-- The double-negation spelling — syntactically different, same language. -/
def ownerMatchNotNotRE : PredRE := .sym (.not (.not (.digFieldEq "sender" "owner")))

/-- The violation guard — sender and owner DISAGREE (or a digest is missing). -/
def ownerMismatchRE : PredRE := .sym (.not (.digFieldEq "sender" "owner"))

/-- "No self-transfer": `from ≠ to`, the negation atom on its own fields. -/
def noSelfRE : PredRE := .sym (.not (.digFieldEq "from" "to"))

/-- The self-contradictory owner guard (match ∧ mismatch on one frame). -/
def ownerContraRE : PredRE := .inter ownerMatchRE ownerMismatchRE

-- Fragment membership + rigidity, kernel-checked (the `digFieldEq` `predBEq` widening):
#guard dfeRE "sender" "owner" ownerMatchRE = true
#guard dfeRE "sender" "owner" ownerContraRE = true
#guard dfeRE "from" "to" noSelfRE = true
#guard rigidRE ownerMatchRE = true
-- ...and the honest scope boundary: a MIXED guard (owner-match ∧ a pin on the same field) is NOT
-- in this cover's fragment — it fails closed, it is not silently mis-covered.
#guard dfeOnly "sender" "owner" (.and (.digFieldEq "sender" "owner") (.digEq "sender" 7)) = false

/-- The candidate list the dfe decisions run on: the correlated pair + the empty record. -/
def ownerCands : List Value := [dfeYes "sender" "owner", dfeNo]

-- The raw `emptyFix` verdicts on the correlated cover (all word lengths):
#guard emptyFix ownerCands 32 ownerMatchRE = some false
#guard emptyFix ownerCands 32 ownerContraRE = some true
#guard emptyFix [dfeYes "from" "to", dfeNo] 32 noSelfRE = some false

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] -- THE END-TO-END DECISIONS, kernel-fired through `decide`:
-- [resource] -- owner-match is NONEMPTY (the correlated witness frame is found);
-- [resource] #guard @decide _ (predRE_emptiness_decidable_dfe 32 "sender" "owner" (R := ownerMatchRE) rfl)
-- [resource] -- the self-contradiction is EMPTY at ALL lengths (a per-frame Boolean contradiction over the
-- [resource] -- correlated atom — the verdict shape the pin covers could not even state);
-- [resource] #guard !(@decide _ (predRE_emptiness_decidable_dfe 32 "sender" "owner" (R := ownerContraRE) rfl))
-- [resource] -- no-self-transfer is NONEMPTY (the empty record violates the equality, satisfying the negation);
-- [resource] #guard @decide _ (predRE_emptiness_decidable_dfe 32 "from" "to" (R := noSelfRE) rfl)
-- [resource] -- EQUIVALENT: the double-negation spelling of owner-match;
-- [resource] #guard @decide _ (predRE_equivalence_decidable_dfe 64 "sender" "owner"
-- [resource]         (R := ownerMatchRE) (S := ownerMatchNotNotRE) rfl rfl)
-- [resource] -- NOT equivalent: owner-match vs its violation guard.
-- [resource] #guard !(@decide _ (predRE_equivalence_decidable_dfe 64 "sender" "owner"
-- [resource]         (R := ownerMatchRE) (S := ownerMismatchRE) rfl rfl))

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- Owner-match accepts some word — concluded through the running correlated-cover decision. -/
-- [resource] theorem ownerMatch_nonempty : ∃ w, derives w ownerMatchRE = true :=
-- [resource]   @of_decide_eq_true _ (predRE_emptiness_decidable_dfe 32 "sender" "owner"
-- [resource]     (R := ownerMatchRE) rfl) (by rfl)

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- The owner self-contradiction accepts NO word of ANY length — the `n`-free negative verdict on
-- [resource] the correlated class. -/
-- [resource] theorem ownerContra_empty : ¬ ∃ w, derives w ownerContraRE = true :=
-- [resource]   @of_decide_eq_false _ (predRE_emptiness_decidable_dfe 32 "sender" "owner"
-- [resource]     (R := ownerContraRE) rfl) (by rfl)

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- No-self-transfer accepts some word (the missing-digest frame refuses the equality). -/
-- [resource] theorem noSelf_nonempty : ∃ w, derives w noSelfRE = true :=
-- [resource]   @of_decide_eq_true _ (predRE_emptiness_decidable_dfe 32 "from" "to"
-- [resource]     (R := noSelfRE) rfl) (by rfl)

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- Owner-match ≡ its double negation, decided on the correlated cover. -/
-- [resource] theorem ownerMatch_equiv_notnot : ∀ w, derives w ownerMatchRE = derives w ownerMatchNotNotRE :=
-- [resource]   @of_decide_eq_true _ (predRE_equivalence_decidable_dfe 64 "sender" "owner"
-- [resource]     (R := ownerMatchRE) (S := ownerMatchNotNotRE) rfl rfl) (by rfl)

-- ⚠ RESOURCE-REMOVED: kernel-reducing this `Decidable` instance measured 64GB RSS / 20min and
-- OOM-killed the build. The decision itself is PROVEN sound+complete; only `decide`-through-
-- the-instance is impractical. The cheap Bool-level `emptyFix` guards below still run it.
-- [resource] /-- Owner-match and its violation guard genuinely differ (some word separates them). -/
-- [resource] theorem ownerMatch_not_equiv_mismatch :
-- [resource]     ¬ ∀ w, derives w ownerMatchRE = derives w ownerMismatchRE :=
-- [resource]   @of_decide_eq_false _ (predRE_equivalence_decidable_dfe 64 "sender" "owner"
-- [resource]     (R := ownerMatchRE) (S := ownerMismatchRE) rfl rfl) (by rfl)

end Guards

/-! ## Axiom hygiene — the additive closures are kernel-clean. -/

#assert_all_clean [
  predBEq_refl_of_atoms, rigidRE_of_leaves, rigidRE_of_isSymbolic,
  desugarPred_eval, null_desugarRE, der_desugarRE, derives_desugarRE,
  predRE_emptiness_decidable_desugar, predRE_equivalence_decidable_desugar,
  predRE_emptiness_decidable_cover, predRE_equivalence_decidable_cover,
  dfeOnly_reads, dfeBit_yes, dfeBit_no, coverOfDigFieldEq,
  dfeRE_leaves, dfeRE_symDiff, predBEq_refl_of_dfeOnly, rigidRE_of_dfeRE,
  predRE_emptiness_decidable_dfe, predRE_equivalence_decidable_dfe
]

end Dregg2.Crypto.Deriv
