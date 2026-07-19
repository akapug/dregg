/-
# Dregg2.Crypto.Deriv.SymbolicMinterms — the PER-R MINTERM generalization of the symbolic
emptiness/equivalence decision: from the braceP-specific fragment to ARBITRARY decidable-leaf guards.

`SymbolicEmptiness.lean` + `SymbolicEmptinessUnbounded.lean` + `SymbolicDecision.lean` decide
unbounded language nonemptiness `∃ w : List Value, derives w R = true` — but ONLY on `IsDeployed R`:
guards whose every leaf reads a frame through the SINGLE atom `braceP = symEq "t" 0`, with the two
GLOBAL minterm witnesses `candidates = [braceVal, dataVal]` hard-coded into `satStep`. This module is
residual 2 of the full-closure audit (`docs/DESIGN-symbolic-decidability-status.md` §3, "tier-1
widening"): per-`R` leaf-set extraction → minterm enumeration → a witness per satisfiable minterm —
the place the tier-0 `predSat_symEq` generality (a witness for EVERY field/symbol) finally plumbs in.

## The construction (standard symbolic-automata minterms, realized constructively)

1. **The signature.** For a leaf-predicate list `L`, `leafSig L a = L.map (leaf · a)` is the MINTERM
   of `L` that the frame `a` inhabits. `der a R` depends on `a` only through `leafSig (leavesOf R) a`
   (`der_factors_over` — the general form of the braceP-specific `der_factors`), because `der`
   branches on a frame exclusively through its leaves' truth.
2. **Per-R candidates.** A `MintermCover L` is a finite list of witness frames hitting EVERY
   inhabited minterm of `L` (satisfiable minterms have a witness in the list; unsatisfiable minterms
   have no frame at all, so they need none — this is how the UNSAT-minterm obstruction from
   `SymbolicEmptiness.lean`'s header is sidestepped, again constructively). The generalized search
   `reachableWithinG C.cands` then canonicalizes an arbitrary accepting `Value` word onto cover
   frames (`derList_factors_canon`), giving the bounded sound∧complete decision and — through the
   ported `StepBridge`/pigeonhole rungs — the `n`-free one.
3. **Building covers.** For the leaf classes the templater actually writes — `tt`, `ff`,
   `symEq f s`, `digEq f d`, `symMemberOf f set`, and arbitrary `and`/`or`/`not` combinations —
   each leaf's single-frame truth is a function of finitely many ATOM PINS "`field f reads the typed
   value u`" (`predAtoms?`/`atomReads`). A cover is then enumerated as one candidate frame per choice
   of at-most-one mentioned pin per mentioned field (`atomCands`, a `List.sections` product): the
   restriction of ANY frame to the mentioned pins is such a candidate (`restrictFrame`), and it
   inhabits the same minterm. This is the `predSat_symEq` witness shape (`{f ↦ sym s}` realizes the
   pin, `{}` realizes its negation), lifted to arbitrarily many interacting pins.

## Deliverables

* `predRE_emptiness_decidable_general : (R : SymbolicRE) → Decidable (∃ w, derives w R.val = true)`
  where `SymbolicRE` is the DECIDABLE-LEAF fragment `IsSymbolic` (a computable check:
  every leaf of `R` is built from `tt/ff/symEq/digEq/symMemberOf` under `and/or/not`).
* `predRE_equivalence_decidable_general : (R S : SymbolicRE) → Decidable (∀ w, derives w R.val =
  derives w S.val)` — the equivalence corollary transports (`symDiff` preserves the leaf set).
* The braceP fragment falls out as an INSTANCE (`noDoubleBraceRE` is `IsSymbolic`), and the
  generalization is STRICT: `symEq "role" 3` (roleP) is provably NOT `LeafDeployed`
  (`roleP_not_leafDeployed`), yet its guards are decided here.

## Honest boundary — the leaf classes NOT covered (named precisely, not faked)

`predAtoms?` returns `none` (so `IsSymbolic` excludes the regex) for leaves mentioning:
  * `atom (c : StateConstraint)` — a scalar atom's truth (`inRange`/`affineLe`/…) is NOT a function
    of finitely many typed value pins; covering it needs a verified LIA-feasibility witness
    enumeration (the priced frontier of `SatOracle.lean`'s design note).
  * `digFieldEq`/`fieldEqField` — CROSS-FIELD equality over an infinite value domain: its minterms
    need witnesses with correlated FRESH values, outside the per-(field,value)-pin vocabulary.
  * `symUnchanged`/`symChanged`/`digUnchanged`/`digChanged` — reactive `(old,new)` atoms; under the
    single-frame reading (`old = ∅`) they are first-write-permissive constants in some cases but not
    all, and are excluded wholesale rather than partially special-cased.
  * `allOf`/`anyOf` — mechanical to add (fold `predAtoms?` over the list), omitted only to keep this
    module's recursion structural; the boolean closure they express is already available via
    `and`/`or`.

The tractability pole is inherited verbatim from `SymbolicDecision.lean`: the `n`-free decision
kernel-evaluates only when `emptinessBound` is tiny (`ε`); the bounded sound∧complete decision runs
on all the concrete guards below. `#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicEquivalence
import Mathlib.Data.List.Sections
import Mathlib.Data.List.Dedup

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Deriv.Combinatorics
open PredRE (der null derives leaf bot Matches correctness step steps derivative derList pieces
  Sim sim_der sim_derList sim_null derives_eq_null_derList)

/-! ## §1 Signatures over a leaf list — the per-`R` minterm structure. -/

/-- **`leafSig L a`** — the minterm of the leaf list `L` that the frame `a` inhabits: the vector of
truth values of every leaf on `a`. Two frames with the same signature are indistinguishable by every
guard whose leaves come from `L`. -/
def leafSig (L : List Pred) (a : Value) : List Bool := L.map (fun φ => leaf φ a)

/-- **`LeafRefines L φ`** — the leaf predicate `φ` reads a single frame ONLY through its `L`-minterm:
same signature ⇒ same verdict. The general form of `LeafDeployed` (which is the special case
`L = [braceP]`). -/
def LeafRefines (L : List Pred) (φ : Pred) : Prop :=
  ∀ a b : Value, leafSig L a = leafSig L b → leaf φ a = leaf φ b

/-- **`SymbolicOver L R`** — every `sym` leaf of `R` is `LeafRefines L`: the whole guard reads a
frame only through its `L`-minterm. Closed under all `PredRE` constructors (so `der` preserves it,
`der_symbolicOver`). Generalizes `IsDeployed` (the case `L = [braceP]`). -/
def SymbolicOver (L : List Pred) : PredRE → Prop
  | .ε         => True
  | .sym φ     => LeafRefines L φ
  | .alt l r   => SymbolicOver L l ∧ SymbolicOver L r
  | .inter l r => SymbolicOver L l ∧ SymbolicOver L r
  | .cat l r   => SymbolicOver L l ∧ SymbolicOver L r
  | .star r    => SymbolicOver L r
  | .neg r     => SymbolicOver L r

/-- A leaf listed in `L` trivially reads a frame through its `L`-minterm (its truth is one of the
signature's coordinates). -/
theorem leafRefines_of_mem {L : List Pred} {φ : Pred} (h : φ ∈ L) : LeafRefines L φ :=
  fun _ _ hab => List.map_inj_left.mp hab φ h

/-- `ff` is `LeafRefines` any `L` (constantly `false`). Needed because `der` introduces `bot`
leaves not present in the original leaf set. -/
theorem leafRefines_ff {L : List Pred} : LeafRefines L .ff := fun _ _ _ => rfl

/-- **`der_factors_over`** — THE general leaf-factoring (the heart of the generalization): for a
guard over `L`, two frames in the SAME `L`-minterm yield the SAME concrete derivative. Structural
induction on `R`; the `sym` case is exactly `LeafRefines`, every other constructor recurses (the
frame-independent `null l` guard of `cat` is untouched — `der` branches on a frame ONLY through
leaf truth). Generalizes `der_factors` (the case `L = [braceP]`). -/
theorem der_factors_over {L : List Pred} {a b : Value} (hab : leafSig L a = leafSig L b) :
    ∀ {R : PredRE}, SymbolicOver L R → der a R = der b R := by
  intro R
  induction R with
  | ε => intro _; rfl
  | sym φ => intro hR; simp only [der]; rw [hR a b hab]
  | alt l r ihl ihr => intro hR; simp only [der, SymbolicOver] at *; rw [ihl hR.1, ihr hR.2]
  | inter l r ihl ihr => intro hR; simp only [der, SymbolicOver] at *; rw [ihl hR.1, ihr hR.2]
  | cat l r ihl ihr => intro hR; simp only [der, SymbolicOver] at *; rw [ihl hR.1, ihr hR.2]
  | star r ih => intro hR; simp only [der, SymbolicOver] at *; rw [ih hR]
  | neg r ih => intro hR; simp only [der, SymbolicOver] at *; rw [ih hR]

/-- The `SymbolicOver L` fragment is CLOSED under `der` — so `der_factors_over` applies at every
step of a derivative walk. Generalizes `der_deployed`. -/
theorem der_symbolicOver {L : List Pred} {a : Value} :
    ∀ {R : PredRE}, SymbolicOver L R → SymbolicOver L (der a R) := by
  intro R
  induction R with
  | ε => intro _; exact leafRefines_ff
  | sym φ => intro _; simp only [der]; split
             · exact True.intro
             · exact leafRefines_ff
  | alt l r ihl ihr => intro hR; simp only [der, SymbolicOver] at *; exact ⟨ihl hR.1, ihr hR.2⟩
  | inter l r ihl ihr => intro hR; simp only [der, SymbolicOver] at *; exact ⟨ihl hR.1, ihr hR.2⟩
  | cat l r ihl ihr =>
      intro hR; simp only [der, SymbolicOver] at *; split
      · exact ⟨⟨ihl hR.1, hR.2⟩, ihr hR.2⟩
      · exact ⟨ihl hR.1, hR.2⟩
  | star r ih => intro hR; simp only [der, SymbolicOver] at *; exact ⟨ih hR, hR⟩
  | neg r ih => intro hR; simp only [der, SymbolicOver] at *; exact ih hR

/-- **`leavesOf R`** — the leaf-predicate set of `R` (the per-`R` leaf extraction of residual 2). -/
def leavesOf : PredRE → List Pred
  | .ε         => []
  | .sym φ     => [φ]
  | .alt l r   => leavesOf l ++ leavesOf r
  | .inter l r => leavesOf l ++ leavesOf r
  | .cat l r   => leavesOf l ++ leavesOf r
  | .star r    => leavesOf r
  | .neg r     => leavesOf r

/-- A regex is `SymbolicOver` any list containing all its leaves. -/
theorem symbolicOver_of_leaves_mem {L : List Pred} :
    ∀ {R : PredRE}, (∀ φ ∈ leavesOf R, φ ∈ L) → SymbolicOver L R := by
  intro R
  induction R with
  | ε => intro _; exact True.intro
  | sym φ => intro h; exact leafRefines_of_mem (h φ (List.mem_singleton.mpr rfl))
  | alt l r ihl ihr =>
      intro h; simp only [leavesOf] at h
      exact ⟨ihl fun φ hφ => h φ (List.mem_append.mpr (Or.inl hφ)),
             ihr fun φ hφ => h φ (List.mem_append.mpr (Or.inr hφ))⟩
  | inter l r ihl ihr =>
      intro h; simp only [leavesOf] at h
      exact ⟨ihl fun φ hφ => h φ (List.mem_append.mpr (Or.inl hφ)),
             ihr fun φ hφ => h φ (List.mem_append.mpr (Or.inr hφ))⟩
  | cat l r ihl ihr =>
      intro h; simp only [leavesOf] at h
      exact ⟨ihl fun φ hφ => h φ (List.mem_append.mpr (Or.inl hφ)),
             ihr fun φ hφ => h φ (List.mem_append.mpr (Or.inr hφ))⟩
  | star r ih => intro h; exact ih h
  | neg r ih => intro h; exact ih h

/-- **Every** regex is symbolic over its own leaf set — the fragment restriction lives entirely in
COVER construction (§6), never here. -/
theorem symbolicOver_leavesOf (R : PredRE) : SymbolicOver (leavesOf R) R :=
  symbolicOver_of_leaves_mem (fun _ h => h)

/-! ## §2 Minterm covers — per-`R` candidate witnesses. -/

/-- **`MintermCover L`** — a finite candidate list hitting every INHABITED minterm of `L`: for
every frame `a` some candidate shares `a`'s signature. This is "a witness per satisfiable minterm"
(the unsatisfiable minterms have no frame to cover). The braceP tower's global
`candidates = [braceVal, dataVal]` is the instance for `L = [braceP]`. -/
structure MintermCover (L : List Pred) where
  /-- The candidate witness frames. -/
  cands : List Value
  /-- Every frame's minterm is inhabited by a candidate. -/
  covers : ∀ a : Value, ∃ c, c ∈ cands ∧ leafSig L c = leafSig L a

namespace MintermCover

variable {L : List Pred}

/-- **`canon C a`** — the computable canonical witness of `a`'s minterm class (the general
`canonicalWitness`): the first candidate with `a`'s signature. -/
def canon (C : MintermCover L) (a : Value) : Value :=
  match C.cands.find? (fun c => leafSig L c == leafSig L a) with
  | some c => c
  | none   => a

theorem canon_mem (C : MintermCover L) (a : Value) : C.canon a ∈ C.cands := by
  unfold canon
  split
  · next c hf => exact List.mem_of_find?_eq_some hf
  · next hf =>
      obtain ⟨c, hc, hsig⟩ := C.covers a
      have := List.find?_eq_none.mp hf c hc
      exact absurd (by simpa using hsig) this

theorem leafSig_canon (C : MintermCover L) (a : Value) : leafSig L (C.canon a) = leafSig L a := by
  unfold canon
  split
  · next c hf => simpa using List.find?_some hf
  · next => rfl

end MintermCover

/-! ## §3 The generalized sat-filtered search — the braceP tower with per-`R` candidates.

Everything in this section and §4/§5 is the `SymbolicEmptiness`/`StepBridge`/
`SymbolicEmptinessUnbounded` tower with the global `candidates` replaced by an arbitrary candidate
list `V` (soundness needs nothing more) and the completeness half parameterized by a `MintermCover`
(the ONLY place the cover is load-bearing). The braceP originals are untouched. -/

/-- The generalized sat-filtered step: concrete derivatives under the candidate frames `V`. -/
def satStepG (V : List Value) (r : PredRE) : List PredRE := V.map (fun a => der a r)

/-- Bounded sat-filtered reachability under candidates `V` (generalizes `reachableWithin`). -/
def reachableWithinG (V : List Value) : Nat → PredRE → List PredRE
  | 0,          R => [R]
  | Nat.succ n, R => (reachableWithinG V n R).flatMap (fun s => s :: satStepG V s)

/-- The bounded decision under candidates `V` (generalizes `nonemptyWithin`). -/
def nonemptyWithinG (V : List Value) (n : Nat) (R : PredRE) : Bool :=
  (reachableWithinG V n R).any null

/-- Length-tracked soundness: a reachable residual is `derList w R` for a word `w` over `V` with
`|w| ≤ n`. (General for ANY `V` — soundness never needs the cover.) -/
theorem reachableWithinG_sound' {V : List Value} :
    ∀ {n : Nat} {R s : PredRE}, s ∈ reachableWithinG V n R →
      ∃ w, w.length ≤ n ∧ derList w R = s := by
  intro n
  induction n with
  | zero =>
      intro R s h
      rw [reachableWithinG, List.mem_singleton] at h
      subst h; exact ⟨[], Nat.le_refl 0, rfl⟩
  | succ n ih =>
      intro R s h
      rw [reachableWithinG, List.mem_flatMap] at h
      obtain ⟨t, ht, hs⟩ := h
      obtain ⟨w, hlen, hw⟩ := ih ht
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨w, Nat.le_succ_of_le hlen, hw⟩
      · simp only [satStepG, List.mem_map] at hs
        obtain ⟨a, _, ha⟩ := hs
        refine ⟨w ++ [a], ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · rw [derList_append]; show der a (derList w R) = s; rw [hw]; exact ha

theorem reachableWithinG_mono_one {V : List Value} {n : Nat} {R : PredRE} :
    ∀ {s}, s ∈ reachableWithinG V n R → s ∈ reachableWithinG V (n + 1) R := by
  intro s hs
  rw [reachableWithinG, List.mem_flatMap]
  exact ⟨s, hs, List.mem_cons.mpr (Or.inl rfl)⟩

theorem reachableWithinG_mono {V : List Value} {n m : Nat} {R : PredRE} (h : n ≤ m) :
    ∀ {s}, s ∈ reachableWithinG V n R → s ∈ reachableWithinG V m R := by
  induction h with
  | refl => exact fun hs => hs
  | step _ ih => exact fun hs => reachableWithinG_mono_one (ih hs)

/-- Reachability completeness over `V`-words (generalizes `reachableWithin_complete`). -/
theorem reachableWithinG_complete {V : List Value} {R : PredRE} :
    ∀ {n : Nat} {v : List Value}, (∀ x ∈ v, x ∈ V) → v.length ≤ n →
      derList v R ∈ reachableWithinG V n R := by
  intro n
  induction n with
  | zero =>
      intro v _ hlen
      have hv0 : v = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst hv0
      exact List.mem_singleton.mpr rfl
  | succ n ih =>
      intro v hv hlen
      rcases List.eq_nil_or_concat v with rfl | ⟨v', a, rfl⟩
      · simp only [derList]
        exact reachableWithinG_mono (Nat.zero_le _) (List.mem_singleton.mpr rfl)
      · simp only [List.concat_eq_append] at hv hlen ⊢
        have ha : a ∈ V := hv a (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
        have hv' : ∀ x ∈ v', x ∈ V := fun x hx =>
          hv x (List.mem_append.mpr (Or.inl hx))
        have hlen' : v'.length ≤ n := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
        have hin : derList v' R ∈ reachableWithinG V n R := ih hv' hlen'
        rw [derList_append, reachableWithinG, List.mem_flatMap]
        refine ⟨derList v' R, hin, List.mem_cons.mpr (Or.inr ?_)⟩
        show der a (derList v' R) ∈ satStepG V (derList v' R)
        simp only [satStepG, List.mem_map]
        exact ⟨a, ha, rfl⟩

/-- Word canonicalization onto the cover (generalizes `derList_factors`): reading `w` lands in the
same residual as reading its minterm-canonicalization `w.map C.canon` — a word entirely over
`C.cands`. -/
theorem derList_factors_canon {L : List Pred} (C : MintermCover L) :
    ∀ (w : List Value) {R : PredRE}, SymbolicOver L R →
      derList w R = derList (w.map C.canon) R := by
  intro w
  induction w with
  | nil => intro R _; rfl
  | cons a as ih =>
      intro R hR
      simp only [derList, List.map_cons]
      rw [der_factors_over (C.leafSig_canon a).symm hR]
      exact ih (der_symbolicOver hR)

/-- Bounded completeness under a cover (generalizes `nonemptyWithin_complete`). -/
theorem nonemptyWithinG_complete {L : List Pred} (C : MintermCover L) {n : Nat} {R : PredRE}
    (hR : SymbolicOver L R)
    (w : List Value) (hw : derives w R = true) (hlen : w.length ≤ n) :
    nonemptyWithinG C.cands n R = true := by
  have hvcand : ∀ x ∈ w.map C.canon, x ∈ C.cands := by
    intro x hx; rw [List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; exact C.canon_mem y
  have hvlen : (w.map C.canon).length ≤ n := by rw [List.length_map]; exact hlen
  have hnull : null (derList (w.map C.canon) R) = true := by
    rw [← derList_factors_canon C w hR, ← derives_eq_null_derList]; exact hw
  rw [nonemptyWithinG, List.any_eq_true]
  exact ⟨_, reachableWithinG_complete hvcand hvlen, hnull⟩

/-- **`nonemptyWithinG_iff_bounded`** — the SOUND ∧ COMPLETE bounded decision on the general
fragment: for `R` symbolic over `L` with cover `C`, the bounded search under `C.cands` reports
nonempty EXACTLY WHEN a word of length `≤ n` (over the infinite `Value` alphabet) is accepted. -/
theorem nonemptyWithinG_iff_bounded {L : List Pred} (C : MintermCover L) {n : Nat} {R : PredRE}
    (hR : SymbolicOver L R) :
    nonemptyWithinG C.cands n R = true ↔ ∃ w, w.length ≤ n ∧ derives w R = true := by
  constructor
  · intro h
    rw [nonemptyWithinG, List.any_eq_true] at h
    obtain ⟨s, hs, hnull⟩ := h
    obtain ⟨w, hlen, hw⟩ := reachableWithinG_sound' hs
    exact ⟨w, hlen, by rw [derives_eq_null_derList, hw]; exact hnull⟩
  · rintro ⟨w, hlen, hw⟩; exact nonemptyWithinG_complete C hR w hw hlen

/-- The bounded `Decidable`, general form (generalizes `boundedNonemptyDecidable`). -/
def boundedNonemptyDecidableG {L : List Pred} (C : MintermCover L) (n : Nat) {R : PredRE}
    (hR : SymbolicOver L R) : Decidable (∃ w, w.length ≤ n ∧ derives w R = true) :=
  decidable_of_iff _ (nonemptyWithinG_iff_bounded C hR)

/-! ## §4 StepBridge + pigeonhole, transported — the `n`-free reduction with per-`R` candidates. -/

/-- The generalized sat-filtered step is contained in the sat-free symbolic step (any `V`) —
`der_mem_step` is already frame-generic. -/
theorem satStepG_subset_step {V : List Value} (r : PredRE) : satStepG V r ⊆ step r := by
  intro s hs
  simp only [satStepG, List.mem_map] at hs
  obtain ⟨a, _, rfl⟩ := hs
  exact PredRE.der_mem_step a r

/-- Generalized reachability lands in the symbolic `steps` (port of
`reachableWithin_mem_steps`). -/
theorem reachableWithinG_mem_steps {V : List Value} :
    ∀ {n : Nat} {R s : PredRE}, s ∈ reachableWithinG V n R → ∃ k, k ≤ n ∧ s ∈ steps R k := by
  intro n
  induction n with
  | zero =>
      intro R s h
      rw [reachableWithinG, List.mem_singleton] at h
      subst h
      exact ⟨0, Nat.le_refl 0, by simp only [steps, List.mem_cons, List.not_mem_nil, or_false]⟩
  | succ n ih =>
      intro R s h
      rw [reachableWithinG, List.mem_flatMap] at h
      obtain ⟨t, ht, hs⟩ := h
      obtain ⟨k, hkn, hk⟩ := ih ht
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨k, Nat.le_succ_of_le hkn, hk⟩
      · exact ⟨k + 1, Nat.succ_le_succ hkn, mem_steps_succ hk (satStepG_subset_step t hs)⟩

/-- The finiteness transfer with the witness exposed (port of `reachableWithin_subset_pieces`):
generalized reachability sits inside `⊕(pieces R)` up to `≅`, uniformly in the depth. -/
theorem reachableWithinG_subset_pieces {V : List Value} {R : PredRE} {n : Nat} :
    reachableWithinG V n R ⊆[ (· ≅ ·) ] ⊕(pieces R) := fun _ hs =>
  have ⟨_, _, hk⟩ := reachableWithinG_mem_steps hs
  PredRE.steps_to_toSumSubsets _ hk

/-- The pigeonhole (port of `exists_sim_prefix_pair`): a `V`-word longer than the `≅`-class budget
has two distinct prefixes driving `R` into `≅`-related states. -/
theorem exists_sim_prefix_pairG {V : List Value} {R : PredRE} {xs : List PredRE}
    (hxs : ∀ {n : Nat}, reachableWithinG V n R ⊆[ (· ≅ ·) ] xs)
    {v : List Value} (hv : ∀ x ∈ v, x ∈ V) (hlen : xs.length < v.length + 1) :
    ∃ i j, i < j ∧ j ≤ v.length ∧ derList (v.take i) R ≅ derList (v.take j) R := by
  have key : ∀ k : Fin (v.length + 1), ∃ idx : Fin xs.length,
      derList (v.take k.val) R ≅ xs.get idx := by
    intro k
    have hcand : ∀ x ∈ v.take k.val, x ∈ V :=
      fun x hx => hv x (List.take_subset _ _ hx)
    have hklen : (v.take k.val).length ≤ k.val := by
      simp only [List.length_take]; omega
    obtain ⟨y, hsim, hy⟩ := hxs _ (reachableWithinG_complete (R := R) (n := k.val) hcand hklen)
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp hy
    exact ⟨idx, by rw [hidx]; exact hsim⟩
  let f : Fin (v.length + 1) → Fin xs.length := fun k => (key k).choose
  have hf : ∀ k, derList (v.take k.val) R ≅ xs.get (f k) := fun k => (key k).choose_spec
  have mk : ∀ p q : Fin (v.length + 1), p.val < q.val → f p = f q →
      ∃ i j, i < j ∧ j ≤ v.length ∧ derList (v.take i) R ≅ derList (v.take j) R := by
    intro p q hpq hfpq
    refine ⟨p.val, q.val, hpq, Nat.lt_succ_iff.mp q.isLt, ?_⟩
    have hq : derList (v.take q.val) R ≅ xs.get (f p) := by rw [hfpq]; exact hf q
    exact Sim.trans (hf p) (Sim.sym hq)
  have hcard : Fintype.card (Fin xs.length) < Fintype.card (Fin (v.length + 1)) := by
    simpa using hlen
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hab' : a.val ≠ b.val := fun h => hab (Fin.val_inj.mp h)
  rcases Nat.lt_or_gt_of_ne hab' with h | h
  · exact mk a b h hfab
  · exact mk b a h hfab.symm

/-- The pumping lemma (port of `pumpDown`): every accepting `V`-word collapses under the
`≅`-class budget. -/
theorem pumpDownG {V : List Value} {R : PredRE} {xs : List PredRE}
    (hxs : ∀ {n : Nat}, reachableWithinG V n R ⊆[ (· ≅ ·) ] xs) :
    ∀ (v : List Value), (∀ x ∈ v, x ∈ V) → derives v R = true →
      ∃ u, u.length ≤ xs.length ∧ derives u R = true := by
  have main : ∀ (n : Nat) (v : List Value), v.length ≤ n → (∀ x ∈ v, x ∈ V) →
      derives v R = true → ∃ u, u.length ≤ xs.length ∧ derives u R = true := by
    intro n
    induction n with
    | zero => intro v hlen _ hd; exact ⟨v, by omega, hd⟩
    | succ n ih =>
      intro v hlen hv hd
      by_cases hb : v.length ≤ xs.length
      · exact ⟨v, hb, hd⟩
      · obtain ⟨i, j, hij, hjv, hsim⟩ := exists_sim_prefix_pairG hxs hv (by omega)
        have hulen : (v.take i ++ v.drop j).length < v.length := excise_length hij hjv
        have hud : derives (v.take i ++ v.drop j) R = true := by
          rw [derives_eq_null_derList] at hd ⊢
          rw [sim_null (derList_excise hsim)]; exact hd
        exact ih _ (by omega) (fun x hx => hv x (excise_mem hx)) hud
  intro v hv hd
  exact main v.length v (Nat.le_refl _) hv hd

/-- **`nonempty_iff_nonemptyWithinG_bound`** — the `n`-FREE reduction on the GENERAL fragment
(port of `nonempty_iff_nonemptyWithin_bound`): unbounded nonemptiness over the infinite alphabet ⟺
the bounded cover-filtered search at the single computable depth `emptinessBound R`. -/
theorem nonempty_iff_nonemptyWithinG_bound {L : List Pred} (C : MintermCover L) {R : PredRE}
    (hR : SymbolicOver L R) :
    (∃ w, derives w R = true) ↔ nonemptyWithinG C.cands (emptinessBound R) R = true := by
  rw [nonemptyWithinG_iff_bounded C hR]
  constructor
  · rintro ⟨w, hw⟩
    have hvc : ∀ x ∈ w.map C.canon, x ∈ C.cands := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      exact C.canon_mem y
    have hvd : derives (w.map C.canon) R = true := by
      rw [derives_eq_null_derList, ← derList_factors_canon C w hR, ← derives_eq_null_derList]
      exact hw
    exact pumpDownG (fun {n} => reachableWithinG_subset_pieces (n := n)) _ hvc hvd
  · rintro ⟨w, _, hw⟩
    exact ⟨w, hw⟩

/-- The `n`-free emptiness decision, general form (port of `predRENonemptyDecidable`): computable
(`decidable_of_iff` off the Boolean search, never `Classical.dec`). -/
def predRENonemptyDecidableG {L : List Pred} (C : MintermCover L) {R : PredRE}
    (hR : SymbolicOver L R) : Decidable (∃ w, derives w R = true) :=
  decidable_of_iff _ (nonempty_iff_nonemptyWithinG_bound C hR).symm

/-- The contrapositive that is the point: a `false` at the computed depth proves EMPTINESS for
words of ANY length (port of `nonemptyWithin_bound_complete`). -/
theorem nonemptyWithinG_bound_complete {L : List Pred} (C : MintermCover L) {R : PredRE}
    (hR : SymbolicOver L R)
    (h : nonemptyWithinG C.cands (emptinessBound R) R = false) :
    ¬ ∃ w, derives w R = true := by
  intro hex
  rw [(nonempty_iff_nonemptyWithinG_bound C hR).mp hex] at h
  exact Bool.noConfusion h

/-! ## §5 Atom pins — the decidable-leaf vocabulary and its witness calculus.

An ATOM PIN `(f, u)` is the assertion "field `f` reads as the typed value `u`" — exactly the shape
tier 0's `predSat_symEq` witnesses (`{f ↦ sym s}` realizes it, `{}` refutes it). Every leaf in the
covered classes is a boolean function of finitely many pins (`predAtoms?`), and a frame's behavior
on a pin set is REALIZED by a finite record (`restrictFrame`) — the two facts the cover needs. -/

/-- A typed pinnable value: the `sym`/`dig` leaves the typed field readers distinguish. -/
inductive AtomVal where
  /-- An interned identity (`Value.sym`). -/
  | sym (s : Nat)
  /-- A digest / cell-reference (`Value.dig`). -/
  | dig (d : Nat)
  deriving Repr, DecidableEq

/-- The `Value` a pin pins. -/
def AtomVal.toValue : AtomVal → Value
  | .sym s => .sym s
  | .dig d => .dig d

theorem AtomVal.toValue_inj : ∀ {u v : AtomVal}, u.toValue = v.toValue → u = v
  | .sym _, .sym _, h => by simpa [AtomVal.toValue] using h
  | .dig _, .dig _, h => by simpa [AtomVal.toValue] using h
  | .sym _, .dig _, h => by simp [AtomVal.toValue] at h
  | .dig _, .sym _, h => by simp [AtomVal.toValue] at h

/-- **`atomReads a f u`** — does frame `a` realize the pin `(f, u)`? Phrased through the SAME typed
readers `Pred.eval` uses (`symField`/`digField`), so leaf truth rewrites to pin reads
definitionally. -/
def atomReads (a : Value) (f : FieldName) : AtomVal → Bool
  | .sym s => a.symField f == some s
  | .dig d => a.digField f == some d

/-- A pin read is exactly a typed field lookup: `atomReads a f u = true ↔ a.field f = some
u.toValue`. The functionality of `Value.field` then makes pins at one field MUTUALLY EXCLUSIVE. -/
theorem atomReads_iff_field {a : Value} {f : FieldName} {u : AtomVal} :
    atomReads a f u = true ↔ a.field f = some u.toValue := by
  cases u with
  | sym s =>
      simp only [atomReads, AtomVal.toValue, Value.symField, beq_iff_eq]
      cases hf : a.field f with
      | none => simp
      | some v => cases v <;> simp
  | dig d =>
      simp only [atomReads, AtomVal.toValue, Value.digField, beq_iff_eq]
      cases hf : a.field f with
      | none => simp
      | some v => cases v <;> simp

/-- Pins at one field are mutually exclusive on any single frame (the field holds ONE value). -/
theorem atomReads_functional {a : Value} {f : FieldName} {u v : AtomVal}
    (hu : atomReads a f u = true) (huv : u ≠ v) : atomReads a f v = false := by
  rw [Bool.eq_false_iff]
  intro hv
  rw [atomReads_iff_field] at hu hv
  rw [hu] at hv
  exact huv (AtomVal.toValue_inj (Option.some.injEq _ _ ▸ hv.symm ▸ rfl))

/-- **`predAtoms? φ`** — the pin set of a decidable leaf: `some pins` when `φ`'s single-frame truth
is a boolean function of the reads of `pins`; `none` outside the covered classes (the honest
boundary — see the header). -/
def predAtoms? : Pred → Option (List (FieldName × AtomVal))
  | .tt => some []
  | .ff => some []
  | .symEq f s => some [(f, .sym s)]
  | .digEq f d => some [(f, .dig d)]
  | .symMemberOf f set => some (set.map (fun s => (f, AtomVal.sym s)))
  | .and l r =>
      match predAtoms? l, predAtoms? r with
      | some A, some B => some (A ++ B)
      | _, _ => none
  | .or l r =>
      match predAtoms? l, predAtoms? r with
      | some A, some B => some (A ++ B)
      | _, _ => none
  | .not p => predAtoms? p
  | _ => none

/-- `symMemberOf`'s eval as a pin-read disjunction (the rewrite that puts it in the vocabulary). -/
theorem eval_symMemberOf_any (f : FieldName) (set : List Nat) (o n : Value) :
    Pred.eval (.symMemberOf f set) o n = set.any (fun s => n.symField f == some s) := by
  simp only [Pred.eval]
  cases h : n.symField f with
  | none =>
      induction set with
      | nil => rfl
      | cons s rest ih => simp only [List.any_cons]; rw [← ih]; rfl
  | some x =>
      induction set with
      | nil => rfl
      | cons s rest ih =>
          simp only [List.any_cons, List.contains_cons, Option.some_beq_some] at *
          rw [ih]

/-- Member-restricted `any` congruence (`List.any_congr` needs GLOBAL pointwise agreement). -/
private theorem anyCongrMem {α : Type _} {l : List α} {p q : α → Bool}
    (h : ∀ a ∈ l, p a = q a) : l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.any_cons]
      rw [h x (List.mem_cons.mpr (Or.inl rfl)),
          ih (fun a ha => h a (List.mem_cons.mpr (Or.inr ha)))]

/-- **`predAtoms?_reads`** — the leaf-truth factoring through pins: when `predAtoms? φ = some A`,
two frames agreeing on every pin of `A` get the same verdict from `φ`. (The general-leaf analogue
of `leaf_braceP` determining `braceP`'s truth.) -/
theorem predAtoms?_reads : ∀ (φ : Pred) {A : List (FieldName × AtomVal)},
    predAtoms? φ = some A →
    ∀ {a b : Value}, (∀ p ∈ A, atomReads a p.1 p.2 = atomReads b p.1 p.2) →
      leaf φ a = leaf φ b
  | .tt, _, _, _, _, _ => rfl
  | .ff, _, _, _, _, _ => rfl
  | .symEq f s, A, h, a, b, hab => by
      simp only [predAtoms?, Option.some.injEq] at h
      subst h
      have := hab (f, .sym s) (List.mem_singleton.mpr rfl)
      simpa only [PredRE.leaf, Pred.eval, atomReads] using this
  | .digEq f d, A, h, a, b, hab => by
      simp only [predAtoms?, Option.some.injEq] at h
      subst h
      have := hab (f, .dig d) (List.mem_singleton.mpr rfl)
      simpa only [PredRE.leaf, Pred.eval, atomReads] using this
  | .symMemberOf f set, A, h, a, b, hab => by
      simp only [predAtoms?, Option.some.injEq] at h
      subst h
      simp only [PredRE.leaf, eval_symMemberOf_any]
      apply anyCongrMem
      intro s hs
      have := hab (f, .sym s) (List.mem_map.mpr ⟨s, hs, rfl⟩)
      simpa only [atomReads] using this
  | .and l r, A, h, a, b, hab => by
      simp only [predAtoms?] at h
      cases hl : predAtoms? l with
      | none => rw [hl] at h; exact absurd h (by simp)
      | some Al =>
        cases hr : predAtoms? r with
        | none => rw [hl, hr] at h; exact absurd h (by simp)
        | some Ar =>
          rw [hl, hr, Option.some.injEq] at h
          subst h
          have ihl := predAtoms?_reads l hl
            (fun p hp => hab p (List.mem_append.mpr (Or.inl hp)))
          have ihr := predAtoms?_reads r hr
            (fun p hp => hab p (List.mem_append.mpr (Or.inr hp)))
          simp only [PredRE.leaf, Pred.eval] at ihl ihr ⊢
          rw [ihl, ihr]
  | .or l r, A, h, a, b, hab => by
      simp only [predAtoms?] at h
      cases hl : predAtoms? l with
      | none => rw [hl] at h; exact absurd h (by simp)
      | some Al =>
        cases hr : predAtoms? r with
        | none => rw [hl, hr] at h; exact absurd h (by simp)
        | some Ar =>
          rw [hl, hr, Option.some.injEq] at h
          subst h
          have ihl := predAtoms?_reads l hl
            (fun p hp => hab p (List.mem_append.mpr (Or.inl hp)))
          have ihr := predAtoms?_reads r hr
            (fun p hp => hab p (List.mem_append.mpr (Or.inr hp)))
          simp only [PredRE.leaf, Pred.eval] at ihl ihr ⊢
          rw [ihl, ihr]
  | .not p, A, h, a, b, hab => by
      have ih := predAtoms?_reads p h hab
      simp only [PredRE.leaf, Pred.eval] at ih ⊢
      rw [ih]

/-! ## §6 The cover construction — one candidate per choice of at-most-one pin per field. -/

/-- The pins mentioned at field `f`. -/
def atomsAt (A : List (FieldName × AtomVal)) (f : FieldName) : List AtomVal :=
  (A.filter (fun p => p.1 == f)).map (·.2)

/-- The distinct mentioned fields. -/
def atomFields (A : List (FieldName × AtomVal)) : List FieldName := (A.map (·.1)).dedup

/-- The pin (if any) that frame `a` realizes at field `f` — at most one can be realized
(`atomReads_functional`), and `find?` selects it. -/
def selectAt (A : List (FieldName × AtomVal)) (a : Value) (f : FieldName) : Option AtomVal :=
  (atomsAt A f).find? (fun v => atomReads a f v)

/-- The restriction of frame `a` to the mentioned pins: keep, per mentioned field, exactly the
pinned value `a` realizes there. A FINITE record with the same pin behavior as `a`
(`atomReads_restrict`) — tier 0's witness shape, generalized. -/
def restrictFrame (A : List (FieldName × AtomVal)) (a : Value) : Value :=
  .record ((atomFields A).filterMap (fun f => (selectAt A a f).map (fun v => (f, v.toValue))))

/-- The candidate frames: one record per choice of at-most-one mentioned pin per mentioned field
(a `List.sections` product). Finite, computable, and containing `restrictFrame A a` for EVERY `a`. -/
def atomCands (A : List (FieldName × AtomVal)) : List Value :=
  (((atomFields A).map
      (fun f => (none :: (atomsAt A f).map some).map (fun o => (f, o)))).sections).map
    (fun ch => .record (ch.filterMap (fun p => p.2.map (fun v => (p.1, v.toValue)))))

/-- Field lookup on a choice-built record: with distinct fields, reading `f` returns exactly the
choice at `f`. -/
theorem field_ofChoices {g : FieldName → Option AtomVal} :
    ∀ {fs : List FieldName}, fs.Nodup → ∀ {f : FieldName}, f ∈ fs →
      (Value.record (fs.filterMap
          (fun x => (g x).map (fun v => (x, v.toValue))))).field f
        = (g f).map AtomVal.toValue := by
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
            simp only [Value.field, Option.map_none]
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

theorem restrictFrame_field {A : List (FieldName × AtomVal)} {a : Value} {f : FieldName}
    (hf : f ∈ atomFields A) :
    (restrictFrame A a).field f = (selectAt A a f).map AtomVal.toValue :=
  field_ofChoices (List.nodup_dedup _) hf

/-- **`atomReads_restrict`** — the restriction realizes EXACTLY the pins `a` realizes: on every
mentioned pin, `restrictFrame A a` and `a` agree. (Both directions of the case split ride
`atomReads_functional` — the one-value-per-field exclusivity.) -/
theorem atomReads_restrict {A : List (FieldName × AtomVal)} {a : Value} {f : FieldName}
    {v : AtomVal} (hfv : (f, v) ∈ A) :
    atomReads (restrictFrame A a) f v = atomReads a f v := by
  have hf : f ∈ atomFields A :=
    List.mem_dedup.mpr (List.mem_map.mpr ⟨(f, v), hfv, rfl⟩)
  have hv : v ∈ atomsAt A f := by
    simp only [atomsAt, List.mem_map, List.mem_filter]
    exact ⟨(f, v), ⟨hfv, by simp⟩, rfl⟩
  cases hsel : selectAt A a f with
  | none =>
      have h1 : atomReads (restrictFrame A a) f v = false := by
        rw [Bool.eq_false_iff]
        intro htrue
        rw [atomReads_iff_field, restrictFrame_field hf, hsel] at htrue
        simp at htrue
      have h2 : atomReads a f v = false := by
        rw [Bool.eq_false_iff]
        exact List.find?_eq_none.mp hsel v hv
      rw [h1, h2]
  | some u =>
      have hu : atomReads a f u = true := List.find?_some hsel
      by_cases huv : u = v
      · subst huv
        rw [hu, atomReads_iff_field, restrictFrame_field hf, hsel]
        rfl
      · have h2 : atomReads a f v = false := atomReads_functional hu huv
        have h1 : atomReads (restrictFrame A a) f v = false := by
          rw [Bool.eq_false_iff]
          intro htrue
          rw [atomReads_iff_field, restrictFrame_field hf, hsel] at htrue
          simp only [Option.map_some, Option.some.injEq] at htrue
          exact huv (AtomVal.toValue_inj htrue)
        rw [h1, h2]

/-- The restriction IS one of the enumerated candidates (membership in the `sections` product). -/
theorem restrictFrame_mem_atomCands (A : List (FieldName × AtomVal)) (a : Value) :
    restrictFrame A a ∈ atomCands A := by
  apply List.mem_map.mpr
  refine ⟨(atomFields A).map (fun f => (f, selectAt A a f)), ?_, ?_⟩
  · apply List.mem_sections.mpr
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    apply List.forall₂_same.mpr
    intro f _
    simp only [List.mem_map]
    refine ⟨selectAt A a f, ?_, rfl⟩
    cases hsel : selectAt A a f with
    | none => exact List.mem_cons.mpr (Or.inl rfl)
    | some u =>
        exact List.mem_cons.mpr (Or.inr
          (List.mem_map.mpr ⟨u, List.mem_of_find?_eq_some hsel, rfl⟩))
  · simp only [List.filterMap_map]
    rfl

/-- **`coverOfAtoms`** — the assembled `MintermCover`: for any leaf list `L` whose members' pin
sets sit inside `A`, the enumerated `atomCands A` cover every minterm — the covering witness for
frame `a` is `restrictFrame A a`, whose signature matches `a`'s by `predAtoms?_reads` +
`atomReads_restrict`. -/
def coverOfAtoms (A : List (FieldName × AtomVal)) (L : List Pred)
    (hL : ∀ φ ∈ L, ∃ Aφ, predAtoms? φ = some Aφ ∧ Aφ ⊆ A) : MintermCover L where
  cands := atomCands A
  covers a := by
    refine ⟨restrictFrame A a, restrictFrame_mem_atomCands A a, ?_⟩
    apply List.map_inj_left.mpr
    intro φ hφ
    obtain ⟨Aφ, hAφ, hsub⟩ := hL φ hφ
    exact predAtoms?_reads φ hAφ (fun p hp => atomReads_restrict (hsub hp))

/-! ## §7 The general fragment as a type, and the assembled decisions. -/

/-- Fold `predAtoms?` over a leaf list (fails closed: one uncovered leaf fails the whole list). -/
def atomsOfLeaves? : List Pred → Option (List (FieldName × AtomVal))
  | [] => some []
  | φ :: rest =>
      match predAtoms? φ, atomsOfLeaves? rest with
      | some A, some B => some (A ++ B)
      | _, _ => none

theorem atomsOfLeaves?_spec : ∀ {l : List Pred} {A : List (FieldName × AtomVal)},
    atomsOfLeaves? l = some A → ∀ φ ∈ l, ∃ Aφ, predAtoms? φ = some Aφ ∧ Aφ ⊆ A := by
  intro l
  induction l with
  | nil => intro A _ φ hφ; simp at hφ
  | cons ψ rest ih =>
      intro A h φ hφ
      simp only [atomsOfLeaves?] at h
      cases hψ : predAtoms? ψ with
      | none => rw [hψ] at h; exact absurd h (by simp)
      | some Aψ =>
        cases hrest : atomsOfLeaves? rest with
        | none => rw [hψ, hrest] at h; exact absurd h (by simp)
        | some B =>
          rw [hψ, hrest, Option.some.injEq] at h
          subst h
          rcases List.mem_cons.mp hφ with rfl | hφ'
          · exact ⟨Aψ, hψ, fun x hx => List.mem_append.mpr (Or.inl hx)⟩
          · obtain ⟨Aφ, hA, hsub⟩ := ih hrest φ hφ'
            exact ⟨Aφ, hA, fun x hx => List.mem_append.mpr (Or.inr (hsub hx))⟩

theorem atomsOfLeaves?_isSome : ∀ {l : List Pred},
    (atomsOfLeaves? l).isSome = true ↔ ∀ φ ∈ l, (predAtoms? φ).isSome = true := by
  intro l
  induction l with
  | nil => simp [atomsOfLeaves?]
  | cons ψ rest ih =>
      simp only [atomsOfLeaves?]
      cases hψ : predAtoms? ψ with
      | none => simp [hψ]
      | some Aψ =>
        cases hrest : atomsOfLeaves? rest with
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

/-- **`IsSymbolic R`** — the general DECIDABLE-LEAF fragment (computable membership check): every
leaf of `R` is built from `tt`/`ff`/`symEq`/`digEq`/`symMemberOf` under `and`/`or`/`not`. This is
the fragment of the guards the templater actually writes; `IsDeployed` guards (leaves in `braceP`'s
algebra) are instances. -/
def IsSymbolic (R : PredRE) : Prop := (atomsOfLeaves? (leavesOf R)).isSome = true

/-- The fragment as a TYPE (the general `DeployedRE`). -/
abbrev SymbolicRE : Type := {R : PredRE // IsSymbolic R}

/-- A cover for `R`'s own leaf set, from a computed pin set. -/
def coverOfSymbolic {R : PredRE} {A : List (FieldName × AtomVal)}
    (h : atomsOfLeaves? (leavesOf R) = some A) : MintermCover (leavesOf R) :=
  coverOfAtoms A (leavesOf R) (atomsOfLeaves?_spec h)

/-- **`predRE_emptiness_decidable_general`** — THE GENERAL DECISION (residual 2, closed): unbounded
language nonemptiness over the infinite `Value` alphabet, `Decidable (∃ w, derives w R = true)`,
for EVERY decidable-leaf guard — arbitrary boolean combinations of `symEq`/`digEq`/`symMemberOf`/
`tt`/`ff` over any fields and symbols, not just `braceP`'s algebra. Per-`R` minterm witnesses
(`coverOfSymbolic`) replace the global `candidates`. Computable, not `Classical.dec`. -/
def predRE_emptiness_decidable_general (R : SymbolicRE) :
    Decidable (∃ w, derives w R.val = true) :=
  match h : atomsOfLeaves? (leavesOf R.val) with
  | some _ => predRENonemptyDecidableG (coverOfSymbolic h) (symbolicOver_leavesOf R.val)
  | none => absurd R.property (by rw [IsSymbolic, h]; simp)

instance instDecidableNonemptySymbolic (R : SymbolicRE) :
    Decidable (∃ w, derives w R.val = true) :=
  predRE_emptiness_decidable_general R

/-- The fragment is closed under `symDiff` (leaf sets concatenate under `alt`/`inter`/`neg`), so
EQUIVALENCE transports. -/
theorem isSymbolic_symDiff {R S : PredRE} (hR : IsSymbolic R) (hS : IsSymbolic S) :
    IsSymbolic (symDiff R S) := by
  rw [IsSymbolic, atomsOfLeaves?_isSome] at *
  intro φ hφ
  simp only [symDiff, leavesOf, List.mem_append] at hφ
  rcases hφ with (h | h) | (h | h)
  · exact hR φ h
  · exact hS φ h
  · exact hR φ h
  · exact hS φ h

/-- **`predRE_equivalence_decidable_general`** — the equivalence corollary on the GENERAL fragment:
decidable language equivalence `∀ w, derives w R = derives w S` for arbitrary decidable-leaf
guards, via emptiness of the symmetric difference (which stays in the fragment). Generalizes
`predRE_equivalence_decidable` off the braceP algebra. -/
def predRE_equivalence_decidable_general (R S : SymbolicRE) :
    Decidable (∀ w, derives w R.val = derives w S.val) :=
  letI : Decidable (∃ w, derives w (symDiff R.val S.val) = true) :=
    predRE_emptiness_decidable_general ⟨symDiff R.val S.val,
      isSymbolic_symDiff R.property S.property⟩
  decidable_of_iff _ (langEq_iff_symDiff_empty R.val S.val).symm

instance instDecidableLangEqSymbolic (R S : SymbolicRE) :
    Decidable (∀ w, derives w R.val = derives w S.val) :=
  predRE_equivalence_decidable_general R S

/-! ## §8 Non-vacuity — the general decision RUNS on guards OUTSIDE braceP's algebra.

The gate: kernel-evaluated verdicts on `symEq`-based guards over fields/symbols `braceP` cannot
express, including a multi-field `sym`+`dig` guard and the UNSAT-minterm canary (two different
symbols pinned to ONE field — the interacting-pin case the braceP tower could not even state). -/

section Guards

open Dregg2.Crypto.HandlebarsGuarded (braceP noDoubleBraceRE)

/-- A guard leaf over a field/symbol outside `braceP`'s algebra. -/
def roleP : Pred := .symEq "role" 3

-- The pin set of `sym roleP`, computed.
#guard atomsOfLeaves? (leavesOf (.sym roleP)) = some [("role", AtomVal.sym 3)]

/-- **The generalization is STRICT**: `roleP` is NOT `LeafDeployed` — `braceP` cannot distinguish
`{role ↦ sym 3}` from `{}`, but `roleP` does — so the braceP tower's decision does not apply to
this guard, and the general one below does. -/
theorem roleP_not_leafDeployed : ¬ LeafDeployed roleP := fun h => by
  have := h (Value.record [("role", .sym 3)]) (Value.record []) rfl
  exact Bool.noConfusion this

/-- The per-R candidates for the `roleP` guard: the two minterm witnesses `{role ↦ sym 3}` / `{}`,
ENUMERATED by the cover construction (not hard-coded). -/
def roleCands : List Value := atomCands [("role", AtomVal.sym 3)]

#guard roleCands.length = 2

-- SAT: the general bounded decision decides the `roleP` guard NONEMPTY by kernel evaluation —
-- a guard outside braceP's algebra, decided with per-R minterm witnesses.
#guard nonemptyWithinG roleCands 1 (.sym roleP) = true

/-- ...and COMPLETE both ways through the general bounded iff: an accepting word of length ≤ 1
genuinely exists (concluded THROUGH the decision, kernel-evaluated). -/
example : ∃ w, w.length ≤ 1 ∧ derives w (.sym roleP) = true :=
  (nonemptyWithinG_iff_bounded (coverOfSymbolic (R := .sym roleP) rfl)
    (symbolicOver_leavesOf _) (n := 1)).mp rfl

/-- The UNSAT-MINTERM canary: TWO different symbols pinned to ONE field — the interacting-pin case
(`SatOracle.lean`'s header names `.and (.symEq f 0) (.symEq f 1)` as exactly what single-leaf
witnesses cannot decide). No frame satisfies both, the cover enumerates no witness for the
contradictory minterm, and the decision returns a COMPLETE false. -/
def roleContra : PredRE := .inter (.sym (.symEq "role" 3)) (.sym (.symEq "role" 4))

def roleContraCands : List Value := atomCands [("role", AtomVal.sym 3), ("role", AtomVal.sym 4)]

#guard roleContraCands.length = 3

-- UNSAT: kernel-evaluated FALSE...
#guard nonemptyWithinG roleContraCands 3 roleContra = false

/-- ...and it is a COMPLETE verdict: NO accepting word of length ≤ 3 exists (not merely "none
found") — through the general bounded iff. -/
theorem roleContra_no_short_word :
    ¬ ∃ w, w.length ≤ 3 ∧ derives w roleContra = true := by
  rw [← nonemptyWithinG_iff_bounded (coverOfSymbolic (R := roleContra) rfl)
        (symbolicOver_leavesOf _) (n := 3)]
  decide

/-- MULTI-FIELD, MULTI-SORT: a `sym` pin on one field concatenated with a `dig` pin on another —
two interacting fields, both sorts of typed reader. Nothing in the braceP tower could state this. -/
def abRE : PredRE := .cat (.sym (.symEq "a" 1)) (.sym (.digEq "b" 2))

def abCands : List Value := atomCands [("a", AtomVal.sym 1), ("b", AtomVal.dig 2)]

-- The product cover: (none | sym 1) × (none | dig 2) — four candidate frames.
#guard abCands.length = 4

-- SAT at length 2 (one frame per pin), kernel-evaluated through the general search.
#guard nonemptyWithinG abCands 2 abRE = true

example : ∃ w, w.length ≤ 2 ∧ derives w abRE = true :=
  (nonemptyWithinG_iff_bounded (coverOfSymbolic (R := abRE) rfl)
    (symbolicOver_leavesOf _) (n := 2)).mp rfl

/-! ### The FULL `n`-free assembled instance, fired end to end.

As in `SymbolicDecision.lean`, only `ε` (bound 4) is within kernel reach for the `n`-free composite;
the guards above are the tractable bounded resolution of the same decision. -/

def epsSymbolic : SymbolicRE := ⟨PredRE.ε, rfl⟩

/-- The WHOLE general assembly — fragment check, per-R cover enumeration, pigeonhole reduction,
bounded search — fired through `decide` by kernel evaluation. -/
theorem general_decision_fires_eps :
    (@decide _ (predRE_emptiness_decidable_general epsSymbolic)) = true := by rfl

#guard @decide _ (predRE_emptiness_decidable_general epsSymbolic)

example : ∃ w, derives w PredRE.ε = true :=
  @of_decide_eq_true _ (predRE_emptiness_decidable_general epsSymbolic)
    general_decision_fires_eps

/-! ### The braceP fragment falls out as an INSTANCE. -/

-- The real deployed templater guard is in the general fragment (computed membership: its leaves
-- `tt`/`braceP` are all pin-representable)...
#guard (atomsOfLeaves? (leavesOf noDoubleBraceRE)).isSome

/-- ...so the actual templater guard is decided by the GENERAL instance — the braceP tower's
coverage, recovered without `braceP`-specific machinery. -/
def noDoubleBraceSymbolic : SymbolicRE := ⟨noDoubleBraceRE, by rw [IsSymbolic]; rfl⟩

/-- The equivalence decision's FALSE pole on the general fragment, proven directly (kernel-cheap):
`ε` and the `roleP` guard disagree on `[]`. -/
theorem eps_not_equiv_roleP :
    ¬ ∀ w, derives w PredRE.ε = derives w (.sym roleP) := fun h => Bool.noConfusion (h [])

-- ...and its tractable-resolution witness through the general search: the symmetric difference is
-- nonempty already at depth 0 (they disagree on the empty word).
#guard nonemptyWithinG roleCands 0 (symDiff PredRE.ε (.sym roleP)) = true

end Guards

/-! ## Axiom hygiene — the generalized tower is kernel-clean. -/

#assert_all_clean [
  der_factors_over, der_symbolicOver, symbolicOver_leavesOf,
  MintermCover.canon_mem, MintermCover.leafSig_canon,
  reachableWithinG_sound', reachableWithinG_complete,
  derList_factors_canon, nonemptyWithinG_complete, nonemptyWithinG_iff_bounded,
  satStepG_subset_step, reachableWithinG_mem_steps, reachableWithinG_subset_pieces,
  exists_sim_prefix_pairG, pumpDownG,
  nonempty_iff_nonemptyWithinG_bound, predRENonemptyDecidableG, nonemptyWithinG_bound_complete,
  atomReads_iff_field, atomReads_functional, predAtoms?_reads,
  field_ofChoices, atomReads_restrict, restrictFrame_mem_atomCands,
  atomsOfLeaves?_spec, isSymbolic_symDiff,
  predRE_emptiness_decidable_general, predRE_equivalence_decidable_general,
  roleP_not_leafDeployed, roleContra_no_short_word, general_decision_fires_eps,
  eps_not_equiv_roleP
]

end Dregg2.Crypto.Deriv
