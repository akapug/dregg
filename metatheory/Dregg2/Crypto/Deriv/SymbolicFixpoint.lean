/-
# Dregg2.Crypto.Deriv.SymbolicFixpoint — the ADAPTIVE `≅`-fixpoint: symbolic emptiness made
RUNNABLE, consuming `AciComplete.simDecide` (previously consumed by NOTHING).

## The problem this closes

`predRE_emptiness_decidable` / `predRE_emptiness_decidable_general` are PROVEN `n`-free decisions,
but they decide at depth `emptinessBound R = |⊕(pieces R)|` — a POWERSET bound that kernel
evaluation cannot reach except for `ε` (bound 4). `SymbolicDecision.lean` §4 had to leave the
`false` verdict on the empty machine as a HYPOTHESIS (`contradiction_empty_of_bound_false`), and
even the BOUND ITSELF is intractable to compute (`⊕` materializes the powerset list).

The audit-named fix (docs/DESIGN-symbolic-decidability-status.md): dedup the reachable derivative
frontier UP TO `≅`, and stop when it saturates. The `≅`-class count is finite
(`satStep_reachable_finite` / `reachableWithinG_subset_pieces`) and SMALL in practice (a handful of
states), so a worklist that adds a derivative only when it is NOT `simDecide`-similar to an
already-seen state closes in a few pops — where the bound-based search needed `3^15+` residuals.

## What is built

* **`reachFixAux`** — the worklist: pop `s`; if `simDecide u s` for some seen `u`, DISCARD (the
  `≅`-dedup, `AciComplete.simDecide` finally consumed); else move `s` to `seen` and push its
  `satStepG` successors. Fuel-indexed (structural termination), returning `none` on fuel
  exhaustion and `some seen` on SATURATION (empty worklist).
* **`reachFix` / `emptyFix`** — the fixpoint and the emptiness verdict off it (`some true` =
  proven empty, `some false` = proven nonempty, `none` = fuel ran out).
* **Correctness** (`reachFix_any_null_iff`, `emptyFix_some_iff`): on saturation, a nullable seen
  state ⟺ a real accepting word — of ANY length, over the INFINITE `Value` alphabet.
  SOUNDNESS: every seen state is a concrete `derList w R` (`reachFixAux_sound`), so a nullable one
  exhibits its word. COMPLETENESS: the saturated `seen` is `satStepG`-closed UP TO `≅`
  (`reachFixAux_closed`), so by the der-congruence `sim_der` every cover-word's residual is
  `≅`-represented in `seen`, and `sim_null` (nullability is `≅`-INVARIANT) guarantees the dedup
  never dropped an accepting state. This is exactly why `≅`-dedup preserves the answer.
* **`predRE_emptiness_decidable_fix`** — the RUNNABLE `n`-free decision on
  `SymbolicRE ∧ RigidFull`: fixpoint first; on fuel exhaustion it falls back to the proven
  bound-based `predRENonemptyDecidableG`, so the instance is TOTAL and correct at EVERY fuel.
* **The `#guard`s fire on non-`ε` machines** — the deliverable the bound-based tower could not
  produce: `rolePlus` (a `symEq`-based cat/star guard) kernel-decides NONEMPTY, and `roleContra`
  (the contradictory machine, `emptinessBound ≥ 15` ⇒ `3^15+` residuals for the bounded search)
  kernel-decides EMPTY at ALL lengths — through `decide`, in a handful of worklist pops.
  `roleContra_empty` lands the very verdict-shape `SymbolicDecision.lean` left hypothetical.

## The `RigidFull`-reachability bridge (the CHECK, answered)

`simDecide` decides `≅` only when its LEFT argument is `RigidFull` (every atomic leaf
`predBEq`-decidable). Two facts make the fixpoint sound:

1. **Reachable derivatives of a `RigidFull` root STAY `RigidFull`** (`rigidRE_der` /
   `rigidRE_derList`, proven below): `der` never invents a leaf — it propagates the existing ones
   and introduces only `bot = sym .ff`, which is rigid. So rigidity is checked ONCE, at the root.
2. **A `SymbolicRE` root need NOT be `RigidFull`** — this is the honest fragment boundary, at the
   ROOT not at the derivatives: `IsSymbolic` admits `symMemberOf` leaves, on which `predBEq`
   fail-closes (`AciComplete`'s residual). The `not`/`and`/`or` compounds are NO LONGER outside:
   `predBEq` descends them structurally (AciNormal, 07-19 widening), so e.g. `contradictionRE`'s
   `¬braceP` leaf is now rigid and `contradictionRE` sits INSIDE the runnable fragment
   (`#guard`ed below). The runnable fragment is therefore `IsSymbolic ∧ RigidFull` = leaves in
   `tt/ff/symEq/digEq` closed under `not`/`and`/`or` — and it widens further exactly as `predBEq`
   is extended over `symMemberOf` (mechanical; every theorem here transports unchanged, as
   `AciComplete`'s residual already states for its own).

## Termination, scoped honestly

Termination of the WORKLIST is structural (fuel). The instance is total and correct at every fuel
(the fallback arm is the already-proven bound-based decision, never `Classical.dec`). What is NOT
proven here: that fuel `(emptinessBound R + 1) * (|V| + 1) + 1` always suffices — the pigeonhole
"pairwise-non-`≅` seen states embed into `⊕(pieces R)` up to `≅`, so `|seen| ≤ emptinessBound R`"
is the named missing counting step (its ingredients, `reachableWithinG_subset_pieces` +
`simDecide_correct`, are both in hand). Saturation at SMALL fuel on the concrete machines is
instead kernel-WITNESSED by the `#guard`s — which is the operational point: the adaptive fixpoint
stops when the `≅`-frontier closes, not at the astronomical bound.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.SymbolicMinterms
import Dregg2.Crypto.Deriv.AciComplete

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open PredRE (der null derives leaf bot Sim sim_der sim_null derList derives_eq_null_derList
  simDecide simDecide_correct RigidFull rigidRE)

/-! ## §1 The rigidity bridge — reachable derivatives of a rigid root stay rigid.

This is the CHECK the fixpoint needs: `simDecide`'s correctness requires `RigidFull` on the left,
and every left argument the worklist ever passes is a reachable derivative. `der` propagates the
existing leaves and introduces only `bot = sym .ff` (rigid), so the whole reachable state space of
a `RigidFull` root is `RigidFull` — rigidity is a ROOT-ONLY obligation. -/

/-- **`rigidRE_der`** — the bridge lemma: the concrete derivative of a rigid regex is rigid.
Structural induction on `R`; `der`'s clauses only recombine subterms and introduce `ε`/`bot`. -/
theorem rigidRE_der (a : Value) : ∀ {R : PredRE}, rigidRE R = true → rigidRE (der a R) = true := by
  intro R
  induction R with
  | ε => intro _; rfl
  | sym φ =>
      intro _
      simp only [der]
      split <;> rfl
  | alt l r ihl ihr =>
      intro h
      simp only [rigidRE, Bool.and_eq_true] at h
      simp only [der, rigidRE, Bool.and_eq_true]
      exact ⟨ihl h.1, ihr h.2⟩
  | inter l r ihl ihr =>
      intro h
      simp only [rigidRE, Bool.and_eq_true] at h
      simp only [der, rigidRE, Bool.and_eq_true]
      exact ⟨ihl h.1, ihr h.2⟩
  | cat l r ihl ihr =>
      intro h
      simp only [rigidRE, Bool.and_eq_true] at h
      simp only [der]
      split
      · simp only [rigidRE, Bool.and_eq_true]
        exact ⟨⟨ihl h.1, h.2⟩, ihr h.2⟩
      · simp only [rigidRE, Bool.and_eq_true]
        exact ⟨ihl h.1, h.2⟩
  | star r ih =>
      intro h
      simp only [rigidRE] at h
      simp only [der, rigidRE, Bool.and_eq_true]
      exact ⟨ih h, h⟩
  | neg r ih =>
      intro h
      simp only [rigidRE] at h
      simp only [der, rigidRE]
      exact ih h

/-- Rigidity along a whole word: every `derList`-reachable residual of a rigid root is rigid —
so `simDecide` decides `≅` on the ENTIRE reachable state space of a `RigidFull` root. -/
theorem rigidRE_derList :
    ∀ (w : List Value) {R : PredRE}, rigidRE R = true → rigidRE (derList w R) = true := by
  intro w
  induction w with
  | nil => intro R h; exact h
  | cons a as ih => intro R h; exact ih (rigidRE_der a h)

/-- One `satStepG` layer preserves rigidity (the shape the worklist consumes). -/
theorem rigid_satStepG {V : List Value} {s t : PredRE} (hs : rigidRE s = true)
    (ht : t ∈ satStepG V s) : rigidRE t = true := by
  simp only [satStepG, List.mem_map] at ht
  obtain ⟨a, _, rfl⟩ := ht
  exact rigidRE_der a hs

/-! ## §2 The worklist fixpoint — frontier dedup UP TO `≅` via `simDecide`. -/

/-- **`seenSim seen s`** — is `s` already represented in `seen` up to `≅`? THE consumption site of
`AciComplete.simDecide`: on rigid states a `true` here is a real `Sim` (`simDecide_correct`). -/
def seenSim (seen : List PredRE) (s : PredRE) : Bool := seen.any (fun u => simDecide u s)

/-- **`reachFixAux`** — the worklist: `none` = fuel exhausted; `some seen` = SATURATED (the pending
list emptied, so `seen` is `satStepG`-closed up to `≅`). Adds a popped state only when it is NOT
`≅`-represented — the adaptive dedup that replaces the `3^n` undeduped frontier growth. -/
def reachFixAux (V : List Value) : Nat → List PredRE → List PredRE → Option (List PredRE)
  | 0, _, _ => none
  | _ + 1, seen, [] => some seen
  | fuel + 1, seen, s :: pending =>
      if seenSim seen s = true then reachFixAux V fuel seen pending
      else reachFixAux V fuel (seen ++ [s]) (pending ++ satStepG V s)

/-- **`reachFix V fuel R`** — the `≅`-deduped reachable frontier of `R` under the sat-filtered
step `satStepG V`, when it saturates within `fuel` pops. -/
def reachFix (V : List Value) (fuel : Nat) (R : PredRE) : Option (List PredRE) :=
  reachFixAux V fuel [] [R]

/-- **`emptyFix V fuel R`** — the adaptive emptiness verdict: `some true` = no reachable
`≅`-class is nullable (language EMPTY, all lengths), `some false` = one is (NONEMPTY, with a real
word behind it), `none` = did not saturate in `fuel`. -/
def emptyFix (V : List Value) (fuel : Nat) (R : PredRE) : Option Bool :=
  (reachFix V fuel R).map (fun seen => !(seen.any null))

/-! ## §3 SOUNDNESS — every state the worklist ever holds is a real reachable derivative.

Stated for an arbitrary `satStepG`-closed predicate `P`, then instantiated at
`P s := ∃ w, derList w R = s`. -/

/-- Any `satStepG`-preserved predicate holding on the initial `seen`/`pending` holds on the
saturated output. -/
theorem reachFixAux_sound {V : List Value} {P : PredRE → Prop}
    (hstep : ∀ s, P s → ∀ t ∈ satStepG V s, P t) :
    ∀ (fuel : Nat) (seen pending out : List PredRE),
      reachFixAux V fuel seen pending = some out →
      (∀ s ∈ seen, P s) → (∀ s ∈ pending, P s) →
      ∀ s ∈ out, P s := by
  intro fuel
  induction fuel with
  | zero =>
      intro seen pending out h _ _
      simp [reachFixAux] at h
  | succ fuel ih =>
      intro seen pending out h hseen hpend
      cases pending with
      | nil =>
          simp only [reachFixAux] at h
          obtain rfl : seen = out := Option.some.inj h
          exact hseen
      | cons s ps =>
          simp only [reachFixAux] at h
          split at h
          · exact ih seen ps out h hseen (fun x hx => hpend x (List.mem_cons_of_mem _ hx))
          · have hPs : P s := hpend s (List.mem_cons_self ..)
            refine ih _ _ out h ?_ ?_
            · intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hseen x hx
              · rw [List.mem_singleton.mp hx]; exact hPs
            · intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hpend x (List.mem_cons_of_mem _ hx)
              · exact hstep s hPs x hx

/-! ## §4 COMPLETENESS — the saturated frontier is `satStepG`-closed up to `≅`, and represents
every state it ever discarded.

The dedup invariant: a discarded state was `simDecide`-similar to a seen one, and (on rigid
states) that is a real `Sim` — so representation transports through `Sim.trans`. This is the ONLY
place `simDecide_correct` fires, and it is what makes the worklist a fixpoint UP TO `≅` rather
than a lossy heuristic. -/

/-- The master invariant: from a saturated run, (1) everything initially held is `≅`-represented
in the output, and (2) the output is `satStepG`-closed up to `≅`. -/
theorem reachFixAux_closed {V : List Value} :
    ∀ (fuel : Nat) (seen pending out : List PredRE),
      reachFixAux V fuel seen pending = some out →
      (∀ s ∈ seen, rigidRE s = true) →
      (∀ s ∈ pending, rigidRE s = true) →
      (∀ s ∈ seen, ∀ t ∈ satStepG V s, ∃ u, (u ∈ seen ∨ u ∈ pending) ∧ u ≅ t) →
      (∀ t, (t ∈ seen ∨ t ∈ pending) → ∃ u ∈ out, u ≅ t) ∧
      (∀ s ∈ out, ∀ t ∈ satStepG V s, ∃ u ∈ out, u ≅ t) := by
  intro fuel
  induction fuel with
  | zero =>
      intro seen pending out h _ _ _
      simp [reachFixAux] at h
  | succ fuel ih =>
      intro seen pending out h hseen hpend hclosed
      cases pending with
      | nil =>
          simp only [reachFixAux] at h
          obtain rfl : seen = out := Option.some.inj h
          refine ⟨?_, ?_⟩
          · intro t ht
            rcases ht with ht | ht
            · exact ⟨t, ht, Sim.rfl⟩
            · cases ht
          · intro s hs t htm
            obtain ⟨u, hu, hsim⟩ := hclosed s hs t htm
            rcases hu with hu | hu
            · exact ⟨u, hu, hsim⟩
            · cases hu
      | cons s ps =>
          simp only [reachFixAux] at h
          split at h
          · -- DISCARD: `s` is `≅`-represented by a seen `u₀`; `simDecide_correct` makes it a `Sim`.
            next hss =>
            have hss' := hss
            unfold seenSim at hss'
            obtain ⟨u₀, hu₀, hdec⟩ := List.any_eq_true.mp hss'
            have hsim₀ : u₀ ≅ s := (simDecide_correct (hseen u₀ hu₀)).mp hdec
            have hpend' : ∀ x ∈ ps, rigidRE x = true := fun x hx =>
              hpend x (List.mem_cons_of_mem _ hx)
            have hclosed' : ∀ s' ∈ seen, ∀ t ∈ satStepG V s',
                ∃ u, (u ∈ seen ∨ u ∈ ps) ∧ u ≅ t := by
              intro s' hs' t htm
              obtain ⟨u, hu, hsim⟩ := hclosed s' hs' t htm
              rcases hu with hu | hu
              · exact ⟨u, Or.inl hu, hsim⟩
              · rcases List.mem_cons.mp hu with rfl | hu
                · exact ⟨u₀, Or.inl hu₀, Sim.trans hsim₀ hsim⟩
                · exact ⟨u, Or.inr hu, hsim⟩
            obtain ⟨h1, h2⟩ := ih seen ps out h hseen hpend' hclosed'
            refine ⟨?_, h2⟩
            intro t ht
            rcases ht with ht | ht
            · exact h1 t (Or.inl ht)
            · rcases List.mem_cons.mp ht with rfl | ht
              · obtain ⟨u', hu', hsim'⟩ := h1 u₀ (Or.inl hu₀)
                exact ⟨u', hu', Sim.trans hsim' hsim₀⟩
              · exact h1 t (Or.inr ht)
          · -- ADD: `s` enters `seen`; its successors enter the worklist (represented literally).
            next hss =>
            have hrigs : rigidRE s = true := hpend s (List.mem_cons_self ..)
            have hseen' : ∀ x ∈ seen ++ [s], rigidRE x = true := by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hseen x hx
              · rw [List.mem_singleton.mp hx]; exact hrigs
            have hpend' : ∀ x ∈ ps ++ satStepG V s, rigidRE x = true := by
              intro x hx
              rcases List.mem_append.mp hx with hx | hx
              · exact hpend x (List.mem_cons_of_mem _ hx)
              · exact rigid_satStepG hrigs hx
            have hclosed' : ∀ s' ∈ seen ++ [s], ∀ t ∈ satStepG V s',
                ∃ u, (u ∈ seen ++ [s] ∨ u ∈ ps ++ satStepG V s) ∧ u ≅ t := by
              intro s' hs' t htm
              rcases List.mem_append.mp hs' with hs' | hs'
              · obtain ⟨u, hu, hsim⟩ := hclosed s' hs' t htm
                rcases hu with hu | hu
                · exact ⟨u, Or.inl (List.mem_append.mpr (Or.inl hu)), hsim⟩
                · rcases List.mem_cons.mp hu with rfl | hu
                  · exact ⟨u, Or.inl (List.mem_append.mpr
                      (Or.inr (List.mem_singleton.mpr rfl))), hsim⟩
                  · exact ⟨u, Or.inr (List.mem_append.mpr (Or.inl hu)), hsim⟩
              · obtain rfl : s' = s := List.mem_singleton.mp hs'
                exact ⟨t, Or.inr (List.mem_append.mpr (Or.inr htm)), Sim.rfl⟩
            obtain ⟨h1, h2⟩ := ih _ _ out h hseen' hpend' hclosed'
            refine ⟨?_, h2⟩
            intro t ht
            rcases ht with ht | ht
            · exact h1 t (Or.inl (List.mem_append.mpr (Or.inl ht)))
            · rcases List.mem_cons.mp ht with rfl | ht
              · exact h1 t (Or.inl (List.mem_append.mpr
                  (Or.inr (List.mem_singleton.mpr rfl))))
              · exact h1 t (Or.inr (List.mem_append.mpr (Or.inl ht)))

/-- **`reachFix_represents`** — the payoff of closure + the der-congruence: EVERY residual of a
`V`-word is `≅`-represented in the saturated frontier. Induction along the word from the right;
each step is one `satStepG` edge transported through `sim_der`. -/
theorem reachFix_represents {V : List Value} {R : PredRE} {fuel : Nat} {seen : List PredRE}
    (hrig : rigidRE R = true)
    (hfix : reachFixAux V fuel [] [R] = some seen) :
    ∀ v : List Value, (∀ x ∈ v, x ∈ V) → ∃ u ∈ seen, u ≅ derList v R := by
  have hpendR : ∀ x ∈ [R], rigidRE x = true := by
    intro x hx
    rw [List.mem_singleton.mp hx]
    exact hrig
  obtain ⟨hrep, hclosure⟩ := reachFixAux_closed fuel [] [R] seen hfix
    (by intro x hx; cases hx) hpendR
    (by intro x hx; cases hx)
  have hbase : ∃ u ∈ seen, u ≅ R := hrep R (Or.inr (List.mem_singleton.mpr rfl))
  have hgen : ∀ (n : Nat) (v : List Value), v.length ≤ n → (∀ x ∈ v, x ∈ V) →
      ∃ u ∈ seen, u ≅ derList v R := by
    intro n
    induction n with
    | zero =>
        intro v hlen _
        have hv0 : v = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
        subst hv0
        exact hbase
    | succ n ihn =>
        intro v hlen hv
        rcases List.eq_nil_or_concat v with rfl | ⟨v', a, rfl⟩
        · exact hbase
        · simp only [List.concat_eq_append] at hv hlen ⊢
          have ha : a ∈ V := hv a (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
          have hv' : ∀ x ∈ v', x ∈ V := fun x hx => hv x (List.mem_append.mpr (Or.inl hx))
          have hlen' : v'.length ≤ n := by
            simp only [List.length_append, List.length_cons, List.length_nil] at hlen
            omega
          obtain ⟨u, hu, hsim⟩ := ihn v' hlen' hv'
          obtain ⟨u', hu', hsim'⟩ := hclosure u hu (der a u)
            (by simp only [satStepG, List.mem_map]; exact ⟨a, ha, rfl⟩)
          refine ⟨u', hu', ?_⟩
          rw [derList_append]
          exact Sim.trans hsim' (sim_der hsim a)
  intro v hv
  exact hgen v.length v (Nat.le_refl _) hv

/-! ## §5 The decision off the fixpoint — sound ∧ complete, all lengths, infinite alphabet. -/

/-- **`reachFix_any_null_iff`** — THE fixpoint decision theorem: on a saturated run over a minterm
cover, some seen state is nullable ⟺ `R` accepts some word (of ANY length). Forward = soundness
(the nullable state IS `derList w R`, its word in hand). Backward = completeness: canonicalize the
accepting word onto the cover (`derList_factors_canon`), `≅`-represent its residual
(`reachFix_represents`), and transport nullability through `sim_null` — the `≅`-dedup cannot drop
an accepting state BECAUSE nullability is `≅`-invariant. -/
theorem reachFix_any_null_iff {L : List Pred} (C : MintermCover L) {R : PredRE}
    {fuel : Nat} {seen : List PredRE}
    (hR : SymbolicOver L R) (hrig : RigidFull R)
    (hfix : reachFixAux C.cands fuel [] [R] = some seen) :
    seen.any null = true ↔ ∃ w, derives w R = true := by
  constructor
  · intro h
    obtain ⟨s, hs, hnull⟩ := List.any_eq_true.mp h
    have hP : ∃ w, derList w R = s := by
      refine reachFixAux_sound (P := fun s => ∃ w, derList w R = s) ?_ fuel [] [R] seen hfix
        ?_ ?_ s hs
      · rintro t ⟨w, rfl⟩ t' ht'
        simp only [satStepG, List.mem_map] at ht'
        obtain ⟨a, _, rfl⟩ := ht'
        exact ⟨w ++ [a], by rw [derList_append]; rfl⟩
      · intro x hx; cases hx
      · intro x hx
        rw [List.mem_singleton.mp hx]
        exact ⟨[], rfl⟩
    obtain ⟨w, hw⟩ := hP
    exact ⟨w, by rw [derives_eq_null_derList, hw]; exact hnull⟩
  · rintro ⟨w, hw⟩
    have hw' : derives (w.map C.canon) R = true := by
      rw [derives_eq_null_derList, ← derList_factors_canon C w hR, ← derives_eq_null_derList]
      exact hw
    have hcand : ∀ x ∈ w.map C.canon, x ∈ C.cands := by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, _, rfl⟩ := hx
      exact C.canon_mem y
    obtain ⟨u, hu, hsim⟩ := reachFix_represents hrig hfix (w.map C.canon) hcand
    refine List.any_eq_true.mpr ⟨u, hu, ?_⟩
    rw [sim_null hsim, ← derives_eq_null_derList]
    exact hw'

/-- **`emptyFix_some_iff`** — the `emptyFix` packaging: on saturation, `emptyFix = some false` ⟺
the language is NONEMPTY (and hence `some true` ⟺ empty at ALL lengths). -/
theorem emptyFix_some_iff {L : List Pred} (C : MintermCover L) {R : PredRE} {fuel : Nat}
    {b : Bool} (hR : SymbolicOver L R) (hrig : RigidFull R)
    (hfix : emptyFix C.cands fuel R = some b) :
    b = false ↔ ∃ w, derives w R = true := by
  unfold emptyFix reachFix at hfix
  cases hres : reachFixAux C.cands fuel [] [R] with
  | none =>
      rw [hres] at hfix
      simp at hfix
  | some seen =>
      rw [hres] at hfix
      obtain rfl : (!(seen.any null)) = b := Option.some.inj hfix
      have hiff := reachFix_any_null_iff C hR hrig hres
      cases hany : seen.any null with
      | true =>
          exact iff_of_true rfl (hiff.mp hany)
      | false =>
          refine iff_of_false (by simp) ?_
          intro hex
          rw [hiff.mpr hex] at hany
          exact Bool.noConfusion hany

/-! ## §6 The RUNNABLE `n`-free decision — fixpoint first, proven fallback on fuel exhaustion. -/

/-- **`predRE_emptiness_decidable_fix`** — the ADAPTIVE `n`-free emptiness decision on the
runnable fragment (`SymbolicRE` root that is also `RigidFull`): decide by the `≅`-fixpoint when it
saturates within `fuel`; fall back to the proven bound-based `predRENonemptyDecidableG` otherwise.
TOTAL and correct at every fuel; kernel-tractable exactly when the fixpoint saturates — which the
`#guard`s below witness on machines the bound-based decision could not touch. -/
def predRE_emptiness_decidable_fix (fuel : Nat) (R : SymbolicRE)
    (hrig : RigidFull R.val) :
    Decidable (∃ w, derives w R.val = true) :=
  match h : atomsOfLeaves? (leavesOf R.val) with
  | some _ =>
      match hfix : reachFixAux (coverOfSymbolic h).cands fuel [] [R.val] with
      | some seen =>
          decidable_of_iff (seen.any null = true)
            (reachFix_any_null_iff (coverOfSymbolic h) (symbolicOver_leavesOf R.val) hrig hfix)
      | none =>
          predRENonemptyDecidableG (coverOfSymbolic h) (symbolicOver_leavesOf R.val)
  | none => absurd R.property (by rw [IsSymbolic, h]; simp)

/-! ## §7 The deliverable `#guard`s — the fixpoint KERNEL-DECIDES non-`ε` machines.

`rolePlus` ("one or more role frames") is a `symEq`-based cat/star guard: NOT nullable at the
root, so its nonemptiness needs a real derivative step — and its `emptinessBound` is astronomical.
`roleContra` is the contradictory machine (`SymbolicMinterms`' UNSAT-minterm canary):
`emptinessBound ≥ 15` put its `n`-free `false` verdict out of kernel reach for the bounded search
(`3^15+` residuals); the fixpoint closes it in 4 `≅`-classes. -/

section Guards

/-- One-or-more `role`-frames: `sym roleP ⬝ star (sym roleP)` — nullable only AFTER a step. -/
def rolePlus : PredRE := .cat (.sym roleP) (.star (.sym roleP))

-- The runnable fragment membership, kernel-checked: both machines are RigidFull...
#guard rigidRE rolePlus = true
#guard rigidRE roleContra = true
-- ...and `contradictionRE` — whose `¬braceP` leaf USED to fail-close `rigidRE` — is now INSIDE
-- the runnable fragment: `predBEq` descends `not`/`and`/`or` structurally (AciNormal, 07-19
-- widening), exactly the "widens as `predBEq` is extended" promise of the module header. The
-- honest ROOT boundary is now exhibited by a `symMemberOf` leaf (`IsSymbolic` — pin-representable
-- — but `predBEq` does not descend it), at the root only (derivatives never escape: `rigidRE_der`).
#guard rigidRE contradictionRE = true
#guard rigidRE (.sym (.symMemberOf "role" [3, 4])) = false

-- SATURATION at tiny fuel — the adaptive fixpoint CLOSES where the bound is `3^15+`:
#guard (reachFix roleCands 32 rolePlus).isSome
#guard (reachFix roleContraCands 32 roleContra).isSome
-- ...and the `≅`-frontier is a HANDFUL of classes, not a powerset (the whole point):
#guard ((reachFix roleContraCands 32 roleContra).map List.length).getD 1000 ≤ 8
#guard ((reachFix roleCands 32 rolePlus).map List.length).getD 1000 ≤ 8

-- THE VERDICTS, kernel-evaluated: nonempty cat/star guard, empty contradictory machine —
-- both at ALL word lengths (this is `emptyFix`, not a bounded search):
#guard emptyFix roleCands 32 rolePlus = some false
#guard emptyFix roleContraCands 32 roleContra = some true

/-- `rolePlus` bundled into the fragment type. -/
def rolePlusSymbolic : SymbolicRE := ⟨rolePlus, by rw [IsSymbolic]; rfl⟩

/-- `roleContra` bundled. -/
def roleContraSymbolic : SymbolicRE := ⟨roleContra, by rw [IsSymbolic]; rfl⟩

theorem rolePlus_rigid : RigidFull rolePlus := show rigidRE rolePlus = true from rfl

theorem roleContra_rigid : RigidFull roleContra := show rigidRE roleContra = true from rfl

/-- **`fix_decides_rolePlus`** — the assembled `n`-free instance DECIDES the cat/star guard
NONEMPTY through `decide`: instance resolution + worklist saturation + kernel evaluation. The
`rfl` is the adaptive fixpoint running. -/
theorem fix_decides_rolePlus :
    (@decide _ (predRE_emptiness_decidable_fix 32 rolePlusSymbolic rolePlus_rigid)) = true := by
  rfl

/-- The proposition itself, concluded FROM the running fixpoint: some word of some length is
accepted by the cat/star guard. -/
theorem rolePlus_nonempty : ∃ w, derives w rolePlus = true :=
  @of_decide_eq_true _ (predRE_emptiness_decidable_fix 32 rolePlusSymbolic rolePlus_rigid)
    fix_decides_rolePlus

/-- **`fix_decides_roleContra`** — THE verdict the bound-based tower could not reach: the `n`-free
instance kernel-decides the contradictory machine EMPTY. `SymbolicDecision.lean` §4 had to leave
this verdict-shape as a hypothesis (`contradiction_empty_of_bound_false`, `3^15+` residuals);
here it is a `rfl`, in a handful of worklist pops. -/
theorem fix_decides_roleContra :
    (@decide _ (predRE_emptiness_decidable_fix 32 roleContraSymbolic roleContra_rigid))
      = false := by
  rfl

/-- The `n`-free EMPTINESS theorem, concluded from the running fixpoint: NO word of ANY length
over the infinite `Value` alphabet is accepted by `roleContra`. -/
theorem roleContra_empty : ¬ ∃ w, derives w roleContra = true :=
  @of_decide_eq_false _ (predRE_emptiness_decidable_fix 32 roleContraSymbolic roleContra_rigid)
    fix_decides_roleContra

-- The two poles, through `decide` on the assembled instance (the end-to-end `#guard`s):
#guard @decide _ (predRE_emptiness_decidable_fix 32 rolePlusSymbolic rolePlus_rigid)
#guard !(@decide _ (predRE_emptiness_decidable_fix 32 roleContraSymbolic roleContra_rigid))

end Guards

/-! ## Axiom hygiene — the fixpoint tower is kernel-clean. -/

#assert_all_clean [
  rigidRE_der, rigidRE_derList, rigid_satStepG,
  reachFixAux_sound, reachFixAux_closed, reachFix_represents,
  reachFix_any_null_iff, emptyFix_some_iff,
  predRE_emptiness_decidable_fix,
  rolePlus_rigid, roleContra_rigid,
  fix_decides_rolePlus, rolePlus_nonempty,
  fix_decides_roleContra, roleContra_empty
]

end Dregg2.Crypto.Deriv
