/-
# Dregg2.Crypto.Deriv.SymbolicEmptiness — Tier 2 of the symbolic-VPA lift: the FIRST
user-visible symbolic decision, `∃ w, derives w R = true` (guarded-regular-language NONEMPTINESS)
over the INFINITE `Value` alphabet, decided by SAT-FILTERED derivative reachability.

Companion to `docs/DESIGN-symbolic-vpa-lift.md` §5 tier 2. Registered in `Dregg2.lean`. Builds on tier 0 (`SatOracle.lean`: `PredSat`, the deployed minterm witnesses)
and the derivative tower (`Core`/`Correctness`/`Finiteness`/`SymbolicDerivative`).

## The over-approximation `step` cannot decide emptiness — and the fix

`SymbolicDerivative.step r = leaves (𝜕 r)` collects EVERY leaf of the symbolic derivative,
IGNORING branch conditions. It is a sat-FREE over-approximation: a residual is listed even when the
branch leading to it is satisfied by NO `Value`. Harmless for finiteness (a finite superset is still
finite); FATAL for emptiness — deciding `∃ w, derives w R` as "some `null`-state is `step`-reachable"
is UNSOUND, reporting words no `Value` sequence realizes.

Two obstructions to naive sat-filtering of `𝜕 r`, both discovered by reading the tower:

  1. `𝜕 r`'s node CONDITIONS are placeholders — `firstPred l := .tt` (`SymbolicDerivative.lean:30`)
     for the `cat` split, which concretely branches on the frame-INDEPENDENT `null l`, not on any
     `Value`. So the symbolic conditions do NOT faithfully encode when `der a r` selects a leaf;
     filtering `𝜕 r`'s leaves by their own branch predicate is unsound for `cat`/`star`.
  2. The branch of a leaf is a CONJUNCTION (a minterm) of the leaf predicates on its path, and tier 0
     only decides single-leaf `PredSat`, not minterms.

The SOUND realization sidesteps both by filtering CONSTRUCTIVELY: take the concrete derivatives
`der a r` under the deployed minterm WITNESSES `candidates = [braceVal, dataVal]` (the two frames
that realize `braceP` / `¬braceP`, from tier 0). Every residual is then `der a r` for a REAL
`a : Value` — SOUNDNESS is BY CONSTRUCTION (no placeholder condition, no minterm oracle), and the
candidate frames ARE the accepting witness word. This is exactly "keep a residual iff SOME deployed
minterm-witness realizes it" = sat-filtering by `PredSat`, realized so the witness is in hand.

## What is decided, and what is the residual (scoped HONESTLY)

* `satStep` (the sat-filtered step) + `reachableWithin`/`nonemptyWithin` (bounded reachability) —
  COMPUTE (kernel `#guard`).
* Decision SOUNDNESS is a real theorem: `nonemptyWithin n R = true → ∃ w, derives w R = true`
  (and via `correctness`, `→ ∃ w, Matches w R`). The witness word is the candidate frames on the
  accepting path.
* The UNSAT canary BITES: a contradictory `R` (`sym braceP ⋒ sym ¬braceP`, and `bot = sym .ff`)
  decides NONEMPTY = FALSE by kernel eval, whereas the sat-FREE `step` reaches a NULLABLE residual
  (`inter ε ε` / `ε`) via a branch no `Value` takes and would WRONGLY call it nonempty.

WHAT IS PROVED (no `sorry`, no laundered `em`, no `native_decide`):
  * the sat-filtered step (`satStep`, via the deployed minterm witnesses) + `nonemptyWithin`;
  * SOUNDNESS (`nonemptyWithin_sound`): a `true` verdict yields a REAL accepting `Value` word;
  * the leaf-factoring `der_factors` — for a DEPLOYED `R`, `der a R` depends on `a` ONLY through
    `leaf braceP a` (two minterm classes), which `candidates` covers (`canonicalWitness`);
  * BOUNDED COMPLETENESS and hence the BOTH-DIRECTIONS bounded decision
    (`nonemptyWithin_iff_bounded`: `nonemptyWithin n R = true ↔ ∃ w, |w| ≤ n ∧ derives w R = true`)
    and a genuine `boundedNonemptyDecidable : Decidable (∃ w, |w| ≤ n ∧ derives w R = true)`;
  * the biting UNSAT canary (a sat-FREE step would call `contradictionRE` nonempty; this does not).

⚠ WHAT IS **NOT** PROVED (stated exactly, so the bounded result is not mistaken for the full one):
the UNBOUNDED decision `Decidable (∃ w, derives w R = true)` — i.e. `nonemptyWithin n R = false →
¬∃ w, derives w R` for words of ANY length. The contrapositive of `nonemptyWithin_iff_bounded`
gives only "no accepting word of length `≤ n`"; it says NOTHING about longer words. Closing it needs
THREE unbanked ingredients (the earlier "`der_finite` + `DecidableEq PredRE`" recipe is INSUFFICIENT):
  (a) a DECIDABLE similarity `≅` (or an ACI normalizer). Plain `DecidableEq PredRE` will NOT
      terminate a fixpoint: `der a (star r) = cat (der a r) (star r)` grows the SYNTACTIC state set
      without bound even though the `≅`-quotient is finite. No `Decidable`/`DecidableRel` instance
      for `Sim` exists anywhere under `Dregg2/Crypto/Deriv/`.
  (b) a BRIDGE from `satStep`/`der`-reachability into `Finiteness.der_finite`'s `steps` — `der_finite`
      bounds the sat-FREE symbolic `step`, not the concrete `der` reachability used here, and the
      `step ↔ der` relation is not banked.
  (c) pigeonhole excision (an accepting word implies one of length `< N`, the finite `≅`-class count)
      plus `≅`-invariance of `null` (derivable from `sim_sound`), and `der`-congruence under `≅`
      (`Sim R S → Sim (der a R) (der a S)`), which `Similarity.lean` does not yet carry.
-/
import Dregg2.Crypto.Deriv.SatOracle
import Dregg2.Crypto.Deriv.SymbolicDerivative
import Dregg2.Crypto.Deriv.Finiteness
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.HandlebarsGuarded (braceP braceVal dataVal leaf_braceP_brace leaf_braceP_data
  noDoubleBraceRE BB)
open PredRE (der null derives leaf bot Matches correctness step derivative)

/-! ## §1 The deployed minterm witnesses and the sat-filtered step. -/

/-- **`candidates`** — the deployed guard leaf algebra's minterm WITNESSES: `braceVal` realizes the
`braceP` minterm and `dataVal` realizes `¬braceP` (tier 0, `SatOracle.predSat_braceP` /
`predSat_not_braceP`; `leaf_braceP_brace`/`leaf_braceP_data`). Every frame the deployed guards can
distinguish is `≈` one of these two, so concrete derivatives under `candidates` capture the whole
sat-filtered fan-out of the deployed fragment. -/
def candidates : List Value := [braceVal, dataVal]

/-- **`satStep r`** — the SAT-filtered derivative step, realized CONSTRUCTIVELY: the concrete
derivatives of `r` under the deployed minterm witnesses. Contrast `step r = leaves (𝜕 r)`, which
lists residuals reachable only via UNSAT branches: here every residual is `der a r` for a REAL
`a ∈ candidates`, so it is genuinely reachable (soundness by construction) and `a` is a witness. -/
def satStep (r : PredRE) : List PredRE := candidates.map (fun a => der a r)

/-- The candidate frames genuinely realize the two deployed minterms (tier-0 witnesses): the
`braceP` branch is taken by `braceVal`, the `¬braceP` branch by `dataVal`. This is "each satStep
edge's branch is `PredSat`", made concrete — the soundness ingredient, exhibited. -/
theorem candidate_minterm_witnesses :
    leaf braceP braceVal = true ∧ leaf braceP dataVal = false :=
  ⟨leaf_braceP_brace, leaf_braceP_data⟩

/-! ## §2 `derList` — the concrete derivative along a word (the accepting-path re-executor). -/

/-- **`derList w R`** — iterate `der` along `w`. `derives w R = null (derList w R)`: a residual
reachable by `derList w` is exactly the Brzozowski state after reading `w`. -/
def derList : List Value → PredRE → PredRE
  | [],      R => R
  | a :: as, R => derList as (der a R)

theorem derList_append (w v : List Value) (R : PredRE) :
    derList (w ++ v) R = derList v (derList w R) := by
  induction w generalizing R with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append, derList]; exact ih (der a R)

/-- `derives` is `null` of the concrete-derivative re-executor. -/
theorem derives_eq_null_derList (w : List Value) (R : PredRE) :
    derives w R = null (derList w R) := by
  induction w generalizing R with
  | nil => rfl
  | cons a as ih => simp only [derives, derList]; exact ih (der a R)

/-! ## §3 Bounded sat-filtered reachability + the decision function. -/

/-- **`reachableWithin n R`** — every residual reachable from `R` by at most `n` sat-filtered steps.
Structurally terminating on `n`; `Finiteness.der_finite` bounds the `n` at which this saturates
(residual C2 — the unbounded fixpoint). -/
def reachableWithin : Nat → PredRE → List PredRE
  | 0,          R => [R]
  | Nat.succ n, R => (reachableWithin n R).flatMap (fun s => s :: satStep s)

/-- **`nonemptyWithin n R`** — the DECISION (bounded): does some residual reachable from `R` within
`n` sat-filtered steps accept the empty word? When `true`, `R`'s language is genuinely nonempty
(`nonemptyWithin_sound`). Sat-FILTERED, so an accepting residual reachable only through an
unsatisfiable branch is NOT counted — unlike the sat-free `step`. -/
def nonemptyWithin (n : Nat) (R : PredRE) : Bool := (reachableWithin n R).any null

/-! ## §4 Decision SOUNDNESS — a `true` answer exhibits a real accepting word. -/

/-- Every sat-reachable residual is a concrete derivative `derList w R` for a real candidate word
`w` — soundness by construction, the candidate frames on the path forming the witness. -/
theorem reachableWithin_sound :
    ∀ {n : Nat} {R s : PredRE}, s ∈ reachableWithin n R → ∃ w, derList w R = s := by
  intro n
  induction n with
  | zero =>
    intro R s h
    rw [reachableWithin, List.mem_singleton] at h
    subst h; exact ⟨[], rfl⟩
  | succ n ih =>
    intro R s h
    rw [reachableWithin, List.mem_flatMap] at h
    obtain ⟨t, ht, hs⟩ := h
    obtain ⟨w, hw⟩ := ih ht
    rw [List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact ⟨w, hw⟩
    · simp only [satStep, List.mem_map] at hs
      obtain ⟨a, _, ha⟩ := hs
      refine ⟨w ++ [a], ?_⟩
      rw [derList_append]
      show der a (derList w R) = s
      rw [hw]; exact ha

/-- **`nonemptyWithin_sound`** — the DECISION IS SOUND: if the bounded sat-filtered search reports
nonempty, then `R`'s guarded regular language over the infinite `Value` alphabet genuinely contains
a word. The witness is the candidate frames along the accepting derivative path. -/
theorem nonemptyWithin_sound {n : Nat} {R : PredRE}
    (h : nonemptyWithin n R = true) : ∃ w, derives w R = true := by
  rw [nonemptyWithin, List.any_eq_true] at h
  obtain ⟨s, hs, hnull⟩ := h
  obtain ⟨w, hw⟩ := reachableWithin_sound hs
  exact ⟨w, by rw [derives_eq_null_derList, hw]; exact hnull⟩

/-- **`nonemptyWithin_matches`** — the same, phrased on the DENOTATIONAL language via the verified
matcher `correctness` (`derives ↔ Matches`): a `true` decision exhibits a word in `{ w | Matches w R }`. -/
theorem nonemptyWithin_matches {n : Nat} {R : PredRE}
    (h : nonemptyWithin n R = true) : ∃ w, Matches w R := by
  obtain ⟨w, hw⟩ := nonemptyWithin_sound h
  exact ⟨w, (correctness w R).mp hw⟩

/-! ## §5 The UNSAT canary — the tell that the sat-filter does real work.

`contradictionRE` = "one frame that is BOTH a brace and not a brace" — empty (no `Value` satisfies
`braceP ∧ ¬braceP`). The sat-filtered decision returns FALSE; the sat-FREE `step` reaches the
NULLABLE residual `inter ε ε` (via the impossible conjunction) and would WRONGLY return true. -/

/-- `R⊥ := (sym braceP) ⋒ (sym ¬braceP)` — a single frame constrained to be a brace AND not a brace.
Genuinely empty. -/
def contradictionRE : PredRE := .inter (.sym braceP) (.sym (.not braceP))

section Canary

-- SAT: `sym braceP` accepts exactly `[braceVal]`. The decision computes NONEMPTY = TRUE — and only
-- because `braceVal` (a real deployed minterm witness) realizes the `braceP` branch.
#guard nonemptyWithin 1 (.sym braceP) = true

-- The `true` answer corresponds to a CONCRETE accepting word (the candidate frame), matched by the
-- verified denotation — no `decide` (which stalls on the `String` field compare), a direct witness.
example : ∃ w, Matches w (.sym braceP) :=
  ⟨[braceVal], by rw [Matches]; exact ⟨braceVal, rfl, leaf_braceP_brace⟩⟩

-- UNSAT #1 (the contradiction): the sat-filtered decision correctly returns FALSE...
#guard nonemptyWithin 3 contradictionRE = false
-- ...while the sat-FREE `step` ALREADY reaches a NULLABLE residual (`inter ε ε`) at depth 1 — the
-- exact over-approximation bug: a nullable state reachable only via the branch `braceP ∧ ¬braceP`
-- that NO `Value` takes. This is the tell that sat-filtering is load-bearing.
#guard (step contradictionRE).any null = true

-- UNSAT #2 (`bot = sym .ff`): the leaf `.ff` fires on no frame, so the language is empty. The
-- sat-filtered decision returns FALSE...
#guard nonemptyWithin 2 bot = false
-- ...while sat-free `step bot = [ε, bot]` lists the NULLABLE `ε` (reachable only via the unsat `.ff`
-- branch) and would call `bot` nonempty.
#guard (step bot).any null = true

end Canary

/-! ## §6 The DEPLOYED fragment and its leaf-factoring — the load-bearing new content (C1).

The completeness residual `(C1)` hinges on a single structural fact: for the guards the templater
actually writes, `der a R` depends on the frame `a` ONLY through `leaf braceP a`. The deployed guard
leaf algebra is the boolean algebra GENERATED by the single atom `braceP` — its members are exactly
the predicates whose single-frame reading cannot distinguish two frames that `braceP` cannot
(`braceP`, `¬braceP`, `tt`, `ff`, and their boolean combinations). We capture that SEMANTICALLY as
`LeafDeployed`, then lift it structurally to `IsDeployed R`. This is strictly the deployed algebra of
tier 0 (`deployed_guard_minterms_decided`: the minterms are `braceP` / `¬braceP`), not a re-authored
peer. -/

/-- **`LeafDeployed φ`** — the leaf predicate `φ` reads a single frame ONLY through `leaf braceP`:
it gives the same verdict on any two frames that `braceP` cannot tell apart. This is EXACTLY the
condition under which `der a (.sym φ)` factors through the two deployed minterm classes, and it holds
for every member of the boolean algebra generated by `braceP` (the deployed guard leaf algebra). -/
def LeafDeployed (φ : Pred) : Prop :=
  ∀ a b : Value, leaf braceP a = leaf braceP b → leaf φ a = leaf φ b

/-- **`IsDeployed R`** — every `sym` leaf of `R` is `LeafDeployed`: `R` is a guard the deployed
templater fragment can write. Closed under all `PredRE` constructors (so `der` preserves it,
`der_deployed`). -/
def IsDeployed : PredRE → Prop
  | .ε         => True
  | .sym φ     => LeafDeployed φ
  | .alt l r   => IsDeployed l ∧ IsDeployed r
  | .inter l r => IsDeployed l ∧ IsDeployed r
  | .cat l r   => IsDeployed l ∧ IsDeployed r
  | .star r    => IsDeployed r
  | .neg r     => IsDeployed r

/-- `leaf (.not p) a = !(leaf p a)` — `Pred.eval` on `.not` is Boolean negation (definitional). -/
theorem leaf_not (p : Pred) (a : Value) : leaf (.not p) a = !(leaf p a) := rfl

/-- `braceP` itself is `LeafDeployed` (trivially — it is the generating atom). -/
theorem leafDeployed_braceP : LeafDeployed braceP := fun _ _ h => h

/-- `¬braceP` is `LeafDeployed`: it reads `a` only through `leaf braceP a`, negated. -/
theorem leafDeployed_not_braceP : LeafDeployed (.not braceP) := fun a b h => by
  rw [leaf_not, leaf_not, h]

/-- `tt` is `LeafDeployed`: constantly `true`, so it distinguishes no frames. -/
theorem leafDeployed_tt : LeafDeployed .tt := fun _ _ _ => rfl

/-- `ff` is `LeafDeployed`: constantly `false`. -/
theorem leafDeployed_ff : LeafDeployed .ff := fun _ _ _ => rfl

/-- **`der_factors`** — the load-bearing structural factoring: for a DEPLOYED `R`, two frames that
`braceP` cannot distinguish (`leaf braceP a = leaf braceP b`) yield the SAME concrete derivative
`der a R = der b R`. Structural induction on `R`: the `sym` case is exactly `LeafDeployed`; every
other constructor recurses (the frame-independent `null l` guard of `cat` is untouched). This is
residual `(C1)`(i), discharged. -/
theorem der_factors {a b : Value} (hab : leaf braceP a = leaf braceP b) :
    ∀ {R : PredRE}, IsDeployed R → der a R = der b R := by
  intro R
  induction R with
  | ε => intro _; rfl
  | sym φ => intro hR; simp only [der]; rw [hR a b hab]
  | alt l r ihl ihr => intro hR; simp only [der, IsDeployed] at *; rw [ihl hR.1, ihr hR.2]
  | inter l r ihl ihr => intro hR; simp only [der, IsDeployed] at *; rw [ihl hR.1, ihr hR.2]
  | cat l r ihl ihr => intro hR; simp only [der, IsDeployed] at *; rw [ihl hR.1, ihr hR.2]
  | star r ih => intro hR; simp only [der, IsDeployed] at *; rw [ih hR]
  | neg r ih => intro hR; simp only [der, IsDeployed] at *; rw [ih hR]

/-- **`der_deployed`** — the deployed fragment is CLOSED under `der`: the concrete derivative of a
deployed guard is again a deployed guard. So the whole reachable state space of a deployed `R` under
`der` stays deployed, and `der_factors` applies at every step (needed for `derList_factors`). -/
theorem der_deployed {a : Value} : ∀ {R : PredRE}, IsDeployed R → IsDeployed (der a R) := by
  intro R
  induction R with
  | ε => intro _; exact leafDeployed_ff
  | sym φ => intro _; simp only [der]; split
             · exact True.intro
             · exact leafDeployed_ff
  | alt l r ihl ihr => intro hR; simp only [der, IsDeployed] at *; exact ⟨ihl hR.1, ihr hR.2⟩
  | inter l r ihl ihr => intro hR; simp only [der, IsDeployed] at *; exact ⟨ihl hR.1, ihr hR.2⟩
  | cat l r ihl ihr =>
      intro hR; simp only [der, IsDeployed] at *; split
      · exact ⟨⟨ihl hR.1, hR.2⟩, ihr hR.2⟩
      · exact ⟨ihl hR.1, hR.2⟩
  | star r ih => intro hR; simp only [der, IsDeployed] at *; exact ⟨ih hR, hR⟩
  | neg r ih => intro hR; simp only [der, IsDeployed] at *; exact ih hR

/-! ## §7 The canonical minterm witness and the word-canonicalization. -/

/-- **`canonicalWitness a`** — the deployed minterm WITNESS of the class `a` lands in: `braceVal` if
`a` fires `braceP`, else `dataVal`. Always a member of `candidates`, and it is `braceP`-equivalent to
`a` (`leaf_braceP_canonicalWitness`). This is residual `(C1)`(ii): `candidates` covers every minterm
of the deployed algebra, made a computable selector. -/
def canonicalWitness (a : Value) : Value := if leaf braceP a then braceVal else dataVal

/-- `canonicalWitness a` is always one of the two deployed candidates. -/
theorem canonicalWitness_mem (a : Value) : canonicalWitness a ∈ candidates := by
  unfold canonicalWitness candidates
  split <;> simp

/-- `canonicalWitness a` fires `braceP` exactly when `a` does — so it is in `a`'s minterm class. -/
theorem leaf_braceP_canonicalWitness (a : Value) :
    leaf braceP (canonicalWitness a) = leaf braceP a := by
  unfold canonicalWitness
  by_cases h : leaf braceP a = true
  · rw [if_pos h, leaf_braceP_brace, h]
  · rw [if_neg h, leaf_braceP_data]
    simp only [Bool.not_eq_true] at h; rw [h]

/-- **`derList_factors`** — the accepting-path canonicalization: for a DEPLOYED `R`, reading the word
`w` gives the SAME residual as reading its canonicalization `w.map canonicalWitness` (a word entirely
over `candidates`). Induction on `w` via `der_factors` (each frame) + `der_deployed` (the residual
stays deployed for the tail). THIS is what makes an arbitrary accepting `Value` word collapse onto a
CANDIDATE word the bounded search enumerates. -/
theorem derList_factors : ∀ (w : List Value) {R : PredRE}, IsDeployed R →
    derList w R = derList (w.map canonicalWitness) R := by
  intro w
  induction w with
  | nil => intro R _; rfl
  | cons a as ih =>
      intro R hR
      simp only [derList, List.map_cons]
      rw [der_factors (leaf_braceP_canonicalWitness a).symm hR]
      exact ih (der_deployed hR)

/-! ## §8 Bounded reachability COMPLETENESS — every candidate word is captured. -/

/-- One more sat-filtered layer never drops a residual: `reachableWithin` is monotone in the bound. -/
theorem reachableWithin_mono_one {n : Nat} {R : PredRE} :
    ∀ {s}, s ∈ reachableWithin n R → s ∈ reachableWithin (n + 1) R := by
  intro s hs
  rw [reachableWithin, List.mem_flatMap]
  exact ⟨s, hs, List.mem_cons.mpr (Or.inl rfl)⟩

theorem reachableWithin_mono {n m : Nat} {R : PredRE} (h : n ≤ m) :
    ∀ {s}, s ∈ reachableWithin n R → s ∈ reachableWithin m R := by
  induction h with
  | refl => exact fun hs => hs
  | step _ ih => exact fun hs => reachableWithin_mono_one (ih hs)

/-- **`reachableWithin_complete`** — the CONVERSE of `reachableWithin_sound`: EVERY residual reached
by a candidate word `v` of length `≤ n` is in `reachableWithin n R`. Induction on `n`, peeling the
LAST frame of `v` (matching `reachableWithin`'s back-growth): the prefix lands by IH, and the final
`der a` is one `satStep` edge (`a ∈ candidates`). This is the reachability half of completeness. -/
theorem reachableWithin_complete {R : PredRE} :
    ∀ {n : Nat} {v : List Value}, (∀ x ∈ v, x ∈ candidates) → v.length ≤ n →
      derList v R ∈ reachableWithin n R := by
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
        exact reachableWithin_mono (Nat.zero_le _) (List.mem_singleton.mpr rfl)
      · simp only [List.concat_eq_append] at hv hlen ⊢
        have ha : a ∈ candidates := hv a (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
        have hv' : ∀ x ∈ v', x ∈ candidates := fun x hx =>
          hv x (List.mem_append.mpr (Or.inl hx))
        have hlen' : v'.length ≤ n := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
        have hin : derList v' R ∈ reachableWithin n R := ih hv' hlen'
        rw [derList_append, reachableWithin, List.mem_flatMap]
        refine ⟨derList v' R, hin, List.mem_cons.mpr (Or.inr ?_)⟩
        show der a (derList v' R) ∈ satStep (derList v' R)
        simp only [satStep, List.mem_map]
        exact ⟨a, ha, rfl⟩

/-! ## §9 The FULL bounded decision — SOUND ⋀ COMPLETE (both directions), and its `Decidable`. -/

/-- **`nonemptyWithin_complete`** — the BOUNDED completeness (C1's leaf-factoring half; the
UNBOUNDED `C1` remains open, see the header — it needs the `≅`-quotient work): for a DEPLOYED `R`, if ANY word `w`
(over the infinite `Value` alphabet) of length `≤ n` is accepted, the bounded sat-filtered search
reports nonempty. The proof canonicalizes `w` (`derList_factors`) onto a candidate word the search
enumerates (`reachableWithin_complete`). Together with `nonemptyWithin_sound`, the bounded decision is
now correct in BOTH directions. -/
theorem nonemptyWithin_complete {n : Nat} {R : PredRE} (hR : IsDeployed R)
    (w : List Value) (hw : derives w R = true) (hlen : w.length ≤ n) :
    nonemptyWithin n R = true := by
  have hvcand : ∀ x ∈ w.map canonicalWitness, x ∈ candidates := by
    intro x hx; rw [List.mem_map] at hx
    obtain ⟨y, _, rfl⟩ := hx; exact canonicalWitness_mem y
  have hvlen : (w.map canonicalWitness).length ≤ n := by rw [List.length_map]; exact hlen
  have hnull : null (derList (w.map canonicalWitness) R) = true := by
    rw [← derList_factors w hR, ← derives_eq_null_derList]; exact hw
  rw [nonemptyWithin, List.any_eq_true]
  exact ⟨_, reachableWithin_complete hvcand hvlen, hnull⟩

/-- **`reachableWithin_sound'`** — length-tracked soundness: a residual in `reachableWithin n R` is
`derList w R` for a real candidate word `w` with `|w| ≤ n`. Strengthens `reachableWithin_sound` with
the length bound needed for the exact bounded ↔. -/
theorem reachableWithin_sound' :
    ∀ {n : Nat} {R s : PredRE}, s ∈ reachableWithin n R →
      ∃ w, w.length ≤ n ∧ derList w R = s := by
  intro n
  induction n with
  | zero =>
      intro R s h
      rw [reachableWithin, List.mem_singleton] at h
      subst h; exact ⟨[], Nat.le_refl 0, rfl⟩
  | succ n ih =>
      intro R s h
      rw [reachableWithin, List.mem_flatMap] at h
      obtain ⟨t, ht, hs⟩ := h
      obtain ⟨w, hlen, hw⟩ := ih ht
      rw [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact ⟨w, Nat.le_succ_of_le hlen, hw⟩
      · simp only [satStep, List.mem_map] at hs
        obtain ⟨a, _, ha⟩ := hs
        refine ⟨w ++ [a], ?_, ?_⟩
        · simp only [List.length_append, List.length_cons, List.length_nil]; omega
        · rw [derList_append]; show der a (derList w R) = s; rw [hw]; exact ha

/-- **`nonemptyWithin_iff_bounded`** — the SOUND ⋀ COMPLETE bounded decision, stated as an `↔`:
for a DEPLOYED `R`, the bounded sat-filtered search reports nonempty EXACTLY WHEN a word of length
`≤ n` is accepted. Forward = `reachableWithin_sound'`; backward = `nonemptyWithin_complete`. -/
theorem nonemptyWithin_iff_bounded {n : Nat} {R : PredRE} (hR : IsDeployed R) :
    nonemptyWithin n R = true ↔ ∃ w, w.length ≤ n ∧ derives w R = true := by
  constructor
  · intro h
    rw [nonemptyWithin, List.any_eq_true] at h
    obtain ⟨s, hs, hnull⟩ := h
    obtain ⟨w, hlen, hw⟩ := reachableWithin_sound' hs
    exact ⟨w, hlen, by rw [derives_eq_null_derList, hw]; exact hnull⟩
  · rintro ⟨w, hlen, hw⟩; exact nonemptyWithin_complete hR w hw hlen

/-- **`boundedNonemptyDecidable`** — a GENUINE `Decidable` for the bounded language-nonemptiness of a
deployed guard: `∃ w, |w| ≤ n ∧ derives w R = true`. Decided by kernel evaluation of `nonemptyWithin`
through the both-directions `nonemptyWithin_iff_bounded`. This is the full bounded decision — sound
AND complete — as a real decision instance (not merely a one-directional `true ⇒`). -/
def boundedNonemptyDecidable (n : Nat) {R : PredRE} (hR : IsDeployed R) :
    Decidable (∃ w, w.length ≤ n ∧ derives w R = true) :=
  decidable_of_iff _ (nonemptyWithin_iff_bounded hR)

/-! ## §10 Deployed-fragment membership + kernel-eval decision `#guard`s. -/

section DeployedGuards

/-- `contradictionRE` is IN the deployed fragment (its leaves are `braceP` and `¬braceP`, both
`LeafDeployed`). So the biting `nonemptyWithin 3 contradictionRE = false` is not merely SOUND but,
via `nonemptyWithin_iff_bounded`, COMPLETE: no accepting word of length `≤ 3` exists. -/
example : IsDeployed contradictionRE := by
  simp only [contradictionRE, IsDeployed]
  exact ⟨leafDeployed_braceP, leafDeployed_not_braceP⟩

/-- `noDoubleBraceRE` — the actual deployed templater guard — is in the fragment (leaves `tt`, from
`star any`, and `braceP`). So the FULL bounded decision applies to the real guard. -/
example : IsDeployed noDoubleBraceRE := by
  simp only [noDoubleBraceRE, BB, PredRE.any, IsDeployed]
  exact ⟨leafDeployed_tt, leafDeployed_braceP, leafDeployed_braceP, leafDeployed_tt⟩

-- SAT: a deployed guard with a real accepting frame decides NONEMPTY = TRUE by kernel eval...
#guard nonemptyWithin 1 (.sym braceP) = true
-- ...and `noDoubleBraceRE` accepts `[]` (no adjacent braces), so it is nonempty at bound 0.
#guard nonemptyWithin 0 noDoubleBraceRE = true
-- UNSAT: the empty guards decide FALSE — now a COMPLETE verdict (both are deployed).
#guard nonemptyWithin 3 contradictionRE = false
#guard nonemptyWithin 2 bot = false

-- The bounded `Decidable` for the real guard `noDoubleBraceRE` is inhabited by a `true` verdict:
-- an accepting word of length `≤ 0` genuinely exists (the empty word), proven THROUGH the
-- both-directions bounded iff (not a bare soundness `⇒`).
example : ∃ w, w.length ≤ 0 ∧ derives w noDoubleBraceRE = true :=
  (nonemptyWithin_iff_bounded (n := 0) (R := noDoubleBraceRE) (by
    simp only [noDoubleBraceRE, BB, PredRE.any, IsDeployed]
    exact ⟨leafDeployed_tt, leafDeployed_braceP, leafDeployed_braceP, leafDeployed_tt⟩)).mp rfl

end DeployedGuards

/-! ## Axiom hygiene — the decision-soundness tower is kernel-clean. -/

#assert_all_clean [
  candidate_minterm_witnesses,
  derList_append, derives_eq_null_derList,
  reachableWithin_sound, nonemptyWithin_sound, nonemptyWithin_matches,
  der_factors, der_deployed, leaf_braceP_canonicalWitness, derList_factors,
  reachableWithin_mono, reachableWithin_complete, reachableWithin_sound',
  nonemptyWithin_complete, nonemptyWithin_iff_bounded
]

end Dregg2.Crypto.Deriv
