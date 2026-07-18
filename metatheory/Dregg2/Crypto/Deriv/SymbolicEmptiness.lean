/-
# Dregg2.Crypto.Deriv.SymbolicEmptiness — Tier 2 of the symbolic-VPA lift: the FIRST
user-visible symbolic decision, `∃ w, derives w R = true` (guarded-regular-language NONEMPTINESS)
over the INFINITE `Value` alphabet, decided by SAT-FILTERED derivative reachability.

Companion to `docs/DESIGN-symbolic-vpa-lift.md` §5 tier 2. UNREGISTERED (built standalone with
`lake env lean`). Builds on tier 0 (`SatOracle.lean`: `PredSat`, the deployed minterm witnesses)
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

RESIDUAL (named precisely, NOT faked, NO `sorry`): the full `Decidable (∃ w, derives w R = true)`
needs two more theorems this lane does not land:
  (C1) COMPLETENESS — `nonemptyWithin n R = false → ¬ ∃ w, derives w R`. This holds for `R` whose
       leaves lie in the deployed algebra `{braceP, tt, ff}`, because there `der a R` depends on `a`
       ONLY through `leaf braceP a` (two classes), and `candidates` covers both; the missing content
       is (i) a structural induction "R's leaves ⊆ {braceP,tt,ff} ⇒ der a R factors through
       `leaf braceP a`" and (ii) `candidates` cover every minterm (the general sat oracle, tier 1).
  (C2) UNBOUNDED TERMINATION — turning bounded `nonemptyWithin n` into an `n`-free decision needs a
       concrete state-count bound (from `Finiteness.der_finite`, imported here) plus `DecidableEq
       PredRE` for fixpoint detection. `der_finite` supplies the finite state space; wiring it to a
       computable fixpoint is the remaining step.
So this lane lands: sat-filtered step + decision SOUNDNESS + finite (bounded) reachability + the
biting UNSAT canary. That is real tier-2 progress; the decision is SOUND and COMPUTES, and its two
missing halves are named, not laundered.
-/
import Dregg2.Crypto.Deriv.SatOracle
import Dregg2.Crypto.Deriv.SymbolicDerivative
import Dregg2.Crypto.Deriv.Finiteness
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Tactics

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.HandlebarsGuarded (braceP braceVal dataVal leaf_braceP_brace leaf_braceP_data)
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

/-! ## Axiom hygiene — the decision-soundness tower is kernel-clean. -/

#assert_all_clean [
  candidate_minterm_witnesses,
  derList_append, derives_eq_null_derList,
  reachableWithin_sound, nonemptyWithin_sound, nonemptyWithin_matches
]

end Dregg2.Crypto.Deriv
