/-
# Dregg2.Crypto.Deriv.Determinize — Stage 4: the derivative automaton AS a `DfaAccepts` run.

The design §3 chains three edges into "the compiled boolean semantics is trusted":
  Edge A (Stage 1 `correctness`)  ∘  Edge B (this file + Stage 3)  ∘  Edge C (`Dfa.lean dfa_bridge`).

Edge C — the in-circuit `Dfa.lean` — consumes a TABLE-OPAQUE automaton: `DfaAccepts δ q₀ accept trace`
over an ABSTRACT `δ : State → Sym → State → Prop`, `accept : State → Prop`. It does not care HOW the
table was built (the AIR is table-opaque, design §3.2). So to connect dregg's derivative matcher to
the deployed AIR it suffices to exhibit the DERIVATIVE AUTOMATON in exactly that `DfaAccepts` shape
and prove it accepts EXACTLY `derives` — UP TO LANGUAGE, which is all the table-opaque AIR needs.

That is what this file does, kernel-clean:

  * the derivative automaton: `State := PredRE`, `Sym := Value`, `δ := derStep` (`s' = der a s`),
    `accept := nullAccept` (`null s = true`);
  * `runTrace R w` — the canonical accepting run threading `der` along `w` (one `Step` per frame);
  * **`derivativeDfa_correct`**: for a non-empty word, the `Dfa.lean`-shaped run `DfaAccepts derStep R
    nullAccept (runTrace R w)` holds IFF `derives w R = true` — the SAME `DfaAccepts` predicate the
    deployed AIR's accepting bit certifies (`Dfa.lean:66`).

Chaining with Stage 1 (`correctness`) and Stage 3's `sim_sound`, this gives: the run the AIR accepts
recognizes EXACTLY the denotational language `Matches`. The in-circuit `Dfa.lean` cascade is UNTOUCHED
(we IMPORT its `DfaAccepts`/`Step`/`dfa_bridge`, we do not edit them).

What is NOT here — `derivativeCompile_eq_tableDfa` against `compiler.rs`'s POWERSET `determinize`: that
needs `der_finite` (Stage 3's combinatorial wall) to know the derivative automaton has finitely many
states before a finite table can be EQUAL (up to a reachable-state bijection) to the powerset table.
Named precisely in the closing note; NOT closed with `sorry`.

`#assert_axioms`-clean, `sorry`-free.
-/
import Dregg2.Crypto.Deriv.Similarity
import Dregg2.Crypto.Dfa

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.Dfa (Step DfaAccepts stepValid chained)

namespace PredRE

/-! ## The derivative automaton — states `PredRE`, transition `der`, accept `null`. -/

/-- **`derStep`** — the transition relation of the derivative automaton: from state `s`, reading
frame `a`, the (deterministic) next state is `der a s`. This IS dregg's `der` viewed as the DFA `δ`
the deployed `Lookup` table would route. -/
def derStep (s : PredRE) (a : Value) (s' : PredRE) : Prop := s' = der a s

/-- **`nullAccept`** — the accepting predicate of the derivative automaton: a state accepts iff its
regex is nullable. This IS dregg's `null` viewed as the DFA accept set. -/
def nullAccept (s : PredRE) : Prop := null s = true

/-- **`runTrace R w`** — the canonical run of the derivative automaton on word `w` from start state
`R`: one `Step` per frame, threading `der`. The `i`-th step is `(Rᵢ, aᵢ, der aᵢ Rᵢ)` where `R₀ = R`
and `Rᵢ₊₁ = der aᵢ Rᵢ`. -/
def runTrace : PredRE → List Value → List (Step PredRE Value)
  | _, []      => []
  | R, a :: as => ⟨R, a, der a R⟩ :: runTrace (der a R) as

/-! ### Structural facts about the run. -/

/-- Every step of `runTrace` is a valid `derStep` transition (by construction). -/
theorem runTrace_stepValid (R : PredRE) (w : List Value) :
    ∀ s ∈ runTrace R w, stepValid derStep s := by
  induction w generalizing R with
  | nil => intro s hs; simp only [runTrace, List.not_mem_nil] at hs
  | cons a as ih =>
    intro s hs
    simp only [runTrace, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact rfl
    · exact ih (der a R) s hs

/-- The run chains: each step's `next` is the following step's `state` (by construction). -/
theorem runTrace_chained (R : PredRE) (w : List Value) : chained (runTrace R w) := by
  induction w generalizing R with
  | nil => exact True.intro
  | cons a as ih =>
    cases as with
    | nil => exact True.intro
    | cons b bs =>
      refine ⟨rfl, ?_⟩
      exact ih (der a R)

/-- The first step starts in state `R` (for a non-empty word). -/
theorem runTrace_head (R : PredRE) (a : Value) (as : List Value) :
    (runTrace R (a :: as)).head? = some ⟨R, a, der a R⟩ := rfl

/-- The last step's `next` is `der`-iterated over the whole word — the state `derives` finishes in. -/
theorem runTrace_getLast_next (R : PredRE) (a : Value) (as : List Value) :
    ∃ last, (runTrace R (a :: as)).getLast? = some last ∧
            (nullAccept last.next ↔ derives (a :: as) R = true) := by
  -- The last `next` is the fully-derived residual; `null` of it is exactly `derives`.
  induction as generalizing R a with
  | nil =>
    refine ⟨⟨R, a, der a R⟩, rfl, ?_⟩
    simp only [nullAccept, derives]
  | cons b bs ih =>
    obtain ⟨last, hlast, hiff⟩ := ih (der a R) b
    refine ⟨last, ?_, ?_⟩
    · simp only [runTrace, List.getLast?_cons_cons]; exact hlast
    · simp only [derives] at hiff ⊢; exact hiff

/-! ## `derivativeDfa_correct` — the run is accepted by the `DfaAccepts` predicate iff `derives`. -/

/-- **`derivativeDfa_correct`** — for a NON-EMPTY word, the derivative automaton's canonical run is a
valid accepting run (the EXACT `Dfa.lean` `DfaAccepts` predicate the deployed AIR certifies, `Dfa.lean:
66`) IFF the derivative matcher accepts the word. This is the design §3.2 step-2 (`derivativeDfa_correct`):
"running the DFA = iterating `der`," transported cleanly off Stages 0–1. The non-empty restriction is
because `DfaAccepts` requires a non-empty trace (≥1 transition); the empty-word case is the pure
boundary `derives [] R = null R`, handled by `Dfa.lean`'s boundary `PiBinding` directly. -/
theorem derivativeDfa_correct (R : PredRE) (a : Value) (as : List Value) :
    DfaAccepts derStep R nullAccept (runTrace R (a :: as)) ↔ derives (a :: as) R = true := by
  constructor
  · rintro ⟨first, last, hfirst, hlast, hstart, hacc, _, _⟩
    -- The accept condition `nullAccept last.next` is exactly `derives`, via runTrace_getLast_next.
    obtain ⟨last', hlast', hiff⟩ := runTrace_getLast_next R a as
    rw [hlast'] at hlast
    obtain rfl := Option.some.inj hlast
    exact hiff.mp hacc
  · intro hderiv
    -- Build the accepting run: head = ⟨R,a,der a R⟩, the valid/chained facts are structural,
    -- and the accept comes from runTrace_getLast_next.
    obtain ⟨last, hlast, hiff⟩ := runTrace_getLast_next R a as
    refine ⟨⟨R, a, der a R⟩, last, rfl, hlast, rfl, ?_, ?_, ?_⟩
    · exact hiff.mpr hderiv
    · exact runTrace_stepValid R (a :: as)
    · exact runTrace_chained R (a :: as)

/-- **`derivativeDfa_matches`** — chaining `derivativeDfa_correct` with Stage 1 `correctness`: the
`Dfa.lean`-shaped accepting run recognizes EXACTLY the denotational language `Matches`. This is the
end-to-end language identity "the run the AIR accepts = the spec language," for non-empty words. -/
theorem derivativeDfa_matches (R : PredRE) (a : Value) (as : List Value) :
    DfaAccepts derStep R nullAccept (runTrace R (a :: as)) ↔ Matches (a :: as) R := by
  rw [derivativeDfa_correct, correctness]

/-! ## Non-vacuity — the run accepts real words and rejects others. -/

section Guards

private def fr7 : Value := .record [("k", .sym 7)]
private def fr9 : Value := .record [("k", .sym 9)]
private def p7 : Pred := .symEq "k" 7

-- The derivative-automaton run on `[fr7, fr7]` ACCEPTS the pattern `(sym p7) ⬝ (sym p7)`…
example : derives [fr7, fr7] (.cat (.sym p7) (.sym p7)) = true := by decide
-- …and REJECTS `[fr7, fr9]` (so the DfaAccepts run does too, by derivativeDfa_correct).
example : derives [fr7, fr9] (.cat (.sym p7) (.sym p7)) = false := by decide

-- The run is a GENUINE accepting run for an accepted word (non-vacuous DfaAccepts witness):
example : DfaAccepts derStep (.sym p7) nullAccept (runTrace (.sym p7) [fr7]) :=
  (derivativeDfa_correct (.sym p7) fr7 []).mpr (by decide)

-- …and NOT an accepting run for a rejected word:
example : ¬ DfaAccepts derStep (.sym p7) nullAccept (runTrace (.sym p7) [fr9]) := by
  rw [derivativeDfa_correct]; decide

end Guards

end PredRE

/-! ## Axiom hygiene. -/

#assert_all_clean [
  PredRE.runTrace_stepValid, PredRE.runTrace_chained, PredRE.runTrace_getLast_next,
  PredRE.derivativeDfa_correct, PredRE.derivativeDfa_matches
]

/-!
## The precise remaining wall for Stage 4 — NAMED, not closed.

`derivativeDfa_correct`/`_matches` above close the LANGUAGE-LEVEL connection the table-opaque AIR
needs: the derivative automaton, presented in the EXACT `Dfa.lean` `DfaAccepts` shape, accepts
exactly `derives` = `Matches`. Chained with `Dfa.lean`'s `dfa_bridge` (Edge C) this already gives
"the AIR's accepting bit certifies the denotational language of the derivative automaton."

What remains is `derivativeCompile_eq_tableDfa` (design §3.1 Edge B's literal table equality): that
the derivative automaton's table EQUALS (up to a reachable-state bijection) the POWERSET table
`compiler.rs::determinize` emits. The wall:

  * It needs `der_finite` (Stage 3's `der_pieces` combinatorial wall) FIRST: a "table" is a finite
    object, so the derivative automaton must be known to have finitely many states (up to `≅`) before
    its `δ`-table can be a finite object to compare. Without finiteness there is no table to equate.
  * It needs a Lean MODEL of `compiler.rs::determinize`'s powerset construction (currently UNVERIFIED
    Rust, design §3.2 sub-gap), then DFA-minimization uniqueness OR a direct language-equivalence
    `derivativeDfa ≃ powersetDfa` (the design says language/bisim equivalence SUFFICES for the
    table-opaque AIR — which is exactly the regime `derivativeDfa_matches` already lives in).

So the CLEANEST close routes everything through the derivative automaton as the single source of
truth (the language identity is already proven here) and reconciles the deployed powerset table by
language-equivalence — but that reconciliation still consumes `der_finite`. Stage 4's language half is
DONE; its table-equality half is GATED ON Stage 3's combinatorial wall, named there. NOT closed with
`sorry`.
-/

end Dregg2.Crypto.Deriv
