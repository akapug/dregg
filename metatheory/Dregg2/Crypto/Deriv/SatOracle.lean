/-
# Dregg2.Crypto.Deriv.SatOracle — the EBA SATISFIABILITY obligation, first concrete slice.

UNREGISTERED (not in any import chain; built standalone with `lake env lean`). Companion to
`docs/DESIGN-symbolic-vpa-lift.md`.

Symbolic automata (Veanes/D'Antoni; symbolic VPA = Alur–D'Antoni CAV'14) preserve boolean closure,
determinization, and decidable equivalence over an INFINITE alphabet exactly when the transition
label algebra is an **effective boolean algebra**: boolean-closed with semantically-correct
operations (dregg's `Pred` has this, `PredAlgebra.eval_and/or/not`), plus a DECIDABLE
SATISFIABILITY for the labels. `Pred.eval` is decidable MEMBERSHIP (given a frame, evaluate);
it is NOT satisfiability (does SOME frame satisfy?). Satisfiability is the one EBA ingredient
absent at HEAD — the entire gap between "PredRE is boolean-closed with a verified matcher" and
"symbolic-VPA decidability lifts".

This file lands the smallest honest piece: **`PredSat`, the obligation, stated over the real
`Value` alphabet, with witness-backed `Decidable` instances covering every minterm of the leaf
algebra the templater's guards actually deploy at HEAD** (`HandlebarsGuarded` writes guards over
the leaf set `{braceP} = {.symEq "t" 0}` plus `tt`/`ff`; its minterms are `braceP` and
`¬braceP`). Also the two generic single-atom facts (`symEq` and its negation are each
satisfiable for EVERY field/symbol), which decide sat for all minterms of any SINGLE `symEq`
leaf — the shape every guard at HEAD has.

Honest scope: this is the WITNESS side (sat by exhibition) for a specific fragment. It is NOT a
decision procedure for `PredSat` of an arbitrary `Pred` — the UNSAT side of compound predicates
(e.g. `.and (.symEq f 0) (.symEq f 1)`) needs a small-model argument over the mentioned fields,
and the full atom catalog (`affineLe`/`affineEq`…) needs a verified LIA feasibility decision.
That cost hierarchy is the subject of the design doc; nothing here overclaims past exhibition.
-/
import Dregg2.Crypto.Deriv.Core
import Dregg2.Crypto.HandlebarsGuarded

namespace Dregg2.Crypto.Deriv

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto.HandlebarsGuarded (braceP braceVal dataVal leaf_braceP_brace leaf_braceP_data)

/-- **`PredSat φ`** — single-frame satisfiability of a leaf predicate under the matcher's leaf
reading (`PredRE.leaf φ a = Pred.eval φ ∅ a`): SOME `Value` frame satisfies `φ`. This is the
effective-boolean-algebra obligation the symbolic-VPA lift turns on; `Decidable (PredSat φ)` for
the label fragment in use is the oracle every summary-saturation edge check consumes. -/
def PredSat (φ : Pred) : Prop := ∃ a : Value, PredRE.leaf φ a = true

/-- `tt` is satisfiable (any frame). -/
theorem predSat_tt : PredSat .tt := ⟨.record [], rfl⟩

/-- `ff` is UNSATISFIABLE — the one leaf whose sat-answer is `false`, pinned so the oracle is
not vacuously `isTrue` everywhere. -/
theorem predSat_ff_false : ¬ PredSat .ff := fun ⟨a, h⟩ => by
  simp only [PredRE.leaf, Pred.eval] at h
  exact Bool.noConfusion h

/-- Every `symEq f s` atom is satisfiable: the one-field record `{f ↦ sym s}` witnesses it,
for EVERY field name and symbol. -/
theorem predSat_symEq (f : FieldName) (s : Nat) : PredSat (.symEq f s) :=
  ⟨.record [(f, .sym s)], by
    simp [PredRE.leaf, Pred.eval, Value.symField, Value.field, List.find?]⟩

/-- Every NEGATED `symEq f s` atom is also satisfiable: the empty record reads `none` at `f`
(fail-closed), so the atom rejects and its negation admits — for EVERY field name and symbol. -/
theorem predSat_not_symEq (f : FieldName) (s : Nat) : PredSat (.not (.symEq f s)) :=
  ⟨.record [], by
    simp [PredRE.leaf, Pred.eval, Value.symField, Value.field, List.find?]⟩

instance : Decidable (PredSat .tt) := .isTrue predSat_tt
instance : Decidable (PredSat .ff) := .isFalse predSat_ff_false
instance (f : FieldName) (s : Nat) : Decidable (PredSat (.symEq f s)) :=
  .isTrue (predSat_symEq f s)
instance (f : FieldName) (s : Nat) : Decidable (PredSat (.not (.symEq f s))) :=
  .isTrue (predSat_not_symEq f s)

/-! ## The DEPLOYED guard leaf algebra (`HandlebarsGuarded`): both minterms decided.

The guards written at HEAD (`noDoubleBraceRE`, `star any`, `Demo`'s strict guard) use exactly the
leaf set `{braceP}` (+ `tt`/`ff`). The boolean algebra it generates has two minterms, `braceP` and
`¬braceP`; a symbolic determinization / emptiness saturation over these guards consults the sat
oracle on exactly these. Both are decided here with concrete witnesses — the embedded token values
`HandlebarsGuarded` itself defines. -/

/-- The `braceP` minterm is satisfiable — witnessed by `braceVal` (reusing the deployed
`leaf_braceP_brace`, not re-proving it). -/
theorem predSat_braceP : PredSat braceP := ⟨braceVal, leaf_braceP_brace⟩

/-- The `¬braceP` minterm is satisfiable — witnessed by `dataVal` via `leaf_braceP_data`. -/
theorem predSat_not_braceP : PredSat (.not braceP) :=
  ⟨dataVal, by simp only [PredRE.leaf, Pred.eval, Bool.not_eq_true']
               exact leaf_braceP_data⟩

instance : Decidable (PredSat braceP) := .isTrue predSat_braceP
instance : Decidable (PredSat (.not braceP)) := .isTrue predSat_not_braceP

/-- **The packaged slice** — every minterm of the deployed guard leaf algebra has a decided
satisfiability, both polarities pinned (`ff` refuses; everything else has a witness). This is the
EBA sat obligation discharged FOR THE GUARDS THE TEMPLATER ACTUALLY WRITES — and only for those;
the general-`Pred` oracle is the priced frontier, not a possession. -/
theorem deployed_guard_minterms_decided :
    PredSat braceP ∧ PredSat (.not braceP) ∧ PredSat .tt ∧ ¬ PredSat .ff :=
  ⟨predSat_braceP, predSat_not_braceP, predSat_tt, predSat_ff_false⟩

#assert_all_clean [
  predSat_tt, predSat_ff_false, predSat_symEq, predSat_not_symEq,
  predSat_braceP, predSat_not_braceP, deployed_guard_minterms_decided
]

end Dregg2.Crypto.Deriv
