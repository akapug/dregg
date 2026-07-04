/-
# Dregg2.Authority.AffineBridge — the ONE affine vocabulary (apps gap 1: unify the two `affineSum`s).

Two layers grew the SAME affine arithmetic independently:

  * **`Exec.Program.affineSum (v) (terms) : Option Int`** — the cell-program layer's reader, over
    `Value.scalar` (the `Option`-propagating, FAIL-CLOSED reader: a missing/ill-typed field yields
    `none`, so an affine atom over an absent field is *unevaluable*, hence rejected). The
    `affineLe`/`affineEq`/`affineDeltaLe` `StateConstraint` atoms read through it.
  * **`Authority.RelationalClosure.affineSum (terms) (rec) : Int`** — the relational-closure layer's
    reader, over `fieldOf` (the TOTAL reader, `(rec.scalar f).getD 0`: a missing field defaults to `0`,
    dregg1's `FIELD_ZERO`). The `RelPred.affineLe` half-space and its Boolean closure read through it.

They are the same affine form `Σ cᵢ·record[fᵢ]` over the same `Term = Int × FieldName` model — the ONLY
difference is the absent-field convention (`none`-propagation vs `0`-default). This module proves they
COINCIDE wherever both are defined, so an affine fact proved in one layer transports to the other with
NO re-proof. We add NO new atom and do NOT refactor the 73-theorem `Program.lean` — an equivalence
bridge, the least-disruptive unification (the brief's explicit preference).

## What is proven (the bridge, both directions of the coincidence)

  * **`programAffineSum_eq_relClosure`** — the CORE: when the program reader SUCCEEDS
    (`Program.affineSum v terms = some s`, i.e. every term field reads as an `int`), its value is
    EXACTLY the relational-closure sum (`RelationalClosure.affineSum terms v = s`). So on the common
    domain (all fields present) the two vocabularies agree pointwise — `getD 0` never fires.
  * **`relClosure_eq_programAffineSum`** — the same fact read the other way: a successful program sum
    EQUALS the (always-defined) closure sum.
  * **`programAffineLe_iff_relClosureLe`** — TRANSPORT for the comparison: a `Program`-layer
    `affineLe terms c` admits IFF the field reads succeed AND the `RelationalClosure` half-space
    `Σ ≤ c` holds. So a `RelPred.affineLe` fact (e.g. one proved via the closure's Boolean algebra)
    lifts to the program `affineLe` admission, and vice-versa, with the fail-closed reads as the only
    side condition.
  * **`programAffineLe_admits_relPredAffineLe`** / **`relPredAffineLe_admits_programAffineLe`** —
    the two one-directional bridges to `RelPred.eval (.affineLe terms c)` directly, so an affine guard
    written in the closure algebra and one written in the program catalog are interchangeable on the
    all-fields-present domain.
  * **§NON-VACUITY** — the bridge is not vacuous: a concrete record where BOTH sums equal the same
    value and the `Program` sum is genuinely `some` (the reads succeed), AND a record where the program
    sum is `none` (a field absent) while the closure sum still totals via `getD 0` — the precise
    witness that the two conventions DIFFER off the common domain, so the bridge's "where both defined"
    qualifier is load-bearing.

NEW file only. Imports BOTH `Exec.Program` (for the cell-program `affineSum`/`evalConstraint`) and
`Authority.RelationalClosure` (for the closure `affineSum`/`RelPred`). Touches neither — it sits
between them. This is a LIGHT module (it does not pull `EffectsState`'s heavy chain into `Program`,
which would happen were the bridge placed in `Program.lean` itself). Every keystone
`#assert_axioms`-pinned to `{propext, Classical.choice, Quot.sound}`.
-/
import Dregg2.Exec.Program
import Dregg2.Authority.RelationalClosure

namespace Dregg2.Authority.AffineBridge

open Dregg2.Exec (Value FieldName)
open Dregg2.Exec.EffectsState (fieldOf)

/-! ## §1 — The core coincidence: the program sum, when defined, IS the relational-closure sum.

`Exec.Program.affineSum v terms` folds with `Value.scalar` (fail-closed); `RelationalClosure.affineSum
terms v` folds with `fieldOf = (·.scalar ·).getD 0` (total). When every term field reads as `some`, the
`getD 0` defaults never fire, so the two sums are equal. We prove it by induction on `terms`, threading
the success of the program fold (a `some` head forces a `some` tail). -/

/-- **`programAffineSum_eq_relClosure` (the core bridge).** When the cell-program reader succeeds —
`Exec.Program.affineSum v terms = some s` (every term field present and `int`) — the value `s` equals
the relational-closure sum `Authority.RelationalClosure.affineSum terms v`. So on the common domain the
two affine vocabularies are the SAME number; the `fieldOf`/`getD 0` total reader and the `Value.scalar`
fail-closed reader agree wherever the latter is defined. -/
theorem programAffineSum_eq_relClosure (v : Value) :
    ∀ (terms : List (Int × FieldName)) (s : Int),
      Dregg2.Exec.affineSum v terms = some s →
      Dregg2.Authority.RelationalClosure.affineSum terms v = s := by
  intro terms
  induction terms with
  | nil =>
    intro s hs
    -- both sums are 0 on the empty term list: `Program.affineSum v [] = some 0`, so `s = 0`,
    -- and `RelationalClosure.affineSum [] v = 0` definitionally.
    have hs' : some (0 : Int) = some s := hs
    have hs0 : (0 : Int) = s := by injection hs'
    show Dregg2.Authority.RelationalClosure.affineSum [] v = s
    rw [← hs0]; rfl
  | cons t rest ih =>
    intro s hs
    -- The cons recurrence (definitional): the head folds the tail program-sum with `v.scalar t.2`.
    have hrec : Dregg2.Exec.affineSum v (t :: rest)
        = (match Dregg2.Exec.affineSum v rest, v.scalar t.2 with
           | some acc, some x => some (acc + t.1 * x)
           | _, _ => none) := rfl
    rw [hrec] at hs
    -- Peel: the head `some` forces both the tail program-sum AND the scalar read to be `some`.
    cases hacc : Dregg2.Exec.affineSum v rest with
    | none => rw [hacc] at hs; simp at hs
    | some acc =>
      cases hx : v.scalar t.2 with
      | none => rw [hacc, hx] at hs; simp at hs
      | some x =>
        rw [hacc, hx] at hs
        simp only [Option.some.injEq] at hs
        -- ih on the tail: RelationalClosure.affineSum rest v = acc.
        have htail : Dregg2.Authority.RelationalClosure.affineSum rest v = acc := ih acc hacc
        -- fieldOf t.2 v = x (since v.scalar t.2 = some x).
        have hfield : fieldOf t.2 v = x := by simp [fieldOf, hx]
        -- The closure sum cons recurrence (definitional) + finish.
        have hclrec : Dregg2.Authority.RelationalClosure.affineSum (t :: rest) v
            = t.1 * fieldOf t.2 v + Dregg2.Authority.RelationalClosure.affineSum rest v := by
          simp only [Dregg2.Authority.RelationalClosure.affineSum, List.map, List.foldr]
        rw [hclrec, hfield, htail]; omega

/-- **`relClosure_eq_programAffineSum`.** The same coincidence read with the closure sum on the left:
a successful program sum equals the (always-defined) relational-closure sum. -/
theorem relClosure_eq_programAffineSum (v : Value) (terms : List (Int × FieldName)) (s : Int)
    (h : Dregg2.Exec.affineSum v terms = some s) :
    s = Dregg2.Authority.RelationalClosure.affineSum terms v :=
  (programAffineSum_eq_relClosure v terms s h).symm

/-! ## §2 — Transport the comparison: program `affineLe` ⟺ closure half-space (where defined).

The program atom `StateConstraint.affineLe terms c` admits iff `affineSum v terms = some s ∧ s ≤ c`
(`evalConstraint_affineLe_iff`). The closure atom `RelPred.affineLe terms c` evaluates iff
`RelationalClosure.affineSum terms v ≤ c` (`RelPred.eval`, total). The bridge ties them: when the program
reads succeed, the two comparisons are the SAME, so an affine bound proved in either layer transports. -/

/-- **`programAffineLe_iff_relClosureLe`.** The program-layer `affineLe terms c` admits IFF every term
field reads (`affineSum v terms = some s`) AND the relational-closure half-space holds at that value
(`s ≤ c`, equivalently `RelationalClosure.affineSum terms v ≤ c`). The comparison transports across the
two vocabularies; the fail-closed read is the only side condition. -/
theorem programAffineLe_iff_relClosureLe (terms : List (Int × FieldName)) (c : Int) (o n : Value) :
    Dregg2.Exec.evalConstraint (.affineLe terms c) o n = true ↔
      ∃ s, Dregg2.Exec.affineSum n terms = some s ∧
           Dregg2.Authority.RelationalClosure.affineSum terms n = s ∧ s ≤ c := by
  rw [Dregg2.Exec.evalConstraint_affineLe_iff]
  constructor
  · rintro ⟨s, hsum, hle⟩
    exact ⟨s, hsum, programAffineSum_eq_relClosure n terms s hsum, hle⟩
  · rintro ⟨s, hsum, _, hle⟩
    exact ⟨s, hsum, hle⟩

/-- **`relPredAffineLe_eval` (closure side, for reference).** The closure atom evaluates exactly the
total half-space — restated here so the bridge lemmas read against one name. -/
theorem relPredAffineLe_eval (terms : List (Dregg2.Authority.RelationalClosure.Term)) (c : Int)
    (rec : Value) :
    (Dregg2.Authority.RelationalClosure.RelPred.affineLe terms c).eval rec
      = decide (Dregg2.Authority.RelationalClosure.affineSum terms rec ≤ c) := rfl

/-- **`programAffineLe_admits_relPredAffineLe`.** If the program `affineLe terms c` ADMITS (so the
field reads succeeded), the closure `RelPred.affineLe terms c` evaluates TRUE on the same record. An
affine guard the program catalog accepts is accepted by the closure algebra — same bound, same record. -/
theorem programAffineLe_admits_relPredAffineLe (terms : List (Int × FieldName)) (c : Int) (o n : Value)
    (h : Dregg2.Exec.evalConstraint (.affineLe terms c) o n = true) :
    (Dregg2.Authority.RelationalClosure.RelPred.affineLe terms c).eval n = true := by
  obtain ⟨s, hsum, hcl, hle⟩ := (programAffineLe_iff_relClosureLe terms c o n).mp h
  rw [relPredAffineLe_eval]
  rw [hcl]; exact decide_eq_true (by omega)

/-- **`relPredAffineLe_admits_programAffineLe`.** The converse on the common domain: if the closure
`RelPred.affineLe terms c` evaluates TRUE *and* every term field reads (`affineSum n terms = some s` —
the fail-closed side condition the closure's `getD 0` hides), the program `affineLe terms c` admits.
So the two affine guards are interchangeable wherever the program reader is defined. -/
theorem relPredAffineLe_admits_programAffineLe (terms : List (Int × FieldName)) (c : Int) (o n : Value)
    (s : Int) (hsum : Dregg2.Exec.affineSum n terms = some s)
    (hcl : (Dregg2.Authority.RelationalClosure.RelPred.affineLe terms c).eval n = true) :
    Dregg2.Exec.evalConstraint (.affineLe terms c) o n = true := by
  rw [Dregg2.Exec.evalConstraint_affineLe_iff]
  refine ⟨s, hsum, ?_⟩
  -- closure eval true ⇒ closure sum ≤ c; and closure sum = s on the common domain.
  rw [relPredAffineLe_eval, decide_eq_true_eq] at hcl
  have : Dregg2.Authority.RelationalClosure.affineSum terms n = s :=
    programAffineSum_eq_relClosure n terms s hsum
  omega

/-! ## §3 — §NON-VACUITY: the coincidence BITES on the common domain, and the conventions DIFFER off it.

The bridge is real: a concrete record where both sums equal 8 and the program sum is genuinely `some 8`
(reads succeed); and a record with a MISSING field where the program sum is `none` (fail-closed) while
the closure sum still totals via `getD 0` — the witness that the "where both defined" qualifier is
load-bearing, not vacuous. -/

/-- A record carrying both term fields: `2·a − b` over `a=10, b=12` = `8`. -/
def recBoth : Value := .record [("a", .int 10), ("b", .int 12)]
/-- The affine terms `2·a − b`. -/
def egTerms : List (Int × FieldName) := [(2, "a"), (-1, "b")]

-- On the common domain BOTH sums equal 8, and the program sum is genuinely `some 8` (reads succeed).
#guard Dregg2.Exec.affineSum recBoth egTerms == some 8
#guard Dregg2.Authority.RelationalClosure.affineSum egTerms recBoth == 8
#guard
  match Dregg2.Exec.affineSum recBoth egTerms with
  | some s => s == Dregg2.Authority.RelationalClosure.affineSum egTerms recBoth
  | none   => false

/-- A record MISSING field `b`: the program reader fails closed (`none`); the closure totals via
`getD 0`, so `2·10 − 0 = 20`. The two conventions DIFFER here — the bridge's qualifier is real. -/
def recMissing : Value := .record [("a", .int 10)]

-- Program sum is `none` (fail-closed on the absent `b`); closure sum is 20 (b defaulted to 0).
#guard Dregg2.Exec.affineSum recMissing egTerms == none
#guard Dregg2.Authority.RelationalClosure.affineSum egTerms recMissing == 20

/-- **`bridge_coincides_on_common_domain` (non-vacuity, theorem form).** There is a record and term
list where the program sum is `some s` AND the closure sum equals that same `s` — the coincidence is
inhabited, not vacuous. -/
theorem bridge_coincides_on_common_domain :
    ∃ (v : Value) (terms : List (Int × FieldName)) (s : Int),
      Dregg2.Exec.affineSum v terms = some s ∧
      Dregg2.Authority.RelationalClosure.affineSum terms v = s :=
  ⟨recBoth, egTerms, 8, by decide, by decide⟩

/-- **`bridge_conventions_differ_off_domain` (the qualifier is load-bearing).** There is a record where
the program reader fails closed (`none`) while the closure reader still totals — so the two affine
vocabularies are NOT literally equal as functions; they coincide only where the program reader is
defined (every field present). This pins WHY the bridge is stated with that hypothesis. -/
theorem bridge_conventions_differ_off_domain :
    ∃ (v : Value) (terms : List (Int × FieldName)),
      Dregg2.Exec.affineSum v terms = none ∧
      Dregg2.Authority.RelationalClosure.affineSum terms v = 20 :=
  ⟨recMissing, egTerms, by decide, by decide⟩

-- The comparison transports: the program `affineLe egTerms 8` admits on `recBoth` (8 ≤ 8), and so does
-- the closure half-space (same bound, same record) — the two affine guards agree where both read.
#guard Dregg2.Exec.evalConstraint (.affineLe egTerms 8) (.record []) recBoth
#guard (Dregg2.Authority.RelationalClosure.RelPred.affineLe egTerms 8).eval recBoth
-- ...and both REJECT a tighter bound (7), so the transported comparison is non-vacuous both polarities.
#guard Dregg2.Exec.evalConstraint (.affineLe egTerms 7) (.record []) recBoth == false
#guard (Dregg2.Authority.RelationalClosure.RelPred.affineLe egTerms 7).eval recBoth == false

/-! ## §4 — Axiom-hygiene tripwires (the honesty pins over every bridge keystone). -/

#assert_all_clean [
  programAffineSum_eq_relClosure,
  relClosure_eq_programAffineSum,
  programAffineLe_iff_relClosureLe,
  relPredAffineLe_eval,
  programAffineLe_admits_relPredAffineLe,
  relPredAffineLe_admits_programAffineLe,
  bridge_coincides_on_common_domain,
  bridge_conventions_differ_off_domain
]

end Dregg2.Authority.AffineBridge
