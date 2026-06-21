/-
# Metatheory.PolisAuthDatalog — the polis discharge gate IS the genuine Datalog consequence closure.

The coordination layer (`PolisAuthCoord`/`PolisAuthReachFull`) grounded knowledge on a two-fact
predicate algebra (`KnowReq`/`FactSet`, `bothFacts`): a faithful but TINY fragment — a single
conjunctive membership check, not a derivation. This file replaces that stub with the REAL object:
the forward-chaining Datalog consequence closure of `Metatheory.PolisDatalog` (`Derivable`), wired
into the deployed cross-vat seam `Dregg2.Laws.{Verifiable, Discharged}`.

The move is to instantiate the seam at the real derivation:

  * `RULES := chainRules`, budget `K` fixed.
  * `instance : Verifiable Atom (List Atom)` with `Verify goal facts := decide (Derivable RULES facts goal K)`.
  * hence `Dregg2.Laws.Discharged goal facts ↔ Derivable RULES facts goal K` — the discharge gate is
    NOW the genuine multi-step consequence closure, not a one-shot membership check.

Over THIS instance the coordination phenomena are re-derived as Datalog facts:

  * **equivocation_underivable** — a goal NOT in the closure cannot be `Discharged` (you can only
    discharge what follows; reuses `PolisDatalog.X_alone_cannot`).
  * **coalition_discharges** — pooled facts `X ++ Y` `Discharge` a conjunctive goal neither agent
    alone can (reuses `PolisDatalog.coalition_derives`).
  * **KnowReachesD** — viability = `Discharged goal facts`, which by the bridge IS the real
    *multi-step* derivation (`a ← b ← c`), not a single check.

No `sorry`; no load-bearing `True`; the discharge bridge is a proven `↔`; `#eval` runs the gate.
-/
import Metatheory.PolisDatalog
import Dregg2.Laws

namespace Metatheory.PolisAuthDatalog

open Dregg2.Laws Metatheory.PolisDatalog

/-! ## The deployed seam, instantiated by the real derivation. -/

/-- The fixed rule-base the polis discharge gate runs against: the genuine multi-step / conjunctive
rule-base of `PolisDatalog` (`a ← b ← c`, `goal ← factX ∧ factY`). -/
def RULES : List Rule := chainRules

/-- The derivation budget (round count) the gate allows. `2` admits the full `a ← b ← c` chain and the
one-round conjunctive coalition rule; it is finite, so the gate stays decidable and terminating. -/
def K : Nat := 2

/-- **The polis discharge gate, as a `Dregg2.Laws.Verifiable` instance over the REAL Datalog.** A
`goal : Atom` is the predicate; the agent's known `facts : List Atom` are the witness; the verifier
ACCEPTS iff the goal is in the bounded consequence closure of `RULES` from `facts`. The seam that the
whole cross-vat admissibility algebra runs on is now instantiated by genuine derivability — the same
decidable, verifier-local check, but the check is forward-chaining Datalog. -/
instance datalogGate : Verifiable Atom (List Atom) where
  Verify goal facts := decide (Derivable RULES facts goal K)

/-- **The bridge: the discharge gate IS Datalog derivability.** `Dregg2.Laws.Discharged goal facts`
unfolds (through the `datalogGate` instance) to exactly `Derivable RULES facts goal K` — the polis
discharge object and the genuine consequence closure are the SAME proposition. This is what makes the
rest of the file `decide`-checked Datalog facts rather than a re-axiomatized toy. -/
theorem discharged_iff_derivable (goal : Atom) (facts : List Atom) :
    Discharged goal facts ↔ Derivable RULES facts goal K := by
  unfold Discharged Verifiable.Verify datalogGate
  exact decide_eq_true_iff

/-! ## Re-expressing the coordination layer over the real closure.

Agent X holds `factsX = [3]`; agent Y holds `factsY = [4]`; `goal=10` needs both (the conjunctive
coalition rule). `goal=0` is the multi-step chain goal derivable from the single fact `c=2`. All
proven through the `PolisDatalog` lemmas via the bridge — no re-derivation, all `decide`-checked. -/

/-! ### Equivocation: you cannot discharge a goal that does not follow. -/

/-- **Equivocation underivable.** Agent X's facts do NOT derive `goal=10` (the body `[3,4]` is never
fully known from `[3]`), so by the bridge the gate REFUSES to discharge it. You can only discharge
what is in the closure — claiming a goal you cannot derive is foreclosed at the verifier. (Reuses
`PolisDatalog.X_alone_cannot`; note `K = 2 ≤ 5`, and X cannot derive it even at 5 rounds, so a
fortiori not within the gate's budget.) -/
theorem equivocation_underivable : ¬ Discharged (10 : Atom) factsX := by
  rw [discharged_iff_derivable]
  -- `goal=10` is not in the 2-round closure of `factsX` — decide on the concrete engine.
  decide

/-- The same refusal stated as the contrapositive of the bridge: a goal outside the closure is not
dischargeable, for ANY budget the gate could pick. (Concretely: X never derives `10`, even at 5
rounds — `PolisDatalog.equivocation_underivable`.) -/
theorem out_of_closure_not_discharged :
    ¬ Derivable RULES factsX 10 5 ∧ ¬ Discharged (10 : Atom) factsX :=
  ⟨Metatheory.PolisDatalog.equivocation_underivable, equivocation_underivable⟩

/-! ### Coalition: pooled facts discharge a goal neither agent alone can. -/

/-- **Coalition discharges.** The pooled facts `factsX ++ factsY = [3,4]` derive the conjunctive
`goal=10` in one round, so by the bridge the coalition's combined knowledge DISCHARGES it — the
cross-vat gate opens for the coalition. (Reuses `PolisDatalog.coalition_derives` via the bridge.) -/
theorem coalition_discharges : Discharged (10 : Atom) (factsX ++ factsY) := by
  rw [discharged_iff_derivable]
  -- `K = 2`; the coalition rule fires within 1 round, monotone up to 2.
  decide

/-- **Neither agent alone discharges the coalition goal.** X lacks fact-4, Y lacks fact-3; neither
single-agent fact set puts `goal=10` in the closure, so the gate refuses each. -/
theorem single_agent_cannot_discharge :
    ¬ Discharged (10 : Atom) factsX ∧ ¬ Discharged (10 : Atom) factsY := by
  constructor <;> · rw [discharged_iff_derivable]; decide

/-- **Coalition strictly adds, at the discharge gate.** Neither X nor Y alone discharges `goal=10`,
yet their pooled facts do — the genuine coordination gain, now measured by the REAL consequence
closure instead of the two-fact stub. -/
theorem coalition_strictly_adds :
    (¬ Discharged (10 : Atom) factsX)
      ∧ (¬ Discharged (10 : Atom) factsY)
      ∧ Discharged (10 : Atom) (factsX ++ factsY) :=
  ⟨single_agent_cannot_discharge.1, single_agent_cannot_discharge.2, coalition_discharges⟩

/-! ### Viability = the real multi-step derivation, not a single check. -/

/-- **Knowledge-viability over the deployed seam.** An agent with `facts` is viable for `goal` iff the
discharge gate accepts — which, by `discharged_iff_derivable`, IS membership in the genuine multi-step
Datalog consequence closure. This is the real replacement for `PolisAuthReachFull`'s `bothFacts`
discharge: the same `Discharged` object, but its verifier is forward-chaining derivation. -/
def KnowReachesD (goal : Atom) (facts : List Atom) : Prop :=
  Discharged goal facts

instance (goal facts) : Decidable (KnowReachesD goal facts) :=
  inferInstanceAs (Decidable (Discharged goal facts))

/-- **Viability is genuinely MULTI-STEP.** From the single fact `c=2`, the agent is viable for the
chain goal `a=0` — which is NOT a fact and NOT one rule away: it is derived through `a ← b ← c` over
two rounds. The discharge gate, being the real closure, accepts this; a one-shot membership check
would not. (Bridges to `PolisDatalog.multi_step_derivation`.) -/
theorem viability_is_multistep : KnowReachesD 0 [2] := by
  unfold KnowReachesD
  rw [discharged_iff_derivable]
  -- `a=0` enters the closure only at round 2 (`a ← b ← c`); `K = 2` admits it.
  decide

/-- **And not a single round.** The chain goal `a=0` is NOT in the one-round closure of `[2]` — so the
viability above is a true multi-step derivation, not a disguised direct fact. (Bridges to
`PolisDatalog.one_step_insufficient`: `a` needs the full chain.) -/
theorem viability_needs_the_chain : ¬ Derivable RULES [2] 0 1 :=
  Metatheory.PolisDatalog.one_step_insufficient

/-- **Coalition restores viability over the real closure, in one line.** With its own facts, an agent
is NOT viable for `goal=10`; pooling with the coalition makes it viable — the same agent, same gate,
viability turned on purely by coordinating REAL knowledge. The discharge object here is the genuine
Datalog consequence closure, not the two-fact stub. -/
theorem coalition_restores_viability :
    KnowReachesD 10 (factsX ++ factsY) ∧ ¬ KnowReachesD 10 factsX :=
  ⟨coalition_discharges, single_agent_cannot_discharge.1⟩

/-! ## Runnable: watch the discharge gate decide on the real engine. -/

-- The gate refuses X's equivocal claim to `goal=10`, accepts the coalition, accepts the multi-step
-- chain goal, and refuses the chain goal to a one-round budget (here the gate's K=2 accepts it).
#eval decide (Discharged (10 : Atom) factsX)            -- false (equivocation refused)
#eval decide (Discharged (10 : Atom) (factsX ++ factsY)) -- true  (coalition discharges)
#eval decide (Discharged (0 : Atom) [2])                 -- true  (multi-step chain a ← b ← c)
#eval deriveWithin RULES (factsX ++ factsY) K            -- [3, 4, 10, ...] — the closure adds the goal

end Metatheory.PolisAuthDatalog
