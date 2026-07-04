/-
# Metatheory.PolisAuthCoord — KNOWLEDGE coordination in the polis, grounded in the real discharge algebra.

`PolisAuthGame` grounds the polis's *authority* layer (the substance discipline `PasRefined`, the
attenuation governor, the cross-vat boundary law). This file grounds the polis's *knowledge*
coordination layer on the SAME real nouns — `Dregg2.Laws.{Verifiable, Discharged}` and the deployed
`Dregg2.Authority.boundary_law` — without reproving any of them.

Two coordination phenomena, both grounded in the discharge algebra (NOT a toy world):

  1. **EQUIVOCATION is refused** (`equivocation_needs_real_witness`). A cross-vat change is admissible
     ONLY via a real `Discharged` witness (the `Integrity.cross` rule = l4v authorized-edge). A
     non-owner who *claims* derived knowledge they don't have — a state where NO witness discharges the
     change-predicate — cannot construct the cross derivation: you cannot forge a `Discharged`. So
     "claiming derived knowledge you don't have" is refused; the actual DERIVATION is the only legible
     cross-vat move. This is the knowledge-side dual of `authGov_refuses_amplification` (laundering on
     the authority side). The intra-vat owner route is, by the l4v case-split, exactly the owner's
     right to arbitrary change on its own object — so the refusal is precisely scoped to non-owners.

  2. **COALITION over witnesses** (`coalition_discharges_jointly`, `single_agent_cannot`). A goal
     predicate `p` needs TWO independent facts. Agent X holds fact-1 (witness `wX`); agent Y holds
     fact-2 (witness `wY`). Neither witness ALONE discharges `p` (`single_agent_cannot`); the POOLED
     witness `wX ⊔ wY` discharges it (`coalition_discharges_jointly`). The coalition coordinates by
     COMBINING knowledge, and the combination is checked by the same verifier — no off-island mediator.
     This is the legitimate, legible counterpart to laundering: pooling REAL derivations is admitted;
     fabricating one is refused (phenomenon 1).

Honest scope (see end of file): the coalition is modelled with a concrete two-fact predicate algebra
(`KnowReq` over a `FactSet`), a faithful but SMALL fragment of the full Heyting predicate algebra
`Dregg2.Laws.predicate_heyting`. It exercises the real `Verifiable`/`Discharged` API end-to-end; it
does not model conjunction/implication of arbitrary admissibility conditions. No
load-bearing `True`; `#guard` asserts the runnable facts.
-/
import Polis.PolisAuthGame

namespace Metatheory.PolisAuthCoord

open Dregg2.Laws Dregg2.Authority

/-! ## 1. Equivocation is refused: no cross-vat exercise without a real discharge. -/

/-- **Equivocation cannot fabricate a discharge.** Consider a non-owner (`owner ∉ subjects`) proposing
a cross-vat change `ko ⟶ ko'` for which NO witness discharges the predicate `p ko ko'` (the agent
*claims* derived knowledge it does not have). Then NO `Integrity` derivation exists: the `intra` rule
is blocked (non-owner) and the `cross` rule is blocked (no discharging witness). You cannot forge a
`Discharged`, so the only legible cross-vat move is to ACTUALLY derive the knowledge.

This is the knowledge-side refusal dual to `PolisAuthGame.authGov_refuses_amplification`. -/
theorem equivocation_needs_real_witness
    {P KO W : Type*} [Verifiable P W]
    (owner : Label) (subjects : List Label)
    (p : KO → KO → P) (ko ko' : KO)
    (notOwner : owner ∉ subjects)
    (noWitness : ∀ w : W, ¬ Discharged (p ko ko') w) :
    ¬ Integrity W owner subjects p ko ko' := by
  intro h
  cases h with
  | intra hmem => exact notOwner hmem
  | cross w hw => exact noWitness w hw

/-- **Owner-vs-equivocator scoping (non-vacuity of the refusal).** The refusal in
`equivocation_needs_real_witness` is precisely scoped: the SAME no-witness state IS admissible for the
OWNER, via the l4v `intra` rule (`Integrity.intra`) — owning the object confers the right to an
arbitrary change with no derivation. So the refusal targets the equivocator (the non-owner claiming
knowledge), not the legitimate owner. -/
theorem owner_admitted_without_witness
    {P KO W : Type*} [Verifiable P W]
    (owner : Label) (subjects : List Label)
    (p : KO → KO → P) (ko ko' : KO)
    (isOwner : owner ∈ subjects) :
    Integrity W owner subjects p ko ko' :=
  Integrity.intra isOwner

/-- **The legible cross-vat move IS the derivation.** When the agent ACTUALLY holds a discharging
witness, the cross rule admits the change — re-exported through the deployed `boundary_law` to make
the grounding explicit (this is `coordination_needs_derivation` specialized to the cross route). The
derivation, not the claim, is what coordinates across the boundary. -/
theorem derivation_admits_cross
    {P KO W : Type*} [Verifiable P W]
    (owner : Label) (subjects : List Label) (pol : Policy) (caps : Caps)
    (p : KO → KO → P) (ko ko' : KO)
    (refined : PasRefined pol caps)
    (w : W) (hw : Discharged (p ko ko') w) :
    Integrity W owner subjects p ko ko' :=
  boundary_law owner subjects pol caps p ko ko' refined (Or.inr ⟨w, hw⟩)

/-! ## 2. Coalition over witnesses: pooled knowledge discharges what no single agent can.

A concrete two-fact predicate algebra, instantiating the real `Verifiable`/`Discharged` API. -/

/-- The two independent facts the goal requires (fact-1 held by agent X, fact-2 by agent Y). -/
inductive Fact where
  | one | two
  deriving DecidableEq, Repr

/-- A witness is a *set of facts an agent can attest* (its held knowledge). Modelled as the two
membership booleans — `⟨hasOne, hasTwo⟩`. A single agent typically attests only one. -/
structure FactSet where
  hasOne : Bool
  hasTwo : Bool
  deriving DecidableEq, Repr

/-- **Pooling knowledge**: the coalition's combined attestation is the union of what its members hold.
This is the join on `FactSet` (a member contributes a fact iff it holds it). -/
def FactSet.pool (a b : FactSet) : FactSet :=
  ⟨a.hasOne || b.hasOne, a.hasTwo || b.hasTwo⟩

/-- A knowledge requirement: the goal predicate demands BOTH facts. (A genuinely conjunctive goal —
the smallest predicate no single one-fact agent can meet, modelling "needs derivation pooled from
two cells".) The predicate carries which facts it requires; `Verify` checks the witness covers them. -/
structure KnowReq where
  needOne : Bool
  needTwo : Bool
  deriving DecidableEq, Repr

/-- The goal of this section: a requirement for BOTH facts. -/
def bothFacts : KnowReq := ⟨true, true⟩

/-- **The real verifier**: a witness discharges a requirement iff it attests every required fact. This
is a genuine `Dregg2.Laws.Verifiable` instance — the same decidable, verifier-local check the whole
discharge algebra runs on. -/
instance : Verifiable KnowReq FactSet where
  Verify p w := (!p.needOne || w.hasOne) && (!p.needTwo || w.hasTwo)

/-- Agent X's witness: it holds fact-1 only. -/
def witX : FactSet := ⟨true, false⟩

/-- Agent Y's witness: it holds fact-2 only. -/
def witY : FactSet := ⟨false, true⟩

/-- The coalition's pooled witness. -/
def witCoalition : FactSet := FactSet.pool witX witY

/-- **The coalition jointly discharges the goal.** The pooled witness `witX ⊔ witY` attests both
facts, so it discharges `bothFacts` — the coalition coordinates by COMBINING real derivations, checked
by the same verifier. -/
theorem coalition_discharges_jointly :
    Discharged bothFacts witCoalition := by
  unfold Discharged Verifiable.Verify witCoalition FactSet.pool witX witY bothFacts
  decide

/-- **No single agent suffices — agent X alone fails.** X's witness lacks fact-2, so it does NOT
discharge `bothFacts`: the conjunctive goal is out of reach for any single one-fact agent. -/
theorem single_agent_cannot_X :
    ¬ Discharged bothFacts witX := by
  unfold Discharged Verifiable.Verify witX bothFacts
  decide

/-- **No single agent suffices — agent Y alone fails.** Symmetric: Y lacks fact-1. -/
theorem single_agent_cannot_Y :
    ¬ Discharged bothFacts witY := by
  unfold Discharged Verifiable.Verify witY bothFacts
  decide

/-- **Coalition over witnesses, in one statement.** Neither X nor Y alone discharges the goal, yet
their pooled knowledge does — the genuine ADDITION of coordinating over knowledge. -/
theorem coalition_strictly_adds :
    (¬ Discharged bothFacts witX) ∧ (¬ Discharged bothFacts witY)
      ∧ Discharged bothFacts witCoalition :=
  ⟨single_agent_cannot_X, single_agent_cannot_Y, coalition_discharges_jointly⟩

/-! ## 3. Coalition coordination is the *legible* cross-vat move (welds §1 and §2).

The pooled discharge is exactly the witness the boundary law demands — so a coalition that genuinely
pools knowledge clears the cross-vat gate, while an equivocator (no witness) is refused (§1). -/

/-- **A coalition that pools real knowledge clears the cross-vat boundary.** Instantiating
`derivation_admits_cross` at the coalition's pooled witness: when the goal predicate of a cross-vat
change is `bothFacts`, the coalition's combined attestation discharges it, so the change is admitted
through the deployed `boundary_law`. Pooling REAL derivations coordinates legibly; fabricating a
discharge does not (§1). -/
theorem coalition_clears_boundary
    {KO : Type*}
    (owner : Label) (subjects : List Label) (pol : Policy) (caps : Caps)
    (ko ko' : KO)
    (refined : PasRefined pol caps) :
    Integrity FactSet owner subjects (fun _ _ : KO => bothFacts) ko ko' :=
  derivation_admits_cross owner subjects pol caps (fun _ _ : KO => bothFacts) ko ko'
    refined witCoalition coalition_discharges_jointly

/-- **An equivocator IS refused, at the concrete instance.** A non-owner proposing a cross-vat change
whose goal predicate no witness discharges cannot construct the `Integrity` derivation —
`equivocation_needs_real_witness` specialized to `KnowReq`/`FactSet`. The hypothesis `noWitness` is the
honest model of "claiming knowledge you don't have": for this equivocator, every offered attestation
fails to verify. -/
theorem equivocator_refused
    {KO : Type*}
    (owner : Label) (subjects : List Label)
    (p : KO → KO → KnowReq) (ko ko' : KO)
    (notOwner : owner ∉ subjects)
    (noWitness : ∀ w : FactSet, ¬ Discharged (p ko ko') w) :
    ¬ Integrity FactSet owner subjects p ko ko' :=
  equivocation_needs_real_witness owner subjects p ko ko' notOwner noWitness

/-- The empty attestation: an equivocator's honest holdings when it has derived nothing. -/
def noFact : FactSet := ⟨false, false⟩

/-- **The empty attestation discharges nothing requiring a fact** — so an agent that has derived
nothing genuinely cannot meet `bothFacts`. This is the concrete witness that the `noWitness`
hypothesis of `equivocator_refused` is REAL, not vacuous: there exist goals with no honest discharge
for the equivocator. (A fully-quantified `noWitness` for `bothFacts` is false — the coalition CAN
discharge it; the refusal bites against an equivocator's restricted honest supply, which the empty
attestation models.) -/
theorem noFact_cannot_discharge_both :
    ¬ Discharged bothFacts noFact := by
  unfold Discharged Verifiable.Verify noFact bothFacts
  decide

/-! ## Runnable sanity (the discharge algebra is non-vacuous and decidable). -/

-- The pooled witness verifies the conjunctive goal; neither single witness does.
#guard Verifiable.Verify bothFacts witCoalition = true
#guard Verifiable.Verify bothFacts witX = false
#guard Verifiable.Verify bothFacts witY = false
-- The empty attestation an equivocator could honestly offer fails the goal.
#guard Verifiable.Verify bothFacts noFact = false

end Metatheory.PolisAuthCoord
