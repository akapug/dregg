/-
# Metatheory.Bridge.HoldingWeightedTally — the "holding → weight → verified OUTCOME,
foldable" vertebra: a weighted TALLY / DECISION as a light-client FOLD, sound over the
chain-agnostic proof-of-holdings model.

`Dregg2.Bridge.ProofOfHoldingsGeneric` proves that a single granted governance weight is
BACKED (a consensus-proven, `Finalized`, genuinely-`Holds`ing snapshot of at least that
weight), NON-CUSTODIAL (the grant never mutates ledger state), and FOLD-COMPATIBLE
(`foldWeights` sums per-holding contributions and `foldWeights_append` is the segment-fold
homomorphism a recursive light client exploits). This file lifts that ONE vertebra from a
single holding up to the VOTE OUTCOME: a list of ballots (consensus-proven holdings) folds
to a weighted total, a `DecisionRule` evaluates on the fold, and the passing decision is
SOUND — the cleared weight is exactly the sum of consensus-proven, non-custodial holdings,
with no inflation.

## The tally / decision model (mirrors the DEPLOYED `dregg-governance` rule)
`DecisionRule` mirrors `dregg-governance/src/lib.rs::DecisionRule` (`:136`) and `passes`
mirrors `VoteEngine::resolve` (`:499`):
  * `threshold w₀`      — an option must clear `w₀` weight (`Threshold { min }`, `:507`).
  * `supermajority n d` — the weighted fraction clears `n/d` of the total
                          (`Supermajority`, the `⌊2n/3⌋+1` gate, `:518`); modeled as the
                          clean rational comparison `n·total ≤ d·weightedTotal`.
  * `plurality q`       — a quorum `q` of total ballot weight must be in before the poll
                          decides (`Plurality { quorum }`, the `if total < quorum` gate,
                          `:531`).
`passes rule weightedTotal total : Prop` is the decision predicate; each branch is a `Nat`
comparison (decidable), so the gate has computable teeth.

## The fold at the DECISION layer
`tallyWeight = foldWeights` and `tallyWeight_append` inherit the segment-fold homomorphism,
so `passes_on_fold` says a recursive verifier may fold two ballot segments INDEPENDENTLY
and evaluate the rule once on the combined weighted total. `FoldableVerifiedOutcome` is the
clean predicate — every ballot backed AND the rule cleared on the fold —
and `foldable_outcome_segments` decomposes it across a concatenation.

## The keystone — `decision_backed`
If `passes rule (foldWeights ballots) total` and every ballot is a `consensusVerified`,
`Finalized`, genuinely-`Holds`ing grant (`AllBacked`), then the passing decision is BACKED:
(1) it still passes on the cleared weight, (2) the cleared weight is EXACTLY the sum of the
proven balances — no inflation, reusing the snapshot-pin from the generic model, and (3)
every counted ballot is a genuine non-custodial `grantsWeightG` of its own proven balance.
`tally_noncustodial` (= `tallyRun_state`) proves running the DEPLOYED grant over every
ballot leaves ledger state definitionally unchanged — evaluating the decision is a pure
read.

## Non-vacuity (the soundness BITES — not `True`-shaped)
Instantiated at the SECOND, genuinely-different `toyChain` of the generic file (state-
dependent finality, non-trivial `Holds`):
  * PASSING: three consensus-proven holdings fold to `150`, clearing a `threshold 120`
    (and a `2/3` supermajority) — `FoldableVerifiedOutcome` + `decision_backed` FIRE.
  * TEETH: a `structureOnly` ballot contributes `0`, so the fold is only `100` and the same
    `threshold 120` does NOT pass (`decision_structureOnly_teeth`); a `plurality 200` does
    NOT reach on `total = 150` (`plurality_below_quorum_teeth`); a shortened weight fails
    the supermajority (`supermajority_teeth`). The gate refuses exactly when the backing is
    short or a ballot is not consensus-proven.

Kernel-clean: `#assert_axioms` hard-gates every theorem ⊆ {propext, Classical.choice,
Quot.sound}. The finality/holds oracles stay ASSUMED `ChainParams` fields — never `axiom`,
never a laundered `def FooHard`.
-/
import Dregg2.Bridge.ProofOfHoldingsGeneric

namespace Dregg2.Bridge.HoldingWeightedTally

open Dregg2.Bridge.ProofOfHoldingsGeneric

/-! ## §1 — The decision rule and the `passes` gate (mirror of `dregg-governance`). -/

/-- **`DecisionRule`** — how a poll decides, mirroring `dregg-governance::DecisionRule`
(`lib.rs:136`). `threshold` = an option clears a minimum weight; `supermajority n d` = the
weighted fraction clears `n/d` of the total; `plurality q` = a total-weight quorum `q` must
be in before the poll decides. -/
inductive DecisionRule
  /-- An option must reach `w₀` weight (`Threshold { min := w₀ }`). -/
  | threshold (w₀ : Nat)
  /-- The weighted total must clear the fraction `num/den` of `total`
  (`Supermajority`, the `⌊2n/3⌋+1` gate; here the clean rational comparison). -/
  | supermajority (num den : Nat)
  /-- A total-weight quorum `q` must be reached before the poll decides
  (`Plurality { quorum := q }`). -/
  | plurality (quorum : Nat)
deriving DecidableEq, Repr

/-- **`passes rule weightedTotal total`** — the decision gate, mirroring
`VoteEngine::resolve` (`lib.rs:499`). `threshold` clears when the weighted total meets the
minimum; `supermajority` when `num·total ≤ den·weightedTotal` (the weighted fraction is at
least `num/den`); `plurality` when the total weight has reached the quorum. Each branch is a
decidable `Nat` comparison. -/
def passes : DecisionRule → Nat → Nat → Prop
  | .threshold w₀,        wt, _   => w₀ ≤ wt
  | .supermajority num den, wt, tot => num * tot ≤ den * wt
  | .plurality quorum,    _,  tot => quorum ≤ tot

/-! ## §2 — The ballot list, its fold, and the decision-layer fold homomorphism.

A ballot is a `(GHolding C × Bool)` — a proof-of-holding and the light client's decidable
finality verdict, exactly the fold step of `ProofOfHoldingsGeneric.foldWeights`. The weighted
tally IS `foldWeights`; the decision layer inherits its segment-fold homomorphism. -/

/-- **`tallyWeight C ballots`** — the weighted total a folding verifier accumulates over a
ballot list: the sum of the per-holding non-custodial contributions. Definitionally the
generic `foldWeights` — the tally layer adds no new arithmetic, it reuses the proven fold. -/
def tallyWeight (C : ChainParams) (ballots : List (GHolding C × Bool)) : Nat :=
  foldWeights C ballots

/-- **DECISION-LAYER FOLD HOMOMORPHISM.** The weighted total over a concatenation of ballot
segments is the sum of the segment totals — inherited from `foldWeights_append`. A recursive
light client folds two segments independently and combines by `+`. -/
theorem tallyWeight_append (C : ChainParams) (l1 l2 : List (GHolding C × Bool)) :
    tallyWeight C (l1 ++ l2) = tallyWeight C l1 + tallyWeight C l2 :=
  foldWeights_append C l1 l2

/-- **THE RULE EVALUATES ON THE FOLD.** A decision over concatenated ballot segments passes
iff it passes on the SUM of the segment totals — so a fold verifier splits the ballots,
folds each part, adds, and evaluates the rule once. The clean "foldable verified outcome"
shape at the decision layer. -/
theorem passes_on_fold (C : ChainParams) (rule : DecisionRule)
    (l1 l2 : List (GHolding C × Bool)) (total : Nat) :
    passes rule (tallyWeight C (l1 ++ l2)) total
      ↔ passes rule (tallyWeight C l1 + tallyWeight C l2) total := by
  rw [tallyWeight_append]

/-! ## §3 — Backed ballots and the anti-inflation / non-custodial keystone. -/

/-- **`BallotBacked C st b`** — a ballot `(g, fv)` is BACKED in state `st` when its holding
is consensus-proven, the light client's finality verdict is affirmative, its height is
genuinely `Finalized` in `st`, and its proof genuinely `Holds` the claimed balance. This is
exactly the hypothesis under which the fold step credits `g`'s full amount. -/
def BallotBacked (C : ChainParams) (st : C.State) (b : GHolding C × Bool) : Prop :=
  b.1.tier = GTier.consensusVerified
    ∧ b.2 = true
    ∧ C.Finalized b.1.height st
    ∧ C.Holds b.1.proof b.1.owner b.1.asset b.1.amount b.1.height

/-- **`AllBacked C st ballots`** — every ballot in the list is backed in `st`. -/
def AllBacked (C : ChainParams) (st : C.State) (ballots : List (GHolding C × Bool)) : Prop :=
  ∀ b ∈ ballots, BallotBacked C st b

/-- A backed ballot's fold contribution is EXACTLY its single proven balance — the fold
credits neither more (no inflation) nor less than the snapshot amount. -/
theorem backed_contribution (C : ChainParams) (st : C.State) (b : GHolding C × Bool)
    (h : BallotBacked C st b) : foldContribution C b.1 b.2 = b.1.amount := by
  obtain ⟨htier, hfv, _, _⟩ := h
  simp [foldContribution, grantWeightCoreG, GTier.isConsensusVerified, htier, hfv]

/-- A backed ballot is a genuine non-custodial weight grant of its own proven balance:
`grantsWeightG` fires for the owner at exactly the amount (via the generic model). -/
theorem backed_grants (C : ChainParams) (st : C.State) (b : GHolding C × Bool)
    (h : BallotBacked C st b) : grantsWeightG C st b.1 b.1.owner b.1.amount := by
  obtain ⟨htier, _, hfin, hholds⟩ := h
  exact ⟨htier, hfin, hholds, rfl, Nat.le_refl _⟩

/-- `foldWeights` on a `cons` peels one contribution — the recursion the anti-inflation
proof folds over. -/
theorem foldWeights_cons (C : ChainParams) (b : GHolding C × Bool)
    (bs : List (GHolding C × Bool)) :
    foldWeights C (b :: bs) = foldContribution C b.1 b.2 + foldWeights C bs := by
  simp [foldWeights]

/-- **NO INFLATION.** Under `AllBacked`, the folded weighted total is EXACTLY the sum of the
proven ballot balances — the tally can credit no more than the consensus-proven snapshots. -/
theorem backed_no_inflation (C : ChainParams) (st : C.State) :
    ∀ (ballots : List (GHolding C × Bool)), AllBacked C st ballots →
      foldWeights C ballots = (ballots.map (fun b => b.1.amount)).sum
  | [], _ => rfl
  | b :: bs, hall => by
      have hb : BallotBacked C st b := hall b (List.mem_cons.mpr (Or.inl rfl))
      have hbs : AllBacked C st bs := fun x hx => hall x (List.mem_cons.mpr (Or.inr hx))
      rw [foldWeights_cons, backed_contribution C st b hb, backed_no_inflation C st bs hbs]
      simp [List.map_cons, List.sum_cons]

/-- **THE KEYSTONE — `decision_backed`.** If a decision passes on the folded weighted total
and every ballot is backed (consensus-proven, finalized, genuinely holding), then the
passing decision is SOUND: (1) it passes on the cleared weight, (2) that cleared weight is
EXACTLY the sum of the proven balances — no inflation, and (3) every counted ballot is a
genuine non-custodial `grantsWeightG` of its own proven balance. The cleared weight is thus
demonstrably the sum of consensus-proven, non-custodial holdings — the vote outcome inherits
the proof-of-holdings guarantee. -/
theorem decision_backed (C : ChainParams) (st : C.State) (rule : DecisionRule)
    (ballots : List (GHolding C × Bool)) (total : Nat)
    (hpass : passes rule (foldWeights C ballots) total)
    (hall : AllBacked C st ballots) :
    passes rule (foldWeights C ballots) total
    ∧ foldWeights C ballots = (ballots.map (fun b => b.1.amount)).sum
    ∧ ∀ b ∈ ballots, grantsWeightG C st b.1 b.1.owner b.1.amount
                     ∧ foldContribution C b.1 b.2 = b.1.amount := by
  refine ⟨hpass, backed_no_inflation C st ballots hall, ?_⟩
  intro b hb
  have hbk := hall b hb
  exact ⟨backed_grants C st b hbk, backed_contribution C st b hbk⟩

/-! ## §4 — `tally_noncustodial`: running the DEPLOYED grant per ballot never mutates state.

`tallyRun` folds the deployed non-custodial `grantWeightG` over the ballots, accumulating the
weighted total AND threading the ledger state. `tallyRun_state` proves the state is left
definitionally unchanged (evaluating the decision is a pure read); `tallyRun_weight` proves
the accumulated total is exactly the fold. -/

/-- One tally step: credit the per-holding contribution and thread the state through the
DEPLOYED grant (whose state output is a pure read). -/
def tallyStep (C : ChainParams) (acc : Nat × C.State) (b : GHolding C × Bool) : Nat × C.State :=
  (acc.1 + foldContribution C b.1 b.2, (grantWeightG C b.1 b.2 acc.2).2)

/-- **`tallyRun C ballots pre`** — fold the deployed grant over the ballots from prior state
`pre`, returning `(weighted total, resulting ledger state)`. -/
def tallyRun (C : ChainParams) (ballots : List (GHolding C × Bool)) (pre : C.State) :
    Nat × C.State :=
  ballots.foldl (tallyStep C) (0, pre)

/-- **`tally_noncustodial`.** Running the deployed grant over EVERY ballot leaves the ledger
state definitionally unchanged — evaluating the whole decision is a pure read of the proofs,
no custody moved. -/
theorem tallyRun_state (C : ChainParams) (ballots : List (GHolding C × Bool)) (pre : C.State) :
    (tallyRun C ballots pre).2 = pre := by
  have h : ∀ (bs : List (GHolding C × Bool)) (acc : Nat × C.State),
      acc.2 = pre → (bs.foldl (tallyStep C) acc).2 = pre := by
    intro bs
    induction bs with
    | nil => intro acc hacc; exact hacc
    | cons b bs' ih =>
      intro acc hacc
      apply ih
      show (grantWeightG C b.1 b.2 acc.2).2 = pre
      rw [grant_preserves_custody_generic]
      exact hacc
  exact h ballots (0, pre) rfl

/-- The tally run accumulates EXACTLY the folded weighted total. -/
theorem tallyRun_weight (C : ChainParams) (ballots : List (GHolding C × Bool)) (pre : C.State) :
    (tallyRun C ballots pre).1 = foldWeights C ballots := by
  have h : ∀ (bs : List (GHolding C × Bool)) (acc : Nat × C.State),
      (bs.foldl (tallyStep C) acc).1 = acc.1 + foldWeights C bs := by
    intro bs
    induction bs with
    | nil => intro acc; simp [foldWeights]
    | cons b bs' ih =>
      intro acc
      show (bs'.foldl (tallyStep C) (tallyStep C acc b)).1 = acc.1 + foldWeights C (b :: bs')
      rw [ih, foldWeights_cons]
      simp only [tallyStep]
      omega
  have := h ballots (0, pre)
  simpa using this

/-! ## §5 — The clean "foldable verified outcome" predicate. -/

/-- **`FoldableVerifiedOutcome C st rule ballots total`** — the composite the light client
carries: every ballot is backed AND the rule clears on the folded weighted total. This is
the "holding → weight → verified outcome, foldable" object. -/
def FoldableVerifiedOutcome (C : ChainParams) (st : C.State) (rule : DecisionRule)
    (ballots : List (GHolding C × Bool)) (total : Nat) : Prop :=
  AllBacked C st ballots ∧ passes rule (foldWeights C ballots) total

/-- `AllBacked` distributes over concatenation — backing a fused ballot list is backing each
segment. -/
theorem AllBacked_append (C : ChainParams) (st : C.State) (l1 l2 : List (GHolding C × Bool)) :
    AllBacked C st (l1 ++ l2) ↔ AllBacked C st l1 ∧ AllBacked C st l2 := by
  constructor
  · intro h
    exact ⟨fun b hb => h b (List.mem_append_left _ hb),
           fun b hb => h b (List.mem_append_right _ hb)⟩
  · rintro ⟨h1, h2⟩ b hb
    rcases List.mem_append.1 hb with h | h
    · exact h1 b h
    · exact h2 b h

/-- **FOLDABLE VERIFIED OUTCOME DECOMPOSES OVER SEGMENTS.** A verified outcome over a
concatenation of ballot segments splits into per-segment backing PLUS the rule evaluated on
the SUM of the segment totals — exactly the work a recursive light client does: verify each
segment's backing independently, fold the weighted totals, evaluate the rule once. -/
theorem foldable_outcome_segments (C : ChainParams) (st : C.State) (rule : DecisionRule)
    (l1 l2 : List (GHolding C × Bool)) (total : Nat)
    (h : FoldableVerifiedOutcome C st rule (l1 ++ l2) total) :
    AllBacked C st l1 ∧ AllBacked C st l2
    ∧ passes rule (tallyWeight C l1 + tallyWeight C l2) total := by
  obtain ⟨hall, hpass⟩ := h
  obtain ⟨h1, h2⟩ := (AllBacked_append C st l1 l2).1 hall
  refine ⟨h1, h2, ?_⟩
  have hp : passes rule (tallyWeight C (l1 ++ l2)) total := hpass
  rwa [tallyWeight_append] at hp

/-! ## §6 — NON-VACUITY at the SECOND (genuinely different) `toyChain`.

`toyChain` (from `ProofOfHoldingsGeneric`) has STATE-DEPENDENT finality (`h ≤ st`) and a
NON-TRIVIAL `Holds` (`proof = amount`) — so the soundness has real teeth, not `True`-shape.
`toyProven` holds `50` (consensus, height `4`); `toyStructureOnly` is the same on the
`structureOnly` tier (grants nothing). -/

/-- Three consensus-proven ballots — fold to `150`. -/
def threeBallots : List (GHolding toyChain × Bool) :=
  [(toyProven, true), (toyProven, true), (toyProven, true)]

/-- The same list but the first ballot is `structureOnly` — it contributes `0`, so the fold
is only `100`. -/
def structBallots : List (GHolding toyChain × Bool) :=
  [(toyStructureOnly, true), (toyProven, true), (toyProven, true)]

/-- A ballot segment (`100`) for the fold-append demonstration. -/
def segA : List (GHolding toyChain × Bool) := [(toyProven, true), (toyProven, true)]

/-- A second ballot segment (`50`) for the fold-append demonstration. -/
def segB : List (GHolding toyChain × Bool) := [(toyProven, true)]

/-- A single consensus-proven toy ballot is backed at confirmed head `10` (height `4 ≤ 10`
final, proof `50 = 50` holds). -/
theorem toyProven_backed : BallotBacked toyChain 10 (toyProven, true) :=
  ⟨rfl, rfl, by decide, rfl⟩

/-- Every ballot in `threeBallots` is backed. -/
theorem allBacked_three : AllBacked toyChain 10 threeBallots := by
  intro b hb
  simp only [threeBallots, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h <;> (subst h; exact toyProven_backed)

/-- **PASSING (threshold).** Three consensus-proven holdings fold to `150`, clearing a
`threshold 120` — the decision passes. -/
theorem decision_pass_example :
    passes (DecisionRule.threshold 120) (foldWeights toyChain threeBallots) 150 := by
  show (120 : Nat) ≤ foldWeights toyChain threeBallots
  decide

/-- **PASSING (supermajority).** The same fold (`150`) clears a `2/3` supermajority of a
`total` of `150` (`2·150 = 300 ≤ 3·150 = 450`). -/
theorem supermajority_example :
    passes (DecisionRule.supermajority 2 3) (foldWeights toyChain threeBallots) 150 := by
  show 2 * 150 ≤ 3 * foldWeights toyChain threeBallots
  decide

/-- **THE FOLDABLE VERIFIED OUTCOME FIRES** — every ballot backed AND `threshold 120`
cleared on the fold. -/
theorem example_foldable_outcome :
    FoldableVerifiedOutcome toyChain 10 (DecisionRule.threshold 120) threeBallots 150 :=
  ⟨allBacked_three, decision_pass_example⟩

/-- **THE KEYSTONE FIRES on a concrete passing decision** — `decision_backed` yields the
sound outcome: passes, no inflation (cleared weight = sum of proven balances = `150`), and
every counted ballot a genuine non-custodial grant. -/
theorem example_decision_backed :
    passes (DecisionRule.threshold 120) (foldWeights toyChain threeBallots) 150
    ∧ foldWeights toyChain threeBallots
        = (threeBallots.map (fun b => b.1.amount)).sum
    ∧ ∀ b ∈ threeBallots, grantsWeightG toyChain 10 b.1 b.1.owner b.1.amount
                          ∧ foldContribution toyChain b.1 b.2 = b.1.amount :=
  decision_backed toyChain 10 (DecisionRule.threshold 120) threeBallots 150
    decision_pass_example allBacked_three

/-- **TEETH (structureOnly).** With the first ballot `structureOnly` it contributes `0`, so
the fold is only `100` and the SAME `threshold 120` does NOT pass. The soundness bites: a
non-consensus ballot cannot inflate the outcome into passing. -/
theorem decision_structureOnly_teeth :
    ¬ passes (DecisionRule.threshold 120) (foldWeights toyChain structBallots) 100 := by
  show ¬ (120 : Nat) ≤ foldWeights toyChain structBallots
  decide

/-- **TEETH (below quorum).** A `plurality 200` does NOT reach on a `total` of `150` — the
quorum gate refuses (the deployed `if total < quorum` law). -/
theorem plurality_below_quorum_teeth :
    ¬ passes (DecisionRule.plurality 200) (foldWeights toyChain threeBallots) 150 := by
  show ¬ (200 : Nat) ≤ 150
  decide

/-- **TEETH (short supermajority).** The `structureOnly`-shortened fold (`100`) fails a `2/3`
supermajority of a `total` of `200` (`2·200 = 400 > 3·100 = 300`). -/
theorem supermajority_teeth :
    ¬ passes (DecisionRule.supermajority 2 3) (foldWeights toyChain structBallots) 200 := by
  show ¬ (2 * 200 ≤ 3 * foldWeights toyChain structBallots)
  decide

/-- **NON-CUSTODIAL WITNESS.** Running the deployed grant over all three ballots from state
`10` leaves the state `10` and accumulates the full `150`. -/
theorem toy_tally_noncustodial :
    (tallyRun toyChain threeBallots 10).2 = 10
    ∧ (tallyRun toyChain threeBallots 10).1 = 150 :=
  ⟨tallyRun_state toyChain threeBallots 10, by rw [tallyRun_weight]; decide⟩

/-! It runs (`#guard`). -/

#guard foldWeights toyChain threeBallots == 150
#guard foldWeights toyChain structBallots == 100
#guard (threeBallots.map (fun b => b.1.amount)).sum == 150
#guard tallyWeight toyChain (segA ++ segB)
        == tallyWeight toyChain segA + tallyWeight toyChain segB
#guard (tallyRun toyChain threeBallots 0).1 == 150

/-! ## §7 — Axiom hygiene — every theorem kernel-clean (CI hard-gate). -/

#assert_axioms passes_on_fold
#assert_axioms tallyWeight_append
#assert_axioms backed_contribution
#assert_axioms backed_grants
#assert_axioms foldWeights_cons
#assert_axioms backed_no_inflation
#assert_axioms decision_backed
#assert_axioms tallyRun_state
#assert_axioms tallyRun_weight
#assert_axioms AllBacked_append
#assert_axioms foldable_outcome_segments

#assert_axioms toyProven_backed
#assert_axioms allBacked_three
#assert_axioms decision_pass_example
#assert_axioms supermajority_example
#assert_axioms example_foldable_outcome
#assert_axioms example_decision_backed
#assert_axioms decision_structureOnly_teeth
#assert_axioms plurality_below_quorum_teeth
#assert_axioms supermajority_teeth
#assert_axioms toy_tally_noncustodial

#print axioms decision_backed
#print axioms foldable_outcome_segments
#print axioms decision_structureOnly_teeth
#print axioms tallyRun_state

end Dregg2.Bridge.HoldingWeightedTally
