/-
# Market.Fairness — DrEX rung 1, the FAIRNESS half: the clearing RESPECTS EVERY DECLARED LIMIT.

**Conservation ≠ fairness.** `Dregg2/Intent/Ring.lean` already proves the multilateral ring
clears SOUNDLY: `settleRing_conserves` (per-asset supply preserved across the whole ring),
`settleRing_atomic` (any leg fails ⇒ the whole ring rolls back), `RingBalanced` (the structural
closed-accounting shape), and the RECEIVE-side individual rationality
(`cycle_individuallyRational`: every participant receives the asset it WANTED, ≥ its declared
minimum). Those are DONE — this module COMPOSES with them and re-proves none of them.

What Ring.lean does NOT state is the **GIVE side**: that no participant is ever debited MORE
than it declared it offers, nor in an asset it did not offer. A conserving, atomic, receive-IR
ring could still gouge a giver (conservation only says the gouged value went to someone). This
module closes that gap:

  * **`settlement_from_sender_within_offer` (NEW)** — in the settlement built from any cycle
    the solver's graph admits (`CycleValid`), the leg debiting participant `j` carries EXACTLY
    `j`'s declared `offerAsset`, in an amount `≤ j`'s declared `offerAmount`. The proof reads
    the edge the graph itself checked (`CycleValid.edges`, the Rust `is_compatible`
    sufficiency): the solver cannot construct an over-debiting leg.
  * **`clearing_respects_limits` (THE FAIRNESS KEYSTONE)** — both sides, per participant:
    debited only its offered asset, never above its offered amount (new), AND credited its
    wanted asset, never below its declared minimum (composed from Ring.lean's
    `cycle_individuallyRational`). Every declared limit order is respected — nobody is worse
    off than their declaration, on either side of their trade.
  * **`cycleValid_fulfilled_respects_limits`** — the end-to-end: a graph-found cycle settled
    through the VERIFIED executor (`settleRing … = some k'`) is conserving (Ring.lean) AND
    `RingBalanced` (Ring.lean) AND limit-respecting for every participant (new). DrEX rung 1,
    both halves, over the running matcher's actual construction rule.

NON-VACUITY, both polarities: `validTriangle` — a genuine 3-party cycle (assets 10→11→12
chaining back) — is `CycleValid` and its settled legs sit STRICTLY inside every limit (amounts
6/5/4 against offers 8/9/7 — the `≤` is not secretly `=`; `#guard`s pin the computed legs). And
the teeth: an over-debiting "cycle" (Ring.lean's `underfundCycle`: the next node demands 50
against an offer of 3) and a wrong-asset one (`assetMismatchCycle`) are NOT `CycleValid`
(`overdebit_refused` / `wrongAsset_refused`) — a clearing that would breach a limit never forms,
so it never reaches `settleRing`.

NEXT RUNGS (named, not claimed): **uniform-price optimality** — all legs of a two-sided batch
on one pair clear at ONE price (the frequent-batch-auction discipline; needs the priced-book
layer of `Market/Clearing.lean` welded to the cycle model); **envy-freeness / TTC core
stability** — no coalition of participants can re-trade among themselves to strictly improve
(the Shapley–Scarf core theorem over `CycleValid`); **on-ledger per-participant deltas** — the
limit bounds read back off `RecordKernelState.bal` after a committed `settleRing` (needs the
per-cell delta induction over the fold). See `Market/Clearing.lean`'s header for the full DrEX
ladder (rung 2 = order-book aggregation soundness; rung 3 = the shielded-pool weld + the
private-matching ZKP).

Pure.
-/
import Dregg2.Intent.Ring
import Dregg2.Tactics

namespace Market

open Dregg2.Intent.Ring
open Dregg2.Exec (AssetId CellId RecordKernelState recTotalAsset)

/-! ## 1. The GIVE-side limit law (the new half). -/

/-- `getD` over the `toRingNode`-projected node list pulls the projection through (in-range).
The same bridge Ring.lean uses inline in `settlement_to_receiver_is_wanted`, surfaced as a
lemma. -/
theorem getD_map_toRingNode (ns : List MatchNode) (i : ℕ) (hi : i < ns.length) :
    (ns.map MatchNode.toRingNode).getD i default = (ns.getD i default).toRingNode := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hi]
  rfl

/-- **THE NEW HALF — no participant is debited beyond its declaration.** In the settlement the
solver builds from ANY graph-admitted cycle (`CycleValid ns`), the leg debiting participant `j`
(leg `j` of the chained ring — the unique leg with `from_ = creator[j]`):

  * debits exactly participant `j` (`from_ = creator[j]`);
  * carries EXACTLY `j`'s declared `offerAsset` — nobody's un-offered assets are touched;
  * in amount `≤ j`'s declared `offerAmount` — nobody gives more than they put on the table.

The amount bound is the graph's own edge (`CycleValid.edges`, the Rust `is_compatible`
sufficiency check `offer_amount ≥ want_min_amount` at `solver.rs:541`): leg `j`'s amount is the
NEXT node's `wantMin`, which the edge `j → j+1` caps by `offerAmount[j]`. The give-side mirror
of Ring.lean's `settlement_to_receiver_is_wanted`. -/
theorem settlement_from_sender_within_offer {ns : List MatchNode} (h : CycleValid ns)
    (j : ℕ) (hj : j < ns.length) :
    (chainedLeg (ns.map MatchNode.toRingNode) j).from_ = (ns.getD j default).creator ∧
      (chainedLeg (ns.map MatchNode.toRingNode) j).asset = (ns.getD j default).offerAsset ∧
      (chainedLeg (ns.map MatchNode.toRingNode) j).amount ≤ (ns.getD j default).offerAmount := by
  have hmpos : 0 < ns.length := by have := h.len; omega
  have hlen' : (ns.map MatchNode.toRingNode).length = ns.length := map_toRingNode_length ns
  have hj' : (j + 1) % ns.length < ns.length := Nat.mod_lt _ hmpos
  refine ⟨?_, ?_, ?_⟩
  · simp only [chainedLeg, hlen', getD_map_toRingNode ns j hj, MatchNode.toRingNode]
  · simp only [chainedLeg, hlen', getD_map_toRingNode ns j hj, MatchNode.toRingNode]
  · have hedge := (h.edges j hj).2
    simp only [chainedLeg, hlen', getD_map_toRingNode ns _ hj', MatchNode.toRingNode]
    exact hedge

/-! ## 2. THE FAIRNESS KEYSTONE — both sides of every participant's declaration. -/

/-- **`clearing_respects_limits` — the clearing RESPECTS EVERY DECLARED LIMIT (DrEX rung-1
fairness).** For every participant `j` of a graph-admitted cycle:

  * (GIVE, new) `j` is debited only its declared `offerAsset`, in amount `≤ offerAmount[j]`
    (`settlement_from_sender_within_offer`);
  * (RECEIVE, composed from Ring.lean) `j` is credited exactly its declared `wantAsset`, in
    amount `≥ wantMin[j]` (`cycle_individuallyRational` — the Shapley–Scarf TTC property).

Together: NO participant is worse off than its declaration on EITHER side of its trade — the
fairness half that conservation (`settleRing_conserves`) cannot express, since conservation is
indifferent to WHO gained the moved value. FALSIFIER: `underfundCycle` (demand 50 of an offer
of 3) — a cycle whose settlement would breach the give-side bound is not `CycleValid` at all
(`overdebit_refused` below), so this statement has real refusing power. -/
theorem clearing_respects_limits {ns : List MatchNode} (h : CycleValid ns)
    (j : ℕ) (hj : j < ns.length) :
    ((chainedLeg (ns.map MatchNode.toRingNode) j).from_ = (ns.getD j default).creator ∧
      (chainedLeg (ns.map MatchNode.toRingNode) j).asset = (ns.getD j default).offerAsset ∧
      (chainedLeg (ns.map MatchNode.toRingNode) j).amount ≤ (ns.getD j default).offerAmount) ∧
    (receivedAsset ns j = (ns.getD j default).wantAsset ∧
      (ns.getD j default).wantMin ≤ receivedAmount ns j) :=
  ⟨settlement_from_sender_within_offer h j hj, cycle_individuallyRational h j hj⟩

/-- **The end-to-end DrEX rung-1 statement** — a graph-found cycle settled through the VERIFIED
executor is (composing Ring.lean, NOT re-proving it):

  * **conserving** — every asset's total supply preserved (`settleRing_conserves`);
  * **balanced** — structurally closed, no phantom value (`cycleValid_settlement_balanced`);
  * **limit-respecting** — every participant within its declaration, both sides (new).

Atomicity rides separately on the same fold (`settleRing_atomic`: if any leg fails there IS no
`some k'`). The exchange's matching engine, as one theorem. -/
theorem cycleValid_fulfilled_respects_limits {ns : List MatchNode}
    (h : CycleValid ns) (hpos : ∀ n ∈ ns, 0 < n.wantMin)
    (k k' : RecordKernelState) (hsettle : settleRing k (settlementsOf ns) = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) ∧
      RingBalanced (settlementsOf ns) ∧
      (∀ j, j < ns.length →
        ((chainedLeg (ns.map MatchNode.toRingNode) j).asset = (ns.getD j default).offerAsset ∧
          (chainedLeg (ns.map MatchNode.toRingNode) j).amount
            ≤ (ns.getD j default).offerAmount) ∧
        (receivedAsset ns j = (ns.getD j default).wantAsset ∧
          (ns.getD j default).wantMin ≤ receivedAmount ns j)) :=
  ⟨settleRing_conserves (settlementsOf ns) k k' hsettle,
   cycleValid_settlement_balanced h hpos,
   fun j hj =>
     ⟨(settlement_from_sender_within_offer h j hj).2, cycle_individuallyRational h j hj⟩⟩

/-! ## 3. NON-VACUITY, positive polarity — a genuine 3-party cycle, strictly inside its limits. -/

/-- A genuine 3-party matching cycle: creator 1 offers 8 of asset 10 (wants ≥ 4 of asset 12),
creator 2 offers 9 of asset 11 (wants ≥ 6 of asset 10), creator 3 offers 7 of asset 12 (wants
≥ 5 of asset 11). The assets chain 10 → 11 → 12 → 10; every offer covers the next want with
STRICT surplus (8 > 6, 9 > 5, 7 > 4), so the settled legs sit strictly inside every limit —
the `≤` of the keystone is not secretly `=`. -/
def validTriangle : List MatchNode :=
  [ { creator := 1, offerAsset := 10, offerAmount := 8, wantAsset := 12, wantMin := 4 },
    { creator := 2, offerAsset := 11, offerAmount := 9, wantAsset := 10, wantMin := 6 },
    { creator := 3, offerAsset := 12, offerAmount := 7, wantAsset := 11, wantMin := 5 } ]

/-- The triangle is a cycle the solver's graph admits: length 3, every consecutive edge
compatible, creators distinct. -/
theorem validTriangle_valid : CycleValid validTriangle where
  len := by decide
  edges := by decide
  distinct := by
    intro i j hi hj hij
    have hlen : validTriangle.length = 3 := rfl
    rw [hlen] at hi hj
    have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases hi3 with rfl | rfl | rfl <;> rcases hj3 with rfl | rfl | rfl <;>
      first
      | (exact absurd rfl hij)
      | decide

/-- The fairness keystone, INSTANTIATED on the triangle — every one of the three participants
is within its declaration on both sides. (The `#guard`s below pin the computed legs: amounts
6/5/4 against offers 8/9/7, each in the declared asset.) -/
theorem validTriangle_respects_limits :
    ∀ j, j < validTriangle.length →
      ((chainedLeg (validTriangle.map MatchNode.toRingNode) j).asset
          = (validTriangle.getD j default).offerAsset ∧
        (chainedLeg (validTriangle.map MatchNode.toRingNode) j).amount
          ≤ (validTriangle.getD j default).offerAmount) ∧
      (receivedAsset validTriangle j = (validTriangle.getD j default).wantAsset ∧
        (validTriangle.getD j default).wantMin ≤ receivedAmount validTriangle j) :=
  fun j hj =>
    ⟨(settlement_from_sender_within_offer validTriangle_valid j hj).2,
     cycle_individuallyRational validTriangle_valid j hj⟩

/-! ## 4. NON-VACUITY, negative polarity — the teeth (an unfair clearing never FORMS). -/

/-- **TOOTH (give side): an over-debiting cycle is REFUSED.** Ring.lean's `underfundCycle` —
node 1 demands a minimum of 50 of asset 10 against node 0's offer of 3 — would, if settled,
debit node 0 by 50 > 3, breaching its declared limit. It never gets that far: the cycle is not
`CycleValid` (the graph admits no edge `0 → 1`, `underfundCycle_no_edge`), so no settlement is
ever constructed from it. Fairness is enforced at FORMATION, not policed after. -/
theorem overdebit_refused : ¬ CycleValid underfundCycle :=
  fun h => underfundCycle_no_edge (h.edges 0 (by decide))

/-- **TOOTH (receive side): a wrong-asset match is REFUSED.** Ring.lean's `assetMismatchCycle`
— node 1 wants asset 99 but node 0 offers asset 10 — would credit node 1 an asset it never
asked for. Not `CycleValid` (`assetMismatchCycle_no_edge`): the graph refuses to match anyone
into an un-wanted asset. -/
theorem wrongAsset_refused : ¬ CycleValid assetMismatchCycle :=
  fun h => assetMismatchCycle_no_edge (h.edges 0 (by decide))

/-! ### `#guard` smoke — the triangle's cleared legs, computed. -/

-- leg j debits creator j+1's want from creator j, in creator j's offered asset:
#guard ((settlementsOf validTriangle).getD 0 default).from_ == 1
#guard ((settlementsOf validTriangle).getD 0 default).to_ == 2
#guard ((settlementsOf validTriangle).getD 0 default).asset == 10
#guard ((settlementsOf validTriangle).getD 0 default).amount == 6   -- ≤ offer 8, STRICT
#guard ((settlementsOf validTriangle).getD 1 default).asset == 11
#guard ((settlementsOf validTriangle).getD 1 default).amount == 5   -- ≤ offer 9, STRICT
#guard ((settlementsOf validTriangle).getD 2 default).asset == 12
#guard ((settlementsOf validTriangle).getD 2 default).amount == 4   -- ≤ offer 7, STRICT
-- every participant receives its wanted asset, at ≥ its declared minimum:
#guard receivedAsset validTriangle 0 == 12
#guard receivedAmount validTriangle 0 == 4
#guard receivedAsset validTriangle 1 == 10
#guard receivedAmount validTriangle 1 == 6
#guard receivedAsset validTriangle 2 == 11
#guard receivedAmount validTriangle 2 == 5

/-! ### Axiom hygiene — the fairness keystones pinned to the three kernel axioms. -/

#assert_all_clean [Market.getD_map_toRingNode, Market.settlement_from_sender_within_offer,
  Market.clearing_respects_limits, Market.cycleValid_fulfilled_respects_limits,
  Market.validTriangle_valid, Market.validTriangle_respects_limits,
  Market.overdebit_refused, Market.wrongAsset_refused]

end Market
