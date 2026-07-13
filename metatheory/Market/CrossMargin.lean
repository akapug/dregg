/-
# Market.CrossMargin — DrEX rung 7: CROSS-MARGIN positions via the attenuable MANDATE.

**DrEX — the Dragon's EXchange** (`docs/deos/DREX-DESIGN.md`) climbs a ladder of proof-carrying
exchange rungs. Rung 7 (§3-#7 / §4) is **cross-margin & derivatives via the capability mandate**: a
trading position whose margin/authority is a *scoped, attenuated capability* — the mandate — backed by
a *proven-solvent* collateral reserve and clearing through the *fair* DrEX engine. Its thesis, from the
design: "a mandate breach is UNCONSTRUCTABLE, not monitored — trade up to $X, assets/venues {…}, no
withdrawals". No Hyperliquid/dYdX margin engine offers cryptographically-scoped, provably-non-amplifying
delegation.

This module **COMPOSES three already-PROVED towers; it re-proves none of them**:

  * **The MANDATE** (`Dregg2/Agent/Mandate.lean`, PROVED + materialized into committed executor moves):
    a position's total authority is a `Mandate` — `budget` (the max aggregate notional), `keep` (the
    rights bound), `caveat` (allowed assets / expiry / methods). Sub-delegated per-leg slices form a
    `DelegTree` whose budget is CONSERVED: `subtree_budget_le_root` (no descendant out-spends the root,
    the *non-amplification* axis for budget) and `children_no_oversubscribe` (the immediate slices SUM
    to ≤ the parent — the cross-margin heart: the shared authority pool is partitioned, never
    over-subscribed).
  * **SOLVENCY** (`Market/Liquidity.lean`, PROVED): `pool_solvent_forever` — the collateral reserve is
    never negative at any reachable state along ANY schedule of fills that respects the reserve floor
    (`ScheduleValid`), the ∀-adversary object lifted from `Dregg2/Verify/StripeReserve.lean`.
  * **FAIRNESS** (`Market/Priced.lean` rung 5 / `Market/Fairness.lean` rung 1, PROVED):
    `priced_clearing_keystone` — every leg of the position's priced book spends ≤ its `offerAmount`,
    executes at or above its `limitPrice`, and delivers ≥ its pro-rata minimum; and, for the
    ledger-realized ring legs, `clearing_respects_limits` (rung 1's exact-book fairness).

## The keystone — `crossMargin_position_sound`

A **cross-margin position** is a trader's scoping `Mandate` (root), a list of open trades (`Fill`s from
rung 5, each tagged with the child-mandate budget slice authorizing it), and one collateral `reserve`
(a rung-6 `Pool`). For a position that is **margin-scoped** (its induced delegation tree is
`WellAttenuated` + `BudgetPartitioned`) and whose reserve schedule is valid, we prove, in ONE theorem:

  * **(a) MARGIN-BOUNDED** — the position's total exposure never exceeds the root mandate's budget
    (`totalExposure ≤ root.budget`), composed from `children_no_oversubscribe` (the leg slices don't
    over-subscribe the mandate) with the per-leg "exposure ≤ its slice" discipline. Non-amplification
    (`subtree_budget_le_root`): every leg's authority ≤ the mandate.
  * **(b) COLLATERAL-BACKED / never-insolvent-under-margin** — the reserve is solvent at EVERY reachable
    state along the position's schedule (`pool_solvent_forever`): the margined position cannot drive the
    collateral reserve negative.
  * **(c) FAIRLY-CLEARED** — every leg respects its declared limit at the cleared price
    (`priced_clearing_keystone`); ring-realized legs additionally respect rung-1's
    `clearing_respects_limits`.

So a cross-margin position is a **mandate-scoped, collateral-backed, fairly-cleared** set of trades.

## Scope, stated plainly (HONEST)

This is a **MODEL-level** rung, like the other upper rungs (rungs 4/5/6, `Market/{Optimality,Priced,
Liquidity}.lean`): the margin bound is over the mandate's `Nat` budget and the priced `Fill` exposure
(ℚ); the collateral solvency is the ∀-schedule `Pool` reserve invariant (`AssetId → ℚ`), NOT welded to
`settleRing`/`recKExec`. Only rung 1 (`clearing_respects_limits` / the ring leg fairness composed here)
carries the executor tie. The design's rung-7 open weld — the **per-trade `caveatBit` reified as an
in-circuit constraint** (`Caveat.lean:59`; today the aggregate caveat still *trusts the executor's
decision*) — is NAMED, not claimed: this rung proves the **margin-bounded + collateral-backed +
fairly-cleared core** of a cross-margin position and names the in-circuit caveat admission + the shielded
cross-margin engine as the remaining build. The mandate's own delegation/budget/revocation are PROVED +
materialized (`materialize_non_amplifying`) upstream; here they SCOPE the margin.

NON-VACUITY, both polarities: a concrete position (`demoPos` — a root mandate, two priced trades within
budget, a backing reserve) satisfies all three keystones (`demoPos_sound`; the budget/exposure/reserve
numbers are `#guard`-pinned); and the teeth — an OVER-LEVERAGED position (leg slices summing beyond the
mandate) is NOT `BudgetPartitioned` (`overleveraged_refused`, and a sub-delegation cannot mint budget:
`cm_overbudget_clamped`), and an UNDER-COLLATERALIZED leg (payout > reserve) is NOT `PoolFillValid`
(`undercollateralized_refused`) and provably drives the reserve negative
(`undercollateralized_drives_negative`), so the position's schedule is refused
(`underPos_schedule_invalid`). Mirrors the rung teeth.

Pure.
-/
import Market.Priced
import Market.Liquidity
import Market.Fairness
import Dregg2.Agent.Mandate
import Dregg2.Tactics

namespace Market

open Dregg2.Exec (AssetId CellId)
open Dregg2.Agent
  (Mandate Caveat DelegTree children_no_oversubscribe subtree_budget_le_root child_budget_le
   subDelegate_budget_le subDelegate_caveat_narrows)
open Dregg2.Authority (Auth)
open Dregg2.Intent.Ring

/-! ## 0. Two arithmetic bridges (pure, self-contained). -/

/-- Pointwise-monotone list sum over ℚ: if `f x ≤ g x` for every element, the mapped sums compare. -/
theorem list_sum_le_sum {α} (l : List α) (f g : α → ℚ) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

/-- `ℕ → ℚ` cast commutes with a mapped list sum. -/
theorem natCast_map_sum {α} (l : List α) (f : α → ℕ) :
    ((l.map f).sum : ℚ) = (l.map (fun x => (f x : ℚ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

/-! ## 1. The model — a cross-margin position. -/

/-- **One open leg of a cross-margin position** — a priced clearing `Fill` (rung 5) tagged with the
child `Mandate` that AUTHORIZES it: the leg's margin slice. The `mandate.budget` is the leg's authorized
notional (a slice carved off the root by strict sub-delegation); `mandate.keep`/`caveat` are its
attenuated rights/allowed-assets window. -/
structure MarginLeg where
  /-- The trade this leg clears (a priced, partial-fillable fill). -/
  fill    : Fill
  /-- The child mandate authorizing this leg — its budget slice + attenuated caveat window. -/
  mandate : Mandate

/-- The leg's **exposure** — the notional it commits: the amount of `offerAsset` actually spent
(`fill.filledIn`), the value the trader puts at risk on this leg. -/
def MarginLeg.exposure (l : MarginLeg) : ℚ := l.fill.filledIn

/-- **A cross-margin position** — a trader's scoping mandate (`root`: budget = max aggregate notional,
`keep`/`caveat` = allowed rights/assets/expiry), a set of open trades (`legs`), and ONE collateral
reserve (`reserve`, a rung-6 `Pool`) backing them all. The "cross" of cross-margin: the legs share the
single `root` budget and the single `reserve`. -/
structure CrossMarginPosition where
  /-- The trader's scoping mandate (the total authority the whole position lives inside). -/
  root    : Mandate
  /-- The open trades, each under its authorizing child mandate. -/
  legs    : List MarginLeg
  /-- The collateral reserve backing the position (rung-6 per-asset `Pool`). -/
  reserve : Pool

/-- The **delegation tree induced by the position**: the root mandate with one child per leg carrying
that leg's authorizing (sub-delegated) mandate. The mandate module's budget/rights invariants
(`subtree_budget_le_root`, `children_no_oversubscribe`) are stated over exactly this shape. -/
def CrossMarginPosition.mandateTree (P : CrossMarginPosition) : DelegTree :=
  DelegTree.node P.root (P.legs.map (fun l => DelegTree.node l.mandate []))

/-- The **total exposure** of the position — the sum of every leg's committed notional. -/
def CrossMarginPosition.totalExposure (P : CrossMarginPosition) : ℚ :=
  (P.legs.map MarginLeg.exposure).sum

/-- The position's **priced book** — the list of its legs' fills (the input to the rung-5 clearing). -/
def CrossMarginPosition.book (P : CrossMarginPosition) : List Fill :=
  P.legs.map MarginLeg.fill

/-- The position's legs as a **reserve schedule** — the stream of fills hitting the collateral (idle
`noopFill` past the last leg). The input to rung-6's `pool_solvent_forever`. -/
def CrossMarginPosition.reserveSched (P : CrossMarginPosition) : PoolSched :=
  fun n => P.book.getD n noopFill

/-- **`MarginScoped P`** — the position's margin authority is a genuine attenuation: its induced
delegation tree is `WellAttenuated` (every leg's rights/budget/caveat strictly attenuate the root) AND
`BudgetPartitioned` (the leg slices do not over-subscribe the root budget — the cross-margin discipline).
This is the invariant the agent runtime maintains (its only tree-builder is `subDelegate`, §2 of the
mandate module); the demo below EXHIBITS a concrete margin-scoped position. -/
def CrossMarginPosition.MarginScoped (P : CrossMarginPosition) : Prop :=
  P.mandateTree.WellAttenuated ∧ P.mandateTree.BudgetPartitioned

/-! ## 2. Keystone (a) — MARGIN-BOUNDED (composes `children_no_oversubscribe`). -/

/-- **`position_margin_bounded` — the position's total exposure never exceeds the mandate's budget.**
Composed from the mandate module's budget conservation: `children_no_oversubscribe` (on the induced
tree) bounds the SUM of the leg budget slices by the root budget, and each leg's exposure fits inside
its own slice (`hexp`). So `Σ exposure ≤ Σ slice ≤ root.budget`. The cross-margin margin bound. -/
theorem position_margin_bounded (P : CrossMarginPosition) (hwf : P.MarginScoped)
    (hexp : ∀ l ∈ P.legs, MarginLeg.exposure l ≤ (l.mandate.budget : ℚ)) :
    P.totalExposure ≤ (P.root.budget : ℚ) := by
  -- (1) the leg slices don't over-subscribe the root — `children_no_oversubscribe` on the tree.
  have hp : (DelegTree.node P.root (P.legs.map (fun l => DelegTree.node l.mandate []))).BudgetPartitioned :=
    hwf.2
  have hnos := children_no_oversubscribe hp
  rw [List.map_map] at hnos
  simp only [DelegTree.mandate] at hnos
  -- hnos : (P.legs.map (fun l => l.mandate.budget)).sum ≤ P.root.budget
  -- (2) each leg's exposure ≤ its slice (hexp), summed.
  have hstep1 : P.totalExposure ≤ (P.legs.map (fun l => (l.mandate.budget : ℚ))).sum :=
    list_sum_le_sum P.legs MarginLeg.exposure (fun l => (l.mandate.budget : ℚ)) hexp
  rw [← natCast_map_sum P.legs (fun l => l.mandate.budget)] at hstep1
  exact le_trans hstep1 (by exact_mod_cast hnos)

/-- **`position_leg_budget_le_root` (NON-AMPLIFICATION)** — every leg's authorized budget ≤ the root
mandate's budget, straight from `subtree_budget_le_root`: a sub-delegated trade can never carry a larger
notional ceiling than the principal's grant. -/
theorem position_leg_budget_le_root (P : CrossMarginPosition) (hwf : P.MarginScoped)
    (l : MarginLeg) (hl : l ∈ P.legs) : l.mandate.budget ≤ P.root.budget := by
  have hbud : l.mandate.budget ∈ P.mandateTree.budgets := by
    rw [CrossMarginPosition.mandateTree, DelegTree.budgets]
    refine List.mem_cons_of_mem _ ?_
    rw [List.mem_flatMap]
    refine ⟨DelegTree.node l.mandate [], List.mem_map.2 ⟨l, hl, rfl⟩, ?_⟩
    rw [DelegTree.budgets]; simp
  have hle := subtree_budget_le_root P.mandateTree hwf.1 l.mandate.budget hbud
  simpa [CrossMarginPosition.mandateTree, DelegTree.mandate] using hle

/-! ## 3. Keystone (b) — COLLATERAL-BACKED (composes `pool_solvent_forever`). -/

/-- **`position_collateral_backed` — the collateral reserve is never insolvent under the margined
position.** For a solvent reserve and a valid schedule (each leg's payout respects the reserve floor at
the state it hits), the reserve is SOLVENT at EVERY reachable state — the margined position cannot drive
the collateral negative. This is `pool_solvent_forever` (rung 6, the ∀-schedule reserve invariant)
instantiated on the position's own leg stream. -/
theorem position_collateral_backed (P : CrossMarginPosition) (hres : Pool.solvent P.reserve)
    (hsched : ScheduleValid P.reserve P.reserveSched) :
    ∀ n, Pool.solvent (poolTraj P.reserve P.reserveSched n) :=
  pool_solvent_forever P.reserve hres P.reserveSched hsched

/-! ## 4. Keystone (c) — FAIRLY-CLEARED (composes `priced_clearing_keystone`). -/

/-- **`position_fairly_cleared` — every leg of the position clears fairly.** For a `BookValid`,
`Conserves` position book, `priced_clearing_keystone` (rung 5) gives: the book conserves per asset, and
every fill spends ≤ its `offerAmount`, executes at or above its `limitPrice`, and delivers ≥ its pro-rata
minimum — the priced lift of `clearing_respects_limits`. -/
theorem position_fairly_cleared (P : CrossMarginPosition)
    (hbook : BookValid P.book) (hcons : Conserves P.book) :
    (∀ a, netFlow P.book a = 0) ∧
    (∀ f ∈ P.book, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
    (∀ f ∈ P.book, orderFilledIn P.book f.orderId ≤ f.order.offerAmount ∧
      f.filledIn + f.remainder = f.order.offerAmount ∧ 0 ≤ f.remainder) :=
  priced_clearing_keystone P.book hbook hcons

/-- **`crossMargin_ring_legs_fair`** — the ledger-realized (rung-1) fairness for a cross-margin position
whose legs are the settlement of a solver-admitted ring: every participant is debited only its offered
asset (≤ its offer) and credited its wanted asset (≥ its minimum). This is `clearing_respects_limits`
(rung 1, the EXECUTOR-tied fairness over `settleRing`) reused verbatim — the fair-clearing guarantee is
available at BOTH the priced substrate (rung 5, above) and the ledger-realized ring (rung 1, here). -/
theorem crossMargin_ring_legs_fair {ns : List MatchNode} (h : CycleValid ns)
    (j : ℕ) (hj : j < ns.length) :
    ((chainedLeg (ns.map MatchNode.toRingNode) j).from_ = (ns.getD j default).creator ∧
      (chainedLeg (ns.map MatchNode.toRingNode) j).asset = (ns.getD j default).offerAsset ∧
      (chainedLeg (ns.map MatchNode.toRingNode) j).amount ≤ (ns.getD j default).offerAmount) ∧
    (receivedAsset ns j = (ns.getD j default).wantAsset ∧
      (ns.getD j default).wantMin ≤ receivedAmount ns j) :=
  clearing_respects_limits h j hj

/-! ## 5. THE KEYSTONE — a cross-margin position is mandate-scoped, collateral-backed, fairly-cleared. -/

/-- **`crossMargin_position_sound` — DrEX rung 7, in one theorem.** A margin-scoped, adequately-reserved
cross-margin position is simultaneously:

  * **(a) MARGIN-BOUNDED** — `totalExposure ≤ root.budget` (`children_no_oversubscribe` ∘ exposure≤slice);
  * **non-amplifying** — every leg's authority ≤ the mandate (`subtree_budget_le_root`);
  * **(b) COLLATERAL-BACKED** — the reserve is solvent at every reachable state (`pool_solvent_forever`);
  * **(c) FAIRLY-CLEARED** — every leg respects its declared limit at the cleared price
    (`priced_clearing_keystone`).

Not one line of the mandate, solvency, or fairness towers is re-proved — this is their COMPOSITION into
a single cross-margin guarantee. -/
theorem crossMargin_position_sound (P : CrossMarginPosition)
    (hwf : P.MarginScoped)
    (hexp : ∀ l ∈ P.legs, MarginLeg.exposure l ≤ (l.mandate.budget : ℚ))
    (hbook : BookValid P.book) (hcons : Conserves P.book)
    (hres : Pool.solvent P.reserve) (hsched : ScheduleValid P.reserve P.reserveSched) :
    (P.totalExposure ≤ (P.root.budget : ℚ)) ∧
    (∀ l ∈ P.legs, l.mandate.budget ≤ P.root.budget) ∧
    (∀ n, Pool.solvent (poolTraj P.reserve P.reserveSched n)) ∧
    (∀ f ∈ P.book, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) :=
  ⟨position_margin_bounded P hwf hexp,
   fun l hl => position_leg_budget_le_root P hwf l hl,
   position_collateral_backed P hres hsched,
   (position_fairly_cleared P hbook hcons).2.1⟩

/-! ## 6. NON-VACUITY, positive polarity — a concrete cross-margin position satisfies the keystones. -/

/-- The trader's scoping mandate: principal `0` grants trader `1` control over target `7`, budget `100`
(max aggregate notional), full rights, any caveat. -/
def cmRoot : Mandate := ⟨0, 1, 7, [Auth.read, Auth.write], 100, Caveat.any⟩

/-- Leg 0: the priced trade `pf0` (rung 5 — offers 8 of 10 gold, receives 4 art), authorized by a
budget-`40` mandate slice sub-delegated from the root. -/
def cmLeg0 : MarginLeg := ⟨pf0, cmRoot.subDelegate 1 [Auth.read, Auth.write] 40 Caveat.any⟩

/-- Leg 1: the priced trade `pf1` (offers 4 of 5 art, receives 8 gold), authorized by a budget-`40`
slice. The two slices sum to `80 ≤ 100`: the cross-margin budget is partitioned, not over-subscribed. -/
def cmLeg1 : MarginLeg := ⟨pf1, cmRoot.subDelegate 2 [Auth.read, Auth.write] 40 Caveat.any⟩

/-- **A concrete cross-margin position** — root mandate + two priced trades within budget + the
100-gold/100-art collateral reserve (`demoPool`, rung 6). Its book is exactly `posFills` (the worked
rung-5 clearing). -/
def demoPos : CrossMarginPosition := ⟨cmRoot, [cmLeg0, cmLeg1], demoPool⟩

/-- The demo position is **margin-scoped**, well-attenuated half — every leg slice strictly attenuates
the root (rights ⊆, budget ≤, caveat ⇒, target shared). Manual (the caveat clause quantifies over all
methods), mirroring the mandate module's `demoTree_wellAttenuated`. -/
theorem demoPos_wellAttenuated : demoPos.mandateTree.WellAttenuated := by
  show (DelegTree.node cmRoot [DelegTree.node cmLeg0.mandate [], DelegTree.node cmLeg1.mandate []]).WellAttenuated
  rw [DelegTree.WellAttenuated]
  refine ⟨?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha
        simp only [DelegTree.mandate, cmLeg0, cmRoot, Mandate.subDelegate, List.mem_filter] at ha ⊢
        exact ha.1
      · exact subDelegate_budget_le cmRoot 1 [Auth.read, Auth.write] 40 Caveat.any
      · exact fun x => subDelegate_caveat_narrows cmRoot 1 [Auth.read, Auth.write] 40 Caveat.any x
      · rfl
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro a ha
        simp only [DelegTree.mandate, cmLeg1, cmRoot, Mandate.subDelegate, List.mem_filter] at ha ⊢
        exact ha.1
      · exact subDelegate_budget_le cmRoot 2 [Auth.read, Auth.write] 40 Caveat.any
      · exact fun x => subDelegate_caveat_narrows cmRoot 2 [Auth.read, Auth.write] 40 Caveat.any x
      · rfl
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      (rw [DelegTree.WellAttenuated]; exact ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩)

/-- The demo position is **budget-partitioned** — at the root the two `40` slices sum to `80 ≤ 100`
(no over-subscription); leaves trivially. The cross-margin conservation discipline, concretely. -/
theorem demoPos_budgetPartitioned : demoPos.mandateTree.BudgetPartitioned := by
  show (DelegTree.node cmRoot [DelegTree.node cmLeg0.mandate [], DelegTree.node cmLeg1.mandate []]).BudgetPartitioned
  rw [DelegTree.BudgetPartitioned]
  refine ⟨?_, ?_⟩
  · simp only [DelegTree.childrenBudget, DelegTree.children, DelegTree.mandate, cmLeg0, cmLeg1, cmRoot,
      Mandate.subDelegate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    decide
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;>
      (rw [DelegTree.BudgetPartitioned]
       refine ⟨?_, fun d hd => by simp at hd⟩
       simp only [DelegTree.childrenBudget, DelegTree.children, List.map_nil, List.sum_nil]
       exact Nat.zero_le _)

/-- Margin scoping of the demo position (both clauses). -/
theorem demoPos_marginScoped : demoPos.MarginScoped :=
  ⟨demoPos_wellAttenuated, demoPos_budgetPartitioned⟩

/-- Each leg's exposure fits inside its authorized slice: `8 ≤ 40`, `4 ≤ 40`. -/
theorem demoPos_exposure : ∀ l ∈ demoPos.legs, MarginLeg.exposure l ≤ (l.mandate.budget : ℚ) := by
  intro l hl
  simp only [demoPos, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · have hb : cmLeg0.mandate.budget = 40 := by decide
    rw [hb]; simp only [MarginLeg.exposure, cmLeg0, pf0]; norm_num
  · have hb : cmLeg1.mandate.budget = 40 := by decide
    rw [hb]; simp only [MarginLeg.exposure, cmLeg1, pf1]; norm_num

/-- The reserve schedule idles (`noopFill`) past the two real legs. -/
theorem demoPos_reserveSchedTail (k : ℕ) : demoPos.reserveSched (k + 2) = noopFill := rfl

/-- Past the two real draws the reserve trajectory stabilizes (the position conserves, so the reserve
returns to its start and the `noopFill` tail holds it there). -/
theorem demoPos_traj_stable :
    ∀ k, poolTraj demoPool demoPos.reserveSched (k + 2) = poolTraj demoPool demoPos.reserveSched 2 := by
  intro k
  induction k with
  | zero => rfl
  | succ m ih =>
    have hstep : poolTraj demoPool demoPos.reserveSched (m + 2 + 1)
        = poolStep (poolTraj demoPool demoPos.reserveSched (m + 2)) (demoPos.reserveSched (m + 2)) := rfl
    rw [hstep, demoPos_reserveSchedTail m, ih, poolStep_noop]

/-- The demo position's reserve schedule is VALID — every leg's payout respects the collateral floor at
the state it hits (art 100 ≥ 4, then gold 108 ≥ 8, then the idle tail against the solvent reserve). -/
theorem demoPos_scheduleValid : ScheduleValid demoPos.reserve demoPos.reserveSched := by
  intro n
  show PoolFillValid (poolTraj demoPool demoPos.reserveSched n) (demoPos.reserveSched n)
  rcases n with _ | _ | k
  · -- leg 0 : pf0 against demoPool (art 100 ≥ 4)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [demoPos, CrossMarginPosition.reserveSched, CrossMarginPosition.book, cmLeg0, cmLeg1,
        poolTraj, pf0, o0, Fill.filledOut, demoPool]
  · -- leg 1 : pf1 against poolTraj … 1 (gold 108 ≥ 8)
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [demoPos, CrossMarginPosition.reserveSched, CrossMarginPosition.book, cmLeg0, cmLeg1,
        poolTraj, poolStep, poolDelta, pf0, pf1, o0, o1, Fill.filledOut, demoPool]
  · -- idle tail : noopFill against the stabilized (solvent) reserve
    rw [demoPos_reserveSchedTail k, demoPos_traj_stable k]
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;>
      norm_num [demoPos, CrossMarginPosition.reserveSched, CrossMarginPosition.book, cmLeg0, cmLeg1,
        poolTraj, poolStep, poolDelta, pf0, pf1, o0, o1, Fill.filledOut, demoPool, noopFill, noopOrder]

/-- **THE KEYSTONE, INSTANTIATED (positive polarity) — the demo cross-margin position is sound.**
Margin-bounded (`totalExposure 12 ≤ 100`), non-amplifying, collateral-backed forever, and fairly cleared
— all four, via `crossMargin_position_sound`, composing the real mandate + solvency + fairness towers. -/
theorem demoPos_sound :
    (demoPos.totalExposure ≤ (demoPos.root.budget : ℚ)) ∧
    (∀ l ∈ demoPos.legs, l.mandate.budget ≤ demoPos.root.budget) ∧
    (∀ n, Pool.solvent (poolTraj demoPos.reserve demoPos.reserveSched n)) ∧
    (∀ f ∈ demoPos.book, f.filledIn ≤ f.order.offerAmount ∧
      f.order.limitPrice ≤ f.execPrice ∧
      f.filledIn * f.order.limitPrice ≤ f.filledOut) :=
  crossMargin_position_sound demoPos demoPos_marginScoped demoPos_exposure
    posFills_valid posFills_conserves demoPool_solvent demoPos_scheduleValid

/-! ### `#guard` smoke — the margin/exposure/reserve numbers behind the keystone. -/

#guard demoPos.totalExposure == (12 : ℚ)          -- Σ exposure: 8 + 4
#guard demoPos.root.budget == 100                 -- the mandate ceiling
#guard cmLeg0.mandate.budget == 40                -- slice 0 (≤ 100)
#guard cmLeg1.mandate.budget == 40                -- slice 1 (40 + 40 = 80 ≤ 100)
#guard cmLeg0.exposure == (8 : ℚ)                 -- leg-0 committed notional
#guard cmLeg1.exposure == (4 : ℚ)                 -- leg-1 committed notional
#guard demoPos.reserve 0 == (100 : ℚ)             -- collateral: gold
#guard demoPos.reserve 1 == (100 : ℚ)             -- collateral: art

/-! ## 7. NON-VACUITY, negative polarity — the teeth. -/

/-! ### Tooth 1 — an OVER-LEVERAGED position is refused (slices over-subscribe the mandate). -/

/-- An over-leveraged leg: the priced trade `pf0`, but tagged with a budget-`80` slice directly. -/
def overLeg0 : MarginLeg := ⟨pf0, { cmRoot with holder := 1, budget := 80 }⟩
/-- A second over-leveraged leg: `pf1` with a budget-`80` slice. Two `80` slices sum to `160 > 100`. -/
def overLeg1 : MarginLeg := ⟨pf1, { cmRoot with holder := 2, budget := 80 }⟩

/-- An over-leveraged position — its two `80`-budget legs demand `160` of margin against a `100`-budget
mandate. -/
def overPos : CrossMarginPosition := ⟨cmRoot, [overLeg0, overLeg1], demoPool⟩

/-- **`overleveraged_refused` (TOOTH):** the over-leveraged position is NOT `BudgetPartitioned` — its
leg slices sum to `160`, exceeding the root budget `100`, so the no-over-subscription clause fails. It is
therefore NOT `MarginScoped`, and the margin-bounded keystone does not apply: a position that
over-subscribes the mandate is unconstructable as a scoped one. -/
theorem overleveraged_refused : ¬ overPos.mandateTree.BudgetPartitioned := by
  show ¬ (DelegTree.node cmRoot [DelegTree.node overLeg0.mandate [], DelegTree.node overLeg1.mandate []]).BudgetPartitioned
  rw [DelegTree.BudgetPartitioned]
  rintro ⟨hbound, -⟩
  simp only [DelegTree.childrenBudget, DelegTree.children, DelegTree.mandate, overLeg0, overLeg1, cmRoot,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hbound
  omega

/-- **`cm_overbudget_clamped` (TOOTH):** and a leg cannot MINT budget by sub-delegating — asking for a
`999` slice against a `100`-budget root still yields `100` (`min 100 999`). Authority cannot be
amplified downward, so the over-leverage above required *forging* the slice mandate (which
`WellAttenuated` then rejects), not a legal sub-delegation. -/
theorem cm_overbudget_clamped :
    (cmRoot.subDelegate 9 [Auth.read] 999 Caveat.any).budget = 100 := by decide

/-! ### Tooth 2 — an UNDER-COLLATERALIZED leg is refused (payout exceeds the reserve). -/

/-- A collateral reserve holding only `3` art (asset 1). -/
def underReserve : Pool := fun a => if a = 1 then (3 : ℚ) else 100

/-- An under-collateralized leg: the order wants `5` art out (`o0`, filled 10 at ½), against a reserve
holding only `3`. -/
def underFill : Fill := { orderId := 0, order := o0, filledIn := 10, execPrice := 1 / 2 }

/-- **`undercollateralized_refused` (TOOTH):** a leg whose payout (`5` art) exceeds the collateral
reserve (`3` art) is NOT `PoolFillValid` — the margined position cannot draw the collateral below zero
because such a fill is not admissible. The solvency backing as a *refusal*. -/
theorem undercollateralized_refused : ¬ PoolFillValid underReserve underFill := by
  rintro ⟨_, hd⟩
  simp only [underFill, o0, Fill.filledOut, underReserve] at hd
  norm_num at hd

/-- **`undercollateralized_drives_negative` (TOOTH, the other face):** were the under-collateralized leg
applied, it provably drives the reserve below zero (`3 − 5 = −2`) — the `ScheduleValid` hypothesis of
`pool_solvent_forever` is exactly what forbids it. -/
theorem undercollateralized_drives_negative : (poolStep underReserve underFill) 1 < 0 := by
  simp only [poolStep, poolDelta, underFill, o0, Fill.filledOut, underReserve]
  norm_num

/-- An under-collateralized position — one under-funded leg against the thin reserve. -/
def underPos : CrossMarginPosition :=
  ⟨cmRoot, [⟨underFill, cmRoot.subDelegate 1 [Auth.read] 40 Caveat.any⟩], underReserve⟩

/-- **`underPos_schedule_invalid` (TOOTH):** the under-collateralized position's reserve schedule is NOT
valid — its first leg is not `PoolFillValid` at the reserve it hits — so the collateral-backed keystone's
hypothesis fails: the position cannot be admitted as collateral-backed. -/
theorem underPos_schedule_invalid : ¬ ScheduleValid underPos.reserve underPos.reserveSched := by
  intro hs
  exact undercollateralized_refused (hs 0)

/-! ## 8. Axiom hygiene — the rung-7 keystones pinned kernel-clean. -/

#assert_all_clean [Market.list_sum_le_sum, Market.natCast_map_sum, Market.position_margin_bounded,
  Market.position_leg_budget_le_root, Market.position_collateral_backed, Market.position_fairly_cleared,
  Market.crossMargin_ring_legs_fair, Market.crossMargin_position_sound, Market.demoPos_wellAttenuated,
  Market.demoPos_budgetPartitioned, Market.demoPos_marginScoped, Market.demoPos_exposure,
  Market.demoPos_scheduleValid, Market.demoPos_sound, Market.overleveraged_refused,
  Market.cm_overbudget_clamped, Market.undercollateralized_refused,
  Market.undercollateralized_drives_negative, Market.underPos_schedule_invalid]

end Market
