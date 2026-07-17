/-
# Market.FhEggAllocation — the per-order pro-rata allocation, verified.

`Market/FhEggClearing.lean` proves the fhEgg clearing rule (fold → volume-argmax crossing) and the
AGGREGATE cleared batch (one buy leg, one sell leg). What it does not model is the PER-ORDER
allocation — how the cleared volume `V*` divides among the individual orders. The Rust engine has
carried that step without a proof (`fhegg-solver/src/clearing.rs::{allocate, ration}`): the short
side fills fully; the long side is rationed pro-rata by quantity with a deterministic
largest-remainder pass (remainder DESC, index ASC on ties) so the integer fills sum EXACTLY to the
target. `FHEGG-SDK-READINESS.md §4.1` names per-order allocation as the first blocker on the
plaintext SDK path. This file is that step's model + proofs.

## What is proved (honest scope)

* **`ration` mirrors the Rust rationing** — floor shares `⌊qᵢ·t/T⌋` (`T = Σq` the active side's
  total, `t` the target) plus one bonus unit to each of the `t − Σ floors` largest remainders, ties
  to the lowest index — the `clearing.rs::ration` computation, including the sort order. The
  `#guard` KATs below evaluate the same fill vectors the Rust unit tests
  (`lean_workbook_golden_vector`, `lean_counterbook_golden_vector`) pin, so the two implementations
  are held together by executable golden vectors (the denotation discipline of
  `Market/FhEggRustDenotation.lean` at KAT grain — extensional source correspondence for the Rust
  sort/scatter loop is NOT claimed as a theorem here).
* **CONSERVATION — `ration_sum`.** The integer fills sum EXACTLY to `min(target, total)`: the
  largest-remainder pass neither mints nor burns a unit. Composed to the book level
  (`allocation_conserves_at_Vstar`): on any valid book BOTH sides of the allocation sum exactly to
  the cleared volume `V*` — the per-order refinement of `clearedBatch_conserves`, resting on
  `activeBidQtys_sum_eq_demand`/`activeAskQtys_sum_eq_supply` (the active totals ARE the aggregate
  curves at `p*`).
* **PER-ORDER CAP — `ration_getD_le`.** On a positive-quantity book no order fills beyond its own
  quantity (a positive-qty order's floor share on a rationed side is strictly below its quantity,
  so even the bonus unit cannot overfill it).
* **FAIRNESS — `ration_fair`.** The spec `FairFills`: right shape, exact conservation, and every
  order within ONE UNIT of its pro-rata share `⌊qᵢ·min(t,T)/T⌋` — no favoritism (a gift beyond
  share + 1), no starvation (below the floor share). `ration` satisfies it, and the spec has teeth:
  `favoritism_refused`/`starvation_refused` exhibit allocations that CONSERVE (the side sums check
  out) yet are refused. Conservation alone cannot see theft between members of the same side;
  `FairFills` can.
* **INDIVIDUAL RATIONALITY — by construction (`buyFills_domain_active`).** The rationed lists are
  built from exactly the orders ACTIVE at the clearing price (a bid with `p* ≤ limit`, an ask with
  `limit ≤ p*`); an inactive order is outside the allocation domain entirely, so it cannot be paid.

Zero-quantity boundary, stated plainly: the cap and fairness theorems assume strictly positive
quantities (a real order puts value on the table). A zero-qty order's remainder is zero, so the
largest-remainder pass never reaches it (`#guard ration [0, 3, 4] 5 == [0, 2, 3]` below) — that
fact rides on the sort order and is witnessed executably here, not proved.

Pure. No axioms.
-/
import Market.FhEggClearing
import Dregg2.Tactics

namespace Market.FhEggAllocation

open Market

set_option autoImplicit false

/-! ## 1. List helpers (self-contained, proved by induction). -/

/-- Pointwise sums of a map distribute over the list sum. -/
theorem sum_map_add {α : Type} (f g : α → ℕ) (l : List α) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    omega

/-- Reading a list back through `getD` over its index range is the list itself. -/
theorem map_range_getD {α : Type} (g : α → ℕ) (d : α) :
    ∀ l : List α, (List.range l.length).map (fun i => g (l.getD i d)) = l.map g := by
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.getD_cons_zero,
      List.map_map]
    refine congrArg (g a :: ·) ?_
    calc (List.range l.length).map ((fun i => g ((a :: l).getD i d)) ∘ Nat.succ)
        = (List.range l.length).map (fun i => g (l.getD i d)) := by
          apply List.map_congr_left
          intro i _
          simp [List.getD_cons_succ]
      _ = l.map g := ih

/-- The equality indicator sums to `1` over a nodup list containing `a` (else `0`). -/
theorem sum_map_eq_indicator (a : ℕ) (l : List ℕ) (hl : l.Nodup) :
    (l.map (fun i => if i = a then 1 else 0)).sum = if a ∈ l then 1 else 0 := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hbl : b ∉ l := (List.nodup_cons.mp hl).1
    have hnd : l.Nodup := (List.nodup_cons.mp hl).2
    by_cases hba : b = a
    · subst hba
      simp [ih hnd, hbl]
    · have hmem : (a ∈ b :: l) ↔ (a ∈ l) := by
        simp [List.mem_cons, Ne.symm hba]
      simp [hba, ih hnd, hmem]

/-- **The indicator-count law**: over a nodup carrier `l`, the membership indicator of a nodup
subset `s ⊆ l` sums to `s.length`. This pins the largest-remainder pass to hand out EXACTLY
`leftover` units. -/
theorem sum_map_indicator_eq_length (l s : List ℕ) (hl : l.Nodup) (hs : s.Nodup)
    (hsub : ∀ x ∈ s, x ∈ l) :
    (l.map (fun i => if i ∈ s then 1 else 0)).sum = s.length := by
  induction s with
  | nil => simp
  | cons a s ih =>
    have has : a ∉ s := (List.nodup_cons.mp hs).1
    have hnd : s.Nodup := (List.nodup_cons.mp hs).2
    have hstep : (l.map (fun i => if i ∈ a :: s then 1 else 0)).sum
        = (l.map (fun i => (if i = a then 1 else 0) + if i ∈ s then 1 else 0)).sum := by
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hia : i = a
      · subst hia
        simp [has]
      · simp [List.mem_cons, hia]
    rw [hstep, sum_map_add, sum_map_eq_indicator a l hl,
      ih hnd (fun x hx => hsub x (List.mem_cons_of_mem _ hx)),
      if_pos (hsub a (by simp))]
    simp only [List.length_cons]
    omega

/-- Sum of pointwise Nat-division is at most division of the sum. -/
theorem sum_div_le (l : List ℕ) (d : ℕ) : (l.map (· / d)).sum ≤ l.sum / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · induction l <;> simp_all
  · induction l with
    | nil => simp
    | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      calc a / d + (l.map (· / d)).sum ≤ a / d + l.sum / d := Nat.add_le_add_left ih _
        _ ≤ (a + l.sum) / d := by
            rw [Nat.le_div_iff_mul_le hd, Nat.add_mul]
            exact Nat.add_le_add (Nat.div_mul_le_self a d) (Nat.div_mul_le_self _ d)

theorem sum_map_mul_right (l : List ℕ) (t : ℕ) : (l.map (· * t)).sum = l.sum * t := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Nat.add_mul]

/-- Summed division algorithm: `T·t = d·Σ⌊qᵢt/d⌋ + Σ(qᵢt mod d)` where `T = Σqᵢ`. -/
theorem sum_div_add_mod (l : List ℕ) (d t : ℕ) :
    l.sum * t = d * (l.map (fun q => q * t / d)).sum + (l.map (fun q => q * t % d)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    calc (a + l.sum) * t = a * t + l.sum * t := by rw [Nat.add_mul]
      _ = (d * (a * t / d) + a * t % d)
          + (d * (l.map (fun q => q * t / d)).sum + (l.map (fun q => q * t % d)).sum) := by
          rw [Nat.div_add_mod, ih]
      _ = d * (a * t / d + (l.map (fun q => q * t / d)).sum)
          + (a * t % d + (l.map (fun q => q * t % d)).sum) := by ring

/-! ## 2. The rationing — `clearing.rs::ration`, modeled. -/

/-- The floor pro-rata shares `⌊qᵢ·t/T⌋` (`T = Σq`; division by a zero total is Nat's `0`). -/
def floorShares (qtys : List ℕ) (target : ℕ) : List ℕ :=
  qtys.map (fun q => q * target / qtys.sum)

/-- The pro-rata remainders `qᵢ·t mod T` — the largest-remainder pass's sort keys. -/
def remShares (qtys : List ℕ) (target : ℕ) : List ℕ :=
  qtys.map (fun q => q * target % qtys.sum)

/-- The units left after the floor pass: `t − Σ floors` (each goes to one distinct order). -/
def leftover (qtys : List ℕ) (target : ℕ) : ℕ :=
  target - (floorShares qtys target).sum

/-- The Rust sort: indices by remainder DESC, index ASC on ties (`clearing.rs::ration`'s
`sort_by(|a, b| b.2.cmp(&a.2).then(a.0.cmp(&b.0)))`). -/
def remOrder (qtys : List ℕ) (target : ℕ) : List ℕ :=
  (List.range qtys.length).mergeSort fun i j =>
    (remShares qtys target).getD j 0 < (remShares qtys target).getD i 0 ||
      ((remShares qtys target).getD i 0 == (remShares qtys target).getD j 0 && i ≤ j)

/-- The indices that receive one bonus unit: the `leftover` largest remainders. -/
def bonusIdxs (qtys : List ℕ) (target : ℕ) : List ℕ :=
  (remOrder qtys target).take (leftover qtys target)

/-- **The rationing** — Rust `clearing.rs::ration`: the short side (`Σq ≤ t`) fills fully; the
long side takes floor shares plus one unit at each of the `leftover` largest remainders. -/
def ration (qtys : List ℕ) (target : ℕ) : List ℕ :=
  if qtys.sum ≤ target then qtys
  else
    (List.range qtys.length).map fun i =>
      qtys.getD i 0 * target / qtys.sum + if i ∈ bonusIdxs qtys target then 1 else 0

theorem ration_length (qtys : List ℕ) (target : ℕ) :
    (ration qtys target).length = qtys.length := by
  unfold ration
  split
  · rfl
  · simp

/-! ### The floor pass never over-assigns, and the leftover fits in the index range. -/

/-- `Σ floors ≤ t` — the floor shares never exceed the target. -/
theorem floorShares_sum_le (qtys : List ℕ) (target : ℕ) :
    (floorShares qtys target).sum ≤ target := by
  rcases Nat.eq_zero_or_pos qtys.sum with h0 | hpos
  · unfold floorShares
    rw [h0]
    induction qtys <;> simp_all
  · calc (floorShares qtys target).sum
        ≤ (qtys.map (· * target)).sum / qtys.sum := by
          have hmm : floorShares qtys target = (qtys.map (· * target)).map (· / qtys.sum) := by
            simp [floorShares, List.map_map, Function.comp]
          rw [hmm]
          exact sum_div_le _ _
      _ = qtys.sum * target / qtys.sum := by rw [sum_map_mul_right]
      _ = target := Nat.mul_div_cancel_left _ hpos

/-- On a genuinely rationed side (`t < T`) the leftover is strictly below the number of orders —
every bonus unit lands on a DISTINCT order. -/
theorem leftover_lt_length (qtys : List ℕ) (target : ℕ) (hlt : target < qtys.sum) :
    leftover qtys target < qtys.length := by
  have hpos : 0 < qtys.sum := Nat.lt_of_le_of_lt (Nat.zero_le _) hlt
  have hfs : (floorShares qtys target).sum ≤ target := floorShares_sum_le qtys target
  -- T·leftover = Σ rems.
  have hkey : qtys.sum * target
      = qtys.sum * (floorShares qtys target).sum + (remShares qtys target).sum :=
    sum_div_add_mod qtys qtys.sum target
  have hTL : qtys.sum * leftover qtys target = (remShares qtys target).sum := by
    have h2 : qtys.sum * leftover qtys target + qtys.sum * (floorShares qtys target).sum
        = qtys.sum * target := by
      rw [← Nat.mul_add]
      unfold leftover
      rw [Nat.sub_add_cancel hfs]
    omega
  -- Σ rems ≤ len·(T−1) < len·T.
  have hbound : (remShares qtys target).sum ≤ qtys.length * (qtys.sum - 1) := by
    have hmem : ∀ x ∈ remShares qtys target, x ≤ qtys.sum - 1 := by
      intro x hx
      simp only [remShares, List.mem_map] at hx
      obtain ⟨q, _, rfl⟩ := hx
      have := Nat.mod_lt (q * target) hpos
      omega
    calc (remShares qtys target).sum
        ≤ (remShares qtys target).length • (qtys.sum - 1) := List.sum_le_card_nsmul _ _ hmem
      _ = qtys.length * (qtys.sum - 1) := by simp [remShares, smul_eq_mul]
  have hlen : 0 < qtys.length := by
    cases qtys with
    | nil => simp at hpos
    | cons _ _ => simp
  have hstrict : qtys.sum * leftover qtys target < qtys.sum * qtys.length := by
    calc qtys.sum * leftover qtys target
        = (remShares qtys target).sum := hTL
      _ ≤ qtys.length * (qtys.sum - 1) := hbound
      _ < qtys.length * qtys.sum := mul_lt_mul_of_pos_left (Nat.sub_lt hpos Nat.one_pos) hlen
      _ = qtys.sum * qtys.length := Nat.mul_comm _ _
  exact Nat.lt_of_mul_lt_mul_left hstrict

/-! ### The bonus set: a nodup subset of the index range of size exactly `leftover`. -/

/-- `getD` at an in-range index is `getElem`. -/
theorem getD_of_lt (l : List ℕ) (i : ℕ) (h : i < l.length) : l.getD i 0 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- `getD` past the end is the default. -/
theorem getD_of_le (l : List ℕ) (i : ℕ) (h : l.length ≤ i) : l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

theorem remOrder_perm (qtys : List ℕ) (target : ℕ) :
    List.Perm (remOrder qtys target) (List.range qtys.length) := List.mergeSort_perm _ _

theorem bonusIdxs_nodup (qtys : List ℕ) (target : ℕ) : (bonusIdxs qtys target).Nodup := by
  have h : (remOrder qtys target).Nodup :=
    (remOrder_perm qtys target).nodup_iff.mpr (List.nodup_range)
  exact (List.take_sublist _ _).nodup h

theorem bonusIdxs_subset (qtys : List ℕ) (target : ℕ) :
    ∀ x ∈ bonusIdxs qtys target, x ∈ List.range qtys.length := by
  intro x hx
  exact ((remOrder_perm qtys target).mem_iff).mp (List.mem_of_mem_take hx)

theorem bonusIdxs_length (qtys : List ℕ) (target : ℕ) (hlt : target < qtys.sum) :
    (bonusIdxs qtys target).length = leftover qtys target := by
  unfold bonusIdxs
  rw [List.length_take, (remOrder_perm qtys target).length_eq, List.length_range]
  exact Nat.min_eq_left (Nat.le_of_lt (leftover_lt_length qtys target hlt))

/-! ## 3. CONSERVATION — the fills sum EXACTLY to `min(target, total)`. -/

/-- **The conservation keystone.** The integer rationing hands out exactly `min(t, T)` units: the
short side moves its whole book; the rationed side moves exactly the target — the floor pass plus
one unit per largest remainder neither mints nor burns. The Lean statement of the Rust test
`pro_rata_conserves_exactly`, proved for EVERY book and target. -/
theorem ration_sum (qtys : List ℕ) (target : ℕ) :
    (ration qtys target).sum = min target qtys.sum := by
  by_cases h : qtys.sum ≤ target
  · simp [ration, if_pos h, Nat.min_eq_right h]
  · have hlt : target < qtys.sum := Nat.not_le.mp h
    rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
    simp only [ration, if_neg h]
    rw [sum_map_add (fun i => qtys.getD i 0 * target / qtys.sum)
      (fun i => if i ∈ bonusIdxs qtys target then 1 else 0) (List.range qtys.length)]
    rw [map_range_getD (fun q => q * target / qtys.sum) 0 qtys]
    rw [sum_map_indicator_eq_length (List.range qtys.length) (bonusIdxs qtys target)
      (List.nodup_range) (bonusIdxs_nodup qtys target) (bonusIdxs_subset qtys target)]
    rw [bonusIdxs_length qtys target hlt]
    have hfs : (floorShares qtys target).sum ≤ target := floorShares_sum_le qtys target
    simp only [floorShares] at hfs
    simp only [leftover, floorShares]
    omega

/-! ## 4. PER-ORDER CAP and FAIRNESS. -/

/-- Pointwise shape of a rationed fill: floor share plus a 0/1 bonus. -/
theorem ration_getD (qtys : List ℕ) (target : ℕ) (hlt : target < qtys.sum)
    (i : ℕ) (hi : i < qtys.length) :
    (ration qtys target).getD i 0
      = qtys.getD i 0 * target / qtys.sum + (if i ∈ bonusIdxs qtys target then 1 else 0) := by
  have hne : ¬ qtys.sum ≤ target := Nat.not_le.mpr hlt
  have hli : i < ((List.range qtys.length).map fun i =>
      qtys.getD i 0 * target / qtys.sum + if i ∈ bonusIdxs qtys target then 1 else 0).length := by
    simpa using hi
  simp only [ration, if_neg hne]
  rw [getD_of_lt _ _ hli, List.getElem_map, List.getElem_range]

/-- **PER-ORDER CAP** — on a positive-quantity book no fill exceeds the order's own quantity (the
Rust `fill cannot exceed order qty` assertion, proved). Positivity matters: the floor share of a
positive-qty order on a rationed side is strictly below its quantity, so even the bonus unit
cannot overfill it. -/
theorem ration_getD_le (qtys : List ℕ) (target : ℕ) (hq : ∀ q ∈ qtys, 0 < q) (i : ℕ) :
    (ration qtys target).getD i 0 ≤ qtys.getD i 0 := by
  by_cases h : qtys.sum ≤ target
  · simp [ration, if_pos h]
  · have hlt : target < qtys.sum := Nat.not_le.mp h
    by_cases hi : i < qtys.length
    · rw [ration_getD qtys target hlt i hi, getD_of_lt _ _ hi]
      have hqi : 0 < qtys[i] := hq _ (List.getElem_mem hi)
      have hfloor : qtys[i] * target / qtys.sum < qtys[i] := by
        rw [Nat.div_lt_iff_lt_mul (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)]
        exact mul_lt_mul_of_pos_left hlt hqi
      split <;> omega
    · rw [getD_of_le _ _ (by rw [ration_length]; omega)]
      exact Nat.zero_le _

/-- The fair pro-rata share of order `i`: `⌊qᵢ · min(t,T) / T⌋` — the floor share on a rationed
side, the full quantity on a short side. -/
def fairShare (qtys : List ℕ) (target i : ℕ) : ℕ :=
  qtys.getD i 0 * min target qtys.sum / qtys.sum

/-- **The fairness spec** an allocation must meet: right shape, exact conservation, and every
order within ONE UNIT of its pro-rata share — no favoritism (a gift beyond share + 1), no
starvation (below the floor share). Decidable, so violations are refutable by `decide`. -/
def FairFills (qtys : List ℕ) (target : ℕ) (fills : List ℕ) : Prop :=
  fills.length = qtys.length ∧
  fills.sum = min target qtys.sum ∧
  ∀ i, i < qtys.length →
    fairShare qtys target i ≤ fills.getD i 0 ∧ fills.getD i 0 ≤ fairShare qtys target i + 1

instance (qtys : List ℕ) (target : ℕ) (fills : List ℕ) :
    Decidable (FairFills qtys target fills) := by
  unfold FairFills
  infer_instance

/-- **FAIRNESS — `ration` meets the spec.** Every order receives at least its floor pro-rata
share and at most one unit more; the sums conserve exactly. -/
theorem ration_fair (qtys : List ℕ) (target : ℕ) (hq : ∀ q ∈ qtys, 0 < q) :
    FairFills qtys target (ration qtys target) := by
  refine ⟨ration_length qtys target, ration_sum qtys target, ?_⟩
  intro i hi
  have hqi : 0 < qtys[i] := hq _ (List.getElem_mem hi)
  have hpos : 0 < qtys.sum :=
    Nat.lt_of_lt_of_le hqi (List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.getElem_mem hi))
  by_cases h : qtys.sum ≤ target
  · -- Short side: the fills are the quantities, and the fair share of a full fill is the full
    -- quantity (`q·T/T = q`).
    have hfs : fairShare qtys target i = qtys.getD i 0 := by
      unfold fairShare
      rw [Nat.min_eq_right h, Nat.mul_div_cancel _ hpos]
    simp only [ration, if_pos h, hfs]
    omega
  · have hlt : target < qtys.sum := Nat.not_le.mp h
    have hfs : fairShare qtys target i = qtys.getD i 0 * target / qtys.sum := by
      unfold fairShare
      rw [Nat.min_eq_left (Nat.le_of_lt hlt)]
    rw [ration_getD qtys target hlt i hi, hfs]
    split <;> omega

/-! ## 5. The book level — the active sides ARE the curves; conservation at `V*`. -/

/-- The quantities of the orders ACTIVE on the buy side at price `p` (a bid with `p ≤ limit`), in
book order — the Rust `active_bids` filter. -/
def activeBidQtys (bk : OrderBook) (p : ℕ) : List ℕ :=
  (bk.filter fun o => decide (o.side = Side.bid ∧ p ≤ o.limit)).map (fun o => o.qty.toNat)

/-- The quantities of the orders ACTIVE on the sell side at price `p` (an ask with `limit ≤ p`). -/
def activeAskQtys (bk : OrderBook) (p : ℕ) : List ℕ :=
  (bk.filter fun o => decide (o.side = Side.ask ∧ o.limit ≤ p)).map (fun o => o.qty.toNat)

/-- **The active buy side IS the demand curve at `p`** — the filter-and-sum equals the fold. This
is what makes book-level conservation a theorem: the rationing target `V* ≤ D(p*)` is genuinely
available among the active bids. -/
theorem activeBidQtys_sum_eq_demand (bk : OrderBook) (hb : OrdersValid bk) (p : ℕ) :
    ((activeBidQtys bk p).sum : ℤ) = demand bk p := by
  induction bk with
  | nil => simp [activeBidQtys]
  | cons o bk ih =>
    have hbk : OrdersValid bk := fun x hx => hb x (by simp [hx])
    have ho : (0 : ℤ) ≤ o.qty := hb o (by simp)
    by_cases hc : o.side = Side.bid ∧ p ≤ o.limit
    · have hcons : activeBidQtys (o :: bk) p = o.qty.toNat :: activeBidQtys bk p := by
        simp [activeBidQtys, hc]
      simp only [demand_cons, demandIncr, if_pos hc]
      rw [hcons, List.sum_cons, Nat.cast_add, Int.toNat_of_nonneg ho, ih hbk]
    · have hcons : activeBidQtys (o :: bk) p = activeBidQtys bk p := by
        simp [activeBidQtys, hc]
      simp only [demand_cons, demandIncr, if_neg hc, zero_add]
      rw [hcons]
      exact ih hbk

/-- **The active sell side IS the supply curve at `p`.** -/
theorem activeAskQtys_sum_eq_supply (bk : OrderBook) (hb : OrdersValid bk) (p : ℕ) :
    ((activeAskQtys bk p).sum : ℤ) = supply bk p := by
  induction bk with
  | nil => simp [activeAskQtys]
  | cons o bk ih =>
    have hbk : OrdersValid bk := fun x hx => hb x (by simp [hx])
    have ho : (0 : ℤ) ≤ o.qty := hb o (by simp)
    by_cases hc : o.side = Side.ask ∧ o.limit ≤ p
    · have hcons : activeAskQtys (o :: bk) p = o.qty.toNat :: activeAskQtys bk p := by
        simp [activeAskQtys, hc]
      simp only [supply_cons, supplyIncr, if_pos hc]
      rw [hcons, List.sum_cons, Nat.cast_add, Int.toNat_of_nonneg ho, ih hbk]
    · have hcons : activeAskQtys (o :: bk) p = activeAskQtys bk p := by
        simp [activeAskQtys, hc]
      simp only [supply_cons, supplyIncr, if_neg hc, zero_add]
      rw [hcons]
      exact ih hbk

/-- The buy-side per-order fills at the clearing price — Rust `allocate`'s
`ration(orders, active_bids, vstar)`. -/
def buyFills (bk : OrderBook) (K : ℕ) : List ℕ :=
  ration (activeBidQtys bk (crossing bk K)) (clearedVolume bk K).toNat

/-- The sell-side per-order fills at the clearing price. -/
def sellFills (bk : OrderBook) (K : ℕ) : List ℕ :=
  ration (activeAskQtys bk (crossing bk K)) (clearedVolume bk K).toNat

/-- The buy side fills EXACTLY the cleared volume: `V* ≤ D(p*)` (the cleared volume is the short
side of the curves), so the rationing's `min` lands on `V*`. -/
theorem buyFills_sum (bk : OrderBook) (K : ℕ) (hb : OrdersValid bk) :
    (buyFills bk K).sum = (clearedVolume bk K).toNat := by
  unfold buyFills
  rw [ration_sum]
  apply Nat.min_eq_left
  have h1 := activeBidQtys_sum_eq_demand bk hb (crossing bk K)
  have h2 : clearedVolume bk K ≤ demand bk (crossing bk K) := by
    rw [clearedVolume_eq]
    exact min_le_left _ _
  omega

/-- The sell side fills EXACTLY the cleared volume. -/
theorem sellFills_sum (bk : OrderBook) (K : ℕ) (hb : OrdersValid bk) :
    (sellFills bk K).sum = (clearedVolume bk K).toNat := by
  unfold sellFills
  rw [ration_sum]
  apply Nat.min_eq_left
  have h1 := activeAskQtys_sum_eq_supply bk hb (crossing bk K)
  have h2 : clearedVolume bk K ≤ supply bk (crossing bk K) := by
    rw [clearedVolume_eq]
    exact min_le_right _ _
  omega

/-- **CONSERVATION AT `V*` — the headline.** On any valid book, BOTH sides of the per-order
allocation sum EXACTLY to the cleared volume: `Σ buy fills = Σ sell fills = V*`. The per-order
refinement of `clearedBatch_conserves` — the allocation neither mints nor burns, and the two
sides match each other through `V*`. (The Rust `Allocation::validate` checks exactly this,
per clearing; here it is a theorem over every book.) -/
theorem allocation_conserves_at_Vstar (bk : OrderBook) (K : ℕ) (hb : OrdersValid bk) :
    (buyFills bk K).sum = (clearedVolume bk K).toNat ∧
    (sellFills bk K).sum = (clearedVolume bk K).toNat :=
  ⟨buyFills_sum bk K hb, sellFills_sum bk K hb⟩

/-- Active quantities inherit strict positivity from the book. -/
theorem activeBidQtys_pos (bk : OrderBook) (hq : ∀ o ∈ bk, 0 < o.qty) (p : ℕ) :
    ∀ q ∈ activeBidQtys bk p, 0 < q := by
  intro q hqm
  simp only [activeBidQtys, List.mem_map] at hqm
  obtain ⟨o, hof, rfl⟩ := hqm
  have := hq o (List.mem_of_mem_filter hof)
  omega

theorem activeAskQtys_pos (bk : OrderBook) (hq : ∀ o ∈ bk, 0 < o.qty) (p : ℕ) :
    ∀ q ∈ activeAskQtys bk p, 0 < q := by
  intro q hqm
  simp only [activeAskQtys, List.mem_map] at hqm
  obtain ⟨o, hof, rfl⟩ := hqm
  have := hq o (List.mem_of_mem_filter hof)
  omega

/-- **PER-ORDER CAP at the book level** — no buy fill exceeds its active order's quantity. -/
theorem buyFills_le_qty (bk : OrderBook) (K : ℕ) (hq : ∀ o ∈ bk, 0 < o.qty) (i : ℕ) :
    (buyFills bk K).getD i 0 ≤ (activeBidQtys bk (crossing bk K)).getD i 0 :=
  ration_getD_le _ _ (activeBidQtys_pos bk hq _) i

theorem sellFills_le_qty (bk : OrderBook) (K : ℕ) (hq : ∀ o ∈ bk, 0 < o.qty) (i : ℕ) :
    (sellFills bk K).getD i 0 ≤ (activeAskQtys bk (crossing bk K)).getD i 0 :=
  ration_getD_le _ _ (activeAskQtys_pos bk hq _) i

/-- **INDIVIDUAL RATIONALITY, by construction** — every order in the buy allocation's domain is a
bid whose limit admits the clearing price (`p* ≤ limit`: a buyer never pays above its limit). An
inactive order is not in the allocation domain at all, so it cannot be paid. -/
theorem buyFills_domain_active (bk : OrderBook) (K : ℕ) :
    ∀ o ∈ bk.filter (fun o => decide (o.side = Side.bid ∧ crossing bk K ≤ o.limit)),
      o.side = Side.bid ∧ crossing bk K ≤ o.limit := by
  intro o ho
  simpa using List.of_mem_filter ho

theorem sellFills_domain_active (bk : OrderBook) (K : ℕ) :
    ∀ o ∈ bk.filter (fun o => decide (o.side = Side.ask ∧ o.limit ≤ crossing bk K)),
      o.side = Side.ask ∧ o.limit ≤ crossing bk K := by
  intro o ho
  simpa using List.of_mem_filter ho

/-! ## 6. TEETH — the fairness spec refuses conserving-but-unfair allocations. -/

/-- **Favoritism REFUSED.** `[8, 0]` on the workBook buy side conserves (`Σ = 8 = V*`) — the
side-sum check passes — but gifts order 0 three units beyond its `⌊6·8/10⌋ + 1 = 5` bound and
starves order 1. Conservation alone cannot see theft between members of the same side. -/
theorem favoritism_refused : ¬ FairFills [6, 4] 8 [8, 0] := by decide

/-- **Starvation REFUSED.** `[0, 9]` on the counterBook sell side conserves (`Σ = 9 = V*`) but
pays order 0 nothing, below its floor share `⌊5·9/20⌋ = 2`. -/
theorem starvation_refused : ¬ FairFills [5, 15] 9 [0, 9] := by decide

/-! ## 7. Golden vectors — the exact Rust fills, computed (the KAT denotation binding).

Each `#guard` below evaluates the SAME fill vector the Rust unit tests pin
(`clearing.rs::tests::{lean_workbook_golden_vector, lean_counterbook_golden_vector,
pro_rata_conserves_exactly}`), including the largest-remainder tie order. -/

-- The rationing itself (workBook buy side): active bids (6,4) share V*=8 →
-- floors (4,3), remainders (8,2), one leftover unit to the larger remainder → (5,3).
#guard ration [6, 4] 8 == [5, 3]
-- workBook sell side: active asks (3,5) total exactly 8 → full fill.
#guard ration [3, 5] 8 == [3, 5]
-- counterBook sell side: asks (5,15) share V*=9 → floors (2,6), remainders (5,15),
-- one leftover unit to index 1 → (2,7).
#guard ration [5, 15] 9 == [2, 7]
-- The Rust `pro_rata_conserves_exactly` book: (33,33,34) vs demand 100 — short side, full fill.
#guard ration [33, 33, 34] 100 == [33, 33, 34]
-- Remainder ties break to the LOWEST index: (3,3,4) share 7 → floors (2,2,2), remainders
-- (1,1,8); leftover 1 goes to index 2 (remainder 8).
#guard ration [3, 3, 4] 7 == [2, 2, 3]
-- A zero-qty order's remainder is 0, so the largest-remainder pass never reaches it.
#guard ration [0, 3, 4] 5 == [0, 2, 3]

-- The BOOK-level composition on the two Lean-proven books (`crossing`/`clearedVolume` computed):
#guard activeBidQtys workBook 1 == [6, 4]
#guard activeAskQtys workBook 1 == [3, 5]
#guard buyFills workBook 3 == [5, 3]
#guard sellFills workBook 3 == [3, 5]
#guard (buyFills workBook 3).sum == 8
#guard (sellFills workBook 3).sum == 8
#guard buyFills counterBook 2 == [9]
#guard sellFills counterBook 2 == [2, 7]
#guard (buyFills counterBook 2).sum == 9
#guard (sellFills counterBook 2).sum == 9
-- The rationed fills satisfy the fairness spec on the golden books (executable pole of
-- `ration_fair`):
#guard decide (FairFills [6, 4] 8 [5, 3]) == true
#guard decide (FairFills [5, 15] 9 [2, 7]) == true

/-! ### Axiom hygiene — the allocation keystones pinned kernel-clean. -/

#assert_all_clean [Market.FhEggAllocation.sum_map_indicator_eq_length,
  Market.FhEggAllocation.sum_div_add_mod, Market.FhEggAllocation.floorShares_sum_le,
  Market.FhEggAllocation.leftover_lt_length, Market.FhEggAllocation.bonusIdxs_length,
  Market.FhEggAllocation.ration_sum, Market.FhEggAllocation.ration_getD,
  Market.FhEggAllocation.ration_getD_le, Market.FhEggAllocation.ration_fair,
  Market.FhEggAllocation.activeBidQtys_sum_eq_demand,
  Market.FhEggAllocation.activeAskQtys_sum_eq_supply,
  Market.FhEggAllocation.buyFills_sum, Market.FhEggAllocation.sellFills_sum,
  Market.FhEggAllocation.allocation_conserves_at_Vstar,
  Market.FhEggAllocation.buyFills_le_qty, Market.FhEggAllocation.sellFills_le_qty,
  Market.FhEggAllocation.buyFills_domain_active, Market.FhEggAllocation.sellFills_domain_active,
  Market.FhEggAllocation.favoritism_refused, Market.FhEggAllocation.starvation_refused]

end Market.FhEggAllocation
