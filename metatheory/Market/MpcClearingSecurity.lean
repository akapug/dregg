/-
# Market.MpcClearingSecurity — exact `(p*, V*)` leakage for volume-argmax clearing

This module joins the actual fhEgg clearing semantics to the output-boundary MPC
security statement.  The runtime rule is

    p* = FhEggClearing.crossing bk K
    V* = FhEggClearing.clearedVolume bk K

where `crossing` is the LOWEST bucket maximizing `min demand supply`.  The public
deterministic view contains only `(p*, V*)` plus public circuit shape.  In
particular it contains no balance sign vector and does not use `balanceCrossing`.

PROVEN here:

* additive n-of-n shares are perfectly hiding from every coalition missing one
  party, with full-collusion teeth;
* the real deterministic view factors exactly through the volume-argmax leakage;
* same-leakage books have identical views, while a private curve coefficient and
  the obsolete balance sign do not factor through that leakage;
* the same clearing is conserving, uniform-price optimal, volume maximizing, and
  reveal-only;
* MaskedBoundaryParty's mod-t row identity reconstructs the hidden coefficient,
  and any correct A2B bit representation denotes that same reconstruction;
* generic reveal-only stages compose, and the exact view instantiates PerfectZK.

HONEST SCOPE: this is the semi-honest, perfect-hiding algebra.  Authentication,
malicious-share validity, dealer-free triples, smudging-to-full-transcript hybrids,
and adaptive/UC composition remain outside this theorem.  The A2B bridge specifies
semantic reconstruction; it does not pretend to verify the Rust gate schedule.

Pure.
-/
import Market.FhEggClearing
import Market.CertF
import Market.RevealNothing
import Metatheory.Open.PerfectZK
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Abel
import Dregg2.Tactics

namespace Market.MpcClearingSecurity

open Market
open Matrix

set_option autoImplicit false

/-! ## 1. Information-theoretic perfect hiding of additive shares. -/

section PerfectHiding

variable {G : Type*} [AddCommGroup G]

/-- A valid additive n-sharing of `secret`. -/
abbrev Sharing (n : ℕ) (secret : G) : Type _ := { s : Fin n → G // ∑ i, s i = secret }

/-- Rebalance one coordinate by `δ`. -/
def rebalanceFn (n : ℕ) (j : Fin n) (δ : G) (s : Fin n → G) : Fin n → G :=
  Function.update s j (s j + δ)

theorem sum_rebalanceFn {n : ℕ} (s : Fin n → G) (j : Fin n) (δ : G) :
    ∑ i, rebalanceFn n j δ s i = (∑ i, s i) + δ := by
  unfold rebalanceFn
  rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  have hs : ∑ i, s i = s j + ∑ i ∈ Finset.univ \ {j}, s i := by
    conv_lhs => rw [← Function.update_eq_self j s]
    rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  rw [hs]
  abel

theorem rebalanceFn_of_ne {n : ℕ} (s : Fin n → G) (j : Fin n) (δ : G)
    {i : Fin n} (hi : i ≠ j) : rebalanceFn n j δ s i = s i := by
  unfold rebalanceFn
  exact Function.update_of_ne hi _ _

/-- A view-preserving bijection between sharings of any two secrets. -/
def rebalanceEquiv (n : ℕ) (j : Fin n) (x y : G) : Sharing n x ≃ Sharing n y where
  toFun s := ⟨rebalanceFn n j (y - x) s.val, by rw [sum_rebalanceFn, s.2]; abel⟩
  invFun s := ⟨rebalanceFn n j (x - y) s.val, by rw [sum_rebalanceFn, s.2]; abel⟩
  left_inv s := by
    apply Subtype.ext
    show rebalanceFn n j (x - y) (rebalanceFn n j (y - x) s.val) = s.val
    unfold rebalanceFn
    simp only [Function.update_self, Function.update_idem]
    rw [show s.val j + (y - x) + (x - y) = s.val j from by abel,
      Function.update_eq_self]
  right_inv s := by
    apply Subtype.ext
    show rebalanceFn n j (y - x) (rebalanceFn n j (x - y) s.val) = s.val
    unfold rebalanceFn
    simp only [Function.update_self, Function.update_idem]
    rw [show s.val j + (x - y) + (y - x) = s.val j from by abel,
      Function.update_eq_self]

/-- Any coalition missing `j` has identical views for every pair of secrets. -/
theorem perfect_hiding (n : ℕ) (j : Fin n) (C : Finset (Fin n)) (hj : j ∉ C) (x y : G) :
    ∃ φ : Sharing n x ≃ Sharing n y,
      ∀ (s : Sharing n x), ∀ i ∈ C, (φ s).val i = s.val i :=
  ⟨rebalanceEquiv n j x y,
    fun s i hi => rebalanceFn_of_ne (i := i) s.val j (y - x) (fun h => hj (h ▸ hi))⟩

def canonicalSharing {n : ℕ} [NeZero n] (secret : G) : Sharing n secret :=
  ⟨Function.update 0 ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ secret, by
    rw [Finset.sum_update_of_mem (Finset.mem_univ _)]
    simp⟩

/-- RED: the full party set reconstructs, so perfect hiding cannot survive full collusion. -/
theorem full_collusion_breaks_hiding {n : ℕ} [NeZero n] {x y : G} (hxy : x ≠ y) :
    ¬ ∃ φ : Sharing n x → Sharing n y,
      ∀ (s : Sharing n x) (i : Fin n), (φ s).val i = s.val i := by
  rintro ⟨φ, hpres⟩
  have hval : (φ (canonicalSharing x)).val = (canonicalSharing (n := n) x).val :=
    funext (hpres (canonicalSharing x))
  have hsum : ∑ i, (φ (canonicalSharing x)).val i =
      ∑ i, (canonicalSharing (n := n) x).val i := by rw [hval]
  rw [(φ (canonicalSharing x)).2, (canonicalSharing (n := n) x).2] at hsum
  exact hxy hsum.symm

/-- Beaver's one-time-pad opening is the two-party `ZMod 2` instance. -/
theorem otpMasks (x y : ZMod 2) :
    ∃ φ : Sharing 2 x ≃ Sharing 2 y,
      ∀ (s : Sharing 2 x), ∀ i ∈ ({1} : Finset (Fin 2)), (φ s).val i = s.val i :=
  perfect_hiding 2 0 {1} (by decide) x y

end PerfectHiding

/-! ## 2. Exact volume-argmax leakage and simulation. -/

theorem demand_nonneg {bk : OrderBook} (hb : OrdersValid bk) (p : ℕ) : 0 ≤ demand bk p := by
  unfold demand
  apply List.sum_nonneg
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  unfold demandIncr
  split
  · exact hb o ho
  · exact le_refl 0

theorem supply_nonneg {bk : OrderBook} (hb : OrdersValid bk) (p : ℕ) : 0 ≤ supply bk p := by
  unfold supply
  apply List.sum_nonneg
  intro z hz
  simp only [List.mem_map] at hz
  obtain ⟨o, ho, rfl⟩ := hz
  unfold supplyIncr
  split
  · exact hb o ho
  · exact le_refl 0

theorem execVol_nonneg {bk : OrderBook} (hb : OrdersValid bk) (p : ℕ) :
    0 ≤ execVol bk p := by
  unfold execVol
  exact le_min (demand_nonneg hb p) (supply_nonneg hb p)

theorem clearedVolume_nonneg {bk : OrderBook} (hb : OrdersValid bk) (K : ℕ) :
    0 ≤ clearedVolume bk K :=
  execVol_nonneg hb _

/-- The exact public leakage of the implemented crossing. -/
structure CrossingLeakage where
  pStar : ℕ
  vStar : ℤ
  deriving DecidableEq, Repr

/-- The deterministic public view: output plus public circuit shape, and nothing else. -/
structure MpcView where
  pStar : ℕ
  vStar : ℤ
  buckets : ℕ
  maskedLen : ℕ
  deriving DecidableEq, Repr

/-- Witness-free simulation from only `(p*,V*)` and public shape. -/
def mpcSim (K maskedLen : ℕ) (q : CrossingLeakage) : MpcView :=
  { pStar := q.pStar, vStar := q.vStar, buckets := K, maskedLen := maskedLen }

/-- One output-boundary clearing on the actual volume-argmax rule. -/
structure MpcClearing where
  bk : OrderBook
  hvalid : OrdersValid bk
  K : ℕ
  hK : 0 < K
  ρ : ℚ
  hρ : 0 < ρ
  maskedLen : ℕ

namespace MpcClearing

variable (mc : MpcClearing)

def pStar : ℕ := crossing mc.bk mc.K
def vStar : ℤ := clearedVolume mc.bk mc.K
def leakage : CrossingLeakage := ⟨mc.pStar, mc.vStar⟩
def mpcView : MpcView :=
  { pStar := mc.pStar, vStar := mc.vStar, buckets := mc.K, maskedLen := mc.maskedLen }

/-- The actual deterministic transcript factors exactly through `(p*,V*)`. -/
theorem reveal_only : mc.mpcView = mpcSim mc.K mc.maskedLen mc.leakage := rfl

theorem same_leakage_indistinguishable (mc₁ mc₂ : MpcClearing)
    (hK : mc₁.K = mc₂.K) (hm : mc₁.maskedLen = mc₂.maskedLen)
    (hq : mc₁.leakage = mc₂.leakage) : mc₁.mpcView = mc₂.mpcView := by
  rw [mc₁.reveal_only, mc₂.reveal_only, hK, hm, hq]

theorem pStar_lt : mc.pStar < mc.K := crossing_lt mc.bk mc.hK

theorem vStar_nonneg : 0 ≤ mc.vStar := clearedVolume_nonneg mc.hvalid mc.K

theorem vStar_optimal {q : ℕ} (hq : q < mc.K) : execVol mc.bk q ≤ mc.vStar :=
  clearedVolume_optimal mc.bk mc.K hq

end MpcClearing

/-! ## 3. RED teeth: the old least-crossing/sign-vector semantics are not this leakage. -/

def bookA : OrderBook := workBook

/-- Same actual output `(1,8)` as `workBook`, but a different private curve and balance sign at 1. -/
def bookB : OrderBook :=
  [ { side := Side.bid, qty := 6, limit := 2 },
    { side := Side.bid, qty := 2, limit := 1 },
    { side := Side.bid, qty := 3, limit := 0 },
    { side := Side.ask, qty := 3, limit := 0 },
    { side := Side.ask, qty := 5, limit := 1 } ]

theorem bookB_valid : OrdersValid bookB := by unfold OrdersValid bookB; decide
theorem bookB_crossing : crossing bookB 3 = 1 := by decide
theorem bookB_clearedVolume : clearedVolume bookB 3 = 8 := by decide
theorem bookAB_demand0_differs : demand bookA 0 = 10 ∧ demand bookB 0 = 11 := by
  constructor <;> decide

/-- RED: the old least balanced bucket is not the implemented clearing price. -/
theorem old_balanceCrossing_disagrees_with_runtime :
    balanceCrossing workBook workBook_crosses ≠ crossing workBook 3 := by
  rw [workBook_balanceCrossing, workBook_crossing]
  decide

/-- RED: the old balance sign is not determined by the actual `(p*,V*)` output. -/
theorem old_sign_not_determined_by_runtime_leakage :
    ¬ ∃ sim : CrossingLeakage → Bool,
      ∀ (bk : OrderBook) (K p : ℕ),
        decide (Clears bk p) = sim ⟨crossing bk K, clearedVolume bk K⟩ := by
  rintro ⟨sim, hsim⟩
  have hA := hsim workBook 3 1
  have hB := hsim bookB 3 1
  rw [workBook_crossing, workBook_clearedVolume] at hA
  rw [bookB_crossing, bookB_clearedVolume] at hB
  have hsignA : decide (Clears workBook 1) = false := by decide
  have hsignB : decide (Clears bookB 1) = true := by decide
  rw [hsignA] at hA
  rw [hsignB] at hB
  exact Bool.false_ne_true (hA.trans hB.symm)

/-- RED: a private curve coefficient cannot be simulated from `(p*,V*)`. -/
theorem mpc_leaky_no_simulator :
    ¬ ∃ sim : CrossingLeakage → ℤ,
      ∀ (bk : OrderBook) (K : ℕ),
        demand bk 0 = sim ⟨crossing bk K, clearedVolume bk K⟩ := by
  rintro ⟨sim, hsim⟩
  have hA := hsim bookA 3
  have hB := hsim bookB 3
  rw [show crossing bookA 3 = 1 from workBook_crossing,
    show clearedVolume bookA 3 = 8 from workBook_clearedVolume] at hA
  rw [bookB_crossing, bookB_clearedVolume] at hB
  rw [(bookAB_demand0_differs).1] at hA
  rw [(bookAB_demand0_differs).2] at hB
  exact absurd (hA.trans hB.symm) (by decide)

/-! ## 4. The joined clearing theorem. -/

theorem cleared_conserving_optimal_and_reveal_only (mc : MpcClearing) :
    ((∀ a, netFlow (clearedBatch (mc.vStar : ℚ) mc.ρ) a = 0) ∧
      (∀ f ∈ clearedBatch (mc.vStar : ℚ) mc.ρ,
        f.filledIn ≤ f.order.offerAmount ∧
        f.order.limitPrice ≤ f.execPrice ∧
        f.filledIn * f.order.limitPrice ≤ f.filledOut) ∧
      (∀ f ∈ clearedBatch (mc.vStar : ℚ) mc.ρ,
        recvValue 0 1 mc.ρ f = spentValue 0 1 mc.ρ f)) ∧
    (∀ q < mc.K, execVol mc.bk q ≤ mc.vStar) ∧
    (mc.mpcView = mpcSim mc.K mc.maskedLen mc.leakage ∧
      mc.leakage = ⟨crossing mc.bk mc.K, clearedVolume mc.bk mc.K⟩) := by
  refine ⟨clearedBatch_optimal (mc.vStar : ℚ) mc.ρ ?_ mc.hρ,
    fun q hq => mc.vStar_optimal hq, mc.reveal_only, rfl⟩
  exact_mod_cast mc.vStar_nonneg

def mcA : MpcClearing :=
  { bk := bookA
    hvalid := workBook_valid
    K := 3
    hK := by norm_num
    ρ := 2
    hρ := by norm_num
    maskedLen := 144 }

theorem mcA_leakage : mcA.leakage = ⟨1, 8⟩ := by
  unfold MpcClearing.leakage MpcClearing.pStar MpcClearing.vStar mcA bookA
  rw [workBook_crossing, workBook_clearedVolume]

def mcA_joined := cleared_conserving_optimal_and_reveal_only mcA

/-! ## 5. MaskedBoundaryParty rows and the semantic A2B bridge. -/

section BoundaryRows

variable {n t : ℕ}

/-- Party 0's `y-r₀` and every other party's `-rᵢ`, expressed by rebalancing
the all-negative mask row at the designated public-opening party. -/
def maskedBoundaryRows (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t) : Fin n → ZMod t :=
  rebalanceFn n j y (fun i => -masks i)

theorem maskedBoundaryRows_designated (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t) :
    maskedBoundaryRows j y masks j = y - masks j := by
  unfold maskedBoundaryRows rebalanceFn
  simp
  abel

theorem maskedBoundaryRows_other (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t)
    {i : Fin n} (hi : i ≠ j) : maskedBoundaryRows j y masks i = -masks i :=
  rebalanceFn_of_ne _ j y hi

theorem sum_maskedBoundaryRows (j : Fin n) (y : ZMod t) (masks : Fin n → ZMod t) :
    ∑ i, maskedBoundaryRows j y masks i = y - ∑ i, masks i := by
  unfold maskedBoundaryRows
  rw [sum_rebalanceFn]
  simp only [Finset.sum_neg_distrib]
  abel

/-- If the only opened value is `y=m+Σrᵢ`, the party-local rows reconstruct `m`. -/
theorem maskedBoundary_reconstruct (j : Fin n) (m y : ZMod t) (masks : Fin n → ZMod t)
    (hpad : y = m + ∑ i, masks i) : ∑ i, maskedBoundaryRows j y masks i = m := by
  rw [sum_maskedBoundaryRows, hpad]
  abel

/-- Numeric value represented by a little-endian boolean vector. -/
def bitsValue {w : ℕ} (bits : Fin w → Bool) : ℕ :=
  ∑ i, if bits i then 2 ^ (i : ℕ) else 0

/-- Semantic contract of the distributed A2B result: its bits are in the declared
`w`-bit range and denote the mod-t sum of the source-party arithmetic rows. -/
def A2BRepresents {w : ℕ} (rows : Fin n → ZMod t) (bits : Fin w → Bool) : Prop :=
  bitsValue bits < 2 ^ w ∧ (bitsValue bits : ZMod t) = ∑ i, rows i

/-- Composition of masked-boundary reconstruction with a correct A2B encoding.
The upstream `< 2^w` bound that makes Rust truncation exact is an explicit
hypothesis; this theorem does not invent a malicious range check. -/
theorem maskedBoundary_a2b_semantic {w : ℕ} (j : Fin n) (m y : ZMod t) (mNat : ℕ)
    (masks : Fin n → ZMod t) (bits : Fin w → Bool)
    (hpad : y = m + ∑ i, masks i) (hrep : (mNat : ZMod t) = m)
    (hrange : mNat < 2 ^ w) (hbits : bitsValue bits = mNat) :
    A2BRepresents (maskedBoundaryRows j y masks) bits := by
  unfold A2BRepresents
  constructor
  · rw [hbits]
    exact hrange
  · rw [maskedBoundary_reconstruct j m y masks hpad, hbits]
    exact hrep

end BoundaryRows

/-! ## 6. Cert-F and modular composition. -/

structure CertifiedMpcClearing (V E : Type*) [Fintype V] [Fintype E] where
  lp : FlowLP V E ℤ
  f : E → ℤ
  π : V → ℤ
  s : E → ℤ
  cert : Certified lp f π s
  K : ℕ
  maskedLen : ℕ
  leak : CrossingLeakage
  view : MpcView
  reveal : view = mpcSim K maskedLen leak

theorem certified_epsilon_optimal_and_reveal_only {V E : Type*} [Fintype V] [Fintype E]
    (cmc : CertifiedMpcClearing V E) {f' : E → ℤ} (hf' : PrimalFeasible cmc.lp f') :
    (cmc.lp.w ⬝ᵥ f' ≤ cmc.lp.w ⬝ᵥ cmc.f + cmc.lp.ε) ∧
    (cmc.view = mpcSim cmc.K cmc.maskedLen cmc.leak) :=
  ⟨certifies_epsilon_optimal cmc.lp cmc.cert hf', cmc.reveal⟩

theorem compose_reveals_only {A B QA QB VA VB : Type*}
    (v₁ : A → VA) (s₁ : QA → VA) (q₁ : A → QA) (h₁ : ∀ a, v₁ a = s₁ (q₁ a))
    (v₂ : B → VB) (s₂ : QB → VB) (q₂ : B → QB) (h₂ : ∀ b, v₂ b = s₂ (q₂ b)) :
    ∀ (a : A) (b : B),
      (v₁ a, v₂ b) = (fun p : QA × QB => (s₁ p.1, s₂ p.2)) (q₁ a, q₂ b) := by
  intro a b
  simp only [h₁, h₂]

theorem fold_then_crossing_reveals_only
    {A QA VA : Type*} (foldView : A → VA) (foldSim : QA → VA) (foldLeak : A → QA)
    (hfold : ∀ a, foldView a = foldSim (foldLeak a)) (mc : MpcClearing) :
    ∀ a, (foldView a, mc.mpcView) =
      (fun p : QA × CrossingLeakage =>
        (foldSim p.1, mpcSim mc.K mc.maskedLen p.2)) (foldLeak a, mc.leakage) := by
  intro a
  simp only [hfold a, mc.reveal_only]

/-! ## 7. PerfectZK bridge. -/

open Metatheory.Open.PerfectZK

def mpcPerfectZK (K maskedLen : ℕ) : PerfectZK where
  S := CrossingLeakage
  W := MpcClearing
  V := MpcView
  view q _ := mpcSim K maskedLen q
  sim q := mpcSim K maskedLen q
  hperf _ _ := rfl

theorem mpcView_eq_perfectZK (mc : MpcClearing) :
    mc.mpcView = (mpcPerfectZK mc.K mc.maskedLen).view mc.leakage mc :=
  mc.reveal_only

theorem mpc_reveal_nothing (K maskedLen : ℕ) (q : CrossingLeakage)
    (mc₁ mc₂ : MpcClearing) :
    (mpcPerfectZK K maskedLen).view q mc₁ = (mpcPerfectZK K maskedLen).view q mc₂ :=
  (mpcPerfectZK K maskedLen).view_indep_of_witness q mc₁ mc₂

/-! Computed RED/positive teeth. -/

#guard (crossing workBook 3, clearedVolume workBook 3) == (1, 8)
#guard (balanceCrossing workBook workBook_crosses) == 2
#guard (crossing bookB 3, clearedVolume bookB 3) == (1, 8)
#guard (decide (Clears workBook 1), decide (Clears bookB 1)) == (false, true)
#guard (demand bookA 0, demand bookB 0) == (10, 11)

/-! Axiom hygiene. -/

#assert_all_clean [Market.MpcClearingSecurity.perfect_hiding,
  Market.MpcClearingSecurity.full_collusion_breaks_hiding,
  Market.MpcClearingSecurity.otpMasks,
  Market.MpcClearingSecurity.MpcClearing.reveal_only,
  Market.MpcClearingSecurity.MpcClearing.same_leakage_indistinguishable,
  Market.MpcClearingSecurity.old_balanceCrossing_disagrees_with_runtime,
  Market.MpcClearingSecurity.old_sign_not_determined_by_runtime_leakage,
  Market.MpcClearingSecurity.mpc_leaky_no_simulator,
  Market.MpcClearingSecurity.cleared_conserving_optimal_and_reveal_only,
  Market.MpcClearingSecurity.mcA_joined,
  Market.MpcClearingSecurity.maskedBoundary_reconstruct,
  Market.MpcClearingSecurity.maskedBoundary_a2b_semantic,
  Market.MpcClearingSecurity.certified_epsilon_optimal_and_reveal_only,
  Market.MpcClearingSecurity.compose_reveals_only,
  Market.MpcClearingSecurity.fold_then_crossing_reveals_only,
  Market.MpcClearingSecurity.mpcView_eq_perfectZK,
  Market.MpcClearingSecurity.mpc_reveal_nothing]

end Market.MpcClearingSecurity
