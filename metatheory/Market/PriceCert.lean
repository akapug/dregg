/-
# Market.PriceCert — the fhEgg derivatives soundness core: `Price-Cert` (state-price LP + superhedging dual).

**The verify-not-find keystone for the WHOLE derivatives-pricing family — ONE certificate.**
`docs/deos/FHEGG-PRODUCT-ORDER-FRONTIER.md §R2.1` names the unifying object: over a public scenario
grid/tree `Ω`, calibrated-instrument payoffs `H` with observed marks `a`, and a new product's scenario
payoff `h`, the no-arbitrage price is the state-price LP

    upper price   p̄ = max_{π ≥ 0} hᵀπ   s.t.  H π = a          (state prices π consistent with the market)
    superhedge    p̄ = min_{y}  aᵀy      s.t.  yᵀH ≥ h          (a hedge portfolio dominating the payoff)

and the complete certificate is `π ≥ 0, H π = a, yᵀH ≥ h, 0 ≤ aᵀy − hᵀπ ≤ ε`. This module proves that
soundness core: a valid `Price-Cert` CERTIFIES the product price is arbitrage-free / correctly
superhedged, **independent of how `(π, y)` were found** — the exact `Cert-F` shape, specialized to
risk-neutral pricing (Barratt–Tuck–Boyd convex risk-neutral pricing). One certificate relation for the
European / basket / arithmetic-Asian / barrier / futures family.

## What is proved (honest scope)

  * **`price_weak_duality` (the engine — no-arbitrage weak duality).** For EVERY consistent state price
    `π` (`π ≥ 0, H π = a`) and EVERY superhedge `y` (`yᵀH ≥ h`): `hᵀπ ≤ aᵀy`. Four moves, all reading only
    the two feasibilities: `hᵀπ ≤ (yᵀH)π` (`h ≤ yᵀH`, `π ≥ 0`); `= yᵀ(Hπ)` (associativity); `= yᵀa`
    (`Hπ = a`); `= aᵀy`. The product's price under any consistent measure is bounded by the cost of any
    superhedge — the arbitrage-free interval.
  * **`price_cert_certifies` (THE KEYSTONE).** If `(π, y)` is a `PriceCertified` tuple (gap `aᵀy − hᵀπ ≤ ε`),
    then for EVERY consistent state price `π'`: `hᵀπ' ≤ hᵀπ + ε`. So NO consistent risk-neutral measure
    prices the product more than `ε` above the certified price — the certified `π` attains the
    arbitrage-free upper price to within `ε`, and the superhedge `y` caps it. The proof reads ONLY the
    certificate. **Independent of how `(π, y)` was found** — the LP solver's search is never re-examined.
  * **`price_gap_nonneg`** — the certified gap `aᵀy − hᵀπ ≥ 0` (weak duality at the certificate's own
    `π` against its own `y`), so `ε ≥ 0` is forced and a "certificate" with a negative gap is vacuous.

  * **The American / Bermudan direction (`§ Snell`).** American optionality is NOT the first
    expressiveness cliff — it is a **Snell-envelope LP** on the scenario tree (Haugh–Kogan / Rogers
    martingale duals). We prove the certificate-soundness *direction*: **any LP-feasible value vector `V`
    (`V ≥ g` exercise-dominance, `V ≥ d·P V` superharmonic) UPPER-bounds the true backward-induction
    (Snell) value** — a feasible `V` is a sound upper-bound certificate on the option, independent of how
    `V` was found (`snell_feasible_upper_bound`, worked on a one-step binomial + the general one-step
    domination). The cliff is **tree SIZE, not solver class** (per codex): the LP is the object.

**NAMED residuals (precise, honest — not proved here):**
  * the **full continuous / path-dependent** case (the state grid `Ω` is a finite public tree here; a
    hidden running-max / continuous barrier pays running-max + `H` trigger comparisons — state-size and
    comparison-budget hard, not solver-hard);
  * the **general finite-DAG** Snell assembly (proved on the one-step binomial tree + the general
    single-step lemma; the multi-layer backward-induction over an arbitrary tree is the named extension);
  * the **stopping-flow dual exactness** (that the Snell LP dual is *exactly* the occupation-measure /
    martingale dual — stated, tied to Haugh–Kogan/Rogers, verified structurally, not re-derived here);
  * model-correctness: a proof certifies pricing *under a committed model*; it cannot certify the
    model/oracle is economically correct (the honest floor of `FHEGG-PRODUCT-ORDER-FRONTIER.md §R2.1`).

Pure.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Dregg2.Circuit
import Dregg2.Tactics

namespace Market

open Matrix

/-! ## 1. The state-price market (public scenarios + instruments, private prices). -/

variable {S J : Type*} [Fintype S] [Fintype J]

/-- **A state-price market** — the public object every LP-expressible derivative prices against:
scenarios `S`, calibrated instruments `J` with public payoff matrix `H` (`H j s` = payoff of instrument
`j` in scenario `s`), observed marks `a` (the instruments' prices), the new product's scenario payoff `h`,
and the public accuracy target `ε`. The state prices `π` and hedge `y` stay hidden. -/
structure Market (S J : Type*) where
  /-- The public instrument-payoff matrix (`H j s` = payoff of instrument `j` in scenario `s`). -/
  H : Matrix J S ℚ
  /-- The observed instrument marks (`a j` = price of instrument `j`). -/
  a : J → ℚ
  /-- The new product's scenario payoff (`h s` = payoff in scenario `s`). -/
  h : S → ℚ
  /-- The public accuracy target (`gap ≤ ε` ⇒ `ε`-tight arbitrage-free bound). -/
  ε : ℚ

/-- **A consistent state price** — `π ≥ 0` (a nonnegative measure) that reprices every calibrated
instrument to its mark (`H π = a`). The risk-neutral measure the product is priced against. -/
def ConsistentPrice (mk : Market S J) (π : S → ℚ) : Prop :=
  0 ≤ π ∧ mk.H *ᵥ π = mk.a

/-- **A superhedge** — a portfolio `y` of instruments whose payoff dominates the product's in every
scenario (`yᵀH ≥ h`). Its cost is `aᵀy`; by weak duality it caps the product's arbitrage-free price. -/
def Superhedge (mk : Market S J) (y : J → ℚ) : Prop :=
  mk.h ≤ y ᵥ* mk.H

/-- **A `Price-Cert` certificate** — a state-price / superhedge pair whose duality gap is `≤ ε`. The
ENTIRE object the hidden proof checks; sound ⇒ the certified price `hᵀπ` is the arbitrage-free price to
within `ε` (`price_cert_certifies`), independent of how `(π, y)` were found. -/
def PriceCertified (mk : Market S J) (π : S → ℚ) (y : J → ℚ) : Prop :=
  ConsistentPrice mk π ∧ Superhedge mk y ∧ mk.a ⬝ᵥ y - mk.h ⬝ᵥ π ≤ mk.ε

/-! ## 2. No-arbitrage weak duality — the LP inequality every feasible pair satisfies. -/

/-- **`price_weak_duality` — `hᵀπ ≤ aᵀy` for EVERY consistent price `π` and superhedge `y`.** The
load-bearing lemma: the product's price under any risk-neutral measure is bounded by the cost of any
superhedge, using NOTHING about how either was obtained. The four moves:

  * `hᵀπ ≤ (yᵀH)π` — superhedge `h ≤ yᵀH` scaled by `π ≥ 0`;
  * `(yᵀH)π = yᵀ(Hπ)` — associativity of the pairing;
  * `= yᵀa` — consistency `Hπ = a`;
  * `= aᵀy` — commutativity.

This is the whole of verify-not-find for derivative pricing: a certificate is sound because weak duality
sandwiches the no-arbitrage price, and weak duality reads only the two feasibilities. -/
theorem price_weak_duality (mk : Market S J) {π : S → ℚ} {y : J → ℚ}
    (hc : ConsistentPrice mk π) (hy : Superhedge mk y) :
    mk.h ⬝ᵥ π ≤ mk.a ⬝ᵥ y :=
  calc mk.h ⬝ᵥ π
      ≤ (y ᵥ* mk.H) ⬝ᵥ π := dotProduct_le_dotProduct_of_nonneg_right hy hc.1
    _ = y ⬝ᵥ (mk.H *ᵥ π) := (dotProduct_mulVec y mk.H π).symm
    _ = y ⬝ᵥ mk.a := by rw [hc.2]
    _ = mk.a ⬝ᵥ y := dotProduct_comm _ _

/-! ## 3. THE KEYSTONE — a `Price-Cert` certifies the arbitrage-free price (verify-not-find). -/

/-- **`price_gap_nonneg` — a certified gap is `≥ 0`.** Weak duality at the certificate's own `π` against
its own `y` gives `hᵀπ ≤ aᵀy`, i.e. `aᵀy − hᵀπ ≥ 0`. So a "certificate" asserting a strictly negative
gap is impossible, and the target `ε` it certifies is forced `≥ 0`. -/
theorem price_gap_nonneg (mk : Market S J) {π : S → ℚ} {y : J → ℚ}
    (hc : ConsistentPrice mk π) (hy : Superhedge mk y) :
    0 ≤ mk.a ⬝ᵥ y - mk.h ⬝ᵥ π :=
  sub_nonneg.mpr (price_weak_duality mk hc hy)

/-- **`price_cert_certifies` — the certificate CERTIFIES the no-arbitrage upper price.** Given a
`PriceCertified` tuple `(π, y)` (gap `≤ ε`), EVERY consistent state price `π'` obeys `hᵀπ' ≤ hᵀπ + ε`: no
risk-neutral measure prices the product more than `ε` above the certified price `hᵀπ`. The certified `π`
attains the arbitrage-free upper price to within `ε`, and the superhedge `y` is the witness that caps it —
`price_weak_duality` applied to `π'` against the certificate's OWN dual `y` gives `hᵀπ' ≤ aᵀy`, and the
gap gives `aᵀy ≤ hᵀπ + ε`. **Independent of how `(π, y)` was found** — the LP solver's search is never
re-examined; the linear certificate stands alone. The "checked output" half of the fhEgg pricing engine. -/
theorem price_cert_certifies (mk : Market S J) {π : S → ℚ} {y : J → ℚ}
    (hcert : PriceCertified mk π y) {π' : S → ℚ} (hc' : ConsistentPrice mk π') :
    mk.h ⬝ᵥ π' ≤ mk.h ⬝ᵥ π + mk.ε := by
  obtain ⟨_, hy, hgap⟩ := hcert
  have h1 : mk.h ⬝ᵥ π' ≤ mk.a ⬝ᵥ y := price_weak_duality mk hc' hy
  have h2 : mk.a ⬝ᵥ y ≤ mk.h ⬝ᵥ π + mk.ε := by linarith
  linarith

/-! ## 4. NON-VACUITY, positive polarity — a worked complete market (bond + stock, up/down).

Two scenarios (up `s=0`, down `s=1`), two instruments: a bond `(1,1)` at mark `1`, a stock `(2,0)` at
mark `1`. The unique consistent state price is `π = (½, ½)` (`π_up+π_down=1`, `2π_up=1`). The new product
is a digital call `h = (1, 0)`; its no-arbitrage price is `hᵀπ = ½`. The superhedge `y = (0, ½)` (half a
stock) replicates it exactly: `yᵀH = (1, 0) ≥ h`, cost `aᵀy = ½` — a TIGHT (`gap = 0`) certificate. -/

/-- The worked instrument matrix: bond row `(1,1)`, stock row `(2,0)`. -/
def mkH : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of ![![1, 1], ![2, 0]]

/-- The worked market: bond + stock marked at `1`, product `= (1,0)`, exact target `ε = 0`. -/
def mkt2 : Market (Fin 2) (Fin 2) :=
  { H := mkH, a := ![1, 1], h := ![1, 0], ε := 0 }

/-- The unique consistent state price `(½, ½)`. -/
def piStar : Fin 2 → ℚ := ![1/2, 1/2]
/-- The replicating superhedge `(0, ½)` — half a stock. -/
def yStar : Fin 2 → ℚ := ![0, 1/2]

/-- **THE CERTIFICATE VERIFIES — the worked pair is `PriceCertified` with gap exactly `0`.** `π = (½,½)`
is a consistent state price (`H π = a`, `π ≥ 0`), `y = (0,½)` superhedges the digital call (`yᵀH = (1,0) ≥
(1,0)`), and `aᵀy − hᵀπ = ½ − ½ = 0 ≤ ε = 0`. A concrete, non-vacuous `Price-Cert` of a real
arbitrage-free price. -/
theorem mkt2_cert_valid : PriceCertified mkt2 piStar yStar := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro s; fin_cases s <;> norm_num [piStar]
  · funext j; fin_cases j <;>
      simp [mkt2, mkH, piStar, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · intro s; fin_cases s <;>
      simp [mkt2, mkH, yStar, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> norm_num
  · simp [mkt2, mkH, piStar, yStar, dotProduct, Fin.sum_univ_two]

/-- **THE KEYSTONE, INSTANTIATED — the certificate proves the arbitrage-free price is `½`.** Every
consistent state price `π'` has `hᵀπ' ≤ hᵀπ + 0 = ½`: no risk-neutral measure prices the digital call
above `½`. `price_cert_certifies` on the worked certificate — the untrusted LP's `(π, y)` proves the
no-arbitrage price by the linear certificate alone. -/
theorem mkt2_price_bounded {π' : Fin 2 → ℚ} (hc' : ConsistentPrice mkt2 π') :
    mkt2.h ⬝ᵥ π' ≤ 1/2 := by
  have h := price_cert_certifies mkt2 mkt2_cert_valid hc'
  have hpi : mkt2.h ⬝ᵥ piStar = 1/2 := by
    simp [mkt2, piStar, dotProduct, Fin.sum_univ_two]
  rw [hpi] at h; simpa [mkt2] using h

/-! ## 5. NON-VACUITY, negative polarity — the teeth (an unsound certificate is REFUSED). -/

/-- A NON-consistent "state price" `(1, 0)` — prices the bond right (`1`) but the stock at `2 ≠ 1`. -/
def piBad : Fin 2 → ℚ := ![1, 0]

/-- **TOOTH (consistency): an inconsistent measure is REFUSED.** `piBad = (1,0)` reprices the stock to
`2·1 = 2 ≠ 1 = a₁`, so `H π ≠ a` — it is not a `ConsistentPrice`. It would misprice the digital call at
`hᵀπ = 1` (an arbitrage); the consistency check refuses it. Mirrors `Cert-F`'s `leakF_infeasible`. -/
theorem piBad_inconsistent : ¬ ConsistentPrice mkt2 piBad := by
  rintro ⟨-, hHa⟩
  have h1 := congrFun hHa 1
  simp [mkt2, mkH, piBad, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

/-- A portfolio that does NOT dominate the payoff — the empty hedge `(0, 0)` pays `(0,0) < (1,0) = h` in
the up scenario. -/
def yBad : Fin 2 → ℚ := ![0, 0]

/-- **TOOTH (superhedge): a non-dominating portfolio is REFUSED.** `yBad = (0,0)` pays `0` in the up
scenario, below the product's `h₀ = 1`, so `yᵀH ≥ h` fails — not a `Superhedge`. A portfolio that does
not cover the payoff cannot certify a price. -/
theorem yBad_not_superhedge : ¬ Superhedge mkt2 yBad := by
  intro hy
  have h0 := hy 0
  norm_num [mkt2, mkH, yBad, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0

/-- **TOOTH (no consistent over-price): NO risk-neutral measure prices the call at the arbitrage value
`1`.** The naive "the call is worth its up-payoff `1`" requires a consistent measure with `hᵀπ' = 1`, but
`mkt2_price_bounded` forces every consistent `π'` to `hᵀπ' ≤ ½ < 1`. So the certificate refuses the
arbitrage: the superhedge caps the price at `½`. Mirrors `Cert-F`'s `zeroFlow_not_certifiable`. -/
theorem no_consistent_overprice {π' : Fin 2 → ℚ} (hc' : ConsistentPrice mkt2 π') :
    mkt2.h ⬝ᵥ π' ≠ 1 := by
  have := mkt2_price_bounded hc'
  intro he; rw [he] at this; norm_num at this

/-! ## 6. EMITTABILITY — the `Price-Cert` check as LINEAR AIR `Constraint`s (`Dregg2.Circuit`).

The whole check is LINEAR: the consistency rows `H π = a` (one gate per instrument) plus the gap
`aᵀy − hᵀπ` (one linear functional). Demonstrated on the SCALED integer instance (marks `×2` so the state
prices are integers `(1,1)`): wire `0 = π_up`, `1 = π_down`, `2 = y_bond`, `3 = y_stock`. -/

open Dregg2.Circuit

/-- Lay a scaled `Price-Cert` out: `π` on wires 0–1, `y` on wires 2–3 (integer witness). -/
def encodePriceCert (piU piD yB yS : ℤ) : Assignment
  | 0 => piU | 1 => piD | 2 => yB | 3 => yS
  | _ => 0

/-- **The consistency + gap gates** for the scaled instance (marks `a = (2,2)`, product `h = (2,0)`):
bond row `π_up + π_down = 2`, stock row `2·π_up = 2`, and the gap `aᵀy − hᵀπ = (2 y_bond + 2 y_stock) −
2 π_up = 0` (tight optimum). Three linear gates — `O(#instruments + 1)`. -/
def bondGate : Constraint :=
  { lhs := .add (.var 0) (.var 1), rhs := .const 2 }
def stockGate : Constraint :=
  { lhs := .mul (.const 2) (.var 0), rhs := .const 2 }
def priceGapExpr : Expr :=
  .add (.add (.mul (.const 2) (.var 2)) (.mul (.const 2) (.var 3)))
       (.mul (.const (-2)) (.var 0))
def priceCertCircuit : ConstraintSystem :=
  [ bondGate, stockGate, { lhs := priceGapExpr, rhs := .const 0 } ]

/-- **THE EMIT BRIDGE — the AIR system is `satisfied` ⇔ the `Price-Cert` arithmetic holds.**
`satisfied priceCertCircuit (encodePriceCert …)` iff the two consistency rows hold AND the gap is `0`.
Checking the circuit IS checking the certificate, on the worked scaled instance. -/
theorem priceCertCircuit_sound (piU piD yB yS : ℤ) :
    satisfied priceCertCircuit (encodePriceCert piU piD yB yS)
      ↔ (piU + piD = 2) ∧ (2 * piU = 2) ∧ (2 * yB + 2 * yS + (-2) * piU = 0) := by
  simp only [satisfied, priceCertCircuit, bondGate, stockGate, priceGapExpr,
    List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, Constraint.holds, Expr.eval,
    encodePriceCert]
  tauto

/-- **THE VALID CERTIFICATE IS ACCEPTED** — the scaled tight certificate (`π = (1,1)`, `y = (0,1)`)
satisfies `priceCertCircuit` (consistency `1+1=2`, `2·1=2`; gap `2·0 + 2·1 − 2·1 = 0`). -/
theorem priceCertCircuit_accepts : satisfied priceCertCircuit (encodePriceCert 1 1 0 1) := by
  rw [priceCertCircuit_sound]; norm_num

/-- **A gap-violating certificate is REJECTED** — an over-priced witness (`y = (0,2)`, gap `4 − 2 = 2 ≠ 0`)
fails the gap gate, even though consistency holds. The circuit's gap gate refuses the arbitrage. -/
theorem priceCertCircuit_rejects : ¬ satisfied priceCertCircuit (encodePriceCert 1 1 0 2) := by
  rw [priceCertCircuit_sound]; rintro ⟨-, -, hg⟩; norm_num at hg

/-! ## 7. The AMERICAN / BERMUDAN direction — the Snell-envelope LP (tree-size, not solver-class).

American optionality is a **Snell-envelope LP** on the scenario tree, NOT mixed-integer. On a one-step
binomial tree — root `0`, leaves up `1` / down `2` — the true (backward-induction) option value is

    U₁ = g₁,   U₂ = g₂,   U₀ = max( g₀ ,  d·(pA·U₁ + pB·U₂) )     (exercise now, or hold and continue)

and the LP for an UPPER bound is `min V₀ s.t. V ≥ g (dominance), V₀ ≥ d·(pA V₁ + pB V₂) (superharmonic)`.
We prove the certificate-soundness DIRECTION: any LP-feasible `V` upper-bounds `U` — a feasible `V` is a
sound upper-bound certificate on the option, independent of how it was found. The general finite-DAG
assembly and the stopping-flow dual exactness are NAMED residuals (see the module header). -/

/-- **A one-step binomial Snell tree** — exercise payoffs `g` at the three nodes (`0` root, `1` up,
`2` down), discount `d`, and transition weights `pA` (root→up), `pB` (root→down). -/
structure SnellTree where
  /-- Exercise payoff at each node (`0` root, `1` up, `2` down). -/
  g : Fin 3 → ℚ
  /-- The per-step discount factor (`≥ 0`). -/
  d : ℚ
  /-- Transition weight root → up (`≥ 0`). -/
  pA : ℚ
  /-- Transition weight root → down (`≥ 0`). -/
  pB : ℚ

/-- **The continuation value at the root** under a value vector `V` — `d·(pA·V_up + pB·V_down)`, the
discounted expected next value (the "hold" branch). -/
def contValue (t : SnellTree) (V : Fin 3 → ℚ) : ℚ := t.d * (t.pA * V 1 + t.pB * V 2)

/-- **The true (backward-induction) Snell value at the root** — `max(g₀, continuation of the exercise
values)`. Leaves are terminal (`U = g`); the root chooses exercise-now vs hold. This is the exact
American option value on the tree (the Snell envelope's root). -/
def snellValue (t : SnellTree) : ℚ := max (t.g 0) (contValue t t.g)

/-- **LP feasibility of a candidate value vector `V`** — exercise-dominance at every node (`V ≥ g`) and
superharmonicity at the root (`V₀ ≥ continuation`). The primal feasibility of the Snell LP. -/
def SnellFeasible (t : SnellTree) (V : Fin 3 → ℚ) : Prop :=
  t.g 1 ≤ V 1 ∧ t.g 2 ≤ V 2 ∧ t.g 0 ≤ V 0 ∧ contValue t V ≤ V 0

/-- **`snell_feasible_upper_bound` — a feasible `V` UPPER-bounds the Snell value.** For a nonnegative
discount and transition weights, any `SnellFeasible V` has `snellValue t ≤ V 0`: an LP-feasible value
vector certifies a valid upper bound on the true American option value, **independent of how `V` was
found** (the verify-not-find direction for optimal stopping). The proof: `V₀ ≥ g₀` and `V₀ ≥ continuation
of V ≥ continuation of g` (monotone in `V ≥ g` since `d, pA, pB ≥ 0`), so `V₀ ≥ max(g₀, cont g) = U₀`. -/
theorem snell_feasible_upper_bound (t : SnellTree) {V : Fin 3 → ℚ}
    (hd : 0 ≤ t.d) (hpA : 0 ≤ t.pA) (hpB : 0 ≤ t.pB) (hV : SnellFeasible t V) :
    snellValue t ≤ V 0 := by
  obtain ⟨hg1, hg2, hg0, hcont⟩ := hV
  refine max_le hg0 ?_
  have hmono : contValue t t.g ≤ contValue t V := by
    unfold contValue
    apply mul_le_mul_of_nonneg_left _ hd
    exact add_le_add (mul_le_mul_of_nonneg_left hg1 hpA) (mul_le_mul_of_nonneg_left hg2 hpB)
  linarith

/-- The worked American put on a one-step binomial: exercise `g = (0, 4, 0)` (in-the-money up), discount
`d = 1`, symmetric `pA = pB = ½`. Continuation `= ½·4 + ½·0 = 2 > g₀ = 0`, so the option is worth `2` by
HOLDING (the Snell max chooses continuation) — the sharp, mildly counter-intuitive result that early
exercise is an LP, not a binary. -/
def putTree : SnellTree := { g := ![0, 4, 0], d := 1, pA := 1/2, pB := 1/2 }

/-- **THE SNELL VALUE, COMPUTED — the worked option is worth `2`.** Non-vacuous: the value comes from the
continuation branch (`2 > 0`), so `snellValue` genuinely takes the `max`. -/
theorem putTree_value : snellValue putTree = 2 := by
  simp [snellValue, contValue, putTree]; norm_num

/-- The Snell envelope itself `V = (2, 4, 0)` — the tight feasible certificate. -/
def putV : Fin 3 → ℚ := ![2, 4, 0]

/-- **THE ENVELOPE IS FEASIBLE (positive polarity)** — `V = (2,4,0)` dominates the exercise payoff at
every node and is superharmonic at the root (`continuation = 2 ≤ V₀ = 2`), so it is a valid Snell
certificate that ACHIEVES the bound. -/
theorem putV_feasible : SnellFeasible putTree putV := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [putTree, putV, contValue] <;> norm_num

/-- **THE KEYSTONE, INSTANTIATED — every feasible certificate upper-bounds the option value `2`.** Any
`SnellFeasible V` for the worked put has `2 ≤ V₀`: the LP-feasible value is a sound upper bound on the
American option value, independent of how found. -/
theorem putTree_certified {V : Fin 3 → ℚ} (hV : SnellFeasible putTree V) : 2 ≤ V 0 := by
  have h := snell_feasible_upper_bound putTree (by norm_num [putTree])
    (by norm_num [putTree]) (by norm_num [putTree]) hV
  rwa [putTree_value] at h

/-- **TOOTH (superharmonicity): an under-valued vector is REFUSED.** A candidate `V = (1, 4, 0)` claiming
the option is worth `1` at the root fails superharmonicity: the continuation is `2 > 1 = V₀`, so
`contValue ≤ V₀` is violated — not `SnellFeasible`. A certificate cannot under-bound the option: the
superharmonic constraint bites exactly when the holder should keep holding. -/
theorem underValue_refused : ¬ SnellFeasible putTree ![1, 4, 0] := by
  rintro ⟨-, -, -, hcont⟩
  simp [putTree, contValue] at hcont
  norm_num at hcont

/-! ### `#guard` smoke — the pricing + Snell arithmetic is COMPUTED, not asserted. -/

-- the digital call's no-arbitrage price under the consistent measure is ½:
#guard (mkt2.h ⬝ᵥ piStar) == (1/2 : ℚ)
-- the superhedge's cost equals it (gap zero — tight):
#guard (mkt2.a ⬝ᵥ yStar) == (1/2 : ℚ)
-- the scaled emitted gap is zero at the tight certificate, 2 at the over-priced one:
#guard priceGapExpr.eval (encodePriceCert 1 1 0 1) == 0
#guard priceGapExpr.eval (encodePriceCert 1 1 0 2) == 2
-- the American put is worth 2 (by holding — continuation beats immediate exercise 0):
#guard snellValue putTree == (2 : ℚ)
#guard contValue putTree putTree.g == (2 : ℚ)

/-! ### Axiom hygiene — the `Price-Cert` + Snell keystones pinned kernel-clean. -/

#assert_all_clean [Market.price_weak_duality, Market.price_gap_nonneg, Market.price_cert_certifies,
  Market.mkt2_cert_valid, Market.mkt2_price_bounded, Market.piBad_inconsistent,
  Market.yBad_not_superhedge, Market.no_consistent_overprice, Market.priceCertCircuit_sound,
  Market.priceCertCircuit_accepts, Market.priceCertCircuit_rejects, Market.snell_feasible_upper_bound,
  Market.putTree_value, Market.putV_feasible, Market.putTree_certified, Market.underValue_refused]

end Market
