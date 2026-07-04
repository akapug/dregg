/-
# Dregg2.Exec.ReachableConservation — `Σ_c bal c a = 0` is a REACHABILITY INVARIANT (W1 keystone).

The DREGG3 §2.2 value law, closed: with `AssetId := CellId` (the asset IS its issuer cell) and
mint/burn/bridgeMint reshaped to ISSUER-MOVES, the kernel has NO non-conserving verb left
(`ledgerDeltaAsset_eq_zero`). So the per-asset total is not merely *invariant* across committed
steps — on any state REACHABLE from a value-empty genesis it is IDENTICALLY ZERO, for every asset,
unconditionally:

  * `Reachable` — genesis (all-zero ledger; live accounts may pre-exist, value may not) closed
    under committed `execFullTurnA` transactions AND committed gate-erased forests (the forest
    erases to a transaction list — `lowerForest`/`eraseG` — so one step constructor covers both);
  * `reachable_total_zero` — THE theorem: every reachable state satisfies `ExactConservation`
    (`∀ a, recTotalAsset k a = 0`). The issuer wells carry −supply; the books always close.

This upgrades Guarantee B from "the sum is invariant" to "the sum is identically zero"
(`AssuranceCase.lean`). Non-vacuity: the `#guard` witnesses run a genesis → create-issuer → mint →
transfer → burn trajectory and check Σ=0 at EVERY step, plus the non-issuer-mint refusal tooth.
-/
import Dregg2.Exec.TurnExecutorFull

namespace Dregg2.Exec.ReachableConservation

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.Exec.TurnExecutorFull

/-- **Genesis (value-empty).** The `bal` ledger is identically zero. Live accounts (issuer cells,
pot cells, users) MAY pre-exist — only VALUE must not: every unit in circulation must enter through
an issuer-move, so the issuer wells account for all of it. -/
def GenesisState (s : RecChainedState) : Prop :=
  s.kernel.bal = fun _ _ => 0

/-- **Reachability**: genesis, closed under committed per-asset transactions (`execFullTurnA` —
the all-or-nothing transaction the forest/turn layers fold; a committed gated forest reaches states
of exactly this shape via `execFullForestG_erases`/`lowerForestG_actions_eq_eraseG`). -/
inductive Reachable : RecChainedState → Prop
  /-- A value-empty genesis state is reachable. -/
  | genesis (s : RecChainedState) (h : GenesisState s) : Reachable s
  /-- A committed transaction from a reachable state reaches its post-state. -/
  | step (s s' : RecChainedState) (tt : List FullActionA) (hs : Reachable s)
      (h : execFullTurnA s tt = some s') : Reachable s'

/-- **`reachable_total_zero` — THE W1 VALUE LAW, CLOSED.** Every reachable state has
`Σ_{c ∈ accounts} bal c a = 0` for EVERY asset `a` — not invariant, ZERO. Genesis is zero
(`genesis_exactConservation`); every committed transaction preserves zero
(`execFullTurnA_conserves_exact`, which needs NO zero-net hypothesis because the delta family
vanishes identically — `ledgerDeltaAsset_eq_zero`). -/
theorem reachable_total_zero (s : RecChainedState) (h : Reachable s) :
    ExactConservation s.kernel := by
  induction h with
  | genesis s hg => exact genesis_exactConservation s.kernel hg
  | step s s' tt _ hcommit ih =>
      intro b
      rw [execFullTurnA_conserves_exact s s' tt b hcommit]
      exact ih b

/-- The per-step face (no reachability needed): a committed transaction takes a zero-sum state to a
zero-sum state. -/
theorem step_preserves_total_zero {s s' : RecChainedState} {tt : List FullActionA}
    (h : execFullTurnA s tt = some s') (hex : ExactConservation s.kernel) :
    ExactConservation s'.kernel := fun b => by
  rw [execFullTurnA_conserves_exact s s' tt b h]
  exact hex b

/-! ## Axiom hygiene. -/

#assert_axioms reachable_total_zero
#assert_axioms step_preserves_total_zero
#assert_axioms Dregg2.Exec.TurnExecutorFull.ledgerDeltaAsset_eq_zero
#assert_axioms Dregg2.Exec.TurnExecutorFull.turnLedgerDeltaAsset_eq_zero
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullA_conserves_exact
#assert_axioms Dregg2.Exec.TurnExecutorFull.execFullTurnA_conserves_exact

/-! ## Non-vacuity (`#guard`): a full issuer-supply TRAJECTORY, Σ=0 asserted at every step.

Genesis: live cells {1 (the issuer of asset 1), 2}, zero ledger. Actor 9 holds `node 1` (mint
authority over the ISSUER cell 1); actor 2 owns cell 2 (ordinary transfer authority via ownership).
Trajectory: mint 1→2 of 5 · transfer 2→3? (no — keep it two-party) · burn 2→1 of 2. -/

/-- Genesis fixture: issuer cell 1 + user cells 2,3 live; zero ledger; actor 9 holds the issuer
cap `node 1`; actor 2 owns cell 2 (`node 2` self-authority for the transfer leg). -/
def g0 : RecChainedState :=
  { kernel :=
      { accounts := {1, 2, 3}
        cell := fun _ => Value.record [("balance", Value.int 0)]
        caps := fun c => if c = 9 then [Cap.node 1] else if c = 2 then [Cap.node 2] else [] }
    log := [] }

/-- The trajectory: mint 5 of asset 1 to cell 2 (well 1 → −5), transfer 3 of it 2 → 3, burn 2 of
cell 3's holding back to the well... (3 lacks burn standing — burn is issuer-authorized: actor 9). -/
def traj : List FullActionA :=
  [ .mintA 9 2 1 5        -- well 1: −5 · cell 2: +5            Σ = 0
  , .balanceA ⟨2, 2, 3, 3⟩ 1  -- cell 2: 2 · cell 3: 3          Σ = 0
  , .burnA 9 3 1 3 ]      -- cell 3: 0 · well 1: −2             Σ = 0

-- genesis is zero-sum, the whole trajectory commits, and Σ=0 holds at EVERY prefix:
#guard (recTotalAsset g0.kernel 1 == 0)
#guard ((execFullTurnA g0 (traj.take 1)).map (fun s => recTotalAsset s.kernel 1)) == some 0
#guard ((execFullTurnA g0 (traj.take 2)).map (fun s => recTotalAsset s.kernel 1)) == some 0
#guard ((execFullTurnA g0 traj).map (fun s => recTotalAsset s.kernel 1)) == some 0
-- the final rows: well 1 carries −(outstanding 2), cell 2 holds 2, cell 3 emptied:
#guard ((execFullTurnA g0 traj).map (fun s => (s.kernel.bal 1 1, s.kernel.bal 2 1, s.kernel.bal 3 1)))
        == some (-2, 2, 0)
-- every OTHER asset stayed zero too:
#guard ((execFullTurnA g0 traj).map (fun s => (recTotalAsset s.kernel 0, recTotalAsset s.kernel 2)))
        == some (0, 0)
-- THE AUTHORITY TOOTH: actor 2 (owns cell 2, no issuer cap) cannot mint asset 1 — production
-- authority is control of the ISSUER, not of the recipient:
#guard ((execFullTurnA g0 [.mintA 2 2 1 5]).isNone)
-- THE GENESIS-ORDER TOOTH: minting an asset whose issuer cell is NOT live refuses:
#guard ((execFullTurnA g0 [.mintA 9 2 7 5]).isNone)

end Dregg2.Exec.ReachableConservation
