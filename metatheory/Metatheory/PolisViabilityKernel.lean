/-
# Metatheory.PolisViabilityKernel — a SECOND deployed viability arena, and a HETEROGENEOUS floor.

`PolisFloorComposed.dreggPoliticianFloor` folds two pullbacks of the SAME deployed bar
(`recoveryFloorBar tinyHash k`) over two different SUBJECTS of one arena. That left a residual: the
composed floor's two constituents are not two *different* deployed bars — they are one bar, twice.
This file closes that residual two ways:

1. **A second, genuinely different deployed viability arena** — the **conservation / solvency**
   bounded game over the live `Dregg2.Exec.Kernel`. Its `Config` is the deployed `KernelState`
   (finite `accounts`, total balance `bal : CellId → ℤ`, the cap table), its moves are unit resource
   transfers, and its `advReact` is the deployed fail-closed `exec` (`(exec K t).toList`). The floor
   is **solvency** — every live account is non-negative — which is decidable and public (it reads only
   the published balances, never any interior). `viableWithinB` over this arena is therefore the REAL
   bounded solvency-recovery game on the deployed kernel: can the cell, in `k` admissible transfers
   against adversarial scheduling, regain a fully-solvent state? `kernelViabilityBar` is its bar.

2. **A heterogeneous compose** — `heteroPoliticianFloor` pulls back `kernelViabilityBar` (over
   `KernelState`) AND `PolisRecoveryFloor.recoveryFloorBar` (over `RecoveryView Nat`) to ONE common
   public trace (`DualView`, carrying both a kernel posture and a recovery posture) and `or`-folds
   them. The two constituents are now TWO DIFFERENT deployed arenas — solvency over the live `exec`
   verb, and KERI recovery over the live `rotateStep` verb — not two subjects of one arena. This is
   the heterogeneous `CaptureBar.or` the residual asked for.

## Honest framing

This stays **BOUNDED, PUBLIC, DECIDABLE**. `floorSolvent` reads only `K.accounts` + `K.bal` (no caps
interior, no controller intent); viability is a finite `k`-bounded game over the deployed `exec`.
The candidate move-set is the explicit unit-transfer roster over a published cell list (you can only
"move" by a transfer `exec` actually admits — a refused transfer is no move, so it cannot be a
spurious vacuous win). It does NOT model market dynamics, off-ledger value, or strategic collusion —
those are not public-decidable and are out of scope by construction. What it captures faithfully:
under the deployed `exec` semantics, whether a fully-solvent state is reachable within `≤ k`
admissible transfers. The conservation law itself is the deployed `exec_conserves`; here we witness
the bounded *solvency-recovery GAME*, not re-prove conservation.

l4v bar: no `sorry`, no load-bearing `:= True`; every floor is `Bool`/decidable and non-vacuous both
polarities (a solvent reachable state passes; an insolvent dead-end is foreclosed). `#guard`s and
`decide` proofs execute both, over the real deployed `exec` and the heterogeneous `or`-fold.
-/
import Metatheory.PolisViability
import Metatheory.PolisRecoveryFloor
import Metatheory.Polis
import Dregg2.Exec.Kernel

namespace Metatheory.PolisViabilityKernel

open Metatheory.Polis
open Metatheory.PolisViability
open Metatheory.PolisRecoveryFloor
open Dregg2.Exec
open Dregg2.Apps.PreRotation

/-! ## §1. The conservation / solvency viability arena over the DEPLOYED kernel. -/

/-- **`floorSolvent` — the public, decidable solvency floor.** Every live account is non-negative:
the cell holds no debt anywhere. Reads only the published `accounts` + `bal` (no caps interior, no
intent); `Finset.decidableBAll` makes it decidable, `decide` makes it `Bool`. This is the conserved
quantity's *health* face — `exec` conserves `total`, and this asks the public question "is the
distribution itself solvent right now". -/
def floorSolvent (K : KernelState) : Bool := decide (∀ c ∈ K.accounts, 0 ≤ K.bal c)

/-- The explicit public candidate move-set over a published cell roster: every unit transfer
`s ⇒ d` (`amt := 1`) between roster cells, each performed under the source's own authority
(`actor := s`, so `authorizedB` holds by ownership — the move-set is the public solvency surface,
not anyone's cap interior). -/
def unitTransfers (cells : List CellId) : List Turn :=
  cells.flatMap (fun s => cells.map (fun d => ({ actor := s, src := s, dst := d, amt := 1 } : Turn)))

/-- **`kernelArena` — the deployed conservation/solvency game as a `PolisViability.Arena`.**

* `floorOk`      = `floorSolvent`: every live account is non-negative.
* `enabledMoves` = the unit transfers over `cells` that the deployed `exec` actually ADMITS from this
  state (gated on `(exec K t).isSome` — a refused transfer is no move, so no vacuous win).
* `advReact`     = the deployed fail-closed `exec` outcome, `(exec K t).toList`: an admitted transfer
  advances to the one real post-state; a refused transfer (never offered) is the empty response.

`PolisViability.viableWithinB` over this arena IS the real bounded solvency-recovery game on the live
kernel: can a fully-solvent state be reached within `k` admissible transfers, against an adversary
scheduling among the kernel's own legal responses? `Foreclosed` = no bounded admissible transfer
sequence regains solvency — insolvency lock-in over the deployed `exec` verb. -/
def kernelArena (cells : List CellId) : Arena KernelState Turn where
  floorOk K := floorSolvent K
  enabledMoves K := (unitTransfers cells).filter (fun t => (exec K t).isSome)
  advReact K t := (exec K t).toList

/-- **`KernelViable` — the REAL bounded solvency game.** A solvent state is guaranteed reachable
within `k` admissible transfers against adversarial scheduling: `PolisViability.viableWithinB` over
the deployed `exec` verb. -/
def KernelViable (cells : List CellId) (k : Nat) (K : KernelState) : Prop :=
  Viable (kernelArena cells) k K

/-- **`KernelForeclosed` — deployed insolvency lock-in as a GAME.** No bounded admissible transfer
sequence regains a fully-solvent state. -/
def KernelForeclosed (cells : List CellId) (k : Nat) (K : KernelState) : Prop :=
  Foreclosed (kernelArena cells) k K

instance (cells : List CellId) (k : Nat) (K : KernelState) : Decidable (KernelViable cells k K) :=
  inferInstanceAs (Decidable (Viable (kernelArena cells) k K))
instance (cells : List CellId) (k : Nat) (K : KernelState) : Decidable (KernelForeclosed cells k K) :=
  inferInstanceAs (Decidable (Foreclosed (kernelArena cells) k K))

/-- **`kernelViabilityBar` — the SECOND deployed viability `CaptureBar`** (different from
`recoveryFloorBar`). The politician's insolvency lock-in — driving the cell into a state with NO
bounded admissible path to solvency — is barred EXACTLY when the bounded solvency game is
`Foreclosed`, decidable from the public balances alone, with NO interior inspection. -/
def kernelViabilityBar (cells : List CellId) (k : Nat) :=
  viabilityBar (kernelArena cells) k

/-! ### The base-case tie: the floor IS the deployed conservation health, not a fresh predicate.

The solvency floor reads the SAME `bal` the deployed `exec_conserves` reasons about; a transfer
admitted by `enabledMoves` is admitted by the deployed `exec`, and `exec_conserves` then guarantees
`total` is preserved across that admitted move. So the game's moves never mint or burn supply — the
arena's responses are conservation-faithful by construction. -/

/-- **`kernelArena_move_conserves`.** Every adversary response in the solvency arena preserves the
deployed `total` supply — the responses are exactly admitted `exec` steps, and `exec` conserves. The
bounded game cannot cheat conservation. -/
theorem kernelArena_move_conserves (cells : List CellId) (K K' : KernelState) (t : Turn)
    (h : K' ∈ (kernelArena cells).advReact K t) : total K' = total K := by
  simp only [kernelArena] at h
  -- `(exec K t).toList` contains `K'` iff `exec K t = some K'`.
  cases hx : exec K t with
  | none => rw [hx] at h; simp [Option.toList] at h
  | some s =>
      rw [hx] at h
      simp only [Option.toList, List.mem_singleton] at h
      subst h
      exact exec_conserves K K' t (by rw [hx])

/-! ## §2. The heterogeneous compose — TWO DIFFERENT deployed arenas over ONE common trace.

`DualView` is the common PUBLIC trace: a single posture carrying BOTH a kernel solvency posture
(`KernelState` — published accounts + balances + cap table) AND a KERI recovery posture
(`RecoveryView Nat` — published key state + roster + recovery target). The projections are
interior-free. `CaptureBar.pullback` carries each DIFFERENT deployed bar to `DualView`;
`CaptureBar.or` folds them. The two constituents are now genuinely different deployed arenas. -/

/-- The common PUBLIC trace: one joint posture carrying both deployed subjects' public views. NO
interior — a `KernelState` is the published ledger, a `RecoveryView Nat` is the published recovery
constitution. -/
structure DualView where
  /-- The published kernel/solvency posture (the deployed `KernelState`). -/
  kernel : KernelState
  /-- The published KERI recovery posture (the deployed `RecoveryView Nat`). -/
  recov  : RecoveryView Nat

/-- Public projection onto the kernel solvency posture. Interior-free. -/
def projKernel (τ : DualView) : KernelState := τ.kernel
/-- Public projection onto the KERI recovery posture. Interior-free. -/
def projRecov (τ : DualView) : RecoveryView Nat := τ.recov

/-- **`heteroPoliticianFloor` — the HETEROGENEOUS composed floor over TWO DIFFERENT deployed bars.**
Neither deployed game is foreclosed along the joint posture: the `or`-fold of (the deployed solvency
bar `kernelViabilityBar`, over the live `exec` verb) pulled back to `DualView`, with (the deployed
recovery bar `recoveryFloorBar`, over the live `rotateStep` verb) pulled back to `DualView`. ONE
`CaptureBar` over ONE common trace whose two constituents are two genuinely-different deployed
arenas — this closes the "both composed bars are the same deployed bar" residual. -/
def heteroPoliticianFloor (cells : List CellId) (k : Nat) :
    CaptureBar DualView
      (fun τ => Foreclosed (kernelArena cells) k (projKernel τ)
              ∨ Foreclosed (recoveryArena tinyHash) k (projRecov τ)) :=
  ((kernelViabilityBar cells k).pullback projKernel).or
    ((recoveryFloorBar tinyHash k).pullback projRecov)

/-- **The heterogeneous composition law transports.** The composed floor bars EXACTLY its union
floor-violation: EITHER the deployed solvency game OR the deployed recovery game is foreclosed along
the joint posture. No astrology, no forgotten subject — `captureBar_exactly_floor_violation` applies
verbatim to the pullback/or-folded heterogeneous composition. -/
theorem heteroPoliticianFloor_exact (cells : List CellId) (k : Nat) (τ : DualView) :
    (heteroPoliticianFloor cells k).badShape τ ↔
      (Foreclosed (kernelArena cells) k (projKernel τ)
        ∨ Foreclosed (recoveryArena tinyHash) k (projRecov τ)) :=
  captureBar_exactly_floor_violation (heteroPoliticianFloor cells k) τ

/-! ## §3. Non-vacuity of the kernel arena, both polarities, EXECUTED over the deployed `exec`.

`solventState`: cell 0 holds 100, cell 1 holds 5 — fully solvent. `insolventDeadEnd`: cell 0 is at
`-3` (debt) and cell 1 holds 0 — no unit transfer can rescue cell 0 (the only inflow would be from
cell 1, which is empty), so insolvency is foreclosed at any budget. The `#guard`s run the real
bounded game over the deployed `exec` verb. -/

/-- A SOLVENT kernel state: every account non-negative (cell 0: 100, cell 1: 5). -/
def solventState : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then 100 else if c = 1 then 5 else 0
    caps := fun _ => [] }

/-- An INSOLVENT DEAD-END: cell 0 holds `-3` (debt), cell 1 holds `0` — no admissible unit transfer
can lift cell 0 to non-negative (the only source that could pay it, cell 1, is empty), so solvency is
foreclosed at any budget over the deployed `exec`. -/
def insolventDeadEnd : KernelState :=
  { accounts := {0, 1}
    bal := fun c => if c = 0 then (-3) else 0
    caps := fun _ => [] }

-- The floor itself: solvent state passes, insolvent dead-end fails (non-vacuous, both polarities):
#guard floorSolvent solventState == true
#guard floorSolvent insolventDeadEnd == false

-- The deployed verb admits real moves from the solvent state (the move-set is non-empty, non-vacuous):
#guard ((kernelArena [0, 1]).enabledMoves solventState).length == 2

-- The REAL bounded solvency game over the deployed `exec`:
-- the solvent state is viable at budget 0 (the floor already holds):
#guard viableWithinB (kernelArena [0, 1]) 0 solventState == true
-- the insolvent dead-end is foreclosed even at a generous budget — no admissible transfer rescues it:
#guard viableWithinB (kernelArena [0, 1]) 5 insolventDeadEnd == false

-- The bar fires EXACTLY on the insolvent dead-end, NOT on the solvent state:
example : (kernelViabilityBar [0, 1] 5).badShape insolventDeadEnd := by
  show KernelForeclosed [0, 1] 5 insolventDeadEnd; decide
example : ¬ (kernelViabilityBar [0, 1] 3).badShape solventState := by
  show ¬ KernelForeclosed [0, 1] 3 solventState; decide

-- And the Prop-level wrappers decide:
example : KernelViable [0, 1] 3 solventState := by decide
example : KernelForeclosed [0, 1] 5 insolventDeadEnd := by decide

/-! ## §4. Non-vacuity of the HETEROGENEOUS floor — each DIFFERENT deployed bar catches on its own.

The three witnesses prove the heterogeneous `or` genuinely composes two different deployed games:
the solvency bar catches kernel insolvency while recovery is fine; the recovery bar catches recovery
lock-in while the kernel is solvent; and a doubly-healthy posture clears both. -/

/-- A doubly-HEALTHY joint posture: solvent kernel AND recoverable KERI view — clears both. -/
def healthyDual : DualView := { kernel := solventState, recov := recoverableView }

/-- An INSOLVENT joint posture: the kernel is in insolvency lock-in, recovery is fine — caught on the
SOLVENCY disjunct (the deployed `exec` arena), proving that constituent is load-bearing. -/
def insolventDual : DualView := { kernel := insolventDeadEnd, recov := recoverableView }

/-- A RECOVERY-LOCKED joint posture: the kernel is solvent but the KERI view is recovery-foreclosed —
caught on the RECOVERY disjunct (the deployed `rotateStep` arena), proving the OTHER, different
constituent is load-bearing too. -/
def recoveryLockedDual : DualView := { kernel := solventState, recov := lockedOutView }

-- Doubly-healthy: the heterogeneous floor CLEARS it (neither deployed game foreclosed):
example : ¬ (heteroPoliticianFloor [0, 1] 5).badShape healthyDual := by
  rw [heteroPoliticianFloor_exact]
  show ¬ (Foreclosed (kernelArena [0, 1]) 5 (projKernel healthyDual)
        ∨ Foreclosed (recoveryArena tinyHash) 5 (projRecov healthyDual))
  decide

-- Insolvency: CAUGHT on the SOLVENCY (kernel/`exec`) disjunct:
example : (heteroPoliticianFloor [0, 1] 5).badShape insolventDual := by
  rw [heteroPoliticianFloor_exact]
  exact Or.inl (by
    show Foreclosed (kernelArena [0, 1]) 5 (projKernel insolventDual); decide)

-- Recovery lock-in: CAUGHT on the RECOVERY (`rotateStep`) disjunct — the OTHER, different bar:
example : (heteroPoliticianFloor [0, 1] 5).badShape recoveryLockedDual := by
  rw [heteroPoliticianFloor_exact]
  exact Or.inr (by
    show Foreclosed (recoveryArena tinyHash) 5 (projRecov recoveryLockedDual); decide)

-- The two catches are genuinely DIFFERENT subjects: insolvency does NOT trip the recovery bar, and
-- recovery lock-in does NOT trip the solvency bar (the heterogeneity is real, not coincidental):
example : ¬ Foreclosed (recoveryArena tinyHash) 5 (projRecov insolventDual) := by
  show ¬ Foreclosed (recoveryArena tinyHash) 5 (projRecov insolventDual); decide
example : ¬ Foreclosed (kernelArena [0, 1]) 5 (projKernel recoveryLockedDual) := by
  show ¬ Foreclosed (kernelArena [0, 1]) 5 (projKernel recoveryLockedDual); decide

/-! ## Axiom hygiene: the load-bearing theorems are kernel-clean. -/

#assert_axioms heteroPoliticianFloor_exact
#assert_axioms kernelArena_move_conserves

end Metatheory.PolisViabilityKernel
