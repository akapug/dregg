/-
# Dregg2.Exec.HandlerOpenFronts — explicit handler-executor open-front registry (Wave 7+).

POLICY: **no lurking holes**. Every unfinished `handler_refines_execFullA_*` / queue-defer front is
named here with an explicit open-hole theorem (or a tracked `HoleStatus`). Silent strengthening gaps
are forbidden — use these portals instead.

Run `#eval countOpenFronts` after each wave to watch the frontier shrink.
-/
import Dregg2.Exec.HandlerExecutor
import Dregg2.Circuit.Inst.ExerciseInnerTurn

namespace Dregg2.Exec.HandlerOpenFronts

open Dregg2.Exec.HandlerExecutor
open Dregg2.Circuit.Inst.ExerciseInnerTurn
open Dregg2.Exec.TurnExecutorFull

/-! ## §0 — front metadata. -/

inductive HoleWave
  | w7_flag_alignment
  | w7_exercise_r4
  | w7_spawn_metadata
  deriving Repr, DecidableEq

structure OpenFront where
  id       : String
  wave     : HoleWave
  action?  : Option String
  note     : String
  deriving Repr

/-! ## §1 — inventory (every named handler gap; shrink this list). -/

-- CLOSED (this wave): `handler_makeSovereign` (handler ALIGNED to the `makeSovereignKernel`
-- commitment-rebind), `handler_receiptArchive` (ALIGNED to the `"lifecycle"` field write), and the
-- queue-allocate `actor ≠ cell` front (handler now stores owner = `actor`, so kernel agreement is
-- UNCONDITIONAL). Their `hole_*` theorems in `HandlerExecutor` are now genuine proofs,
-- and the `portal_*` re-exports below delegate to them. Removed from the open inventory.
-- CLOSED (this wave): `exercise_inner_turn_witness` — the inner `List FullActionA` emitted fold from
-- the hold post-state now refines `turnSpec` via `ExerciseInnerTurn.exercise_inner_emitted_refines_turnSpec`
-- (the `portal_exercise_inner_turn` re-export below delegates to it). Removed from the
-- open inventory.
-- CLOSED (F2b): the queue-ENQUEUE `actor ≠ cell` front died with the queue verb family — there is
-- no queue verb left to align (the factory story, `Apps/QueueFactory.lean`). Only the spawn
-- front remains.
-- CLOSED (P2 canonical-semantics): `exercise_r4_facet_mask` — `execFullA`'s `exerciseA` now ENFORCES
-- the R4 facet mask (`innerFacetsAdmittedA`) and the handler bridge tags each inner with its REAL
-- `requiredFacetA fa` (not blanket `Auth.control`), so the two facet gates are the SAME check. The
-- facet front is discharged (`ExerciseInnerTurn.exercise_r4_facet_mask`); only the
-- ORTHOGONAL inner-turn fold remains, carried as an explicit `hinner` hypothesis there.
def openFronts : List OpenFront := [
  -- Wave 7: spawn/factory metadata beyond the born-empty createCell core.
  -- RESIDUAL (precise): the handler dispatch (`HandlerExecutor.toClosedEffect`) maps BOTH `spawnA` and
  -- `createCellFromFactoryA` onto the born-empty `createCellH` effect — `spawnA` DROPS its `target`
  -- (`.spawnA actor child _target => spawnEffect actor child`) and `createCellFromFactoryA` DROPS its
  -- `vk`. So `handler_refines_execFullA_{spawn,createCellFromFactory}` prove kernel-agreement only
  -- against `execFullA (.createCellA …)` (the shared account-growth core), NOT against the full
  -- chained effect. UNVERIFIED by the handler refinement:
  --   • spawn delegation handoff — `spawnChainA`'s parent-cap gate (`confersEdgeTo target` ∧
  --     `target ∈ accounts`) and the writes it commits: `caps child := [heldCapTo … actor target]`
  --     plus the `delegate`/`delegations` snapshots (the least-amplifying authority copy);
  --   • factory install — `createCellFromFactoryChainA`'s factory gates (found ∧ `conforms` ∧ `0 ≤ vk`)
  --     and the writes it commits: the `factoryVkField` slot, `installInitialFields`, and `slotCaveats`.
  -- WHY OPEN (not closeable here): the handler MUST first model these writes for a refinement to exist;
  -- closing requires aligning the handler dispatch in `HandlerExecutor`, an Exec-executor change (owned
  -- elsewhere), not a proof over the present born-empty handler. Honest residual, narrowed to the cap
  -- handoff + factory-field install — the account-growth core IS proven.
  ⟨"spawn_factory_metadata", .w7_spawn_metadata, some "spawnA",
    "handler maps spawnA/createCellFromFactoryA to born-empty createCellH (drops target/vk): spawnChainA's parent-cap handoff (caps/delegate/delegations) and createCellFromFactoryChainA's factory install (factoryVkField/initialFields/slotCaveats) are UNVERIFIED by the handler refinement; only the createCellA account-growth core is proven"⟩
]

def countOpenFronts : Nat := openFronts.length

/-! ## §2 — explicit open-hole portals (re-exported from keystones; FAIL `#assert_axioms` until proved). -/

section HolePortals

variable {s s' : RecChainedState}

/-- CLOSED: `makeSovereignA` handler ⊑ `execFullA` (commitment-rebind ALIGNED; proved). -/
theorem portal_handler_makeSovereign
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.makeSovereignA actor cell) s = some s') :
    ∃ s'', execFullA s (.makeSovereignA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_makeSovereign s s' actor cell hmem h

/-- CLOSED: `receiptArchiveA` handler ⊑ `execFullA` (`"lifecycle"` field ALIGNED; proved). -/
theorem portal_handler_receiptArchive
    (actor cell : CellId) (hmem : cell ∈ s.kernel.accounts)
    (h : execHandlerOne (.receiptArchiveA actor cell) s = some s') :
    ∃ s'', execFullA s (.receiptArchiveA actor cell) = some s'' ∧ s''.kernel = s'.kernel :=
  handler_refines_execFullA_receiptArchive s s' actor cell hmem h

-- F2b: the §6.6 queue-allocate portal died with the queue verb family (factory story:
-- `Apps/QueueFactory.lean`).

/-- HOLE W7: exercise inner emitted fold ⊑ `turnSpec`. -/
theorem portal_exercise_inner_turn
    (lookup : Dregg2.Circuit.TurnEmit.DescriptorLookup)
    (compress : ℤ → ℤ → ℤ) (stepRoot : Dregg2.Circuit.TurnWitness.StepWitness → ℤ)
    (hstep :
      ∀ (sw : Dregg2.Circuit.TurnWitness.StepWitness) (st st' : RecChainedState) (fa : FullActionA),
        Dregg2.Circuit.TurnEmit.stepEmittedSat lookup sw st st' fa →
          Dregg2.Circuit.ActionDispatch.fullActionStep st fa st')
    (holdPost post : RecChainedState) (inner : List FullActionA)
    (w : exerciseInnerTurnWitness lookup compress stepRoot holdPost post inner) :
    Dregg2.Circuit.ActionDispatch.turnSpec holdPost inner post :=
  exercise_inner_emitted_refines_turnSpec lookup compress stepRoot hstep holdPost post inner w

/-- **R4 facet-mask CLOSED** (P2 canonical-semantics): `execFullA`'s `exerciseA` now enforces the same
facet mask the handler bridge tags, so a handler-committed exercise refines `execFullA` on the same
kernel — given the orthogonal inner-turn fold (`hinner`). Delegates to
`ExerciseInnerTurn.exercise_r4_facet_mask`. -/
theorem portal_exercise_r4_facet_mask (actor target : CellId) (inner : List FullActionA)
    (hinner : ∃ s₁, execInnerA (Dregg2.Exec.HandlerExecutor.exerciseHoldState s actor) inner = some s₁ ∧
        s₁.kernel = s'.kernel)
    (h : execHandlerOne (.exerciseA actor target inner) s = some s') :
    ∃ s'', execFullA s (.exerciseA actor target inner) = some s'' ∧ s''.kernel = s'.kernel :=
  Dregg2.Exec.HandlerExecutor.handler_refines_execFullA_exercise s s' actor target inner hinner h

end HolePortals

-- The frontier has exactly ONE GENUINELY-open handler front (drift-free: `countOpenFronts`
-- IS `openFronts.length`, so this catches any future add/remove). Non-vacuity: the registry is
-- non-empty (open work remains) yet bounded. Down from 3 — the R4 facet-mask front is now CLOSED
-- (the facet mask is enforced on `execFullA`, the canonical semantics; `portal_exercise_r4_facet_mask`),
-- and the `exercise_inner_turn_witness` fold front is CLOSED (`portal_exercise_inner_turn`). Only the
-- `spawn_factory_metadata` delegation/factory-install front remains.
#guard countOpenFronts == openFronts.length
#guard countOpenFronts == 1
#guard ¬ openFronts.isEmpty
-- The closed `exercise_inner_turn_witness` AND `exercise_r4_facet_mask` fronts are not listed.
#guard (openFronts.filter (fun f => f.id == "exercise_inner_turn_witness")).isEmpty

end Dregg2.Exec.HandlerOpenFronts