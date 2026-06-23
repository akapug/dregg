/-
# Metatheory.PolisGrandGovernor — the GRAND capstone: many textures, ONE governor, ONE guarantee.

The unified sandbox (`PolisSandboxUnified`) carries three simultaneous forms of political leverage
on one public world — foreclosure (the distance axis), laundering (the tier axis), hoarding (the
resource axis) — bounded by one combined floor and one governed step. The governor theory
(`PolisGovernorTheory`) proves the SHAPE once: a governed step keeps its floor at every tick for
every controller, and `combineFloor` composition is MONOTONE — a refusal on any one axis is a
refusal of the combined governor (adding an axis only grows refusals, never weakens).

This file is the capstone that welds the two. We name three concrete adversaries — the **forecloser**,
the **launderer**, the **hoarder** — each a `World → Move` policy whose capture move attacks exactly
its axis. We then prove ONE clean theorem family: under the SINGLE combined governor, EACH named
adversary's capture move is REFUSED (it breaks the relevant axis → breaks the combined floor → the
governor shields), and any MIX of them is refused move-for-move. The grand theorem
`grand_no_adversary_captures` is `sandbox_governed_safe` read at full strength: the combined floor
holds at every tick for EVERY controller — so NONE of forecloser / launderer / hoarder / any-mix /
any-controller-whatsoever ever achieves capture.

The structure is deliberate: each named-adversary refusal is grounded in the COMPOSITION theory.
The forecloser breaks the foreclosure axis, so by `combine_monotone` (foreclosure is a component of
the combined floor) the combined governor refuses it; likewise the launderer and the hoarder. One
governor, one guarantee, three textures, grounded in the algebra of `combineFloor`.

Honest scope: the unified world is small and finite (two `Bool` agents, `decide`-cheap), and each
named adversary is a scripted / bounded Lean policy, not an LLM. What is genuinely universal is the
governor: `grand_no_adversary_captures` quantifies over ALL controllers, so the three named
adversaries are merely the recognizable witnesses that the universal guarantee is non-vacuous.
Every concrete claim is `decide`-checked on the live world.
-/
import Metatheory.PolisSandboxUnified
import Metatheory.PolisGovernorTheory

namespace Metatheory.PolisGrandGovernor

open Metatheory.PolisSandboxUnified
open Metatheory.PolisGovernorTheory

/-! ## §1. The combined floor IS an iterated `combineFloor`, and `govStep` IS `genGovStep`.

The unified sandbox hand-wrote `worldFloor = foreclosureFloor ∧ launderingFloor ∧ hoardingFloor` and
`govStep w m = if worldFloor (stepMove w m) then stepMove w m else w`. We re-read both through the
general theory so the capstone's refusals descend from `combine_monotone`, not from a fresh hand
proof. -/

/-- The unified `worldFloor` is exactly the iterated `combineFloor` of its three axes. This is the
hook that lets `combine_monotone_left/right` apply: a refusal on `foreclosureFloor` (or
`launderingFloor`, or `hoardingFloor`) is a refusal of the combined floor. -/
theorem worldFloor_is_combine (w : World) :
    worldFloor w
      = combineFloor foreclosureFloor (combineFloor launderingFloor hoardingFloor) w := rfl

/-- The unified `govStep` is exactly `genGovStep worldFloor stepMove` — the one governed step the
whole theory is about. So every general lemma (`genGov_safe`, `combine_monotone_*`, …) applies to it
directly. -/
theorem govStep_is_genGovStep (w : World) (m : Move) :
    govStep w m = genGovStep worldFloor stepMove w m := rfl

/-- The combined governor is `genGovStep` over the iterated `combineFloor`; combined with
`worldFloor_is_combine` this is the form `combine_monotone_*` consumes. -/
theorem govStep_is_combined (w : World) (m : Move) :
    govStep w m
      = genGovStep (combineFloor foreclosureFloor (combineFloor launderingFloor hoardingFloor))
          stepMove w m := rfl

/-! ## §2. The three NAMED adversaries, each a concrete `World → Move` policy.

Each adversary is the politician (agent `false`) reaching for a different lever. A policy is a total
`World → Move`: at every world it proposes its signature capture move. The governor is universal over
exactly such policies, so naming three is naming three recognizable points in the space the universal
theorem already covers. -/

/-- **The forecloser** — attacks the DISTANCE axis. At every world it proposes to trap agent `true`
past its recovery budget (foreclosure: the victim can no longer exit). -/
def forecloser : World → Move := fun _ => ⟨false, .trap true⟩

/-- **The launderer** — attacks the TIER axis. At every world it proposes to inflate its own claimed
authority above what it earned (laundering: authority without production). -/
def launderer : World → Move := fun _ => ⟨false, .launder⟩

/-- **The hoarder** — attacks the RESOURCE axis. At every world it proposes to drain the shared
commons below the reserve everyone relies on (hoarding). -/
def hoarder : World → Move := fun _ => ⟨false, .hoard⟩

/-! ## §3. Each named adversary's capture move is REFUSED — grounded in `combine_monotone`.

For each adversary we show: from genesis `w0`, the capture move is FRESH (it would change the world)
but is REFUSED (the governor shields, leaving the world intact). The refusal descends from the
composition theory: the move breaks its own axis, so by `combine_monotone_*` it breaks the combined
floor, so the combined governor shields. We make that descent explicit per adversary. -/

/-- `view` is a faithful read-out of the full `Bool`-agent world (six per-agent fields + the pool),
so distinct `view`s witness distinct worlds. This lets us discharge the freshness side-condition of
`combine_monotone` by `decide` on the decidable `view` tuple — `World` itself carries functions
(`AgentId → Nat`) and is not `DecidableEq`. -/
theorem world_ne_of_view_ne {w w' : World} (h : view w ≠ view w') : w ≠ w' :=
  fun he => h (he ▸ rfl)

/-- A capture move is fresh at genesis: each adversary's signature move genuinely changes the world
(so the shield below is a real refusal, not a coincidental no-op). Proven through `view`. -/
theorem forecloser_move_fresh : stepMove w0 (forecloser w0) ≠ w0 :=
  world_ne_of_view_ne (by decide)
theorem launderer_move_fresh : stepMove w0 (launderer w0) ≠ w0 :=
  world_ne_of_view_ne (by decide)
theorem hoarder_move_fresh : stepMove w0 (hoarder w0) ≠ w0 :=
  world_ne_of_view_ne (by decide)

/-- The forecloser's capture move breaks the FORECLOSURE axis (agent `true` is pushed to `trapDist`,
above `budget`). The recognizable per-axis break that drives the monotone refusal. -/
theorem forecloser_breaks_foreclosure : ¬ foreclosureFloor (stepMove w0 (forecloser w0)) := by decide
/-- The launderer's capture move breaks the LAUNDERING axis (claimed tier exceeds earned). -/
theorem launderer_breaks_laundering : ¬ launderingFloor (stepMove w0 (launderer w0)) := by decide
/-- The hoarder's capture move breaks the HOARDING axis (the pool falls below `reserve`). -/
theorem hoarder_breaks_hoarding : ¬ hoardingFloor (stepMove w0 (hoarder w0)) := by decide

/-- **The forecloser is refused** — via `combine_monotone`. The single-axis foreclosure governor
would refuse the trap (it breaks `foreclosureFloor`); since `foreclosureFloor` is the LEFT component
of the combined floor, `combine_monotone_left` lifts that refusal to the combined governor: `govStep`
shields, the world is intact. -/
theorem forecloser_refused : govStep w0 (forecloser w0) = w0 := by
  rw [govStep_is_combined]
  -- The foreclosure-only governor refuses the trap (it breaks `foreclosureFloor`).
  have hf : genGovStep foreclosureFloor stepMove w0 (forecloser w0) = w0 := by
    unfold genGovStep; rw [if_neg forecloser_breaks_foreclosure]
  -- Lift to the combined governor: foreclosure is the LEFT axis.
  exact combine_monotone_left foreclosureFloor (combineFloor launderingFloor hoardingFloor)
    stepMove w0 (forecloser w0) hf forecloser_move_fresh

/-- **The launderer is refused** — via `combine_monotone` on the laundering axis. Laundering sits in
the RIGHT half of the combined floor (`combineFloor laundering hoarding`), so we first lift the
laundering refusal to that inner combined floor (`combine_monotone_left` there), then lift to the
whole floor (`combine_monotone_right`). The nesting mirrors `worldFloor_is_combine`. -/
theorem launderer_refused : govStep w0 (launderer w0) = w0 := by
  rw [govStep_is_combined]
  have hl : genGovStep launderingFloor stepMove w0 (launderer w0) = w0 := by
    unfold genGovStep; rw [if_neg launderer_breaks_laundering]
  -- Lift to the inner combined floor (laundering ∧ hoarding), laundering = its LEFT axis.
  have hlh : genGovStep (combineFloor launderingFloor hoardingFloor) stepMove w0 (launderer w0) = w0 :=
    combine_monotone_left launderingFloor hoardingFloor stepMove w0 (launderer w0) hl launderer_move_fresh
  -- Lift to the whole floor: (laundering ∧ hoarding) is the RIGHT axis.
  exact combine_monotone_right foreclosureFloor (combineFloor launderingFloor hoardingFloor)
    stepMove w0 (launderer w0) hlh launderer_move_fresh

/-- **The hoarder is refused** — via `combine_monotone` on the hoarding axis. Hoarding is the RIGHT
axis of the inner combined floor, which is itself the RIGHT axis of the whole floor — two
`combine_monotone_right` lifts. -/
theorem hoarder_refused : govStep w0 (hoarder w0) = w0 := by
  rw [govStep_is_combined]
  have hh : genGovStep hoardingFloor stepMove w0 (hoarder w0) = w0 := by
    unfold genGovStep; rw [if_neg hoarder_breaks_hoarding]
  have hlh : genGovStep (combineFloor launderingFloor hoardingFloor) stepMove w0 (hoarder w0) = w0 :=
    combine_monotone_right launderingFloor hoardingFloor stepMove w0 (hoarder w0) hh hoarder_move_fresh
  exact combine_monotone_right foreclosureFloor (combineFloor launderingFloor hoardingFloor)
    stepMove w0 (hoarder w0) hlh hoarder_move_fresh

/-! ## §4. Honest play, per axis, is ADMITTED — the governor refuses abuse, not exercise.

Each named abuse has a lawful counterpart (the unified sandbox's honest moves). The governor lets the
counterpart through unchanged, so the refusals above are about the ABUSE, not the axis itself. -/

/-- The honest counterpart of foreclosure: step toward your OWN home (advances the distance axis
legitimately). Admitted unchanged from genesis. -/
theorem honest_stepHome_admitted :
    govStep w0 ⟨false, .stepHome⟩ = stepMove w0 ⟨false, .stepHome⟩ :=
  govStep_admits_benign w0 ⟨false, .stepHome⟩ (by decide)

/-- The honest counterpart of laundering: claim EXACTLY what you earned. From `wEarned` (agent `false`
has earned a tier) the lawful claim is admitted unchanged. -/
theorem honest_claim_admitted :
    govStep wEarned ⟨false, .claim⟩ = stepMove wEarned ⟨false, .claim⟩ :=
  govStep_admits_benign wEarned ⟨false, .claim⟩ (by decide)

/-- The honest counterpart of hoarding: CONTRIBUTE to the commons (grows it). Admitted unchanged. -/
theorem honest_contribute_admitted :
    govStep w0 ⟨false, .contribute⟩ = stepMove w0 ⟨false, .contribute⟩ :=
  govStep_admits_benign w0 ⟨false, .contribute⟩ (by decide)

/-! ## §5. THE GRAND THEOREM — no adversary, named or unnamed, ever captures.

`sandbox_governed_safe` (itself `genGov_safe` over the combined floor) says the combined floor holds
at every tick for EVERY controller. Read at full strength that is the capstone: capture on ANY axis
is exactly a tick where the combined floor fails, and that NEVER happens — for the forecloser, the
launderer, the hoarder, any mixture, or any controller whatsoever. -/

/-- **`grand_no_adversary_captures`** — the capstone. Starting from any floor-satisfying genesis,
under the SINGLE combined governor, the combined floor (foreclosure ∧ laundering ∧ hoarding) holds at
EVERY tick for EVERY controller. Therefore no controller — forecloser, launderer, hoarder, any mix,
or any adversary not yet named — ever forecloses a victim, launders a tier, or hoards the commons:
none achieves capture, ever. -/
theorem grand_no_adversary_captures (ctrl : World → Move) (w0' : World) (h0 : worldFloor w0') :
    ∀ n, worldFloor (govTraj ctrl w0' n) :=
  sandbox_governed_safe ctrl w0' h0

/-- Capture, named precisely: a controller "captures on axis A by tick `n`" iff axis A's floor fails
at tick `n`. The grand theorem says this is impossible on every axis. We unpack the three projections
so "no capture" is legible per dimension. -/
theorem grand_no_capture_per_axis (ctrl : World → Move) (w0' : World) (h0 : worldFloor w0') (n : Nat) :
    foreclosureFloor (govTraj ctrl w0' n)
      ∧ launderingFloor (govTraj ctrl w0' n)
      ∧ hoardingFloor (govTraj ctrl w0' n) :=
  grand_no_adversary_captures ctrl w0' h0 n

/-- The three named adversaries are concrete instances of the universal guarantee: run from genesis,
each leaves the combined floor intact at every tick (no capture, ever). This connects the named
refusals of §3 to the universal theorem — the named adversaries are exactly witnesses that the
∀-controller guarantee is inhabited and non-vacuous. -/
theorem named_adversaries_never_capture (n : Nat) :
    worldFloor (govTraj forecloser w0 n)
      ∧ worldFloor (govTraj launderer w0 n)
      ∧ worldFloor (govTraj hoarder w0 n) :=
  ⟨grand_no_adversary_captures forecloser w0 genesis_floor_holds n,
   grand_no_adversary_captures launderer w0 genesis_floor_holds n,
   grand_no_adversary_captures hoarder w0 genesis_floor_holds n⟩

/-- And a MIXED controller — one that picks its lever by reading the world (here: foreclose while the
victim is still recoverable, else launder, else hoard) — is equally bound: the combined floor holds
at every tick. Mixing textures does not escape the single governor. -/
def mixedAdversary : World → Move := fun w =>
  if w.dist true ≤ budget then ⟨false, .trap true⟩
  else if w.claimed false ≤ w.earned false then ⟨false, .launder⟩
  else ⟨false, .hoard⟩

theorem mixed_adversary_never_captures (n : Nat) :
    worldFloor (govTraj mixedAdversary w0 n) :=
  grand_no_adversary_captures mixedAdversary w0 genesis_floor_holds n

/-! ## §6. The observatory: read each named adversary's verdict off public state.

`decide` on the live world — refused-when-harmful, admitted-when-honest — so the theorems above are
backed by a computable per-tick verdict, not just a proof object. -/

-- REFUSED: each named adversary's capture move is shielded — the world is unchanged from genesis.
#eval view (govStep w0 (forecloser w0))   -- ((0,0),(0,0),(0,0),10)  (trap refused)
#eval view (govStep w0 (launderer w0))     -- ((0,0),(0,0),(0,0),10)  (launder refused)
#eval view (govStep w0 (hoarder w0))       -- ((0,0),(0,0),(0,0),10)  (hoard refused)

-- Each refusal is a GENUINE refusal: the raw (ungoverned) move would break the floor.
#eval decide (worldFloor (stepMove w0 (forecloser w0)))   -- false  (foreclosed)
#eval decide (worldFloor (stepMove w0 (launderer w0)))     -- false  (laundered)
#eval decide (worldFloor (stepMove w0 (hoarder w0)))       -- false  (hoarded)

-- ADMITTED-WHEN-HONEST: the lawful counterpart of each abuse passes unchanged.
#eval view (govStep w0 ⟨false, .stepHome⟩)      -- ((0,0),(0,0),(0,0),10)  (already home; honest, admitted)
#eval view (govStep wEarned ⟨false, .claim⟩)     -- claim of an EARNED tier, admitted
#eval view (govStep w0 ⟨false, .contribute⟩)     -- ((0,0),(0,0),(0,0),11)  (commons grew; admitted)

-- The mixed adversary, run a few ticks under governance, never leaves the floor.
#eval decide (worldFloor (govTraj mixedAdversary w0 8))   -- true

/-- A compact `decide` bundle: each named adversary's capture move is refused (world intact) AND its
raw move is genuinely harmful (floor broken) — the both-polarity certificate that the governor does
real work against every named texture. -/
theorem named_adversaries_refused_and_genuine :
    (govStep w0 (forecloser w0) = w0 ∧ ¬ worldFloor (stepMove w0 (forecloser w0)))
      ∧ (govStep w0 (launderer w0) = w0 ∧ ¬ worldFloor (stepMove w0 (launderer w0)))
      ∧ (govStep w0 (hoarder w0) = w0 ∧ ¬ worldFloor (stepMove w0 (hoarder w0))) := by
  refine ⟨⟨forecloser_refused, ?_⟩, ⟨launderer_refused, ?_⟩, ⟨hoarder_refused, ?_⟩⟩ <;> decide

/-! ## Axiom hygiene — the capstone and its composition-grounded refusals are kernel-clean. -/

#print axioms grand_no_adversary_captures
#print axioms forecloser_refused
#print axioms launderer_refused
#print axioms hoarder_refused
#print axioms named_adversaries_never_capture
#print axioms mixed_adversary_never_captures

/-!
The grand-unified governance capstone, in one breath:

  1. ONE world, THREE textures of leverage (foreclosure / laundering / hoarding) — reused from
     `PolisSandboxUnified`; its combined floor IS an iterated `combineFloor`, its `govStep` IS
     `genGovStep`.
  2. THREE NAMED adversaries (forecloser / launderer / hoarder), each a concrete `World → Move`
     policy attacking exactly its axis.
  3. EACH is REFUSED — grounded in `PolisGovernorTheory.combine_monotone`: a refusal on any one axis
     is a refusal of the combined governor (adding an axis only grows refusals).
  4. HONEST play, per axis, is ADMITTED — the governor refuses abuse, never legitimate exercise.
  5. THE GRAND THEOREM `grand_no_adversary_captures` — the combined floor holds at every tick for
     EVERY controller: forecloser, launderer, hoarder, any mix, or any adversary not yet named —
     none captures, ever. Many textures, one governor, one guarantee.
-/

end Metatheory.PolisGrandGovernor
