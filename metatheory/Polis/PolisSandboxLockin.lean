/-
# Metatheory.PolisSandboxLockin — LOCK-IN / HOLE-RENT: a polis texture of the OPEN obligation.

A genuinely different politics than the foreclosure trap. Here the leverage is not pushing a victim
past a recovery budget — it is the refusal to CLOSE a shared obligation. A single agent controls a
shared `hole` (an open register / pending obligation / unredeemed gate). While the hole stays open it
ages WITHOUT progress, and a rent meter ticks up: that aging-without-progress IS the extracted
leverage ("hole-rent" — pay me, or the obligation never resolves). The same agent can also `lock`
the gate, setting a committed flag that bars another agent's `pass` forever (lock-in).

The shared floor here is two clauses, both about *not being permanently stuck*:
  * no obligation is open past a budget without progress (`age ≤ budget`), and
  * no agent is locked out of the gate (`locked b = false`).

The experiment, proven end-to-end:
  * UNGOVERNED — the rentier just keeps the hole open (`stall`) and `lock`s the gate. The hole ages
    past budget collecting rent, and the other agent is locked out. The floor BREAKS and the
    lock-in / hole-rent detector fires (`ungoverned_lockin_emerges`, `ungoverned_is_lockin`).
  * GOVERNED — the SAME rentier, under the polis envelope (admit a move iff it preserves the floor,
    else shield), is REFUSED exactly on the harmful moves: stalling past budget is refused (forcing
    progress) and the lock-out is refused (the gate stays passable). The floor holds for the whole
    episode and for EVERY controller (`sandbox_lockin_governed_safe`).

Pure Lean 4 core (imports `Metatheory.PolisSandbox` for the `Move`-style envelope shape).
The detector and the demo are decidable and PROVEN by `decide`, not asserted.
-/
import Metatheory.PolisSandbox

namespace Metatheory.PolisSandboxLockin

/-- Agents (two, for the demo): `false` is the rentier who controls the gate. -/
abbrev AgentId := Bool

/-- The shared world. A single OBLIGATION (`open?`) with how long it has stayed open without
progress (`age`) and the rent extracted while open (`rent`); plus a per-agent lock-out flag for the
gate. No interior, no motive — only public state. -/
structure World where
  /-- Is the shared obligation/hole currently open (unresolved)? -/
  open? : Bool
  /-- Ticks the obligation has stayed open WITHOUT progress — the hole-rent leverage. -/
  age : Nat
  /-- Total rent extracted while the hole stayed open. -/
  rent : Nat
  /-- Per-agent gate lock-out: `locked b = true` ⇒ agent `b` can never pass. -/
  locked : AgentId → Bool

/-- How long an open obligation may age without progress before it counts as lock-in. -/
def budget : Nat := 3

/-- An action on the shared gate/obligation.
  * `progress` — do the work: resolve (close) the open obligation, reset its age, free rent pressure.
  * `stall`    — keep the hole OPEN one more tick: age++ and collect one unit of rent (the leverage).
  * `lock v`   — set the committed lock-out flag against agent `v` (lock-in: bar them forever).
  * `unlock v` — release agent `v`'s lock-out (restore passability).
  * `idle`     — do nothing. -/
inductive Act
  | progress
  | stall
  | lock (victim : AgentId)
  | unlock (victim : AgentId)
  | idle
deriving DecidableEq, Repr

/-- A scheduled move: which agent acts, and how. -/
structure Move where
  actor : AgentId
  action : Act

/-- Apply an action to the world. `progress` closes the hole and resets its age; `stall` ages an
already-open hole and accrues rent (an honest agent opening fresh work would `idle`/`progress`). -/
def act (w : World) : Act → World
  | .progress => { w with open? := false, age := 0 }
  | .stall    => { w with open? := true, age := w.age + 1, rent := w.rent + 1 }
  | .lock v   => { w with locked := fun i => if i = v then true else w.locked i }
  | .unlock v => { w with locked := fun i => if i = v then false else w.locked i }
  | .idle     => w

/-- One world step from a move. -/
def stepMove (w : World) (m : Move) : World := act w m.action

/-- **The shared floor**: no obligation aged past budget (so every open hole progresses in time), and
no agent is locked out of the gate. Decidable. -/
def worldFloor (w : World) : Prop :=
  w.age ≤ budget ∧ w.locked false = false ∧ w.locked true = false

instance (w : World) : Decidable (worldFloor w) :=
  inferInstanceAs (Decidable (w.age ≤ budget ∧ w.locked false = false ∧ w.locked true = false))

/-- **The polis-governed step**: admit the proposed move iff it preserves the shared floor, else
SHIELD (no-op). Computable on the live world. -/
def govStep (w : World) (m : Move) : World :=
  if worldFloor (stepMove w m) then stepMove w m else w

/-- A governed episode: iterate the governed step under a controller (an agent-scheduler/policy). -/
def govTraj (ctrl : World → Move) (w0 : World) : Nat → World
  | 0 => w0
  | n + 1 => govStep (govTraj ctrl w0 n) (ctrl (govTraj ctrl w0 n))

/-- The governed step preserves the floor (admit-or-shield). -/
theorem govStep_preserves (w : World) (m : Move) (h : worldFloor w) : worldFloor (govStep w m) := by
  unfold govStep
  by_cases hp : worldFloor (stepMove w m)
  · rw [if_pos hp]; exact hp
  · rw [if_neg hp]; exact h

/-- **`sandbox_lockin_governed_safe` — governance, proven.** Under the polis-governed step, the
shared floor holds at EVERY tick for EVERY controller: no obligation is held open past budget, and no
agent is ever locked out. The controller is universally quantified, never inspected (cage, not
animal). -/
theorem sandbox_lockin_governed_safe (ctrl : World → Move) (w0 : World) (h0 : worldFloor w0) :
    ∀ n, worldFloor (govTraj ctrl w0 n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact govStep_preserves _ _ ih

/-! ## Gentle governance — admits benign, refuses only harm (∀ world, ∀ move). -/

/-- **Gentle governance, half 1 — admits all honest play.** Any move that preserves the floor
(progressing the obligation, unlocking, idling, even a single early stall within budget) is admitted
UNCHANGED. -/
theorem govStep_admits_benign (w : World) (m : Move) (hb : worldFloor (stepMove w m)) :
    govStep w m = stepMove w m := by
  unfold govStep; rw [if_pos hb]

/-- **Gentle governance, half 2 — refuses ONLY harm.** Every refusal is a genuine floor-breaking
move: stalling past budget, or locking an agent out. Honest play is never refused. -/
theorem govStep_refuses_only_harmful (w : World) (m : Move) (h : govStep w m ≠ stepMove w m) :
    ¬ worldFloor (stepMove w m) := by
  unfold govStep at h
  by_cases hb : worldFloor (stepMove w m)
  · rw [if_pos hb] at h; exact absurd rfl h
  · exact hb

/-! ## The detector — read lock-in / hole-rent off public state. -/

/-- **The lock-in / hole-rent detector**: an obligation aged past budget (held open collecting rent),
OR an agent locked out of the gate. Decidable — it is exactly the negation of the floor. -/
def lockinDetected (w : World) : Prop :=
  w.age > budget ∨ w.locked false = true ∨ w.locked true = true

instance (w : World) : Decidable (lockinDetected w) :=
  inferInstanceAs (Decidable (w.age > budget ∨ w.locked false = true ∨ w.locked true = true))

/-! ## The experiment: a rentier, ungoverned vs governed. -/

/-- Genesis: the obligation is closed (fresh), nobody locked out — the floor holds. -/
def w0 : World := { open? := false, age := 0, rent := 0, locked := fun _ => false }

/-- The **rentier**: agent `false` stalls the open obligation every turn — a move that keeps the hole
open and accrues rent without progress. -/
def rentier : World → Move := fun _ => ⟨false, .stall⟩

/-- The **gatekeeper**: agent `false` locks agent `true` out of the gate. -/
def lockMove : Move := ⟨false, .lock true⟩
/-- An honest move: stall the obligation one tick (within budget this is fine). -/
def stallMove : Move := ⟨false, .stall⟩
/-- An honest move: resolve the obligation. -/
def progressMove : Move := ⟨true, .progress⟩

/-- **UNGOVERNED — lock-in emerges.** The rentier stalls past budget: after `budget+1` stalls the
hole's age exceeds the budget, breaking the floor — the obligation is held open for rent. -/
theorem ungoverned_lockin_emerges :
    ¬ worldFloor
        (stepMove (stepMove (stepMove (stepMove w0 stallMove) stallMove) stallMove) stallMove) := by
  decide

/-- **The lock-in detector fires** on the ungoverned episode (the counterfactual on live state): the
obligation was viable at genesis (`worldFloor w0`) and is held open past budget after four stalls. -/
theorem ungoverned_is_lockin :
    worldFloor w0 ∧
      lockinDetected (stepMove (stepMove (stepMove (stepMove w0 stallMove) stallMove) stallMove)
        stallMove) := by decide

/-- **The lock-OUT detector fires** too: a single `lock true` move bars agent `true` from the gate. -/
theorem ungoverned_lockout_detected :
    worldFloor w0 ∧ lockinDetected (stepMove w0 lockMove) := by decide

/-- **GOVERNED — lock-in prevented.** The SAME rentier, under the polis envelope, is refused once a
stall would push age past budget; the floor holds across the whole episode. (12 ticks, kernel.) -/
theorem governed_prevents_lockin : worldFloor (govTraj rentier w0 12) := by decide

/-- … and not just for this rentier: the governed floor holds for EVERY controller. -/
theorem governed_no_lockin (ctrl : World → Move) :
    ∀ n, worldFloor (govTraj ctrl w0 n) :=
  sandbox_lockin_governed_safe ctrl w0 (by decide)

/-- The detector is CLEAR on the governed episode — no lock-in survives the envelope. -/
theorem governed_clear : ¬ lockinDetected (govTraj rentier w0 12) := by decide

/-! ## A runnable episode — watch lock-in emerge, and the polis refuse it (gently). -/

/-- Read the world as `(open?, age, rent, locked-false, locked-true)`. -/
def view (w : World) : Bool × Nat × Nat × Bool × Bool :=
  (w.open?, w.age, w.rent, w.locked false, w.locked true)

/-- Fold a move list with the RAW (ungoverned) step. -/
def runRaw (ms : List Move) (w : World) : World := ms.foldl stepMove w
/-- Fold a move list with the GOVERNED step (the polis envelope). -/
def runGov (ms : List Move) (w : World) : World := ms.foldl govStep w

/-- The episode: the rentier stalls five times (collecting rent, aging the hole) and then locks agent
`true` out — the full hole-rent + lock-in play. -/
def episode : List Move :=
  [stallMove, stallMove, stallMove, stallMove, stallMove, lockMove]

-- ── Run it (read the output) ──────────────────────────────────────────────
-- UNGOVERNED: the hole rents forever and the gate locks — age 5 > budget 3, rent 5, `true` locked.
#eval view (runRaw episode w0)   -- (true, 5, 5, false, true)
-- GOVERNED: stalls past budget are refused (age capped at budget 3) and the lock-out is refused —
-- the gate stays passable. The hole is FORCED to stay within progress range; rent stops at 3.
#eval view (runGov episode w0)   -- (true, 3, 3, false, false)

/-- The same, as PROVEN facts (not just `#eval`): ungoverned ends in over-budget rent + lock-out;
governed caps age at budget with no lock-out. -/
theorem ungoverned_view_eq : view (runRaw episode w0) = (true, 5, 5, false, true) := by decide
theorem governed_view_eq   : view (runGov episode w0) = (true, 3, 3, false, false) := by decide

/-- And the floor is intact at the end of the governed episode — within-budget age, nobody locked. -/
theorem governed_floor_intact : worldFloor (runGov episode w0) := by decide

/-- … while the ungoverned end-state genuinely violates it (the texture is non-vacuous). -/
theorem ungoverned_floor_broken : ¬ worldFloor (runRaw episode w0) := by decide

end Metatheory.PolisSandboxLockin
