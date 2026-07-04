/-
# Metatheory.PolisSandboxLaunder — a fully-in-Lean polis sandbox for GRADE LAUNDERING.

A genuinely different politics texture from foreclosure (`PolisSandbox`'s trap). There the
politician PUSHED a victim out of reach; here the launderer INFLATES ITS OWN STANDING — it claims a
finality/claim TIER it has not earned. Nobody is shoved; the harm is a counterfeit of merit.

The world: each agent carries two public numbers — the `claim` tier it advertises, and the `earned`
work it has actually done. Honest play raises `earned` (you do the work) and may then raise `claim`
to match. The LAUNDERER skips the work and just escalates `claim`.

  * **Floor** (`worldFloor`): every agent's advertised claim is backed by earned work
    (`claim ≤ earned`). A claim you didn't earn is laundering.
  * **Detector** (`launderingDetected`): fires when ANY agent's claim outruns its earned work —
    read off public state, no interior, no motive.
  * **Governance** (`govStep`): admit a move iff it leaves every claim backed, else SHIELD (no-op).
  * **Gentle**: a move that keeps claims backed is admitted UNCHANGED (honest earning-then-claiming
    is never blocked); every refusal is a genuine unearned escalation.

Proven end-to-end:
  * UNGOVERNED — the launderer reaches a high claim with zero earned work; the floor BREAKS and the
    detector fires.
  * GOVERNED — the SAME launderer, under the envelope, is pinned to what it earned; the floor holds
    for the whole episode and for EVERY controller (`sandbox_governed_safe`).

The `claim`/`earned` numbers are the live-world shadow of `Dregg2.Finality.Tier`'s no-downgrade
ladder: a tier is only legitimate when the underlying quorum/work actually committed it. Here
`claim ≤ earned` is exactly "the advertised tier is one the work supports."

Pure Lean 4 core; no imports beyond `Nat`/`Bool`. Two agents (`Bool`) for the demo; the shape
generalizes to any `Fintype` of agents.
-/

namespace Metatheory.PolisSandboxLaunder

/-- Agents (two, for the demo). -/
abbrev AgentId := Bool

/-- Each agent's public standing: the tier it `claim`s, and the work it has `earned`. No interior. -/
structure Standing where
  /-- The finality/claim tier the agent advertises. -/
  claim : Nat
  /-- The work the agent has actually done (what legitimately backs a claim). -/
  earned : Nat
deriving DecidableEq, Repr

/-- The public world state: each agent's standing. -/
abbrev World := AgentId → Standing

/-- A claim is BACKED iff it does not exceed earned work. -/
def Standing.backed (s : Standing) : Prop := s.claim ≤ s.earned

instance (s : Standing) : Decidable s.backed := inferInstanceAs (Decidable (s.claim ≤ s.earned))

/-- An action an agent may propose:
* `noop` — idle.
* `work` — do one unit of legitimate work (raises `earned`).
* `claimUpTo t` — advertise tier `t` (the honest use: claim what you earned).
* `launder t` — advertise tier `t` outright, doing NO work — the unearned escalation. -/
inductive Act
  | noop
  | work
  | claimUpTo (tier : Nat)
  | launder (tier : Nat)
deriving DecidableEq, Repr

/-- A scheduled move: which agent acts, and how (the controller's public proposal). -/
structure Move where
  actor : AgentId
  action : Act

/-- Apply `actor`'s action to its standing.
Note `claimUpTo` and `launder` have the SAME state effect (set the claim) — the difference is purely
the honest INTENT label; the governor judges the resulting STATE, not the label, so a launderer
cannot escape by relabelling its move as `claimUpTo`. -/
def actStanding (s : Standing) : Act → Standing
  | .noop => s
  | .work => { s with earned := s.earned + 1 }
  | .claimUpTo t => { s with claim := t }
  | .launder t => { s with claim := t }

/-- Apply `actor`'s action to the world (only the actor's standing changes). -/
def act (w : World) (actor : AgentId) (a : Act) : World :=
  fun i => if i = actor then actStanding (w i) a else w i

/-- One world step from a move. -/
def stepMove (w : World) (m : Move) : World := act w m.actor m.action

/-- **The shared floor**: EVERY agent's advertised claim is backed by earned work. Decidable. -/
def worldFloor (w : World) : Prop := (w false).backed ∧ (w true).backed

instance (w : World) : Decidable (worldFloor w) :=
  inferInstanceAs (Decidable ((w false).backed ∧ (w true).backed))

/-- **The laundering detector**: fires when ANY agent's claim outruns its earned work — an unearned
escalation, read off public state. (Exactly the negation of the floor.) -/
def launderingDetected (w : World) : Prop :=
  (w false).earned < (w false).claim ∨ (w true).earned < (w true).claim

instance (w : World) : Decidable (launderingDetected w) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The detector fires exactly when the floor is broken (it IS the negation of the floor). -/
theorem detect_iff_floor_broken (w : World) : launderingDetected w ↔ ¬ worldFloor w := by
  unfold launderingDetected worldFloor Standing.backed
  omega

/-- **The polis-governed step**: admit the proposed move iff it keeps every claim backed, else SHIELD
(no-op). The constitution's envelope, computable on the live world. -/
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

/-- **`sandbox_governed_safe` — governance, proven.** Under the polis-governed step, every claim
stays backed at EVERY tick for EVERY controller (the launderer included): no agent ever advertises a
tier it did not earn. The live-world instance of the constitution's `polis_safety` (verify the cage,
not the animal — the controller is universally quantified, never inspected). -/
theorem sandbox_governed_safe (ctrl : World → Move) (w0 : World) (h0 : worldFloor w0) :
    ∀ n, worldFloor (govTraj ctrl w0 n) := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact govStep_preserves _ _ ih

/-! ## Gentle governance — least-restrictive, proven for ALL worlds/moves. -/

/-- **Gentle governance, half 1 — admits all honest play.** A move that keeps every claim backed is
admitted UNCHANGED: doing work, claiming what you earned, idling are never blocked (∀ world, ∀ move). -/
theorem govStep_admits_benign (w : World) (m : Move) (hb : worldFloor (stepMove w m)) :
    govStep w m = stepMove w m := by
  unfold govStep; rw [if_pos hb]

/-- **Gentle governance, half 2 — refuses ONLY harm.** Every refusal is a genuine unearned
escalation; an honest move is never refused (∀ world, ∀ move). The live-world `override_only_unsafe`. -/
theorem govStep_refuses_only_harmful (w : World) (m : Move) (h : govStep w m ≠ stepMove w m) :
    ¬ worldFloor (stepMove w m) := by
  unfold govStep at h
  by_cases hb : worldFloor (stepMove w m)
  · rw [if_pos hb] at h; exact absurd rfl h
  · exact hb

/-! ## The experiment: a launderer, ungoverned vs governed. -/

/-- Genesis: everyone honest and idle (claim 0, earned 0 — the floor holds). -/
def w0 : World := fun _ => ⟨0, 0⟩

/-- The **launderer**: agent `false` advertises tier `4` (the top of the four-tier ladder) every turn
without doing any work — a move whose RESULT is an unearned claim. -/
def launderer : World → Move := fun _ => ⟨false, .launder 4⟩

/-- An honest worker's move: agent `true` does a unit of legitimate work. -/
def workMove : Move := ⟨true, .work⟩
/-- An honest claim move: agent `true` advertises tier `1` (which one unit of work backs). -/
def claimMove : Move := ⟨true, .claimUpTo 1⟩
/-- The launderer's move, named, for the episode. -/
def launderMove : Move := ⟨false, .launder 4⟩

/-- **UNGOVERNED — laundering emerges.** The launderer's move sets `claim 4` over `earned 0`: the
floor BREAKS (the advertised tier is unbacked). -/
theorem ungoverned_laundering_emerges : ¬ worldFloor (stepMove w0 (launderer w0)) := by decide

/-- **The laundering detector fires** (on the live world): agent `false` advertises a tier its earned
work does not support — read off public state with no interior. -/
theorem ungoverned_is_laundering :
    worldFloor w0 ∧ launderingDetected (stepMove w0 (launderer w0)) := by decide

/-- **GOVERNED — laundering prevented.** The SAME launderer, under the polis envelope, is refused at
every turn; every claim stays backed across the whole episode. (Kernel-evaluated for 12 ticks.) -/
theorem governed_prevents_laundering : worldFloor (govTraj launderer w0 12) := by decide

/-- … and the detector is CLEAR on the governed episode (no unearned claim survives). -/
theorem governed_detector_clear : ¬ launderingDetected (govTraj launderer w0 12) := by decide

/-- … and not just for this launderer: the governed floor holds for EVERY controller. -/
theorem governed_no_laundering (ctrl : World → Move) :
    ∀ n, worldFloor (govTraj ctrl w0 n) :=
  sandbox_governed_safe ctrl w0 (by decide)

/-! ## A runnable episode — watch a tier get laundered, and the polis pin it to what was earned. -/

/-- Read the world as `((false.claim, false.earned), (true.claim, true.earned))`. -/
def view (w : World) : (Nat × Nat) × (Nat × Nat) :=
  (((w false).claim, (w false).earned), ((w true).claim, (w true).earned))

/-- Fold a move list with the RAW (ungoverned) step. -/
def runRaw (ms : List Move) (w : World) : World := ms.foldl stepMove w
/-- Fold a move list with the GOVERNED step (the polis envelope). -/
def runGov (ms : List Move) (w : World) : World := ms.foldl govStep w

/-- Start: everyone at claim 0 / earned 0. -/
def startW : World := w0

/-- The episode: the honest worker `true` does work then legitimately claims tier 1, while the
launderer `false` keeps trying to advertise tier 4 it never earned. -/
def episode : List Move := [workMove, launderMove, claimMove, launderMove]

-- ── Run it (read the output) ──────────────────────────────────────────────
-- UNGOVERNED: the launderer reaches claim 4 on earned 0 — an unearned tier. Laundering emerges.
-- Output reads ((false.claim, false.earned), (true.claim, true.earned)).
#eval view (runRaw episode startW)     -- ((4, 0), (1, 1))
-- GOVERNED: the launder moves are refused — `false` is pinned to claim 0 (earned 0), while `true`'s
-- honest work-then-claim is ALLOWED (claim 1 on earned 1). Gentle governance.
#eval view (runGov episode startW)     -- ((0, 0), (1, 1))

-- The bare detector verdict in each regime (True = laundering present).
#eval decide (launderingDetected (runRaw episode startW))   -- true
#eval decide (launderingDetected (runGov episode startW))   -- false

/-- The same, as PROVEN facts (not just `#eval`): ungoverned the launderer holds an unearned tier 4;
governed it is pinned to its earned 0, while the honest agent's earned claim stands. -/
theorem ungoverned_launders : view (runRaw episode startW) = ((4, 0), (1, 1)) := by decide
theorem governed_pins_to_earned : view (runGov episode startW) = ((0, 0), (1, 1)) := by decide

/-- The detector verdicts, proven: it fires ungoverned, clears governed. -/
theorem ungoverned_detector_fires : launderingDetected (runRaw episode startW) := by decide
theorem governed_detector_clear_episode : ¬ launderingDetected (runGov episode startW) := by decide

/-- And the floor is intact at the end of the governed episode — no claim went unearned. -/
theorem governed_floor_intact : worldFloor (runGov episode startW) := by decide

end Metatheory.PolisSandboxLaunder
