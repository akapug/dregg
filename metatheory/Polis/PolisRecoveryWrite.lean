/-
# Metatheory.PolisRecoveryWrite — the non-lock-in viability floor on the LIVE register-carrier verb.

`PolisRecoveryFloor` binds the bounded recovery game to the abstract `rotateStep : KeyState → … →
Option KeyState`. But the DEPLOYED recovery verb is the REGISTER-CARRIER guarded write
`rotateWrite : RecChainedState → … → Option RecChainedState` (`Dregg2.Apps.PreRotation §3`): a
caveat-gated field write through `stateStepGuarded` over the live record kernel — it carries the
authority gate (the council must hold the cell), the membership + lifecycle-liveness gates, and the
cell's OWN per-slot caveats (the council's threshold/monotone constitution), and it audits one
receipt row per rotation. This file CLOSES the residual: the recovery game now plays over the REAL
`rotateWrite`, not the abstract step.

## What is bound (the live register-carrier surface)

* **`Config` = `RecChainedState`** — the deployed live state (`{ kernel, log }`), NOT a projection.
  The recovery context (the acting council `actor`, the identity `idCell`, the public recovery
  `roster` of key sets, and the recovery `target` digest) is the PUBLIC recovery constitution, fixed
  by the arena; the game's state that evolves is the real cell state.
* **`floorOk`** = "control is recoverable right now on the live register": some roster set hashes to
  the cell's committed `next_keys_digest` REGISTER (`fieldOf nextKeysDigestField (s.kernel.cell
  idCell)`), so the deployed `rotateWrite` preimage gate would admit it. DECIDABLE (`List.any` of
  `DecidableEq Int`), public — reads only the committed register + the published roster.
* **`enabledMoves`** = the roster sets the live verb actually ADMITS from this state — `rotateWrite …
  = some _` (which is exactly authority ∧ membership ∧ liveness ∧ caveats ∧ preimage). A presentation
  the live verb refuses is no move at all; no spurious vacuous win.
* **`advReact`** = the deployed `rotateWrite` outcome (installing the recovery `target` as the fresh
  next-commitment): the rotation advances to the REAL post-state (register holds the fresh digest,
  one receipt appended, balance/caps untouched — by the §3 keystones), so the game continues from the
  genuine live successor.

Then `PolisViability.viableWithinB` over this arena IS the **bounded recovery game on the live
register-carrier verb**: the council can GUARANTEE it still controls a recovery key set within `k`
public rotations of the deployed `rotateWrite`, against adversarial scheduling among its own legal
responses. `Foreclosed` = the deployed lock-in on the live substrate.

## The bridges (load-bearing ties to the deployed verb)

* `writeRecoverableNow_iff_register_admits` — `floorOk` holds iff some roster set, presented to the
  LIVE `rotateWrite`, exhibits the committed register preimage (the base case IS the live verb's
  preimage gate). Uses the deployed `rotateWrite_exhibits_preimage`.
* `enabled_move_admits` / `enabled_move_step` — every enabled move is admitted by `rotateWrite` and
  its `advReact` is the single real live successor (no empty, vacuously-winning response set).
* `floorOk_of_writeStep` — the live game and the abstract chain agree: a register rotation that
  reaches a floor-holding cell is the multi-link recovery `rotChain` witness on the register.

## Honest framing

BOUNDED, PUBLIC, DECIDABLE. `floorOk` reads only the published roster + the cell's committed register
(no private keys, no controller intent); viability is a finite `k`-bounded game over the LIVE verb. It
does NOT model coercion economics, off-protocol custody, or council honesty — not public-decidable,
out of scope by construction. What it captures faithfully: under the deployed `rotateWrite` semantics
(authority+membership+liveness+caveats+preimage), whether a committed recovery path of length `≤ k`
to a designated set EXISTS. The crypto floor (`KeySetCR`, hash collision-resistance) lives in the
deployed module and is the one TERMINAL seam — it cannot be proven in Lean; here we witness the GAME
over the live verb, never re-prove the hash.

l4v bar: `floorOk` is `Bool`-valued, non-vacuous both
polarities (a recoverable live state passes; a locked-out live state is foreclosed). `#guard`s run
the real bounded game over the deployed `rotateWrite`.
-/
import Polis.PolisViability
import Dregg2.Apps.PreRotation

namespace Metatheory.PolisRecoveryWrite

open Metatheory.PolisViability
open Dregg2.Exec
open Dregg2.Exec.EffectsState
open Dregg2.Apps.PreRotation

variable {Key : Type}

/-- **The public recovery context** — the fixed, PUBLIC recovery constitution the arena closes over:
which council `actor` acts, on which identity `idCell`, the published `roster` of key sets it may
lawfully present, and the digest of the designated recovery `target` it seeks to (re)control. No
private controller state. The game state that *evolves* is the live `RecChainedState`, not this. -/
structure RecoveryCtx (Key : Type) where
  /-- The acting council cell (must hold authority over `idCell` for the live verb to admit). -/
  actor  : CellId
  /-- The identity cell whose `next_keys_digest` register is being recovered. -/
  idCell : CellId
  /-- The council's PUBLIC recovery roster: the key sets it may lawfully present. -/
  roster : List (List Key)
  /-- The digest of the designated recovery key set the council seeks to control. -/
  target : Int

/-- **`writeRecoverableNow` — the live non-lock-in floor (DECIDABLE, `Bool`).** Control is
recoverable *right now on the live register* iff some roster member hashes to the cell's committed
`next_keys_digest` register — i.e. the deployed `rotateWrite` preimage gate would admit it. Reads only
the published roster + the committed register field of the live cell; no interior. -/
def writeRecoverableNow (hash : List Key → Int) (ctx : RecoveryCtx Key) (s : RecChainedState) :
    Bool :=
  ctx.roster.any (fun ks => hash ks == fieldOf nextKeysDigestField (s.kernel.cell ctx.idCell))

/-- **`recoveryWriteArena` — the deployed register-carrier recovery as a `PolisViability.Arena`.**

* `floorOk`      = `writeRecoverableNow`: a present-able admissible register rotation exists.
* `enabledMoves` = the roster sets the deployed `rotateWrite` actually ADMITS from this live state
  (authority ∧ membership ∧ liveness ∧ caveats ∧ preimage — the full live gate). A refused
  presentation is no move; no spurious vacuous win.
* `advReact`     = the deployed `rotateWrite` outcome of presenting an (already-admitted) set with
  the recovery `target` as its fresh next-commitment: it advances to the REAL installed
  `RecChainedState` (register holds the fresh digest, one receipt appended). An enabled move is
  always admitted, so `advReact` always has exactly the one real live successor — no empty response.

Faithfulness note: gating `enabledMoves` on actual `rotateWrite` admission is the deployed semantics,
NOT a cheat — the public option-space IS "the register rotations the live verb accepts".
`writeRecoverableNow_iff_register_admits` ties `floorOk` to the live verb's preimage gate. -/
def recoveryWriteArena (hash : List Key → Int) (ctx : RecoveryCtx Key) :
    Arena RecChainedState (List Key) where
  floorOk s := writeRecoverableNow hash ctx s
  enabledMoves s :=
    ctx.roster.filter (fun ks =>
      (rotateWrite hash s ctx.actor ctx.idCell ks ctx.target).isSome)
  advReact s ks :=
    match rotateWrite hash s ctx.actor ctx.idCell ks ctx.target with
    | some s' => [s']
    | none    => []

/-- **`RecoveryWriteViable` — the REAL bounded recovery game on the LIVE register-carrier verb.** The
council can GUARANTEE it still controls a designated recovery set within `k` public `rotateWrite`
rotations, against adversarial scheduling among its own legal responses. This is
`PolisViability.viableWithinB` over the deployed `rotateWrite` — the deployed non-lock-in property on
the live substrate, decidable. -/
def RecoveryWriteViable (hash : List Key → Int) (ctx : RecoveryCtx Key) (k : Nat)
    (s : RecChainedState) : Prop :=
  Viable (recoveryWriteArena hash ctx) k s

/-- **`RecoveryWriteForeclosed` — deployed lock-in on the live substrate, as a GAME.** No bounded
sequence of admissible `rotateWrite` rotations regains a designated set: the exit-foreclosure over the
live register-carrier recovery verb. -/
def RecoveryWriteForeclosed (hash : List Key → Int) (ctx : RecoveryCtx Key) (k : Nat)
    (s : RecChainedState) : Prop :=
  Foreclosed (recoveryWriteArena hash ctx) k s

instance (hash : List Key → Int) (ctx : RecoveryCtx Key) (k : Nat) (s : RecChainedState) :
    Decidable (RecoveryWriteViable hash ctx k s) :=
  inferInstanceAs (Decidable (Viable (recoveryWriteArena hash ctx) k s))
instance (hash : List Key → Int) (ctx : RecoveryCtx Key) (k : Nat) (s : RecChainedState) :
    Decidable (RecoveryWriteForeclosed hash ctx k s) :=
  inferInstanceAs (Decidable (Foreclosed (recoveryWriteArena hash ctx) k s))

/-- **The live-register recovery-floor CaptureBar.** The politician's lock-in — driving the identity
cell into a live state with NO bounded admissible `rotateWrite` recovery — is barred EXACTLY when the
bounded recovery game over the live verb is `Foreclosed`, decidable from the public recovery context +
the committed register alone. -/
def recoveryWriteFloorBar (hash : List Key → Int) (ctx : RecoveryCtx Key) (k : Nat) :=
  viabilityBar (recoveryWriteArena hash ctx) k

/-! ### The bridges: the floor IS the live `rotateWrite` preimage gate. -/

/-- **`writeRecoverableNow_iff_register_admits`.** The floor holds iff some roster key set, presented
to the deployed `rotateWrite` (with the recovery target as fresh next), is ADMITTED — equivalently,
hashes to the cell's committed register. The abstract floor and the LIVE register verb agree on the
base case. (One direction needs only the live verb's preimage gate `rotateWrite_exhibits_preimage`;
the other is the definitional `if`-guard of `rotateWrite`.) -/
theorem writeRecoverableNow_iff_register_admits (hash : List Key → Int) (ctx : RecoveryCtx Key)
    (s : RecChainedState) :
    writeRecoverableNow hash ctx s = true ↔
      ∃ ks ∈ ctx.roster,
        hash ks = fieldOf nextKeysDigestField (s.kernel.cell ctx.idCell) := by
  unfold writeRecoverableNow
  rw [List.any_eq_true]
  constructor
  · rintro ⟨ks, hmem, hbeq⟩
    exact ⟨ks, hmem, (beq_iff_eq).1 hbeq⟩
  · rintro ⟨ks, hmem, hg⟩
    exact ⟨ks, hmem, (beq_iff_eq).2 hg⟩

/-- **`enabled_move_admits`.** Every move the arena enables is genuinely admitted by the deployed
`rotateWrite` — the option-space is the LIVE verb's accept set, not a paper move set. -/
theorem enabled_move_admits (hash : List Key → Int) (ctx : RecoveryCtx Key) (s : RecChainedState)
    {ks : List Key} (hm : ks ∈ (recoveryWriteArena hash ctx).enabledMoves s) :
    (rotateWrite hash s ctx.actor ctx.idCell ks ctx.target).isSome = true := by
  simp only [recoveryWriteArena, List.mem_filter] at hm
  exact hm.2

/-- **`enabled_move_step`.** An enabled move's `advReact` is exactly the SINGLE real live successor
produced by the deployed `rotateWrite` — never the empty (vacuously-winning) response. -/
theorem enabled_move_step (hash : List Key → Int) (ctx : RecoveryCtx Key) (s : RecChainedState)
    {ks : List Key} (hm : ks ∈ (recoveryWriteArena hash ctx).enabledMoves s) :
    ∃ s', rotateWrite hash s ctx.actor ctx.idCell ks ctx.target = some s' ∧
      (recoveryWriteArena hash ctx).advReact s ks = [s'] := by
  have hsome := enabled_move_admits hash ctx s hm
  obtain ⟨s', hs'⟩ := Option.isSome_iff_exists.1 hsome
  refine ⟨s', hs', ?_⟩
  simp only [recoveryWriteArena, hs']

/-- **`floorOk_of_register_commit`.** If the live `rotateWrite` reaches a state whose committed
register equals the digest of an in-roster set, the floor holds at that successor — the game's
"recovered" base case is literally the live register holding a roster commitment. This ties the
multi-link recovery (a `rotateWrite` chain) back to the floor: after the chain installs a roster set's
commitment, the council controls a designated set. -/
theorem floorOk_of_register_commit (hash : List Key → Int) (ctx : RecoveryCtx Key)
    (s' : RecChainedState) {ks : List Key} (hmem : ks ∈ ctx.roster)
    (hreg : fieldOf nextKeysDigestField (s'.kernel.cell ctx.idCell) = hash ks) :
    (recoveryWriteArena hash ctx).floorOk s' = true := by
  show writeRecoverableNow hash ctx s' = true
  rw [writeRecoverableNow_iff_register_admits]
  exact ⟨ks, hmem, hreg.symm⟩

/-- **`writeStep_commits_target`.** A committed `rotateWrite` installs the recovery `target` as the
cell's fresh register — the live forward chain's next link, in the committed state. (Direct lift of
the deployed `rotateWrite_commits_fresh`.) This is the link that makes the MULTI-LINK register
recovery chain advance: each move drives the register to `target`. -/
theorem writeStep_commits_target (hash : List Key → Int) (ctx : RecoveryCtx Key)
    {s s' : RecChainedState} {ks : List Key}
    (h : rotateWrite hash s ctx.actor ctx.idCell ks ctx.target = some s') :
    fieldOf nextKeysDigestField (s'.kernel.cell ctx.idCell) = ctx.target :=
  rotateWrite_commits_fresh h

/-! ## Non-vacuity, both polarities, EXECUTED — over the LIVE `rotateWrite`.

`tinyHash` + a real `RecChainedState` (the deployed module's `idState`: an identity council cell `0`,
balance `0`, register committing to `[3,4]`). A recoverable context (a roster member is the committed
register, with a reachable next link) and a locked-out context (NO roster member is the committed
register — no admissible live rotation). The `#guard`s run the real bounded game over the deployed
`rotateWrite`, exercising authority/membership/liveness/caveats/preimage on every step. -/

/-- A RECOVERABLE context: the council (cell `0`) acts on the identity cell `0`; the roster carries
`[3,4]` (the cell's committed register — present-able now) and `[5,6]`; the recovery target is the
digest of `[5,6]` (also on the roster, so the next link is reachable). -/
def recoverableCtx : RecoveryCtx Nat :=
  { actor := 0, idCell := 0, roster := [[3, 4], [5, 6]], target := tinyHash [5, 6] }

/-- A LOCKED-OUT context: same identity cell, but a roster containing NEITHER the committed register
`[3,4]` nor anything that hashes to it — no roster set is present-able, so no admissible live
rotation exists. Lock-in, by the deployed `rotateWrite`. -/
def lockedOutCtx : RecoveryCtx Nat :=
  { actor := 0, idCell := 0, roster := [[5, 6], [7, 8]], target := tinyHash [5, 6] }

/-- An UNAUTHORIZED context: the right roster + target, but actor `9` does NOT hold the cell — so the
live verb's AUTHORITY gate refuses every MOVE (`enabledMoves idState = []`). Yet the floor is
authority-INDEPENDENT: it reads only the published roster + the cell's committed register, never who
acts. Here `[3,4]` is on the roster and IS the committed register, so the floor already HOLDS — the
context is VIABLE at budget `0` with no move needed. This is the file's honest framing made concrete:
recoverability-of-control is a PUBLIC property of the register + roster, not of the actor's authority;
the authority gate governs whether a ROTATION can advance, not whether control is presently held. -/
def unauthorizedCtx : RecoveryCtx Nat :=
  { actor := 9, idCell := 0, roster := [[3, 4], [5, 6]], target := tinyHash [5, 6] }

-- The floor itself: recoverable ctx passes (register commits a roster member), locked-out fails:
#guard writeRecoverableNow tinyHash recoverableCtx idState == true
#guard writeRecoverableNow tinyHash lockedOutCtx idState == false

-- The REAL bounded game over the deployed `rotateWrite`:
-- recoverable within budget 3 (present [3,4] → register now commits target=hash[5,6]; the floor
-- holds there because [5,6] is on the roster and hashes to the new register):
#guard viableWithinB (recoveryWriteArena tinyHash recoverableCtx) 3 idState == true
-- locked-out: foreclosed at a generous budget — no admissible live rotation, ever:
#guard viableWithinB (recoveryWriteArena tinyHash lockedOutCtx) 5 idState == false
-- unauthorized actor: the floor is authority-INDEPENDENT, so it is VIABLE — control is presently held
-- on the public register ([3,4] commits it) even though actor 9 can make NO admissible rotation:
#guard viableWithinB (recoveryWriteArena tinyHash unauthorizedCtx) 5 idState == true
-- ...and the AUTHORITY-gate tooth itself: actor 9 enables NO move (would-be rotations are refused):
#guard (recoveryWriteArena tinyHash unauthorizedCtx).enabledMoves idState == []

-- The bar fires EXACTLY on the locked-out live state, NOT on the recoverable one — and NOT on the
-- unauthorized one, whose PUBLIC floor (control held on the register) holds regardless of authority:
example : (recoveryWriteFloorBar tinyHash lockedOutCtx 5).badShape idState := by
  show RecoveryWriteForeclosed tinyHash lockedOutCtx 5 idState; decide
example : ¬ (recoveryWriteFloorBar tinyHash recoverableCtx 3).badShape idState := by
  show ¬ RecoveryWriteForeclosed tinyHash recoverableCtx 3 idState; decide
example : ¬ (recoveryWriteFloorBar tinyHash unauthorizedCtx 5).badShape idState := by
  show ¬ RecoveryWriteForeclosed tinyHash unauthorizedCtx 5 idState; decide

-- And the Prop-level wrappers decide (BOTH polarities over the live verb):
example : RecoveryWriteViable tinyHash recoverableCtx 3 idState := by decide
example : RecoveryWriteForeclosed tinyHash lockedOutCtx 5 idState := by decide
example : RecoveryWriteViable tinyHash unauthorizedCtx 5 idState := by decide

/-! ## Axiom hygiene: the bridges pin {propext, Classical.choice, Quot.sound}. -/

#assert_axioms writeRecoverableNow_iff_register_admits
#assert_axioms enabled_move_admits
#assert_axioms enabled_move_step
#assert_axioms floorOk_of_register_commit
#assert_axioms writeStep_commits_target

end Metatheory.PolisRecoveryWrite
