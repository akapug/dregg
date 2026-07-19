/-
# Dregg2.Circuit.Emit.AutomataflStepCapstone — LEG A, the n-GENERIC ray fuel induction and the
board-decode / four-ray landing interface the `n = 11` step capstone stands on.

## Why this file exists (and where it sits)

`AutomataflStepRefine` closed the automaton-step refinement at the FROZEN `NN = 2` board: its four
`raycast_*_of_sat` are two-step finite scans (`raycastFuel` unfolded twice, `size = 2` hardcoded) and
its `astep_sat_imp_automatonStep` is stated over the `n = 2` `boardDecode`. `AutomataflCoord` then
supplied the `n`-generic coordinate/one-hot FOUNDATION (`oneHotN_of_sat`, `coordN_of_sat`,
`dot_oneHot(2)`, the `evalH` bridge) and imports `AutomataflStepRefine`. So the Leg-A capstone for the
deployed `n = 11` board CANNOT live in `AutomataflStepRefine` (that would be an import cycle through
`AutomataflCoord`); it lives HERE, downstream of `AutomataflCoord`.

## What this file LANDS (proven, non-vacuous, no `sorry`/`native_decide`/assumed hypothesis)

  * **§1 — THE RAY FUEL INDUCTION.** The `n = 2` scans do not scale: the `n = 11` ray is up to eleven
    steps long, so the reference `Board.raycast` reduction must be an INDUCTION on the step index, not
    a fixed unfolding. `raycastFuel_scan` fast-forwards `m` consecutive in-bounds vacuum steps
    (induction on `m` via the one-step peel `raycastFuel_succ_vac`); `raycast_at_hit` composes it into
    the whole-scan collapse to the single read at the hit step `K`. n-GENERIC — one proof for every
    board size and every cardinal direction.

  * **§2 — `boardDecodeN` + `raycast_of_hit`.** The `n`-generic step board decode, and the single
    four-ray landing lemma: for ANY `Dir` and size `n`, `Board.raycast (boardDecodeN n e) auto d`
    collapses through `raycast_at_hit` to `{ cell-or-wall, K }` given the strictly-before facts. This
    is the ready target each `raycast_*_of_sat` calls once its circuit extraction supplies `K` and the
    before-facts.

## What this file does NOT yet land — the PRECISE residual (§3)

The circuit-side wiring that turns a satisfying `automataflStepDescN 11` witness INTO `raycast_of_hit`'s
arguments (`K`, the strictly-before in-bounds/vacuum facts) is NOT here: the `ibEqHead` prefix-sum
window collapse, the `rcReadHead` gated-read collapse, the hit one-hot → `K`, and the occlusion /
`cond_nonzero` teeth — each an `n`-generic re-derivation of what the `n = 2` proof did by concrete
`rfl`. `decideAxis`/`chooseOffset` restated over `automataflStepDescN n`, `automatonOffset_of_sat` and
`astep_sat_imp_automatonStep` at `n = 11` are downstream of that wiring and are likewise NOT here.
Nothing below is stated over the deployed capstone; the composition is not asserted.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AutomataflCoord

namespace Dregg2.Circuit.Emit.AutomataflStepCapstone

open Dregg2.Games.Automatafl (Board Coord Particle Dir raycastFuel Raycast)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Circuit.Emit.AutomataflStepRefine (codeToParticle)
open Dregg2.Circuit.Emit.AutomataflStepEmit.NGen (AX AY old)

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## §1 — THE RAY FUEL INDUCTION (pure, n-generic).

The `n = 2` `raycast_*_of_sat` lemmas reduced the reference `Board.raycast` by hand as a two-step
finite scan (`raycastFuel` unfolded twice, `size = 2` hardcoded). At `n = 11` the ray is up to eleven
steps long, so the scan must be an INDUCTION on the step index, not a fixed unfolding.

`raycastFuel_succ_vac` peels one in-bounds vacuum step; `raycastFuel_scan` fast-forwards `m`
consecutive in-bounds vacuum steps (induction on `m`); `raycast_at_hit` combines them: given the ray
is vacuum+in-bounds strictly before step `K`, the whole scan collapses to the single read at step `K`.
This is the pure semantic engine every ray-of-sat lemma calls at ANY board size. -/

/-- Peel one in-bounds vacuum step off a `raycastFuel` scan. -/
theorem raycastFuel_succ_vac (b : Board) (x y dx dy : Int) (dist f : Nat)
    (hin : 0 ≤ x + dx ∧ x + dx < (b.size : Int) ∧ 0 ≤ y + dy ∧ y + dy < (b.size : Int))
    (hvac : (b.cellAt ⟨(x + dx).toNat, (y + dy).toNat⟩).isVacuum = true) :
    raycastFuel b x y dx dy dist (f + 1)
      = raycastFuel b (x + dx) (y + dy) dx dy (dist + 1) f := by
  rw [raycastFuel]
  rw [if_pos hin, if_pos hvac]

/-- Fast-forward `m` consecutive in-bounds vacuum steps of a `raycastFuel` scan (induction on `m`). -/
theorem raycastFuel_scan (b : Board) (dx dy : Int) :
    ∀ (m : Nat) (x y : Int) (dist fuel : Nat), m ≤ fuel →
      (∀ j, 1 ≤ j → j ≤ m →
        (0 ≤ x + (j : Int) * dx ∧ x + (j : Int) * dx < (b.size : Int)
          ∧ 0 ≤ y + (j : Int) * dy ∧ y + (j : Int) * dy < (b.size : Int))
        ∧ (b.cellAt ⟨(x + (j : Int) * dx).toNat, (y + (j : Int) * dy).toNat⟩).isVacuum = true) →
      raycastFuel b x y dx dy dist fuel
        = raycastFuel b (x + (m : Int) * dx) (y + (m : Int) * dy) dx dy (dist + m) (fuel - m) := by
  intro m
  induction m with
  | zero =>
    intro x y dist fuel _ _
    simp
  | succ k ih =>
    intro x y dist fuel hfuel hbefore
    -- fuel = f + 1
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    -- peel step 1
    have hstep1 := hbefore 1 (le_refl 1) (by omega)
    rw [show ((1 : Nat) : Int) * dx = dx by push_cast; ring] at hstep1
    rw [show ((1 : Nat) : Int) * dy = dy by push_cast; ring] at hstep1
    obtain ⟨hin1, hvac1⟩ := hstep1
    rw [raycastFuel_succ_vac b x y dx dy dist f hin1 hvac1]
    -- apply IH at the shifted point
    have hshift := ih (x + dx) (y + dy) (dist + 1) f (by omega)
      (fun j hj1 hjk => by
        rw [show x + dx + (j : Int) * dx = x + ((j + 1 : Nat) : Int) * dx by push_cast; ring]
        rw [show y + dy + (j : Int) * dy = y + ((j + 1 : Nat) : Int) * dy by push_cast; ring]
        exact hbefore (j + 1) (by omega) (by omega))
    rw [hshift]
    -- reconcile the shifted target with the (k+1)-step target
    congr 1
    · push_cast; ring
    · push_cast; ring
    · omega
    · omega

/-- **THE HIT LEMMA — the ray fuel induction, packaged.** If the ray is in-bounds and vacuum at
every step strictly before `K` (`1 ≤ K ≤ fuel`), the whole scan from `(x, y)` collapses to the single
read at step `K`: the `K`-th cell if in bounds, else the wall-vacuum sentinel — both at distance `K`.
This is the semantic target each `raycast_*_of_sat` matches its witnessed `(dist, what)` against. -/
theorem raycast_at_hit (b : Board) (x y dx dy : Int) (K fuel : Nat)
    (hK : 1 ≤ K) (hKf : K ≤ fuel)
    (hbefore : ∀ j, 1 ≤ j → j < K →
      (0 ≤ x + (j : Int) * dx ∧ x + (j : Int) * dx < (b.size : Int)
        ∧ 0 ≤ y + (j : Int) * dy ∧ y + (j : Int) * dy < (b.size : Int))
      ∧ (b.cellAt ⟨(x + (j : Int) * dx).toNat, (y + (j : Int) * dy).toNat⟩).isVacuum = true) :
    raycastFuel b x y dx dy 0 fuel
      = if (0 ≤ x + (K : Int) * dx ∧ x + (K : Int) * dx < (b.size : Int)
            ∧ 0 ≤ y + (K : Int) * dy ∧ y + (K : Int) * dy < (b.size : Int))
        then (if (b.cellAt ⟨(x + (K : Int) * dx).toNat, (y + (K : Int) * dy).toNat⟩).isVacuum
              then raycastFuel b (x + (K : Int) * dx) (y + (K : Int) * dy) dx dy K (fuel - K)
              else { what := b.cellAt ⟨(x + (K : Int) * dx).toNat, (y + (K : Int) * dy).toNat⟩,
                     dist := K })
        else { what := .vacuum, dist := K } := by
  -- scan K-1 vacuum steps
  rw [raycastFuel_scan b dx dy (K - 1) x y 0 fuel (by omega)
        (fun j hj1 hjm => hbefore j hj1 (by omega))]
  -- one more step off the fast-forwarded scan
  have hfuel : fuel - (K - 1) = (fuel - K) + 1 := by omega
  rw [hfuel, raycastFuel]
  -- reconcile x + (K-1)dx + dx = x + K dx, and 0 + (K-1) + 1 = K
  have exK : x + ((K - 1 : Nat) : Int) * dx + dx = x + (K : Int) * dx := by
    have : ((K - 1 : Nat) : Int) = (K : Int) - 1 := by
      rw [Nat.cast_sub hK]; simp
    rw [this]; ring
  have eyK : y + ((K - 1 : Nat) : Int) * dy + dy = y + (K : Int) * dy := by
    have : ((K - 1 : Nat) : Int) = (K : Int) - 1 := by
      rw [Nat.cast_sub hK]; simp
    rw [this]; ring
  have edK : 0 + (K - 1) + 1 = K := by omega
  rw [exK, eyK, edK]

/-! ## §2 — The n-generic step board decode + the four-ray landing interface.

`boardDecodeN` reads a satisfying row of `automataflStepDescN n` back into the reference `Board` at
size `n` (the `n`-generic twin of `AutomataflStepRefine.boardDecode`, which froze `NN = 2`).
`raycast_of_hit` is the SINGLE landing lemma every ray-of-sat proof calls: it unfolds the reference
`Board.raycast` onto the `raycastFuel` scan and discharges it through `raycast_at_hit` — one statement
covering all four cardinal directions at any board size. What a per-ray circuit extraction must still
supply to CALL it is the hit index `K` and the strictly-before in-bounds/vacuum facts (the residual
wiring; see §3). -/

/-- Decode a satisfying `automataflStepDescN n` row's OLD-board columns into the reference `Board` at
size `n`: the auto at `(AX n, AY n)`, cell `(x,y)` the felt-decode of `old[y·n+x]`. -/
def boardDecodeN (n : Nat) (e : VmRowEnv) : Board where
  size          := n
  automaton     := ⟨(e.loc (AX n)).toNat, (e.loc (AY n)).toNat⟩
  cells         := fun c => codeToParticle (e.loc (old n (c.y * n + c.x)))
  useColumnRule := true

@[simp] theorem boardDecodeN_size (n : Nat) (e : VmRowEnv) : (boardDecodeN n e).size = n := rfl

/-- **THE FOUR-RAY LANDING LEMMA.** For ANY cardinal `d` and board size `n`, the reference
`Board.raycast` of the decoded board collapses — via the fuel induction — to the single read at the
hit step `K`, provided the ray is in-bounds and vacuum at every step strictly before `K`
(`1 ≤ K ≤ n`). This is the semantic value each ray's witnessed `(dist, what)` must match; it sits
directly on `raycast_at_hit`, so a ray-of-sat proof reduces to supplying `K` and the before-facts. -/
theorem raycast_of_hit (n : Nat) (e : VmRowEnv) (d : Dir) (K : Nat)
    (hK : 1 ≤ K) (hKn : K ≤ n)
    (hbefore : ∀ j, 1 ≤ j → j < K →
      (0 ≤ ((boardDecodeN n e).automaton.x : Int) + (j : Int) * d.delta.1
        ∧ ((boardDecodeN n e).automaton.x : Int) + (j : Int) * d.delta.1 < (n : Int)
        ∧ 0 ≤ ((boardDecodeN n e).automaton.y : Int) + (j : Int) * d.delta.2
        ∧ ((boardDecodeN n e).automaton.y : Int) + (j : Int) * d.delta.2 < (n : Int))
      ∧ ((boardDecodeN n e).cellAt
          ⟨(((boardDecodeN n e).automaton.x : Int) + (j : Int) * d.delta.1).toNat,
           (((boardDecodeN n e).automaton.y : Int) + (j : Int) * d.delta.2).toNat⟩).isVacuum
          = true) :
    Board.raycast (boardDecodeN n e) (boardDecodeN n e).automaton d
      = if (0 ≤ ((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1
            ∧ ((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1 < (n : Int)
            ∧ 0 ≤ ((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2
            ∧ ((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2 < (n : Int))
        then (if ((boardDecodeN n e).cellAt
                    ⟨(((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1).toNat,
                     (((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2).toNat⟩).isVacuum
              then raycastFuel (boardDecodeN n e)
                     (((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1)
                     (((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2)
                     d.delta.1 d.delta.2 K (n + 1 - K)
              else { what := (boardDecodeN n e).cellAt
                       ⟨(((boardDecodeN n e).automaton.x : Int) + (K : Int) * d.delta.1).toNat,
                        (((boardDecodeN n e).automaton.y : Int) + (K : Int) * d.delta.2).toNat⟩,
                     dist := K })
        else { what := .vacuum, dist := K } := by
  have h := raycast_at_hit (boardDecodeN n e)
    ((boardDecodeN n e).automaton.x : Int) ((boardDecodeN n e).automaton.y : Int)
    d.delta.1 d.delta.2 K (n + 1) hK (by omega) hbefore
  simpa only [Board.raycast, boardDecodeN_size] using h

/-! ## §3 — Axiom pins. -/

#assert_axioms raycastFuel_succ_vac
#assert_axioms raycastFuel_scan
#assert_axioms raycast_at_hit
#assert_axioms raycast_of_hit

end Dregg2.Circuit.Emit.AutomataflStepCapstone
