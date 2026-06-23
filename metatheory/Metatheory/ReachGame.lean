/-
# Metatheory.ReachGame — the REACHABILITY game / attractor (the μ-dual of the viability kernel).

`SafetyGame` builds the viability kernel `K = νX. floor ∧ CPre X` (a GREATEST fixpoint, `gfp`): the
maximal region from which the controller can keep the floor FOREVER. Safety is a `ν`.

This file builds its dual — the **attractor** of a target set `home`:

    Attr home = μX. home ∨ (floor ∧ CPre X)        (a LEAST fixpoint, `lfp`)

the set of worlds from which the controller can FORCE arrival at `home` in finitely many steps,
never leaving the floor on the way. Reachability is a `μ`. (gpt5.5's caution, made literal:
safety = `gfp`/`ν`, reachability = `lfp`/`μ`.) The two genuinely differ — `Attr` is the LEAST set
closed under "home, or one controllable step into the set"; the kernel is the GREATEST set closed
under "floor and one controllable step staying in the set."

Three facts on the `lfp` object:
  * `attr_unfold` — `Attr` is the fixpoint: `home ∨ (floor ∧ CPre Attr) = Attr`.
  * `home_subset_attr` — the target is reachable from itself (`home ⊆ Attr`).
  * `attr_least` — `Attr` is the LEAST such: any `X ⊇ home` closed under `floor ∧ CPre` contains it
    (`OrderHom.lfp_le`). This is what makes a *bounded* under-approximation `reachWithin n` SOUND.

Then the monitorable face: `reachWithin : Nat → World → Prop`, an explicit `n`-step unfolding
(decidable whenever `home`/`floor`/the move-space are), with
  * `reachWithin_mono` (a spare tick never hurts), `reachWithin_subset_succ` (the `n`-step set sits
    inside the `n+1`-step set), and
  * `reachWithin_sound` — `reachWithin n w → Attr w` (every bounded witness is a genuine attractor
    member, via `attr_least`). Bounded reach is the enforceable/monitorable one — you can *check* it
    at a horizon; the unbounded `Attr` is the spec it under-approximates.

Connection: `PolisSandboxLiveness.reachHome` IS `reachWithin` for the gate game (target = "home now",
one move = the victim's step through an open gate). Recorded as `reachHome_is_reachWithin_shape`.

`#guard` asserts TRUE props (`decide` tells the truth).
-/
import Mathlib.Order.FixedPoints
import Metatheory.SafetyGame
import Metatheory.PolisSandboxLongGame

namespace Metatheory.ReachGame

open Metatheory.SafetyGame

universe u

variable (G : Game)

/-! ## §1. The attractor as a least fixpoint. -/

/-- The reachability functional `Ψ X = home ∨ (floor ∧ CPre X)`, monotone on `World → Prop`. A world
is in `Ψ X` iff it is already `home`, or it satisfies the floor AND there is a controllable move
landing every adversary response into `X`. -/
def Ψ (home : G.World → Prop) : (G.World → Prop) →o (G.World → Prop) where
  toFun X := fun w => home w ∨ (G.floor w ∧ CPre G X w)
  monotone' := by
    intro X Y hXY w hw
    rcases hw with hh | ⟨hf, hc⟩
    · exact Or.inl hh
    · exact Or.inr ⟨hf, CPre_mono G hXY w hc⟩

/-- **The attractor** of `home` — the LEAST set from which the controller can force arrival at
`home` while never leaving the floor (`μX. home ∨ (floor ∧ CPre X)`). -/
def Attr (home : G.World → Prop) : G.World → Prop := OrderHom.lfp (Ψ G home)

/-- **`attr_unfold`** — the attractor is its own `Ψ`-image: `home ∨ (floor ∧ CPre Attr) = Attr`. -/
theorem attr_unfold (home : G.World → Prop) :
    Ψ G home (Attr G home) = Attr G home :=
  OrderHom.map_lfp (Ψ G home)

/-- **`home_subset_attr`** — the target is reachable from itself: every `home` world is in `Attr`
(zero steps to arrival). -/
theorem home_subset_attr (home : G.World → Prop) (w : G.World) (h : home w) :
    Attr G home w := by
  have := attr_unfold G home
  rw [← this]
  exact Or.inl h

/-- A one-step ingress: a floor world with a controllable move into the attractor is in the
attractor. (The other arm of `attr_unfold`, named for use.) -/
theorem step_into_attr (home : G.World → Prop) (w : G.World)
    (hf : G.floor w) (hc : CPre G (Attr G home) w) : Attr G home w := by
  have := attr_unfold G home
  rw [← this]
  exact Or.inr ⟨hf, hc⟩

/-- **`attr_least`** — the attractor is the LEAST set closed under `Ψ`: any `X` that contains `home`
and is closed under `floor ∧ CPre` (i.e. `Ψ home X ⊆ X`) already contains the whole attractor. This
is the soundness backbone — a bounded under-approximation cannot escape the true attractor. -/
theorem attr_least (home : G.World → Prop) (X : G.World → Prop)
    (hX : ∀ w, (home w ∨ (G.floor w ∧ CPre G X w)) → X w) :
    ∀ w, Attr G home w → X w :=
  OrderHom.lfp_le (Ψ G home) (fun w hw => hX w hw)

/-! ## §2. The bounded, monitorable attractor — `reachWithin`.

The `lfp` is the spec; `reachWithin n` is the *checkable* under-approximation at horizon `n`: "the
controller can force `home` within `n` steps, never leaving the floor." It is decidable whenever the
target/floor are decidable and `Move` is a finite/searchable space (the `∃ m` in `CPre`). -/

/-- **`reachWithin n w`** — the controller can force arrival at `home` within `n` steps without ever
leaving the floor: either `w` is already `home`, or `w` satisfies the floor and some controllable
move lands every adversary response into a world reachable within `n` more steps. The explicit
`n`-step unfolding of `Ψ`. -/
def reachWithin (home : G.World → Prop) : Nat → G.World → Prop
  | 0,     w => home w
  | n + 1, w => home w ∨ (G.floor w ∧ CPre G (reachWithin home n) w)

/-- **`reachWithin_subset_succ`** — the `n`-step reachable set sits inside the `n+1`-step set: a spare
tick can only add worlds. (Mutually with `reachWithin_mono`, this is "horizon only helps".) -/
theorem reachWithin_subset_succ (home : G.World → Prop) :
    ∀ (n : Nat) (w : G.World), reachWithin G home n w → reachWithin G home (n + 1) w := by
  intro n
  induction n with
  | zero =>
      intro w h
      -- `reachWithin 0 w = home w`; then `reachWithin 1 w = home w ∨ …`.
      exact Or.inl h
  | succ k ih =>
      intro w h
      -- Peel: either already home (stays home), or a floor world stepping into the `k`-set, which
      -- by IH is also the `k+1`-set.
      rcases h with hh | ⟨hf, hc⟩
      · exact Or.inl hh
      · exact Or.inr ⟨hf, CPre_mono G (ih) w hc⟩

/-- **`reachWithin_mono`** — `reachWithin` is monotone in the horizon: if reachable within `m`, then
reachable within any `n ≥ m`. (The set form: `m ≤ n → reachWithin m ⊆ reachWithin n`.) -/
theorem reachWithin_mono (home : G.World → Prop) {m n : Nat} (hmn : m ≤ n) :
    ∀ (w : G.World), reachWithin G home m w → reachWithin G home n w := by
  induction hmn with
  | refl => exact fun _ h => h
  | step _ ih =>
      intro w h
      exact reachWithin_subset_succ G home _ w (ih w h)

/-- **`reachWithin_sound`** — every bounded witness is a genuine attractor member: `reachWithin n w`
implies `Attr w`. Proven by induction on the horizon `n`, using `home_subset_attr` and the one-step
ingress `step_into_attr` (the attractor is closed under exactly `reachWithin`'s two formation rules).
This is why a horizon-`n` monitor is *sound* for the unbounded reachability spec. -/
theorem reachWithin_sound (home : G.World → Prop) :
    ∀ (n : Nat) (w : G.World), reachWithin G home n w → Attr G home w := by
  intro n
  induction n with
  | zero =>
      intro w h
      -- `reachWithin 0 w = home w`; home worlds are in the attractor.
      exact home_subset_attr G home w h
  | succ k ih =>
      intro w h
      rcases h with hh | ⟨hf, hc⟩
      · exact home_subset_attr G home w hh
      · -- A floor world with a controllable move into the `k`-set; by IH that lands in `Attr`, so
        -- `w` enters via the one-step ingress.
        exact step_into_attr G home w hf (CPre_mono G (ih) w hc)

/-- The exact converse-direction bridge to the spec, packaged: the bounded family is an increasing
chain of under-approximations of `Attr` (each `reachWithin n ⊆ reachWithin (n+1) ⊆ Attr`). -/
theorem reachWithin_chain_under_attr (home : G.World → Prop) (n : Nat) (w : G.World)
    (h : reachWithin G home n w) :
    reachWithin G home (n + 1) w ∧ Attr G home w :=
  ⟨reachWithin_subset_succ G home n w h, reachWithin_sound G home n w h⟩

end Metatheory.ReachGame

/-! ## §3. Connection — `PolisSandboxLiveness.reachHome` is `reachWithin` for the gate game.

The gate game's `reachHome : Nat → GW → Bool` is `reachWithin` specialized to the deterministic gate
world: the target `home := (vdist = 0)`, the floor trivial, and the single controllable move = the
victim's step through an open gate (`vdist ↦ vdist - 1`, gated on `gate = true`). Its recursion

    reachHome 0       w = (w.vdist == 0)
    reachHome (k + 1) w = (w.vdist == 0) || (w.gate && reachHome k {w with vdist := w.vdist - 1})

is exactly `reachWithin`'s `home w ∨ (floor w ∧ CPre … w)` with the disjunction as `||`, the floor
absorbed into the gate guard, and `CPre`'s `∃ move` collapsed to the one deterministic victim step.
We record this as a runnable shape-equality on the gate game's own `reachHome`, so the abstract
soundness above applies to the concrete liveness monitor used in `PolisSandboxLiveness`. -/

namespace Metatheory.ReachGame.GateConnection

open Metatheory.PolisSandboxLongGame

/-- The gate game's `reachHome` IS the `reachWithin`-shape recursion: at every horizon it is the
disjunction of "home now" with "one gated victim step into the next horizon's reach-set". This is the
definitional unfold the abstract `reachWithin` mirrors (`home ∨ step-into-the-n-set`). -/
theorem reachHome_is_reachWithin_shape (k : Nat) (w : GW) :
    reachHome (k + 1) w
      = (w.vdist == 0 || (w.gate && reachHome k { w with vdist := w.vdist - 1 })) := rfl

/-- And the base case is "home now" (`reachWithin 0`). -/
theorem reachHome_base_is_home (w : GW) :
    reachHome 0 w = (w.vdist == 0) := rfl

-- The gate game's monitor agrees with the `reachWithin` shape: from `start` (3 from home, gate open)
-- the victim is reach-home within budget, and the bounded family is monotone in the horizon.
#guard reachHome budget start == true
#guard reachHome (budget + 1) start == true            -- a spare tick never hurts
#guard reachHome 0 (⟨0, false⟩ : GW) == true           -- already home, any gate
#guard reachHome 3 (⟨3, true⟩  : GW) == true            -- exactly enough open-gate steps
#guard reachHome 2 (⟨3, true⟩  : GW) == false           -- one tick short — bounded under-approx bites

/-- **`reachHome_shape_monotone`** — concretely, the gate monitor is horizon-monotone (the runnable
witness of `reachWithin_mono` for this game): reach within `3` ⟹ reach within `4`, from a typical
start. Proven by `decide` (the monitor is decidable — the whole point of the bounded face). -/
theorem reachHome_shape_monotone :
    (reachHome 3 (⟨3, true⟩ : GW) = true → reachHome 4 (⟨3, true⟩ : GW) = true)
      ∧ reachHome 2 (⟨3, true⟩ : GW) = false := by decide

end Metatheory.ReachGame.GateConnection
