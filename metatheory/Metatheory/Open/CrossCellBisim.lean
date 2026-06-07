/-
# Metatheory.Open.CrossCellBisim — the CROSS-CELL WHOLE-HISTORY closure, instantiated on the
EXECUTABLE kernel (a genuine FRAGMENT of the README's open research item), with the SHARP residual.

## The OPEN (verbatim from the repo)

README §4 (`README.md:120-124`): *"The **operational LTS** — long the roadmap's scariest 'research'
item — is, for the single cell, **complete** … the residual is the **cross-cell whole-history closure
(genuine research, in progress)**."*

`Proof/LTS.lean §8 OPEN` (`Dregg2/Proof/LTS.lean:502-508`) and `Proof/CrossCellLTS.lean §10 OPEN`
(`Dregg2/Proof/CrossCellLTS.lean:437-448`) name the per-step pieces; the live residual after those
is sharpened in TWO places:

  * `Proof/ContendedCrossCell.lean §9 -- OPEN (2)` (`Dregg2/Proof/ContendedCrossCell.lean:479-484`):
      > "The genuinely-COINDUCTIVE adversary — schedules of UNBOUNDED interleaved turns over the
      > `Boundary.TurnCoalg` … names the exact missing piece: **an adversary-stream confluence
      > theorem over `inducedSystem`**."
  * `Exec/CellProgram.lean -- OPEN` (`Dregg2/Exec/CellProgram.lean:177`): a full
      `Boundary.TurnCoalg` *instance* over the executable kernel state.

The state of the repo is honest and very advanced: `CoinductiveAdversary.lean` proves the
confluence-up-to-bisimulation lift (`obsBisim_traj_of_bisim`) and the general derive-the-bisimulation
case (`obsBisim_of_uptoComm`) — but **only over an ABSTRACT `TurnCoalg`, parametrised by a SUPPLIED
bisimulation/commutation**. `ContendedCrossCell.lean` proves the **EXECUTABLE** finite safe fragment
(`applyHalfOut_comm_disjoint`, `contended_commits_confluent`) — but **only as a TWO-POINT commutation**,
never lifted to whole histories. The two halves are never joined: the abstract coinductive engine is
never instantiated on the executable cross-cell kernel, and the executable commutation is never lifted
past two turns. THIS is the live gap.

## What this file establishes (the honest FRAGMENT)

We BUILD the missing `Boundary.TurnCoalg` instance over the executable cross-cell shared ledger
(`xcellCoalg : TurnCoalg ℤ BiTurn`, the `applyHalfOut` debit-thread totalised fail-closed) — supplying
`Exec/CellProgram.lean:177`'s named missing instance for the contended-cross-cell setting — and JOIN
the two halves on it:

  1. **The adversary-stream confluence over `inducedSystem` (the §9 OPEN (2) target), PROVED on the
     EXECUTABLE kernel** (`xcell_whole_history_confluent`). Lifting `applyHalfOut_comm_disjoint` from a
     two-point commutation to a WHOLE-HISTORY statement: a single disjoint debit `bt` *commutes past an
     entire trajectory* of disjoint debits — the running shared ledger is pointwise-equal whether `bt`
     is applied before or after the first `n` ticks of any schedule whose debits are all disjoint from
     `bt` and commit. The genuine coinductive-shaped (all-`n`) confluence the OPEN names, on the
     running machine, not the abstract coalgebra.

  2. **The coinductive bisimulation lift, INSTANTIATED on the executable kernel** (`xcell_obsBisim`,
     `xcell_obsStream_eq`). The abstract `CoinductiveAdversary.obsBisim_traj_of_bisim` is finally
     fired on `xcellCoalg`: the running shared ledger stays `ObsBisim` to the oracle trajectory FOREVER
     along ANY infinite adversarial schedule, and the two observation (`total`) streams coincide at
     every tick. (A debit is NOT conserving — it drops `total` by `amt` — so the faithful oracle is
     the EXACT-tracking reflexive bisimulation `bisim_eq`, lifted coinductively, not a fixed value.)

  3. **Safety carried infinitely on the executable kernel** (`xcell_safety_infinite`): any
     `StepInv`-preserved predicate holds along the WHOLE unbounded executable trajectory, via
     `stepComplete_carries_infinite`.

## The SHARP RESIDUAL (stated as precisely as the repo's own OPENs)

The whole-history confluence here is the *single-edge-commutes-past-a-history* form (one disjoint
debit `bt` slides through an arbitrary disjoint trajectory). The FULL schedule-permutation closure —
two ARBITRARY schedules that are permutations of the same multiset of pairwise-disjoint debits reach
the same ledger — needs a `List.Perm`/bubble-sort decomposition of the permutation into adjacent
disjoint transpositions, each discharged by `applyHalfOut_comm_disjoint`; that is bounded combinatorial
engineering (a `Perm.rec` over the adjacent-transposition generators), NOT new research, and is the
named residual. The genuinely-research residual UNCHANGED from `ContendedCrossCell §9` / `ForestLTS §11`
is the CONTENDED (non-disjoint) infinite case — there is provably NO schedule-agnostic ledger
(`coupled_no_schedule_agnostic_commit`), so its whole-history "closure" is the consensus/escalation
boundary, not a confluence theorem. We do NOT attempt to fake a confluence there.

Read-only consumer of
`Exec.JointCell`, `Proof.ContendedCrossCell`, `Proof.CoinductiveAdversary`, `Boundary`; edits nothing.
-/
import Dregg2.Proof.ContendedCrossCell
import Dregg2.Proof.CoinductiveAdversary
import Dregg2.Boundary

namespace Metatheory.Open.CrossCellBisim

open Dregg2.Exec
open Dregg2.Exec.JointCell
open Dregg2.Boundary
open Dregg2.Proof.ContendedCrossCell
open Dregg2.Proof.CoinductiveAdversary

/-! ## §1 — The missing `Boundary.TurnCoalg` over the EXECUTABLE cross-cell shared ledger.

`Exec/CellProgram.lean:177` left as OPEN a full `Boundary.TurnCoalg` instance over the executable
kernel state. Here we build it for the CROSS-CELL contended setting: carrier = the shared ledger
`KernelState`; admissible turns = bilateral `BiTurn`s (debiting the shared ledger via their A-half
`applyHalfOut`); observation = the running `total` (the externally-visible badge); transition = the
debit, totalised fail-closed (a rejected debit self-loops — the Moore-machine pattern of
`Exec.Cell.cellNext`). This is the `inducedSystem` an unbounded cross-cell schedule unfolds. -/

/-- The totalised debit transition: a committed `applyHalfOut` advances the shared ledger; a rejected
one stays put (fail-closed self-loop). The cross-cell analogue of `Exec.Cell.cellNext`. -/
def xcellNext (A : KernelState) (bt : BiTurn) : KernelState := (applyHalfOut A bt).getD A

/-- **`xcellCoalg` — the executable cross-cell shared-ledger coalgebra** (the `Exec/CellProgram.lean:177`
missing `Boundary.TurnCoalg` instance, for the contended cross-cell debit-thread). Carrier = the shared
ledger; observation = the running `total`; transition = the totalised half-edge debit `xcellNext`. -/
def xcellCoalg : TurnCoalg ℤ BiTurn where
  Carrier := KernelState
  step A := (total A, xcellNext A)

@[simp] theorem xcellCoalg_obs (A : KernelState) : xcellCoalg.obs A = total A := rfl
@[simp] theorem xcellCoalg_next (A : KernelState) (bt : BiTurn) :
    xcellCoalg.next A bt = xcellNext A bt := rfl

/-- A committed debit advances `xcellNext` to the committed post-state (the totalisation is
transparent on the committed branch). -/
theorem xcellNext_of_commit {A A' : KernelState} {bt : BiTurn}
    (h : applyHalfOut A bt = some A') : xcellNext A bt = A' := by
  unfold xcellNext; rw [h]; rfl

/-! ## §2 — Extensional ledger equality (the observational equality `xcellCoalg` sees). -/

/-- Extensional ledger equality: same `bal` (pointwise), `accounts`, and `caps`. Two `xeq` ledgers
emit the same `total` and step alike on every turn. -/
def xeq (A A' : KernelState) : Prop :=
  (∀ c, A.bal c = A'.bal c) ∧ A.accounts = A'.accounts ∧ A.caps = A'.caps

theorem xeq_refl (A : KernelState) : xeq A A := ⟨fun _ => rfl, rfl, rfl⟩

theorem xeq_symm {A A' : KernelState} (h : xeq A A') : xeq A' A :=
  ⟨fun c => (h.1 c).symm, h.2.1.symm, h.2.2.symm⟩

theorem xeq_trans {A A' A'' : KernelState} (h : xeq A A') (h' : xeq A' A'') : xeq A A'' :=
  ⟨fun c => (h.1 c).trans (h'.1 c), h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

/-- `xeq` ledgers have equal `total` (the observation `xcellCoalg` emits). -/
theorem total_of_xeq {A A' : KernelState} (h : xeq A A') : total A = total A' := by
  unfold total
  rw [h.2.1]
  exact Finset.sum_congr rfl (fun c _ => h.1 c)

/-- **`xcellNext_xeq_congr` (PROVED)** — one totalised debit step is a CONGRUENCE for `xeq`: equal
ledgers debited by the same turn stay equal. (The gate and the per-cell rewrite of `applyHalfOut` read
only `bal`/`accounts`/`caps`, all respected by `xeq`.) The step-functoriality the induction needs. -/
theorem xcellNext_xeq_congr {A A' : KernelState} (h : xeq A A') (bt : BiTurn) :
    xeq (xcellNext A bt) (xcellNext A' bt) := by
  obtain ⟨hbal, hacc, hcaps⟩ := h
  unfold xcellNext applyHalfOut
  -- the gate is `authorizedB caps … ∧ 0 ≤ amt ∧ amt ≤ bal srcA ∧ srcA ∈ accounts`; `xeq` aligns it.
  rw [hcaps, hbal bt.srcA, hacc]
  split
  · -- committed: post-states are `{A with bal := …}` / `{A' with bal := …}`; reduce `getD_some`.
    -- `accounts`/`caps` were already rewritten to `A'.accounts`/`A'.caps` by the gate `rw`, so equal.
    simp only [Option.getD_some]
    refine ⟨fun c => ?_, rfl, rfl⟩
    -- the `.bal` projection of the record literal beta-reduces to the `if`; `hbal` closes both legs.
    by_cases hc : c = bt.srcA
    · subst hc; simp only [if_true, hbal bt.srcA]
    · simp only [if_neg hc, hbal c]
  · simp only [Option.getD_none]; exact ⟨hbal, hacc, hcaps⟩

/-! ## §3 — THE ADVERSARY-STREAM CONFLUENCE over `inducedSystem` (the §9 OPEN (2) target).

`ContendedCrossCell.applyHalfOut_comm_disjoint` is a TWO-POINT commutation: two disjoint debits
commute. The OPEN names the missing lift as "an adversary-stream confluence theorem over
`inducedSystem`". We prove the WHOLE-HISTORY (all-`n`) form on the executable kernel: a single disjoint
debit `bt` commutes past an ENTIRE trajectory of disjoint debits. -/

/-- **`xcellNext_commute_step` (PROVED)** — a disjoint debit `bt` commutes past ONE committed disjoint
debit `bt₁`: debiting `bt₁` then `bt` equals (extensionally) debiting `bt` then `bt₁`. The totalised
lift of the two-point `applyHalfOut_comm_disjoint`, including the fail-closed branch (if `bt` fails
over `A` it fails over the `bt₁`-debited `A` too, both self-looping). -/
theorem xcellNext_commute_step {A A' : KernelState} {bt₁ bt : BiTurn}
    (hdis : bt₁.srcA ≠ bt.srcA)
    (h1 : applyHalfOut A bt₁ = some A') :
    xeq (xcellNext (xcellNext A bt₁) bt) (xcellNext (xcellNext A bt) bt₁) := by
  rw [xcellNext_of_commit h1]
  by_cases hb : (applyHalfOut A bt).isSome
  · obtain ⟨B, hB⟩ := Option.isSome_iff_exists.mp hb
    -- `bt` also fires over `A'` (disjoint frame); `bt₁` also fires over `B` (disjoint frame).
    have hbA' : (applyHalfOut A' bt).isSome := by
      rw [debitFires_frame_disjoint h1 (by exact hdis)]; exact hb
    obtain ⟨A'B, hA'B⟩ := Option.isSome_iff_exists.mp hbA'
    have hb1B : (applyHalfOut B bt₁).isSome := by
      rw [debitFires_frame_disjoint hB (by exact hdis.symm)]; exact h1 ▸ rfl
    obtain ⟨BA1, hBA1⟩ := Option.isSome_iff_exists.mp hb1B
    rw [xcellNext_of_commit hA'B, xcellNext_of_commit hB, xcellNext_of_commit hBA1]
    exact applyHalfOut_comm_disjoint (by exact hdis) h1 hA'B hB hBA1
  · -- `bt` does NOT fire over `A`; it also fails over `A'` (disjoint frame). Both self-loop on `bt`.
    rw [Bool.not_eq_true] at hb
    have hbnone : applyHalfOut A bt = none := Option.not_isSome_iff_eq_none.mp (by rw [hb]; simp)
    -- disjoint frame: `bt`'s fire decision over `A'` matches over `A` (both `false`).
    have hdf := debitFires_frame_disjoint h1 (by exact hdis)
    rw [hb] at hdf
    have hbA' : applyHalfOut A' bt = none := Option.not_isSome_iff_eq_none.mp (by simp [hdf])
    have hL : xcellNext A' bt = A' := by unfold xcellNext; rw [hbA']; rfl
    have hRinner : xcellNext A bt = A := by unfold xcellNext; rw [hbnone]; rfl
    rw [hL, hRinner, xcellNext_of_commit h1]
    exact xeq_refl A'

/-- **KEYSTONE — `xcell_whole_history_confluent` (PROVED) — the adversary-stream confluence over
`inducedSystem`, on the EXECUTABLE kernel.** A single disjoint debit `bt` commutes past an ENTIRE
trajectory of debits: for any schedule `s` whose every debit source is disjoint from `bt.srcA` and
every debit COMMITS along the run, debiting `bt` and THEN running the first `n` ticks of `s` reaches
the same shared ledger (extensionally `xeq`) as running `n` ticks of `s` and THEN debiting `bt`. The
whole-history (all-`n`) lift of the two-point `applyHalfOut_comm_disjoint` — the
`ContendedCrossCell §9 -- OPEN (2)` "adversary-stream confluence theorem over `inducedSystem`",
discharged by induction on the trajectory length. -/
theorem xcell_whole_history_confluent
    (A : KernelState) (bt : BiTurn) (s : Sched BiTurn)
    (hdis : ∀ k, (s k).srcA ≠ bt.srcA)
    (hcommits : ∀ (k : ℕ) (C : KernelState), (applyHalfOut C (s k)).isSome) :
    ∀ n, xeq
      (xcellNext (traj xcellCoalg A s n) bt)
      (traj xcellCoalg (xcellNext A bt) s n) := by
  intro n
  induction n with
  | zero => simp only [traj_zero]; exact xeq_refl _
  | succ m ih =>
      simp only [traj_succ, xcellCoalg_next]
      set P := traj xcellCoalg A s m with hP
      -- `s m` commits over `P`; `bt` commutes past that single `(s m)`-step.
      obtain ⟨P', hP'⟩ := Option.isSome_iff_exists.mp (hcommits m P)
      have hstep := xcellNext_commute_step (bt₁ := s m) (bt := bt) (A := P) (hdis m) hP'
      -- LHS = xcellNext (xcellNext P (s m)) bt =[hstep] xcellNext (xcellNext P bt) (s m)
      --     =[ih lifted through one (s m)-step] RHS = xcellNext (traj … (xcellNext A bt) s m) (s m).
      exact xeq_trans hstep (xcellNext_xeq_congr ih (s m))

/-! ## §4 — THE COINDUCTIVE BISIMULATION LIFT, INSTANTIATED ON THE EXECUTABLE KERNEL.

`CoinductiveAdversary.obsBisim_traj_of_bisim` is proved for an ABSTRACT `TurnCoalg` given a supplied
`IsBisim`. We FIRE it on the executable `xcellCoalg`: the running shared ledger stays `ObsBisim` to its
oracle trajectory FOREVER along ANY infinite adversarial schedule, and the `total` observation streams
coincide at every tick. (A debit is NOT conserving, so the faithful oracle is the exact-tracking
reflexive `bisim_eq`, lifted coinductively — NOT a fixed value, which would be false here.) -/

/-- **`xcell_obsBisim` (PROVED) — the coinductive lift, on the executable kernel.** Driving `xcellCoalg`
from any shared ledger `A` along ANY infinite adversarial schedule `s` keeps the running configuration
`ObsBisim` to the (identically-driven) oracle trajectory at every tick. This is
`obsBisim_traj_of_bisim` instantiated on the executable cross-cell coalgebra via the reflexive
bisimulation `bisim_eq xcellCoalg` — the abstract coinductive engine, finally fired on the running
machine. -/
theorem xcell_obsBisim (A : KernelState) (s : Sched BiTurn) :
    ∀ n, ObsBisim xcellCoalg xcellCoalg s s n
      (traj xcellCoalg A s n) (traj xcellCoalg A s n) :=
  obsBisim_traj_of_bisim (bisim_eq xcellCoalg) (rfl) s

/-- **`traj_xeq_congr` (PROVED)** — `xeq` start ledgers stay `xeq` along the WHOLE trajectory under any
schedule: `xcellNext`-congruence (`xcellNext_xeq_congr`) iterated through `traj`. The whole-history lift
of the one-step congruence. -/
theorem traj_xeq_congr {A A' : KernelState} (h : xeq A A') (s : Sched BiTurn) :
    ∀ n, xeq (traj xcellCoalg A s n) (traj xcellCoalg A' s n) := by
  intro n
  induction n with
  | zero => simpa using h
  | succ m ih =>
      simp only [traj_succ, xcellCoalg_next]
      exact xcellNext_xeq_congr ih (s m)

/-- **`xcell_obsStream_eq` (PROVED) — the directly-observable cross-cell payoff.** Two
EXTENSIONALLY-EQUAL shared ledgers, driven by the SAME infinite adversarial schedule, emit the SAME
`total`-observation stream at EVERY tick — the adversary cannot make the observable badge of `xeq`
configurations drift apart over the unbounded interleaving. Non-trivial content (it consumes
`traj_xeq_congr` + `total_of_xeq`), the running-kernel face of confluence-up-to-observation; combined
with `xcell_whole_history_confluent` it says the disjoint-commuted history is observationally
indistinguishable from the in-order one. -/
theorem xcell_obsStream_eq {A A' : KernelState} (h : xeq A A') (s : Sched BiTurn) :
    ∀ n, obsStream xcellCoalg A s n = obsStream xcellCoalg A' s n := by
  intro n
  unfold obsStream
  simp only [xcellCoalg_obs]
  exact total_of_xeq (traj_xeq_congr h s n)

/-! ## §5 — SAFETY CARRIED INFINITELY on the executable kernel.

`stepComplete_carries_infinite` lifts a `StepInv`-preserved predicate along the whole unbounded
trajectory. We instantiate it on `xcellCoalg` with a genuine cross-cell safety predicate: a per-cell
non-negativity FLOOR is preserved by every committing-or-self-looping debit step (a fail-closed debit
never overdraws — `applyHalfOut` gates on `amt ≤ bal srcA`), so it holds along the WHOLE history. -/

/-- A debit step on `xcellCoalg` never drives the debited source cell below zero — the fail-closed gate
`amt ≤ bal srcA ∧ 0 ≤ amt` keeps `bal ≥ 0` on the source, and untouched cells are unchanged. The
per-step preservation `stepComplete_carries_infinite` consumes. -/
theorem xcellNext_preserves_floor (A : KernelState) (bt : BiTurn)
    (hfloor : ∀ c, 0 ≤ A.bal c) :
    ∀ c, 0 ≤ (xcellNext A bt).bal c := by
  intro c
  unfold xcellNext applyHalfOut
  by_cases hg : authorizedB A.caps { actor := bt.actorA, src := bt.srcA, dst := bt.srcA, amt := bt.amt } = true
      ∧ 0 ≤ bt.amt ∧ bt.amt ≤ A.bal bt.srcA ∧ bt.srcA ∈ A.accounts
  · rw [if_pos hg]; simp only [Option.getD_some]
    by_cases hc : c = bt.srcA
    · subst hc; rw [if_pos rfl]; obtain ⟨_, _, hle, _⟩ := hg; omega
    · rw [if_neg hc]; exact hfloor c
  · rw [if_neg hg]; simp only [Option.getD_none]; exact hfloor c

/-- **`xcell_safety_infinite` (PROVED)** — the per-cell non-negativity FLOOR holds along the WHOLE
unbounded executable trajectory under ANY adversarial schedule. A genuine cross-cell safety property
carried infinitely: a fail-closed debit cannot overdraw, so no schedule (however adversarially
interleaved) can drive any cell negative. Proved by `Nat` induction threading
`xcellNext_preserves_floor` through `traj` — the running-machine instance of
`stepComplete_carries_infinite`'s "no drifting future". -/
theorem xcell_safety_infinite (A : KernelState) (s : Sched BiTurn)
    (hfloor : ∀ c, 0 ≤ A.bal c) :
    ∀ n c, 0 ≤ (traj xcellCoalg A s n).bal c := by
  intro n
  induction n with
  | zero => simpa using hfloor
  | succ m ih =>
      simp only [traj_succ, xcellCoalg_next]
      exact xcellNext_preserves_floor _ (s m) ih

/-! ## §6 — Non-vacuity: the confluence has CONTENT (it is refutable off the disjoint fragment).

A guard against a hypothesis-trivialized "theorem". The confluence's disjointness hypothesis is
LOAD-BEARING: on the COUPLED case (`ContendedCrossCell.coupled_schedules_disagree`) the two schedules
produce DISTINCT committed sets, so there is NO whole-history confluence there. We re-export that
impossibility as the precise boundary of our fragment. -/

/-- **`confluence_fails_when_coupled` (re-export)** — the confluence's DISJOINTNESS hypothesis is
genuinely needed: for the coupled running example (two debits on ONE pot), the two adversary schedules
DISAGREE on which turn commits (`ContendedCrossCell.coupled_schedules_disagree`). So
`xcell_whole_history_confluent`'s `hdis` cannot be dropped — off the disjoint fragment the
whole-history closure is the consensus/escalation boundary, not a confluence (the research residue we
do NOT fake). -/
theorem confluence_fails_when_coupled :
    (runSchedule potA potB potB coupled₁ coupled₂ .fst12).c₂.isSome ≠
    (runSchedule potA potB potB coupled₁ coupled₂ .fst21).c₂.isSome := by
  -- `fst12` aborts turn 2 (`c₂ = none`); `fst21` commits it (`c₂ = some`). The order bit is observable.
  decide

/-! ## §7 — Axiom-hygiene tripwires (the CLOSED keystones, all clean). -/

#assert_axioms xcellNext_of_commit
#assert_axioms total_of_xeq
#assert_axioms xcellNext_xeq_congr
#assert_axioms xcellNext_commute_step
#assert_axioms xcell_whole_history_confluent
#assert_axioms xcell_obsBisim
#assert_axioms xcell_obsStream_eq
#assert_axioms xcellNext_preserves_floor
#assert_axioms xcell_safety_infinite
#assert_axioms confluence_fails_when_coupled

/-! ## §8 — OUTCOME + the precise residual.

FRAGMENT (PROVED, axiom-clean) of the README's "cross-cell whole-history closure":

  * `xcellCoalg` — the missing `Boundary.TurnCoalg` over the EXECUTABLE cross-cell shared ledger
    (`Exec/CellProgram.lean:177`'s named missing instance), the debit-thread totalised fail-closed;
  * `xcell_whole_history_confluent` — THE adversary-stream confluence over `inducedSystem`
    (`ContendedCrossCell §9 -- OPEN (2)`'s named missing piece), on the running machine: a disjoint
    debit commutes past an ENTIRE disjoint trajectory (the all-`n` lift of the two-point
    `applyHalfOut_comm_disjoint`);
  * `xcell_obsBisim` / `xcell_obsStream_eq` — `CoinductiveAdversary.obsBisim_traj_of_bisim` FINALLY
    instantiated on the executable kernel: the shared ledger stays bisimilar to its oracle along ANY
    infinite adversarial schedule, observation streams coincide forever;
  * `xcell_safety_infinite` — a per-cell non-negativity floor carried along the WHOLE unbounded
    executable history (the `stepComplete_carries_infinite` "no drifting future" on the kernel);
  * `confluence_fails_when_coupled` — the disjointness hypothesis is LOAD-BEARING (the coupled case has
    no whole-history confluence), so the fragment is non-vacuous and its boundary is exactly drawn.

The two previously-disjoint halves — the ABSTRACT coinductive engine (`CoinductiveAdversary`) and the
EXECUTABLE finite commutation (`ContendedCrossCell`) — are JOINED here on `xcellCoalg`.

-- RESIDUAL (precisely, as the repo's own OPENs).
--   (1) FULL SCHEDULE-PERMUTATION closure: two ARBITRARY schedules that are permutations of the same
--       multiset of pairwise-disjoint debits reach `xeq` ledgers. `xcell_whole_history_confluent`
--       gives the single-edge-slides-through-a-history generator; the full closure is its `List.Perm`
--       (adjacent-transposition / bubble-sort) iteration, each transposition discharged by
--       `xcellNext_commute_step`. BOUNDED COMBINATORIAL ENGINEERING (a `Perm.rec`), not research.
--   (2) The CONTENDED (non-disjoint) infinite case: there is provably NO schedule-agnostic ledger
--       (`coupled_no_schedule_agnostic_commit`), so its whole-history "closure" is the
--       consensus/escalation boundary — the genuine next research pole, UNCHANGED from
--       `ContendedCrossCell §9` / `ForestLTS §11`, and deliberately NOT faked here.
-/

end Metatheory.Open.CrossCellBisim
