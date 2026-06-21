/-
# Dregg2.Proof.ContendedForest — the CONTENDED / adversary-scheduled N-ary FOREST commit.

This module discharges the residual named at `ForestLTS.lean §11 -- OPEN` (and at
`ContendedCrossCell.lean §9 (1)`): **two OVERLAPPING forests under an adversarial interleaver** —
a single family of cells `(cells : ι → KernelState)` to which TWO `ForestTurn`s `ft₁ ft₂` are
simultaneously incident (they may share cell-source incidences), with a hostile `Schedule` picking
which forest runs against the shared family first. Does the system still simulate the abstract
spec when forests overlap and the scheduler interleaves them?

The bilateral case (`ContendedCrossCell`) found a DICHOTOMY: disjoint debits commute, coupled
debits (a Σ=0 settlement contending for a pot that funds only ONE) have NO schedule-agnostic
commit (the BEC/CAP obstruction). The driver of that impossibility was the **availability gate**
`amt ≤ bal` of the bilateral half `applyHalfOut`: a coupled overdraw lets the SECOND turn's
admissibility flip with the order.

The forest half `ForestLTS.applyForestHalf` is **gate-free**: a forest incidence commits iff
`authorizedB ∧ src ∈ accounts` — there is NO `amt ≤ bal` availability gate (a forest cell may go
net-negative; ℤ is debt-capable, and the CG-5 `Σ δ = 0` binding — not a per-cell pot — is what
funds the move). Two structural facts follow, and they are the whole content of this module:

  * **`applyForestHalf` fire-decision is balance-INDEPENDENT** — it reads only `caps` (frame-stable)
    and `src ∈ accounts` (frame-stable). The scheduler cannot use one forest to abort the other.
  * **`applyForestHalf` writes are ADDITIVE and commute** — even on the SAME cell:
    `(bal − δ₁) − δ₂ = (bal − δ₂) − δ₁`. There is no overdraw to make order observable.

Hence — and this is the PROVED N-ary §11 result — the contended forest scheduler is
**UNCONDITIONALLY schedule-agnostic** (`contended_forest_commutes`): for ANY two forests over ANY
shared family, both schedule orders yield the SAME final family pointwise AND the SAME commit
decisions. No disjointness hypothesis is needed; contention is *serialized away* by the additive,
gate-free structure of the forest half. The §11 contended case is closed by SERIALIZATION
(Path B), strengthened: the safe fragment is the WHOLE space.

This is **not** a contradiction of the bilateral impossibility: that impossibility lives entirely
in the availability gate. We make the boundary precise (§5): re-introduce the `amt ≤ bal` gate —
the "coupled overdraw" — and contention returns, exactly the bilateral
`ContendedCrossCell.coupled_no_schedule_agnostic_commit`. So the dichotomy is: **gate-free forest
(Σ=0-bound) ⟹ commutes unconditionally; availability-gated pot ⟹ coupled-overdraw can disagree.**
The forest LTS lives on the safe side BY CONSTRUCTION (the Σ=0 binding replaces the pot gate).

The adversary/scheduler enters as EXPLICIT data (`Schedule`, `runForestSchedule`), never an oracle.
Read-only consumer of `Proof.ForestLTS` (the forest half + transition) and `Proof.ContendedCrossCell`
(the bilateral coupled impossibility, relayed for the boundary).
-/
import Dregg2.Proof.ForestLTS
import Dregg2.Proof.ContendedCrossCell

namespace Dregg2.Proof.ContendedForest

open Dregg2.Exec
open Dregg2.Proof.ForestLTS

universe v

/-! ## §1 — Per-incidence frame lemmas for the gate-free forest half.

`applyForestHalf` commits iff `authorizedB caps … ∧ src ∈ accounts`; on commit it rewrites only
`bal src`. We need: it preserves `caps`/`accounts` (frame-stable, so the fire-decision of a
later half cannot be flipped through them), and a committed debit on `src` leaves the balance of
any *other* cell untouched (the frame the same-family commutation rests on). -/

/-- A committed forest half rewrites only `bal`; `accounts` and `caps` are preserved. (Repackages
`ForestLTS.applyForestHalf_accounts`/`_caps` as a pair for the scheduler frame.) -/
theorem half_frame {k k' : KernelState} {actor src : CellId} {d : ℤ}
    (h : applyForestHalf k actor src d = some k') :
    k'.accounts = k.accounts ∧ k'.caps = k.caps :=
  ⟨applyForestHalf_accounts h, applyForestHalf_caps h⟩

/-- A committed forest debit on `src` leaves the balance of a *different* cell `c ≠ src` untouched.
The frame lemma the same-family commutation rests on. -/
theorem half_bal_frame {k k' : KernelState} {actor src : CellId} {d : ℤ}
    (h : applyForestHalf k actor src d = some k') {c : CellId} (hc : c ≠ src) :
    k'.bal c = k.bal c := by
  unfold applyForestHalf at h
  by_cases hg : authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true
      ∧ src ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show (if c = src then k.bal c - d else k.bal c) = k.bal c
    rw [if_neg hc]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- A committed forest debit on `src` drops `bal src` by exactly `d`. -/
theorem half_bal_src {k k' : KernelState} {actor src : CellId} {d : ℤ}
    (h : applyForestHalf k actor src d = some k') : k'.bal src = k.bal src - d := by
  unfold applyForestHalf at h
  by_cases hg : authorizedB k.caps { actor := actor, src := src, dst := src, amt := d } = true
      ∧ src ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h
    show (if src = src then k.bal src - d else k.bal src) = k.bal src - d
    rw [if_pos rfl]
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`half_fires_frame`.** The fire-decision of a forest half is INDEPENDENT of any prior
committed forest half on the same cell — `applyForestHalf` reads only `caps` (frame-stable) and
`src ∈ accounts` (frame-stable); it does NOT read `bal`. So no scheduler can use one forest to
abort the other's incidence. This is the gate-free property that kills the bilateral impossibility.
-/
theorem half_fires_frame {k k' : KernelState} {actor₁ src₁ : CellId} {d₁ : ℤ}
    (h : applyForestHalf k actor₁ src₁ d₁ = some k') (actor₂ src₂ : CellId) (d₂ : ℤ) :
    (applyForestHalf k' actor₂ src₂ d₂).isSome = (applyForestHalf k actor₂ src₂ d₂).isSome := by
  obtain ⟨hacc, hcaps⟩ := half_frame h
  unfold applyForestHalf
  rw [hcaps, hacc]
  split <;> rfl

/-- **`half_commute`.** Two committed forest debits on the SAME ledger COMMUTE — even when they
hit the SAME source cell. The forest half is a pure additive debit (`bal src := bal src − d`); two
debits compose as `(bal − d₁) − d₂ = (bal − d₂) − d₁`, equal by commutativity of `ℤ`. On distinct
cells they are independent; on the same cell the additivity makes order irrelevant. This is the
`Finset.sum`-telescoping commutation `ContendedCrossCell §9 (1)` named — here UNCONDITIONAL,
because the forest half has no availability gate to make an overdraw observable. -/
theorem half_commute {k k₁ k₁₂ k₂ k₂₁ : KernelState} {a₁ s₁ a₂ s₂ : CellId} {d₁ d₂ : ℤ}
    (h1 : applyForestHalf k a₁ s₁ d₁ = some k₁) (h12 : applyForestHalf k₁ a₂ s₂ d₂ = some k₁₂)
    (h2 : applyForestHalf k a₂ s₂ d₂ = some k₂) (h21 : applyForestHalf k₂ a₁ s₁ d₁ = some k₂₁) :
    (∀ c, k₁₂.bal c = k₂₁.bal c) ∧ k₁₂.accounts = k₂₁.accounts ∧ k₁₂.caps = k₂₁.caps := by
  refine ⟨fun c => ?_, ?_, ?_⟩
  · -- pointwise: split on whether c is s₁, s₂, or neither. Same-cell (s₁ = s₂) is subsumed:
    -- both branches reduce to k.bal c − d₁ − d₂ vs k.bal c − d₂ − d₁ (commute).
    by_cases hc1 : c = s₁
    · subst hc1  -- eliminates s₁, replacing it by c in h1, h21
      by_cases hc2 : c = s₂
      · -- SAME cell (c = s₂): order 12 debits c by d₁ (h1) then d₂ (h12);
        --                     order 21 debits c by d₂ (h2) then d₁ (h21).
        subst hc2  -- eliminates s₂, replacing it by c in h2, h12
        have e12 : k₁₂.bal c = k₁.bal c - d₂ := half_bal_src h12
        have d1  : k₁.bal c = k.bal c - d₁ := half_bal_src h1
        have e21 : k₂₁.bal c = k₂.bal c - d₁ := half_bal_src h21
        have d2  : k₂.bal c = k.bal c - d₂ := half_bal_src h2
        rw [e12, d1, e21, d2]; ring
      · -- DISTINCT cells, c = s₁ ≠ s₂.
        have e12 : k₁₂.bal c = k₁.bal c := half_bal_frame h12 hc2
        have d1  : k₁.bal c = k.bal c - d₁ := half_bal_src h1
        have e21 : k₂₁.bal c = k₂.bal c - d₁ := half_bal_src h21
        have a2  : k₂.bal c = k.bal c := half_bal_frame h2 hc2
        rw [e12, d1, e21, a2]
    · by_cases hc2 : c = s₂
      · -- c = s₂ ≠ s₁.
        subst hc2  -- eliminates s₂, replacing it by c in h2, h12
        have e21 : k₂₁.bal c = k₂.bal c := half_bal_frame h21 hc1
        have d2  : k₂.bal c = k.bal c - d₂ := half_bal_src h2
        have e12 : k₁₂.bal c = k₁.bal c - d₂ := half_bal_src h12
        have a1  : k₁.bal c = k.bal c := half_bal_frame h1 hc1
        rw [e21, d2, e12, a1]
      · -- neither: untouched by either order.
        have l12 : k₁₂.bal c = k₁.bal c := half_bal_frame h12 hc2
        have l1  : k₁.bal c = k.bal c := half_bal_frame h1 hc1
        have l21 : k₂₁.bal c = k₂.bal c := half_bal_frame h21 hc1
        have l2  : k₂.bal c = k.bal c := half_bal_frame h2 hc2
        rw [l12, l1, l21, l2]
  · rw [(half_frame h12).1, (half_frame h1).1, (half_frame h21).1, (half_frame h2).1]
  · rw [(half_frame h12).2, (half_frame h1).2, (half_frame h21).2, (half_frame h2).2]

/-! ## §2 — The contended forest scheduler.

Two forests `ft₁ ft₂` over a shared family `cells : ι → KernelState`. Each forest is applied
atomically (`forestApply`, fail-closed all-or-none); the adversary's `Schedule` picks the order;
the second forest sees the family the first left. The whole question: is the committed `Outcome`
INDEPENDENT of the adversary's order bit? -/

/-- The adversary's scheduling choice for two contending forests. -/
inductive Schedule where
  | fst12
  | fst21
  deriving DecidableEq, Repr

/-- The committed outcome of a contended forest run: the final shared family, and WHICH forests
committed (`isSome`). `none` for a forest means the scheduler forced it to abort. -/
structure Outcome (ι : Type v) where
  /-- The final shared family after the scheduled run. -/
  fam : ι → KernelState
  /-- Whether forest `1` committed. -/
  c₁ : Bool
  /-- Whether forest `2` committed. -/
  c₂ : Bool

/-- Apply one forest atomically against the threaded shared family. Fail-closed: on failure the
family is UNCHANGED (no incidence committed) and the commit flag is `false`. -/
def stepForest {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells : ι → KernelState) (ft : ForestTurn ι) : (ι → KernelState) × Bool :=
  match forestApply cells ft with
  | some cells' => (cells', true)
  | none        => (cells, false)

/-- **`runForestSchedule`** — the deterministic fail-closed semantics of a contended forest
schedule. The two forests are applied in the adversary's order; the second sees the family the
first left. -/
def runForestSchedule {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells : ι → KernelState) (ft₁ ft₂ : ForestTurn ι) : Schedule → Outcome ι
  | .fst12 =>
      let (c₁, r₁) := stepForest cells ft₁
      let (c₂, r₂) := stepForest c₁ ft₂
      { fam := c₂, c₁ := r₁, c₂ := r₂ }
  | .fst21 =>
      let (c₁, r₂) := stepForest cells ft₂
      let (c₂, r₁) := stepForest c₁ ft₁
      { fam := c₂, c₁ := r₁, c₂ := r₂ }

/-- `stepForest` on a committed forest threads the post-state and flags `true`. -/
theorem stepForest_commit {ι : Type v} [Fintype ι] [DecidableEq ι]
    {cells cells' : ι → KernelState} {ft : ForestTurn ι}
    (h : forestApply cells ft = some cells') : stepForest cells ft = (cells', true) := by
  unfold stepForest; rw [h]

/-! ## §3 — Per-cell, both forests commit when run first ⟹ each fires after the other.

The crux: `forestApply` is the per-`i` conjunction of `applyForestHalf` fires (atomic). When a
forest commits run-first, every incidence fired; by `half_fires_frame` (the gate-free,
balance-independent fire-decision) every incidence STILL fires after the OTHER forest has run.
So both forests commit under EITHER order — the scheduler cannot abort either. -/

/-- If forest `ft` commits on `cells`, every incidence's half is `isSome` on `cells`. (The
forward direction of `forestApply`'s defining `dite`.) -/
theorem forest_commit_all_some {ι : Type v} [Fintype ι] [DecidableEq ι]
    {cells cells' : ι → KernelState} {ft : ForestTurn ι}
    (h : forestApply cells ft = some cells') :
    ∀ i, (applyForestHalf (cells i) (ft.actorA i) (ft.srcA i) (ft.δ i)).isSome :=
  fun i => by rw [forestApply_atomic h i]; rfl

/-- The converse packager: if every incidence's half is `isSome` on `cells`, `forestApply`
commits (to the canonical assembled family). -/
theorem forest_commit_of_all_some {ι : Type v} [Fintype ι] [DecidableEq ι]
    {cells : ι → KernelState} {ft : ForestTurn ι}
    (hall : ∀ i, (applyForestHalf (cells i) (ft.actorA i) (ft.srcA i) (ft.δ i)).isSome) :
    (forestApply cells ft).isSome := by
  unfold forestApply; rw [dif_pos hall]; rfl

/-- **`other_forest_still_commits`.** If forest `ftB` commits on the family `Q` that forest `ftA`
left (`forestApply P ftA = some Q`), then `ftB` ALSO commits on the ORIGINAL family `P`, and vice
versa — the fire-decision of each incidence of `ftB` is independent of whether `ftA` already ran
(`half_fires_frame`, per `i`). Formally: `forestApply` of `ftB` is `isSome` on `Q` iff on `P`. -/
theorem other_forest_fire_indep {ι : Type v} [Fintype ι] [DecidableEq ι]
    {P Q : ι → KernelState} {ftA ftB : ForestTurn ι}
    (hA : forestApply P ftA = some Q) :
    (forestApply Q ftB).isSome = (forestApply P ftB).isSome := by
  -- per-i fire-decisions agree (gate-free), so the all-quantified dite condition agrees.
  have hi : ∀ i, (applyForestHalf (Q i) (ftB.actorA i) (ftB.srcA i) (ftB.δ i)).isSome
              = (applyForestHalf (P i) (ftB.actorA i) (ftB.srcA i) (ftB.δ i)).isSome := by
    intro i
    -- Q i is P i after ftA's i-th half committed (forestApply is atomic per i).
    have hcommit : applyForestHalf (P i) (ftA.actorA i) (ftA.srcA i) (ftA.δ i) = some (Q i) :=
      forestApply_atomic hA i
    exact half_fires_frame hcommit (ftB.actorA i) (ftB.srcA i) (ftB.δ i)
  unfold forestApply
  by_cases hQ : ∀ i, (applyForestHalf (Q i) (ftB.actorA i) (ftB.srcA i) (ftB.δ i)).isSome = true
  · have hP : ∀ i, (applyForestHalf (P i) (ftB.actorA i) (ftB.srcA i) (ftB.δ i)).isSome = true :=
      fun i => (hi i).symm.trans (hQ i)
    rw [dif_pos hQ, dif_pos hP]; rfl
  · have hP : ¬ ∀ i, (applyForestHalf (P i) (ftB.actorA i) (ftB.srcA i) (ftB.δ i)).isSome = true := by
      intro hP; exact hQ (fun i => (hi i).trans (hP i))
    rw [dif_neg hQ, dif_neg hP]

/-! ## §4 — THE KEYSTONE: contended forests commute UNCONDITIONALLY.

When both forests commit run-first, both schedule orders yield the SAME final family (pointwise
`bal`, `accounts`, `caps`) AND the SAME commit decisions (both forests commit under either order).
NO disjointness hypothesis: the gate-free additive forest half serializes contention away. This is
the proved closure of `ForestLTS §11`, the contended/overlapping case, by SERIALIZATION (Path B). -/

/-- The post-family `forestApply` produces is determined cellwise by the per-incidence halves:
`(forestApply cells ft).get = fun i => (applyForestHalf …).get`. We extract the concrete committed
family from a successful run. -/
theorem forestApply_componentwise {ι : Type v} [Fintype ι] [DecidableEq ι]
    {cells cells' : ι → KernelState} {ft : ForestTurn ι}
    (h : forestApply cells ft = some cells') (i : ι) :
    applyForestHalf (cells i) (ft.actorA i) (ft.srcA i) (ft.δ i) = some (cells' i) :=
  forestApply_atomic h i

/-- **KEYSTONE — `contended_forest_commutes`.** THE N-ARY §11 CLOSURE. For ANY two forests
`ft₁ ft₂` over ANY shared family `cells`, IF both forests commit when run first (`hc1`/`hc2`),
then the two adversary schedules `fst12` and `fst21` produce:

  * the SAME final family — pointwise equal `bal` on every cell, equal `accounts`, equal `caps`;
  * the SAME commit decisions — BOTH forests commit under EITHER order (`c₁ = c₂ = true` both ways).

So the committed outcome is SCHEDULE-AGNOSTIC with NO disjointness hypothesis. Overlapping forests
(a cell incident to both) serialize into a definite, order-independent result, because the forest
half is a gate-free additive debit (`half_commute` on the same cell, `half_fires_frame` on the
fire-decision). The contended/overlapping case of `ForestLTS §11` is CLOSED by serialization. -/
theorem contended_forest_commutes {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells C₁ C₂ : ι → KernelState) (ft₁ ft₂ : ForestTurn ι)
    (hc1 : forestApply cells ft₁ = some C₁)
    (hc2 : forestApply cells ft₂ = some C₂) :
    let o12 := runForestSchedule cells ft₁ ft₂ .fst12
    let o21 := runForestSchedule cells ft₁ ft₂ .fst21
    (∀ i c, (o12.fam i).bal c = (o21.fam i).bal c) ∧
    (∀ i, (o12.fam i).accounts = (o21.fam i).accounts) ∧
    (∀ i, (o12.fam i).caps = (o21.fam i).caps) ∧
    o12.c₁ = true ∧ o12.c₂ = true ∧ o21.c₁ = true ∧ o21.c₂ = true := by
  -- the SECOND forest commits after the FIRST in both orders (gate-free fire-independence).
  have h12fires : (forestApply C₁ ft₂).isSome := by
    rw [other_forest_fire_indep hc1]; exact hc2 ▸ rfl
  have h21fires : (forestApply C₂ ft₁).isSome := by
    rw [other_forest_fire_indep hc2]; exact hc1 ▸ rfl
  obtain ⟨C₁₂, hC12⟩ := Option.isSome_iff_exists.mp h12fires
  obtain ⟨C₂₁, hC21⟩ := Option.isSome_iff_exists.mp h21fires
  -- compute all four `stepForest`s.
  simp only [runForestSchedule, stepForest_commit hc1, stepForest_commit hc2,
    stepForest_commit hC12, stepForest_commit hC21]
  refine ⟨fun i c => ?_, fun i => ?_, fun i => ?_, ?_, ?_, ?_, ?_⟩
  -- per cell i: the two orders run the SAME pair of incidence-halves on cells i, commuted.
  · exact (half_commute (forestApply_componentwise hc1 i) (forestApply_componentwise hC12 i)
        (forestApply_componentwise hc2 i) (forestApply_componentwise hC21 i)).1 c
  · exact (half_commute (forestApply_componentwise hc1 i) (forestApply_componentwise hC12 i)
        (forestApply_componentwise hc2 i) (forestApply_componentwise hC21 i)).2.1
  · exact (half_commute (forestApply_componentwise hc1 i) (forestApply_componentwise hC12 i)
        (forestApply_componentwise hc2 i) (forestApply_componentwise hC21 i)).2.2
  -- the four commit flags are all `true` (both forests commit under either order).
  all_goals trivial

/-- **`contended_forest_schedule_agnostic`.** The committed-flag corollary in the
`ContendedCrossCell` shape: there IS a schedule-agnostic verdict for contended forests — the
constant `(true, true)` — that agrees with the fail-closed run on EVERY schedule (given both
forests commit run-first). The exact opposite pole from the bilateral coupled impossibility
(`¬ ∃ verdict …`): the forest's gate-free structure puts it on the safe side. -/
theorem contended_forest_schedule_agnostic {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells C₁ C₂ : ι → KernelState) (ft₁ ft₂ : ForestTurn ι)
    (hc1 : forestApply cells ft₁ = some C₁)
    (hc2 : forestApply cells ft₂ = some C₂) :
    ∃ verdict : Bool × Bool,
      ∀ sch : Schedule,
        ((runForestSchedule cells ft₁ ft₂ sch).c₁,
         (runForestSchedule cells ft₁ ft₂ sch).c₂) = verdict := by
  obtain ⟨_, _, _, h12c1, h12c2, h21c1, h21c2⟩ :=
    contended_forest_commutes cells C₁ C₂ ft₁ ft₂ hc1 hc2
  refine ⟨(true, true), fun sch => ?_⟩
  cases sch with
  | fst12 => rw [h12c1, h12c2]
  | fst21 => rw [h21c1, h21c2]

/-! ## §5 — The boundary: WHY this is unconditional, and where contention DOES return.

The keystone has no disjointness hypothesis — strictly STRONGER than the bilateral
`ContendedCrossCell.contended_commits_confluent` (which needed `DisjointDebits`). The strength
comes from a structural fact, not luck: the forest half has NO availability gate. The bilateral
impossibility `coupled_no_schedule_agnostic_commit` lives ENTIRELY in that gate — a coupled
overdraw makes the second turn's admissibility order-dependent. We re-state that impossibility
here, unchanged, as the precise residual boundary: re-introduce the `amt ≤ bal` gate (the pot
model) and contention returns. The forest LTS lives on the safe side BY CONSTRUCTION because the
Σ=0 binding replaces the per-cell pot gate. -/

/-- **`forest_unconditional_vs_gated_boundary`.** The dichotomy, sharply, in one statement:

  * **Forest (gate-free, this module):** ANY two committing forests over a shared family commute
    schedule-agnostically — there EXISTS a constant verdict (`contended_forest_schedule_agnostic`).
  * **Gated pot (bilateral, `ContendedCrossCell`):** there EXIST a shared ledger and two
    availability-GATED turns contending for one pot for which NO constant verdict agrees with every
    schedule (`coupled_no_schedule_agnostic_commit`).

The two poles do not contradict: they are the same scheduler over DIFFERENT half-applies. The
availability gate is the sole source of the impossibility; the gate-free forest half is the sole
source of the unconditional commutation. -/
theorem forest_unconditional_vs_gated_boundary :
    -- gate-free forest: a schedule-agnostic verdict always exists (for committing forests).
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
        (cells C₁ C₂ : ι → KernelState) (ft₁ ft₂ : ForestTurn ι),
        forestApply cells ft₁ = some C₁ → forestApply cells ft₂ = some C₂ →
        ∃ verdict : Bool × Bool,
          ∀ sch : Schedule,
            ((runForestSchedule cells ft₁ ft₂ sch).c₁,
             (runForestSchedule cells ft₁ ft₂ sch).c₂) = verdict) ∧
    -- availability-gated pot: NO schedule-agnostic verdict for the coupled overdraw.
    (∃ (A B₁ B₂ : KernelState) (bt₁ bt₂ : Dregg2.Exec.JointCell.BiTurn),
      ¬ ∃ verdict : Bool × Bool,
        (∀ sch : ContendedCrossCell.Schedule,
          ((ContendedCrossCell.runSchedule A B₁ B₂ bt₁ bt₂ sch).c₁.isSome,
           (ContendedCrossCell.runSchedule A B₁ B₂ bt₁ bt₂ sch).c₂.isSome) = verdict)) :=
  ⟨fun cells C₁ C₂ ft₁ ft₂ hc1 hc2 =>
      contended_forest_schedule_agnostic cells C₁ C₂ ft₁ ft₂ hc1 hc2,
   ContendedCrossCell.coupled_no_schedule_agnostic_commit⟩

/-! ## §6 — MUTATION-CONFIRM: the commutation BITES (it is not vacuously trivial).

Two confirmations that the property does real work:

  (1) **The forest half is genuinely additive-not-gated** — there is a SAME-CELL contended forest
      that would OVERDRAW under an availability gate (`δ₁ + δ₂ > bal`) yet BOTH incidences commit
      and the two schedule orders agree. So `contended_forest_commutes` covers the very case the
      bilateral impossibility rejected — it is not silently dodging contention.

  (2) **The gated pot still disagrees** — the relayed bilateral counterexample
      (`coupled_schedules_disagree`) shows the same scheduler over the gated half is order-sensitive.
      So the unconditional forest commutation is a PROPERTY OF THE GATE-FREE HALF, not of the
      scheduler being weak. -/

/-- A concrete contended FOREST over `ι = Fin 1` (one cell), where both forests debit the SAME
source `0` of the single cell, with deltas summing to MORE than the cell's balance — an "overdraw"
that the bilateral availability gate would reject. We show: both forests commit (gate-free), and
the two schedule orders agree on the final balance of cell `0` AND the commit flags. The mutation
that would break a gated half (over-subtraction) is exactly where the forest half commutes. -/
def potCell : KernelState :=
  { accounts := {0}, bal := fun _ => 100, caps := fun _ => [] }

/-- Forest `1`: the sole incidence (cell `0`) debits `60` from source `0`, owner-authorized. -/
def overForest₁ : ForestTurn (Fin 1) :=
  { actorA := fun _ => 0, srcA := fun _ => 0, δ := fun _ => 60, sid := 1 }

/-- Forest `2`: the sole incidence debits ANOTHER `60` from the SAME source `0`. Together `120 > 100`
— an overdraw a gated half would reject, but the gate-free forest half commits both. -/
def overForest₂ : ForestTurn (Fin 1) :=
  { actorA := fun _ => 0, srcA := fun _ => 0, δ := fun _ => 60, sid := 2 }

/-- **`overdraw_forest_both_commit`.** Both contending same-cell overdraw forests COMMIT — the
forest half has no availability gate, so `120 > 100` does not abort either. Machine-checked. -/
theorem overdraw_forest_both_commit :
    (forestApply (fun _ : Fin 1 => potCell) overForest₁).isSome = true ∧
    (forestApply (fun _ : Fin 1 => potCell) overForest₂).isSome = true := by
  constructor <;> decide

/-- **`overdraw_forest_schedules_agree`.** Despite the same-cell overdraw, the two adversary
schedules produce the SAME commit flags AND the SAME final balance of cell `0` (`100 − 60 − 60 =
−20`, order-independent). The mutation that would make a gated half disagree is exactly where the
forest half commutes — the property BITES on the genuinely-contended overdraw. Machine-checked. -/
theorem overdraw_forest_schedules_agree :
    ((runForestSchedule (fun _ : Fin 1 => potCell) overForest₁ overForest₂ .fst12).c₁,
     (runForestSchedule (fun _ : Fin 1 => potCell) overForest₁ overForest₂ .fst12).c₂)
      =
    ((runForestSchedule (fun _ : Fin 1 => potCell) overForest₁ overForest₂ .fst21).c₁,
     (runForestSchedule (fun _ : Fin 1 => potCell) overForest₁ overForest₂ .fst21).c₂) ∧
    ((runForestSchedule (fun _ : Fin 1 => potCell) overForest₁ overForest₂ .fst12).fam 0).bal 0
      =
    ((runForestSchedule (fun _ : Fin 1 => potCell) overForest₁ overForest₂ .fst21).fam 0).bal 0 := by
  constructor <;> decide

/-- **`gated_pot_still_disagrees`.** The relayed bilateral counterexample: the SAME scheduler over
the availability-GATED half IS order-sensitive — `(true,false)` one order, `(false,true)` the other.
So the unconditional forest commutation is a property of the gate-free half, NOT of a weak
scheduler. (Relay of `ContendedCrossCell.coupled_schedules_disagree`.) -/
theorem gated_pot_still_disagrees :
    ((ContendedCrossCell.runSchedule ContendedCrossCell.potA ContendedCrossCell.potB
        ContendedCrossCell.potB ContendedCrossCell.coupled₁ ContendedCrossCell.coupled₂
        .fst12).c₁.isSome,
     (ContendedCrossCell.runSchedule ContendedCrossCell.potA ContendedCrossCell.potB
        ContendedCrossCell.potB ContendedCrossCell.coupled₁ ContendedCrossCell.coupled₂
        .fst12).c₂.isSome)
    ≠
    ((ContendedCrossCell.runSchedule ContendedCrossCell.potA ContendedCrossCell.potB
        ContendedCrossCell.potB ContendedCrossCell.coupled₁ ContendedCrossCell.coupled₂
        .fst21).c₁.isSome,
     (ContendedCrossCell.runSchedule ContendedCrossCell.potA ContendedCrossCell.potB
        ContendedCrossCell.potB ContendedCrossCell.coupled₁ ContendedCrossCell.coupled₂
        .fst21).c₂.isSome) :=
  ContendedCrossCell.coupled_schedules_disagree

/-! ## §7 — The contended forest result lifts the §11 square: commuted outcome simulates abstract.

The non-contended forest square (`ForestLTS.forestAbsStep_forward`) matches a single committed
forest with an abstract step. Here we tie the contended result back: the order-independent
committed family of two overlapping Σ=0-bound forests is matched by a `ForestAbsRun` — the
adversary's interleaving does not escape the abstract LTS. So contention is not just confluent at
the concrete level; the SIMULATION survives it. -/

/-- **`contended_forest_simulates`.** Two overlapping Σ=0-bound forests under EITHER adversary
schedule yield a family whose forest-abstraction is reachable by a `ForestAbsRun` of length two from
the initial abstraction. The order does not matter (`contended_forest_commutes` gives one final
family); the abstract LTS simulates the interleaving. The hostile scheduler cannot fool the
light-client abstraction. -/
theorem contended_forest_simulates {ι : Type v} [Fintype ι] [DecidableEq ι]
    (cells C₁ : ι → KernelState) (ft₁ ft₂ : ForestTurn ι)
    (hb1 : ∑ i, ft₁.δ i = 0) (hb2 : ∑ i, ft₂.δ i = 0)
    (hc1 : forestApply cells ft₁ = some C₁)
    (h12 : (forestApply C₁ ft₂).isSome) :
    ForestAbsRun (forestAbsOf cells)
      (forestAbsOf ((runForestSchedule cells ft₁ ft₂ .fst12).fam)) := by
  obtain ⟨C₁₂, hC12⟩ := Option.isSome_iff_exists.mp h12
  -- the fst12 outcome family is exactly C₁₂.
  have hfam : (runForestSchedule cells ft₁ ft₂ .fst12).fam = C₁₂ := by
    simp only [runForestSchedule, stepForest_commit hc1, stepForest_commit hC12]
  rw [hfam]
  -- two genuine abstract steps: cells → C₁ (ft₁), C₁ → C₁₂ (ft₂), both Σ=0-bound.
  exact ForestAbsRun.step (forestAbsStep_forward_exists cells C₁ ft₁ hb1 hc1)
    (ForestAbsRun.step (forestAbsStep_forward_exists C₁ C₁₂ ft₂ hb2 hC12)
      (ForestAbsRun.refl _))

/-! ## §8 — Axiom-hygiene tripwires (the CLOSED keystones, all clean). -/

#assert_axioms half_frame
#assert_axioms half_bal_frame
#assert_axioms half_bal_src
#assert_axioms half_fires_frame
#assert_axioms half_commute
#assert_axioms stepForest_commit
#assert_axioms forest_commit_all_some
#assert_axioms forest_commit_of_all_some
#assert_axioms other_forest_fire_indep
#assert_axioms forestApply_componentwise
#assert_axioms contended_forest_commutes
#assert_axioms contended_forest_schedule_agnostic
#assert_axioms forest_unconditional_vs_gated_boundary
#assert_axioms overdraw_forest_both_commit
#assert_axioms overdraw_forest_schedules_agree
#assert_axioms gated_pot_still_disagrees
#assert_axioms contended_forest_simulates

/-! ## §9 — Summary.

`ForestLTS §11` — the CONTENDED / adversary-scheduler case of overlapping forests — is CLOSED by
SERIALIZATION (Path B), and the closure is UNCONDITIONAL. `contended_forest_commutes`: ANY two
committing forests over ANY shared family yield the SAME final family and the SAME commit flags
under both adversary orders — no disjointness hypothesis. The driver is structural: the forest half
`applyForestHalf` is gate-free and additive (`half_fires_frame`: the fire-decision is
balance-independent; `half_commute`: two debits commute even on the same cell). The abstract LTS
survives the interleaving (`contended_forest_simulates`): a hostile scheduler cannot escape the
forest abstraction.

This does NOT contradict the bilateral coupled impossibility
(`ContendedCrossCell.coupled_no_schedule_agnostic_commit`): that impossibility lives entirely in
the availability gate `amt ≤ bal` of the bilateral half. `forest_unconditional_vs_gated_boundary`
states the dichotomy as one theorem; `overdraw_forest_*` confirms the forest half commits the very
overdraw the gated half rejects, and `gated_pot_still_disagrees` confirms the gated half still
disagrees. The forest LTS lives on the SAFE side BY CONSTRUCTION because the CG-5 `Σ δ = 0` binding
replaces the per-cell pot gate.

-- PRECISE RESIDUAL (named, beyond this module):
-- (1) AVAILABILITY-GATED N-ary forest: a forest variant carrying a per-cell `δ i ≤ bal (srcA i)`
--     availability gate (NOT the dregg forest half — dregg uses Σ=0, not pots) would inherit the
--     bilateral coupled impossibility at any co-debited cell; the N-ary classifier is then
--     pairwise-disjoint debit supports (the safe fragment) vs a co-debited overdraw (must escalate).
--     This is `ContendedCrossCell.coupled_*` lifted; the gate is the boundary, NOT the dregg model.
-- (2) COINDUCTIVE: schedules of UNBOUNDED interleaved forests over `Boundary.TurnCoalg` (an infinite
--     adversary stream), confluence-up-to-bisimulation over νF — `Proof.CoinductiveAdversary`.
-/

end Dregg2.Proof.ContendedForest
