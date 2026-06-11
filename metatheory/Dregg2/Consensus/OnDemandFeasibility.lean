/-
# Dregg2.Consensus.OnDemandFeasibility — the afternoon-sized soundness core of
# CONSENSUS-ON-DEMAND (`docs/CONSENSUS-FLEX.md`), proved; the wave obligations named.

**The thesis this serves.** Total order (tau) is a special case the system overpays for:
the blocklace gives causal order free (`Coord/CausalOrder`, `LaceMerge`), and the
I-confluence classifier (`Confluence.IConfluent`) prices which turns actually conflict.
Commutative turns could finalize at causal acknowledgment depth (the fast path); only
contended turns need tau. *The lace is the truth; tau is one linearization you call when
you contend.*

**What is PROVED here (T1 of CONSENSUS-FLEX §4, the afternoon theorem).**

  * `fastpath_linearization_agnostic` — for a pairwise-commuting list of turns, EVERY
    permutation folds the executor to the SAME state. So on an all-commuting block set,
    the tau linearization and any causal-ack linearization agree: the fast path cannot
    diverge from the slow path where the classifier says "independent."
  * `frame_fastpath_sound` — the assembled corollary: given a footprint discipline
    (`FrameCommutes`: disjoint/monotone-overlap footprints ⇒ commute, the T2 interface),
    any pairwise-footprint-independent turn list is linearization-agnostic. T2's
    discharge for the full `RecordKernelState` executor is the named WAVE obligation;
    its reference instance at the JointCell kernel is already proved
    (`Proof.ContendedCrossCell.contended_commits_confluent`).
  * `revoke_exercise_noncommuting` — the NEG pole, kernel-checked: a revoke and an
    exercise on the same authority register do NOT commute (order decides whether the
    exercise lands). The commuting hypothesis is load-bearing, not decorative — exactly
    the `grant/revoke × exercise` row of the CONSENSUS-FLEX §2.2 conflict table, and the
    operational face of `Confluence.cardLeOne_not_iconfluent`.
  * `join_steps_commute` — the POS pole beyond the trivial: ⊔-shaped (CRDT/monotone)
    steps ALWAYS pairwise commute, so every grow-only footprint (shield/commitment
    inserts, clist appends, evidence ledgers) is fast-eligible by construction. This is
    the bridge to `Confluence.IConfluent`: the registers the classifier calls monotone
    are exactly the ⊔-actions, and those commute.

**What is STATED, not proved (the named ladder — see CONSENSUS-FLEX §4/§9).**

  * T2 (`FrameCommutes` for `recKExecAsset`) — wave: per-verb frame lemmas.
  * T3 (Mazurkiewicz trace convergence: linear extensions agreeing on conflicting pairs
    fold equal) — epoch: T1 is its empty-conflict case.
  * T5 — RESOLVED in `Dregg2.Consensus.TauPrefixMonotone`: REFUTED unconditionally (an
    honest laggard's late wave-end ratifier grows a final wave's coverage mid-prefix —
    the node's `executed_up_to` slicing does NOT sit inside the truth) and PROVED
    conditional (`tau_finalized_prefix_monotone` under `FinalizedRegionStable`, the
    stability check the node is missing).

No import of the executor or the blocklace: this module is the pure order-theoretic
core, deliberately dependency-light so the fast-path argument is reusable against any
deterministic `step`. `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound});
NO `sorry`/`:=True`/`native_decide`.
Verified with `lake build Dregg2.Consensus.OnDemandFeasibility`.
-/
import Mathlib.Data.List.Perm.Basic
import Mathlib.Order.Lattice
import Dregg2.Tactics

namespace Dregg2.Consensus.OnDemandFeasibility

universe u v

variable {S : Type u} {T : Type v}

/-! ## §1 The commutation relation — the semantic independence of two turns. -/

/-- **`Commute step t₁ t₂`** — the two turns commute under the (deterministic,
fail-closed-totalized) executor `step`: applying them in either order from ANY state
reaches the same state. This is the Mazurkiewicz independence relation instantiated at
the executor; its negation is THE conflict relation `⊥` of CONSENSUS-FLEX §2.1. -/
def Commute (step : S → T → S) (t₁ t₂ : T) : Prop :=
  ∀ s : S, step (step s t₁) t₂ = step (step s t₂) t₁

/-- `Commute` is symmetric — independence has no orientation. -/
theorem Commute.symm {step : S → T → S} {t₁ t₂ : T}
    (h : Commute step t₁ t₂) : Commute step t₂ t₁ :=
  fun s => (h s).symm

/-- **`PairwiseCommuting step l`** — every pair drawn from the turn list commutes: the
"all-commuting block set" hypothesis under which the fast path is exact (no conflicting
pair, so no order to adjudicate). The classifier's job (CONSENSUS-FLEX §2) is to certify
a SOUND syntactic under-approximation of this. -/
def PairwiseCommuting (step : S → T → S) (l : List T) : Prop :=
  ∀ x ∈ l, ∀ y ∈ l, Commute step x y

/-! ## §2 T1 — THE AFTERNOON THEOREM: linearization agnosticism on commuting sets.

Any two linearizations of a pairwise-commuting turn set fold the executor to the same
state. Instantiated at the real objects: `l` = the fast-classified blocks of a lace
segment, one permutation = the verified `tauOrder` restriction, the other = the causal
acknowledgment order a fast replica applied. The theorem is what LICENSES the executor
to apply fast turns before tau places them. -/

/-- **`fastpath_linearization_agnostic` (T1).** For a pairwise-commuting list `l` and any
permutation `l'` of it, the executor folds to the SAME state from every start state. The
proof rides Mathlib's `List.Perm.foldl_eq'` (fold invariance under permutation given
in-list commutation). -/
theorem fastpath_linearization_agnostic (step : S → T → S) {l l' : List T}
    (hperm : l.Perm l') (hcomm : PairwiseCommuting step l) (s : S) :
    l.foldl step s = l'.foldl step s :=
  hperm.foldl_eq' (fun x hx y hy z => hcomm x hx y hy z) s

/-- **`tau_agrees_with_fastpath`** — the CONSENSUS-FLEX §4 reading: if the tau
linearization `tauSeg` and the fast path's causal application order `fastSeg` are
permutations of the same commuting block set, the slow-path state and the fast-path
state are EQUAL. "Any tau linearization agrees with the fast path on commutative
prefixes," at the all-commuting pole. -/
theorem tau_agrees_with_fastpath (step : S → T → S) {tauSeg fastSeg : List T}
    (hperm : tauSeg.Perm fastSeg) (hcomm : PairwiseCommuting step tauSeg) (s : S) :
    tauSeg.foldl step s = fastSeg.foldl step s :=
  fastpath_linearization_agnostic step hperm hcomm s

/-! ## §3 The POS pole — ⊔-shaped (monotone/CRDT) steps always commute.

The classifier declares a register "monotone" when its updates are joins in a
semilattice (grow-only sets: commitments, nullifier-ledger inserts, clist appends,
evidence). Here is WHY that classification is sound: join-actions commute pairwise,
unconditionally — the operational face of `Confluence.IConfluent`'s ⊔. -/

/-- **`join_steps_commute`** — steps that act by joining a per-turn delta
(`step s t = s ⊔ δ t`) commute for EVERY pair of turns. Every grow-only footprint is
fast-eligible by construction. -/
theorem join_steps_commute {S : Type u} [SemilatticeSup S] {T : Type v}
    (δ : T → S) (t₁ t₂ : T) :
    Commute (fun s t => s ⊔ δ t) t₁ t₂ := by
  intro s
  simp only [sup_right_comm]

/-! ## §4 The NEG pole — revoke × exercise does NOT commute (kernel-checked).

The sharpest row of the §2.2 conflict table: a revocation and an exercise of the same
authority register are order-dependent. State = (authority live?, effects landed); the
revoke clears the bit; the exercise lands an effect iff the bit is live. The two orders
reach DIFFERENT states — so the commuting hypothesis of T1 is falsifiable, and the
classifier MUST demote this pair to tau (or adopt the bounded-staleness reading,
CONSENSUS-FLEX §8). This is the operational face of
`Confluence.cardLeOne_not_iconfluent` for the authority substance. -/

/-- A two-register toy cell: `live` = the authority register (the cap/epoch bit),
`landed` = how many exercises landed. -/
structure ToyCell where
  live   : Bool
  landed : Nat
  deriving DecidableEq, Repr

/-- The two contending turns: `revoke` clears the authority; `exercise` lands an effect
iff the authority is live (fail-closed refusal otherwise). -/
inductive ToyTurn | revoke | exercise
  deriving DecidableEq, Repr

/-- The toy executor. -/
def toyStep (s : ToyCell) : ToyTurn → ToyCell
  | .revoke   => { s with live := false }
  | .exercise => if s.live then { s with landed := s.landed + 1 } else s

/-- **`revoke_exercise_noncommuting`** — the NEG witness: from the live state,
exercise-then-revoke lands the effect, revoke-then-exercise refuses it. The conflict
relation is non-empty; T1's hypothesis is load-bearing. -/
theorem revoke_exercise_noncommuting :
    ¬ Commute toyStep ToyTurn.revoke ToyTurn.exercise := by
  intro h
  have := h ⟨true, 0⟩
  simp [toyStep] at this

/-- And the POS sibling on the same toy: two exercises commute (both read, neither
clears) — so the toy also witnesses that the conflict relation is strictly smaller than
"touches the same cell": same-cell pairs CAN be fast-eligible. -/
theorem exercise_exercise_commute :
    Commute toyStep ToyTurn.exercise ToyTurn.exercise := fun _ => rfl

/-! ## §5 T2 INTERFACE — the footprint discipline, and the assembled fast-path corollary.

`FrameCommutes` is the named WAVE obligation (CONSENSUS-FLEX §4 T2): a footprint map and
an independence predicate under which the REAL executor commutes. Its reference instance
at the JointCell kernel is `Proof.ContendedCrossCell.contended_commits_confluent`
(disjoint debit wells ⇒ schedule-agnostic); the full-`RecordKernelState` discharge is
per-verb frame lemmas. Packaging it as a structure keeps THIS module dependency-light
while making the corollary below available the day T2 lands. -/

/-- **`FrameCommutes`** — a footprint discipline for an executor: an `indep`endence
predicate on turns (in the intended instance: footprints∪read-sets intersect only on
monotone registers) together with the proof that independent turns commute. T2 = the
construction of this structure for `recKExecAsset`. -/
structure FrameCommutes (step : S → T → S) where
  /-- The syntactic independence the classifier computes (footprint disjointness up to
  monotone-register overlap — CONSENSUS-FLEX §2.1). -/
  indep : T → T → Prop
  /-- Independence is symmetric (footprint intersection is). -/
  indep_symm : ∀ {t₁ t₂}, indep t₁ t₂ → indep t₂ t₁
  /-- THE FRAME LAW: independent turns commute under the executor. -/
  commute_of_indep : ∀ {t₁ t₂}, indep t₁ t₂ → Commute step t₁ t₂

/-- **`frame_fastpath_sound`** — the assembled corollary (T2 ⇒ T1's hypothesis): under a
footprint discipline, any pairwise-INDEPENDENT turn list is linearization-agnostic — the
fast path is sound for every block set the classifier certifies. The day `FrameCommutes`
is constructed for the real executor, consensus-on-demand's safety on the commuting
fragment is THIS theorem applied. -/
theorem frame_fastpath_sound {step : S → T → S} (fc : FrameCommutes step)
    {l l' : List T} (hperm : l.Perm l')
    (hindep : ∀ x ∈ l, ∀ y ∈ l, fc.indep x y) (s : S) :
    l.foldl step s = l'.foldl step s :=
  fastpath_linearization_agnostic step hperm
    (fun x hx y hy => fc.commute_of_indep (hindep x hx y hy)) s

/-! ## §6 Non-vacuity `#guard`s — the toy fast path RUNS, both poles concrete. -/

-- Two exercises + an unrelated join: any order of the commuting pair lands both effects.
#guard (([ToyTurn.exercise, ToyTurn.exercise] : List ToyTurn).foldl toyStep ⟨true, 0⟩).landed == 2
-- The NEG pole, concretely: the two orders of (revoke, exercise) DISAGREE.
#guard ([ToyTurn.exercise, ToyTurn.revoke].foldl toyStep ⟨true, 0⟩).landed == 1
#guard ([ToyTurn.revoke, ToyTurn.exercise].foldl toyStep ⟨true, 0⟩).landed == 0

/-! ## §7 The named REMAINING ladder (stated for the record, not faked).

  * **T2** — construct `FrameCommutes recKExecAsset` (per-verb frame lemmas; reference
    instance: `ContendedCrossCell.contended_commits_confluent`). WAVE.
  * **T3** — trace convergence: two linear extensions of happened-before agreeing on the
    relative order of every NON-commuting pair fold equal (T1 = the all-commuting case).
    EPOCH; unlocks the executor dual-frontier.
  * **T5** — RESOLVED (`Dregg2.Consensus.TauPrefixMonotone`): the unconditional claim is
    REFUTED by an insert-valid honest-laggard counterexample; the corrected theorem
    `tau_finalized_prefix_monotone` holds under `FinalizedRegionStable` (executable
    mirror `stableCheck`), which `blocklace_sync.rs::poll_finalized_blocks` does NOT
    check — a reported node-side soundness gap, not a wall.
  * **T6** — supermajority ack-depth ⇒ eventual tau membership (after T5; the
    quorum-intersection arithmetic is `EpochReconfig.quorums_intersect`'s shape).
-/

/-! ## §8 Axiom hygiene. -/

#assert_axioms fastpath_linearization_agnostic
#assert_axioms tau_agrees_with_fastpath
#assert_axioms join_steps_commute
#assert_axioms revoke_exercise_noncommuting
#assert_axioms exercise_exercise_commute
#assert_axioms frame_fastpath_sound

end Dregg2.Consensus.OnDemandFeasibility
