/-
# `Dregg2.Tactics.ThreadAdvantageBound` — the `thread_advantage_bound` tactic:
the MECHANICAL SWEEP that re-threads an old-floor-conditioned lemma onto the PROPER computational floor.

## What this closes

The 07-13 floor-fix (`Dregg2/Circuit/HashFloorHonesty.lean` + `Dregg2/Crypto/CryptoFloorTeeth.lean`)
proved the OLD floors — `HashCR` / `Poseidon2SpongeCR` / `compressNInjective` / `MSISHard` — stated as
INJECTIVITY / existence-refutation, VACUOUS at real parameters, and defined the PROPER computational
replacements: `CollisionResistant` (a keyed hash family: every collision-finder's advantage `Negl`) and
the adversary-indexed `MSISHardQuant`/`HashCRHardQuant` (`∀ s, Negl (adv s)`). That left ~180 downstream
consumers to re-thread. The threading is UNIFORM: each old-floor use — a Boolean "two openings ⟹ equal"
— becomes an ADDITIVE negligible advantage term, and the resulting `Negl` obligation is discharged by the
negligibility-closure algebra of `Dregg2/Crypto/ConcreteSecurity.lean`
(`negl_zero`, `negl_add`, `negl_const_mul`, `negl_finset_sum`, `negl_two_pow`).

## The tactic

`thread_advantage_bound` closes a goal `Negl e` by STRUCTURAL RECURSION over the closure algebra,
pulling the proper floor from the local context at the leaves:

  * `Negl (fun _ => 0)`                      ↦ `negl_zero`                         (a bound-with-no-hash leg)
  * `Negl (fun n => 1/2ⁿ)`                   ↦ `negl_two_pow`                      (an explicit decaying term)
  * `Negl (collisionAdv F A)`                ↦ the floor `hCR : CollisionResistant F` applied to `A`
                                                (the single-use equivocation leaf — an equivocating opener
                                                 IS a collision finder, so its success is the floor's bound)
  * `Negl (adv s)`                           ↦ the floor `hfloor : MSISHardQuant adv` (etc.) applied to `s`
  * `Negl (fun n => f n + g n)`              ↦ `negl_add`, recurse on both      (two independent hash legs)
  * `Negl (fun n => a * f n)`                ↦ `negl_const_mul`, recurse         (a query-count / RLC factor)
  * `Negl (fun n => nᵏ * f n)`               ↦ `negl_mul_monomial`, recurse      (a polynomial factor)
  * `Negl (fun n => ∑ i ∈ s, f i n)`         ↦ `negl_finset_sum`, recurse per i  (the FRI/STARK multi-round
                                                 fold — a soundness error summed over `rounds` Merkle checks)

So the two commonest consumer SHAPES thread mechanically:

  1. **SINGLE-USE binding / equivocation** (`HermineHintMLWE.commitment_binding`,
     `OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR`, `FinBindsKernel`): the Boolean
     "opens ⟹ equal" restates as "the equivocation advantage is negligible", a single floor leaf.
  2. **SUMMED multi-round** (the `friFold` / `StarkSound` chain): a total binding-failure advantage =
     `∑ r ∈ rounds, collisionAdv F (finder r)`, negligible by `negl_finset_sum` at every round.

and the MIXED tower shape — a de-batching term SCALED by a query count, PLUS the multi-round sum, PLUS a
zero leg — threads by composing all of the above additively (`stark_sound_tower_advantage_bound` below).

## Scope — what it does NOT do (honest boundary)

The tactic discharges the UNIFORM part: the `Negl` obligation the restatement introduces. It does NOT
synthesize the restatement's STATEMENT — that is per-theorem-shaped (you name the `CollisionFinder` built
from the specific equivocating opener, and the ensemble the specific protocol's soundness error tracks).
Nor does it discharge a `negl_of_eventually_le` DOMINATION step (which needs a concrete bounding witness),
or a `PolyBounded` side-goal (`negl_mul_poly`) — those carry real content and are left for the caller.
It covers the closure-algebra spine (sum / scale / monomial / finite-sum / decay / zero) and the two floor
leaves (`CollisionResistant`, the `*HardQuant` family); that is the mechanical majority of the ~180.

## Axiom hygiene

The emitted proofs compose only the `#assert_all_clean` closure lemmas and the floor hypothesis — no
`sorry`, no fresh `axiom`. Every prototype below is pinned `#assert_axioms`-clean
(⊆ {propext, Classical.choice, Quot.sound}); the floor enters as a HYPOTHESIS, so the restatements are
genuine implications, and a `fail_if_success` tooth shows the tactic REFUSES a non-negligible goal (it is
a real discharger, not a `sorry` in tactic costume).
-/
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.ConcreteSecurity
import Dregg2.Crypto.ProbCrypto

namespace Dregg2.Tactics.ThreadAdvantageBound

open Dregg2.Crypto.ConcreteSecurity
  (Negl negl_zero negl_two_pow negl_add negl_const_mul negl_mul_monomial negl_finset_sum Ensemble)
open Dregg2.Crypto.ProbCrypto (MSISHardQuant MLWEHardQuant DLHardQuant HashCRHardQuant)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv)

set_option autoImplicit false

/-! ## The floor LEAF — close `Negl (collisionAdv F A)` / `Negl (adv s)` from the proper floor in context.

The proper floors are `∀`-statements (`CollisionResistant F := ∀ A, Negl (collisionAdv F A)`,
`MSISHardQuant adv := ∀ s, Negl (adv s)`), so a floor leaf is the floor hypothesis APPLIED to the
adversary/index the goal names. `‹CollisionResistant _›` finds the floor in context; `_` is the
adversary, unified from the goal. `assumption` catches a bare `Negl _` hypothesis. -/
syntax "advantage_floor_leaf" : tactic
macro_rules
  | `(tactic| advantage_floor_leaf) =>
    `(tactic| first
        | exact ‹CollisionResistant _› _
        | exact ‹HashCRHardQuant _› _
        | exact ‹MSISHardQuant _› _
        | exact ‹MLWEHardQuant _› _
        | exact ‹DLHardQuant _› _
        | assumption)

/-! ## `thread_advantage_bound` — the recursive closure-algebra discharger.

Leaves are tried BEFORE the recursive combinators (so a `collisionAdv`/`0`/`1/2ⁿ` leaf never regresses),
and each combinator recurses via `<;> thread_advantage_bound` on strictly smaller goals — the recursion
terminates when the advantage expression bottoms out at a floor leaf. -/
syntax "thread_advantage_bound" : tactic
macro_rules
  | `(tactic| thread_advantage_bound) =>
    `(tactic| first
        | exact negl_zero
        | exact negl_two_pow
        | advantage_floor_leaf
        | (refine negl_add ?_ ?_ <;> thread_advantage_bound)
        | (refine negl_const_mul _ ?_ <;> thread_advantage_bound)
        | (refine negl_mul_monomial _ ?_ <;> thread_advantage_bound)
        | (refine negl_finset_sum _ (fun _ _ => ?_) <;> thread_advantage_bound))

/-! ## §1 — PROTOTYPE on real consumer SHAPE 1: single-use equivocation binding.

`HermineHintMLWE.commitment_binding` and `OodCommitmentBinding.commitmentOpening_binds_of_poseidon2CR` are
the Boolean form "two openings of one commitment ⟹ the reveals are equal", conditioned on the (vacuous)
injective floor. The concrete-security restatement: an equivocating opener — one that opens a commitment
to two DISTINCT reveals colliding under the hash — IS a `CollisionFinder`, so under the proper
`CollisionResistant` floor its equivocation advantage is negligible. The `Negl` obligation is a single
floor leaf, discharged by `thread_advantage_bound`. -/

/-- **SHAPE-1 restatement (commitment / opening binding).** The advantage-bounded form of
`commitment_binding` / `commitmentOpening_binds_of_poseidon2CR`: under the proper keyed-hash floor, the
equivocation adversary's advantage is negligible — "opens ⟹ equal" becomes "opens ⟹ equal except with
negligible probability". Proof: `thread_advantage_bound` (the `CollisionResistant` floor leaf). -/
theorem commitment_binding_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (equivocator : CollisionFinder F) :
    Negl (collisionAdv F equivocator) := by
  thread_advantage_bound

/-! ## §2 — PROTOTYPE on real consumer SHAPE 2: the multi-round FRI/STARK fold.

The `StarkSound` / FRI-proximity chain runs `rounds` Merkle-binding checks, each an
`OodCommitmentBinding.merkleRecomputeZ_binds` leg consuming the hash floor. The total binding-failure
advantage is the finite SUM of the per-round collision advantages, negligible by `negl_finset_sum` — the
union-bound step. The `Negl` obligation is a `negl_finset_sum` followed by a floor leaf per round, both
emitted by `thread_advantage_bound`. -/

/-- **SHAPE-2 restatement (multi-round FRI/STARK binding).** The advantage-bounded form of the `friFold` /
`StarkSound` chain: the total opening-binding failure advantage across `rounds` Merkle checks is a finite
sum of per-round collision advantages, negligible under the proper floor. Proof: `thread_advantage_bound`
(`negl_finset_sum`, then the `CollisionResistant` leaf at each round). -/
theorem friFold_binding_advantage_bound {F : KeyedHashFamily} (rounds : Finset ℕ)
    (finder : ℕ → CollisionFinder F) (hCR : CollisionResistant F) :
    Negl (fun n => ∑ r ∈ rounds, collisionAdv F (finder r) n) := by
  thread_advantage_bound

/-! ## §3 — PROTOTYPE on the MIXED tower shape: de-batch scale + multi-round sum + zero leg.

A full `AlgoStarkSoundTransferV3`-style soundness error threads THREE contributions additively: an RLC
de-batching term SCALED by a query-count factor, the multi-round Merkle fold SUM, and an algebra leg that
carries no hash (advantage `0`). `thread_advantage_bound` composes `negl_add` / `negl_const_mul` /
`negl_finset_sum` / `negl_zero` and closes every collision leaf from the one floor — the whole tower's
"no equivocation anywhere" becomes "negligible total binding-failure advantage". -/

/-- **MIXED tower restatement.** A composite STARK soundness-error advantage
`c · (debatch term) + ∑_{r ∈ rounds} (per-round collision) + 0` is negligible under the proper floor —
the additive threading of every hash leg through the tower. Proof: `thread_advantage_bound` (the full
closure spine: const-scale, finite-sum, zero, all bottoming at the `CollisionResistant` leaf). -/
theorem stark_sound_tower_advantage_bound {F : KeyedHashFamily}
    (c : ℝ) (debatch : CollisionFinder F) (rounds : Finset ℕ) (finder : ℕ → CollisionFinder F)
    (hCR : CollisionResistant F) :
    Negl (fun n => c * collisionAdv F debatch n
        + (∑ r ∈ rounds, collisionAdv F (finder r) n) + 0) := by
  thread_advantage_bound

/-! ## §4 — PROTOTYPE on the ADVERSARY-INDEXED floor (the crypto/lattice leg).

The `CryptoFloorTeeth` re-grounding replaces the Boolean `MSISHard` with the adversary-indexed
`MSISHardQuant adv := ∀ s, Negl (adv s)`. A forger's advantage at a fixed solver index threads directly
through the floor leaf — the same tactic covers the lattice side of the sweep. -/

/-- **ADVERSARY-INDEXED restatement.** Under `MSISHardQuant adv` (the proper resource-bounded floor), the
advantage of any fixed solver index `s` is negligible — the leaf that re-threads every `MSISHard`
consumer. Proof: `thread_advantage_bound` (the `MSISHardQuant` floor leaf). -/
theorem forger_advantage_bound_under_msis {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : MSISHardQuant adv) :
    Negl (adv s) := by
  thread_advantage_bound

/-- A mixed lattice bound: a decaying challenge-space term `1/2ⁿ` PLUS the solver's advantage, negligible
under the floor — `negl_two_pow` on the challenge leg, the floor leaf on the solver leg. -/
theorem forger_advantage_with_challenge_bound {S : Type*} (adv : S → Ensemble) (s : S)
    (hfloor : MSISHardQuant adv) :
    Negl (fun n => (1 / (2 : ℝ) ^ n) + adv s n) := by
  thread_advantage_bound

/-! ## §5 — TEETH: the tactic is a REAL discharger, not a `sorry` in tactic costume.

It closes a `Negl` goal ONLY when the negligibility is genuinely available (a floor leaf or a decaying
term through the closure algebra). On a NON-negligible goal — the constant `1`, with no floor to appeal
to — it FAILS. `fail_if_success` witnesses the refusal; a `sorry`-in-disguise tactic would pass here. -/

/-- **(TOOTH — the tactic REFUSES a non-negligible goal.)** The constant-`1` ensemble is NOT negligible
(`ConcreteSecurity.not_negl_one`); `thread_advantage_bound` cannot close it (no leaf matches, no floor in
context), so the inner `have` fails and `fail_if_success` succeeds. This is the non-vacuity teeth: the
tactic discharges REAL negligibility, it does not fabricate it. -/
example : True := by
  fail_if_success
    (have : Negl (fun _ : ℕ => (1 : ℝ)) := by thread_advantage_bound)
  trivial

-- **(TOOTH — the tactic REFUSES a floor leaf with NO floor in context.)** Even a genuine `collisionAdv`
-- advantage is not closable without the `CollisionResistant` floor hypothesis — the tactic does not invent
-- the assumption.
set_option linter.unusedVariables false in
example (F : KeyedHashFamily) (A : CollisionFinder F) : True := by
  fail_if_success
    (have : Negl (collisionAdv F A) := by thread_advantage_bound)
  trivial

/-! ## §6 — axiom-hygiene pins. -/

#assert_all_clean [
  commitment_binding_advantage_bound,
  friFold_binding_advantage_bound,
  stark_sound_tower_advantage_bound,
  forger_advantage_bound_under_msis,
  forger_advantage_with_challenge_bound
]

end Dregg2.Tactics.ThreadAdvantageBound
