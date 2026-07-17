/-
# `Dregg2.Crypto.SpongeCompressionRegrounded` — the `CompressionCR` consumers RE-GROUNDED off the
FALSE-AS-NAMED injective floor onto a REAL collision game carrying an explicit `Eff`.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `CompressionCR` site)

`SpongeReduction.CompressionCR M := ∀ s t a b, M.step s a = M.step t b → s = t ∧ a = b` is stated as
**injectivity** of the per-block compression `step = perm ∘ absorb`, uncurried
`State × List ℤ → State`. Its DOMAIN is infinite (`List ℤ` is infinite — `HashFloorHonesty`'s own
instance — and `State` is inhabited, so the product is infinite). Its CODOMAIN is `State`, which for a
REAL sponge is a fixed-width array of felts: a FINITE type. So the floor is **FALSE at deployed
parameters by pigeonhole** (§1, `compressionCR_false_of_finite_range` /
`compressionCR_false_of_finite_state`) — no Poseidon2 collision need be exhibited; cardinality
suffices, and `[Finite State]` needs no numeric bound because a real sponge state IS a finite type.

⚑ **This is the file's headline that goes vacuous.** `SpongeReduction.spongeCR_of_reduction` is what
makes the whole full-state commitment tower's `spongeCR` carrier "a THEOREM over `CompressionCR` +
`SqueezeBindsReachable`" rather than an assumption — it is the reason primitive #4 was demoted from
"the unbounded list-hash is injective" to "ONE permutation call is CR". If `CompressionCR` is EMPTY at
deployed parameters, that demotion is vacuous there, and so are `foldl_step_eq`, `finalState_inj` and
`realizedSpongeOfReduction`. `#assert_axioms` is blind: those proofs are clean; the HYPOTHESIS is the
flaw.

`SpongeReduction`'s own non-vacuity witnesses give FALSE COMFORT, exactly as `HashFloorHonesty`'s
header predicts: `Reference.refCompressionCR` satisfies the floor with an INJECTIVE toy "permutation"
(increment a tag, append the block to an unbounded list — a state that GROWS with the input, i.e. not
a fixed-width state at all), and `badMachine_not_squeezeBinds` refutes a DIFFERENT carrier. Toy
witness satisfiable, real fixed-width sponge false.

## The re-grounding (the `PreRotationKeySetRegrounded` pattern)

  * **§1 — FALSE AS NAMED.** The counting core (`HashFloorHonesty.not_injective_of_finite_range`)
    fires on the uncurried `step`; `compressionCR_false_of_finite_state` is the deployed form.
  * **§2 — the KEYED family.** `SpongeDeployment` bundles the deployed machine with its
    domain-separation tag space (the effective key — the standard keyed-from-unkeyed model).
    `compressionFamily` lifts it to a `HashFloorHonesty.KeyedHashFamily`;
    `deployed_step_is_family_instance` pins FAITHFULNESS — the game is about the very compression the
    circuit computes.
  * **§3 — the ATTACK GAMES.** Three, one per old consumer, each a first-class λ-indexed game: the MD
    peel game (`mdPeelGame`, `foldl_step_eq`'s content), the final-state collision game
    (`finalStateCollisionGame`, `finalState_inj`'s), and — the headline — the SPONGE DIGEST COLLISION
    game (`spongeCollisionGame`, exactly what `spongeCR_of_reduction` rules out).
  * **§4 — THE REDUCTION, and it is CONSTRUCTIVE.** ⚑ The lane brief's suggested attack game ("output
    two `(state, block)` pairs colliding under `step`") IS the compression-collision game, which would
    have made the extractor an IDENTITY and the reduction decoration. So the attack games here are the
    real consumers' events instead, and `peel` is a genuine extractor: it walks the two `foldl step`
    chains from the LAST block inward and RETURNS THE FIRST DIVERGENCE as an explicit compression
    collision (`peel_spec`). It is the MD peel of `foldl_step_eq` read as an algorithm, uses the
    adversary's actual output, and needs no `Classical.choice` to find the collision — the
    init-vs-step boundary case is discharged by the structural `InitStepSeparated`, exactly where the
    length prefix earns its keep.
  * **§5 — the RE-GROUNDED CONSUMERS.** `foldl_step_eq_advantage_bound`,
    `finalState_inj_advantage_bound`, and the headline `spongeCR_of_reduction_advantage_bound`: the
    Boolean "a digest collision is impossible" becomes "except with negligible probability", from the
    compression-collision floor VIA the reduction.

## ⚑ THE `Eff` PARAMETER IS THE WHOLE HONESTY, AND IT IS UNDISCHARGED

The sweep's load-bearing result (`FloorGames` §2, `hard_top_iff_solvableFrac_negl`): at the
UNRESTRICTED adversary class a game floor IS the existence floor, so it is FALSE wherever collisions
exist — and §1 proves they exist at any fixed-width state. §7 instantiates both poles at THIS carrier:
`compression_floor_top_false_of_finite_state` (`Eff := ⊤` is FALSE at a real sponge state — no bound,
no parameter, just `Finite State`) and `compression_floor_bot_vacuous` (`Eff := ⊥` is vacuous). So
`Eff` is a PARAMETER, in the open, at every use site: this tree has no cost model (`FloorGames` §8),
and inventing a shallow imitation would be another costume. Hiding the `Eff` dependence is the
disease; naming it is the repair.

## Non-fake

The floor is REFUTABLE (`brokenSponge_floor_top_false`: a machine whose permutation is constant has a
finder winning at every tag, advantage `1`) and the reduction is LOAD-BEARING (§6's canary: the
keystone does NOT follow from the floor applied at some OTHER finder). The OLD `CompressionCR`
consumers are KEPT untouched in `SpongeReduction`; siblings ADDED. `#assert_all_clean`; no `sorry`, no
fresh `axiom`.

## Coordination

This is the SPONGE compression lane. The beacon honest-slot carrier is re-grounded in
`Crypto.BeaconSlotRegrounded`; the pre-rotation key-set carrier in
`Apps.PreRotationKeySetRegrounded`; the STARK/FRI/Merkle hash consumers in
`Circuit.FloorRegroundedConsumers` / `Circuit.Poseidon2KeyedBridge`.
-/
import Dregg2.Crypto.SpongeReduction
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames

namespace Dregg2.Crypto.SpongeCompressionRegrounded

open Dregg2.Crypto.SpongeReduction
  (SpongeMachine CompressionCR SqueezeBindsReachable InitStepSeparated foldl_step_eq finalState_inj
   spongeCR_of_reduction)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv injective_family_CR
   not_injective_of_finite_range)
open Dregg2.Crypto.ProbCrypto (winProb winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED: the injective `CompressionCR` floor is refuted by a fixed-width state.

`CompressionCR M` IS `Function.Injective (fun p : State × List ℤ => M.step p.1 p.2)`. The domain is
INFINITE (`List ℤ` is infinite; `State` is inhabited via the machine's own `init`), the codomain of a
REAL sponge compression is the fixed-width state — a FINITE type. The counting core fires. -/

/-- **TOOTH — `CompressionCR` is FALSE for any range-bounded compression.** Literally the counting
core: the floor IS injectivity of the uncurried `step` on the infinite `State × List ℤ`, while a real
compression's range is finite. Stated in the same shape as the flagged siblings' teeth
(`HashFloorHonesty.compressInjective_false_of_finite_range`, which derives the pair equality from the
same `a = c ∧ b = d` conjunction). -/
theorem compressionCR_false_of_finite_range {State : Type} [Nonempty State] (M : SpongeMachine State)
    (hfin : (Set.range (fun p : State × List ℤ => M.step p.1 p.2)).Finite) : ¬ CompressionCR M := by
  intro hCR
  refine not_injective_of_finite_range (fun p : State × List ℤ => M.step p.1 p.2) hfin ?_
  rintro ⟨s, a⟩ ⟨t, b⟩ heq
  obtain ⟨h1, h2⟩ := hCR s t a b heq
  simp [h1, h2]

/-- **⚑ TOOTH (deployed form) — `CompressionCR` is FALSE at any FIXED-WIDTH sponge state.** The whole
point of `SpongeReduction` is that the genuine primitive is ONE call of a FIXED-WIDTH permutation
`P : State → State` — a fixed-width array of felts, i.e. a `Finite` type. That single instance
assumption is all the refutation needs: no numeric bound, no field modulus, no parameter regime. The
floor is not merely un-proven at the real Poseidon2 compression; it is provably FALSE there, so
`foldl_step_eq`, `finalState_inj`, `spongeCR_of_reduction` and `realizedSpongeOfReduction` are all
VACUOUS at deployed parameters — and with them the tower's demotion of primitive #4. -/
theorem compressionCR_false_of_finite_state {State : Type} [Nonempty State] [Finite State]
    (M : SpongeMachine State) : ¬ CompressionCR M :=
  compressionCR_false_of_finite_range M (Set.toFinite _)

/-- **THE COLLISION THE FALSITY EXHIBITS.** A range-bounded compression has, at every parameter, a
genuine chaining collision — two DISTINCT `(state, block)` pairs with the same next state. This is the
counting core in the positive form the game floors below consume: it is what makes the `⊤`-class floor
false (§7), and therefore what makes the `Eff` parameter load-bearing rather than decorative. -/
theorem exists_step_collision_of_finite_range {State : Type} [Nonempty State]
    (M : SpongeMachine State)
    (hfin : (Set.range (fun p : State × List ℤ => M.step p.1 p.2)).Finite) :
    ∃ q : (State × List ℤ) × (State × List ℤ),
      q.1 ≠ q.2 ∧ M.step q.1.1 q.1.2 = M.step q.2.1 q.2.2 := by
  by_contra hno
  push_neg at hno
  refine not_injective_of_finite_range (fun p : State × List ℤ => M.step p.1 p.2) hfin ?_
  intro a b hab
  by_contra hne
  exact hno (a, b) hne hab

/-- **(Deployed form of the same.)** A fixed-width state has a chaining collision, full stop. -/
theorem exists_step_collision_of_finite_state {State : Type} [Nonempty State] [Finite State]
    (M : SpongeMachine State) :
    ∃ q : (State × List ℤ) × (State × List ℤ),
      q.1 ≠ q.2 ∧ M.step q.1.1 q.1.2 = M.step q.2.1 q.2.2 :=
  exists_step_collision_of_finite_range M (Set.toFinite _)

/-! ## §2 — the KEYED family: domain separation is the key.

The deployed Poseidon2 permutation is a FIXED unkeyed function; its effective key is the
domain-separation tag / parameter regime the deployment instantiates (`Poseidon2KeyedBridge` §1-§2).
Modelling that tag as the key is the standard keyed-from-unkeyed treatment and is what stops the
"hardcode a known collision" degeneracy that collapses an unkeyed floor. -/

/-- **The deployed sponge compression scheme.** `machine t` is the deployed `SpongeMachine` at
domain-separation tag `t` (the real `hash_many` wiring: `perm`, `init`, `absorb`, `squeeze`, `rate`);
`Tag` is the finite, inhabited tag space the CR game samples; `deployedTag` is the tag the circuit
computes at. `stateDecEq`/`stateNonempty` are what the game needs to CHECK a collision and what the
machine's own `init` already gives. -/
structure SpongeDeployment (State : Type) where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The deployed sponge machine at each tag — the real `hash_many` wiring. -/
  machine : Tag → SpongeMachine State
  /-- Decidable equality on states (the game checks two chaining values are distinct). -/
  stateDecEq : DecidableEq State
  /-- The state type is inhabited (the machine's own `init` already witnesses this). -/
  stateNonempty : Nonempty State
  /-- The specific domain-separation tag the circuit computes. -/
  deployedTag : Tag

/-- **`compressionFamily D`** — the deployed per-block compression lifted to a `KeyedHashFamily`,
keyed by its domain-separation tag, with the uncurried `(state, block) ↦ next state` as the hash. This
is the object `HashFloorHonesty.CollisionResistant` is realized at for the real permutation. -/
def compressionFamily {State : Type} (D : SpongeDeployment State) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := State × List ℤ
  Out := State
  H := fun _ t p => (D.machine t).step p.1 p.2
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := letI := D.stateDecEq; inferInstance
  outDecEq := D.stateDecEq

/-- **FAITHFULNESS.** The deployed FIXED compression IS the keyed family's instance at the deployed
tag — a definitional equality, no idealization. So the CR game below is a game about the very
`perm ∘ absorb` the circuit computes. -/
theorem deployed_step_is_family_instance {State : Type} (D : SpongeDeployment State) (n : ℕ) :
    (fun p : State × List ℤ => (D.machine D.deployedTag).step p.1 p.2)
      = (compressionFamily D).H n D.deployedTag := rfl

/-- **THE OLD-FLOOR ⟹ NEW-FLOOR BRIDGE.** If the injective `CompressionCR` held at every tag it would
discharge `CollisionResistant (compressionFamily D)` (no collisions ⟹ every finder's advantage `0`).
So the OLD floor was STRICTLY STRONGER than the honest computational floor — and, being FALSE at any
fixed-width state (§1), it was an EMPTY hypothesis. Nothing is lost re-grounding; a false hypothesis
is replaced by one a real permutation can satisfy. -/
theorem compressionFamily_CR_of_compressionCR {State : Type} (D : SpongeDeployment State)
    (hCR : ∀ t : D.Tag, CompressionCR (D.machine t)) : CollisionResistant (compressionFamily D) :=
  injective_family_CR (compressionFamily D) (fun _ t => by
    rintro ⟨s, a⟩ ⟨u, b⟩ heq
    obtain ⟨h1, h2⟩ := hCR t s u a b heq
    simp [h1, h2])

/-! ## §3 — the compression COLLISION GAME and the three ATTACK GAMES, as first-class objects.

⚑ A note on the shape, because it is part of the deliverable. The obvious attack game — "the adversary
outputs two `(state, block)` pairs that collide under `step`" — is DEFINITIONALLY the collision game,
so the extractor would be the identity and the "reduction" a rename. The attack games below are the
events the OLD consumers actually rule out (a block-list ambiguity, a final-state collision, a digest
collision), and §4's `peel` is a genuine extractor from each of them to a chaining collision. -/

/-- **THE COMPRESSION COLLISION GAME.** Instances are sampled domain-separation tags; the adversary
outputs two `(state, block)` pairs and WINS iff they are a GENUINE chaining collision of the deployed
compression at that tag — distinct pairs, equal next state. This is the game the floor below
quantifies over, with an explicit adversary class, and it is exactly the event the MD peel in
`foldl_step_eq` rules out. -/
def compressionCollisionGame {State : Type} (D : SpongeDeployment State) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (State × List ℤ) × (State × List ℤ)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t q =>
    q.1 ≠ q.2 ∧ (D.machine t).step q.1.1 q.1.2 = (D.machine t).step q.2.1 q.2.2
  winsDec := fun _ t q => by
    letI := D.stateDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine
chaining collision of the real deployed `perm ∘ absorb`. Not a docstring: the `Prop` itself. -/
theorem compressionCollisionGame_wins_iff {State : Type} (D : SpongeDeployment State) (n : ℕ)
    (t : D.Tag) (q : (State × List ℤ) × (State × List ℤ)) :
    (compressionCollisionGame D).wins n t q ↔
      (q.1 ≠ q.2 ∧ (D.machine t).step q.1.1 q.1.2 = (D.machine t).step q.2.1 q.2.2) :=
  Iff.rfl

/-- **THE MD-PEEL ATTACK GAME (`foldl_step_eq`'s event).** The adversary outputs two
`(block list, length tag)` pairs and WINS iff the two `foldl step` runs land on the SAME state while
the runs are NOT the same — different length tag or different blocks. Winning IS the ambiguity
`foldl_step_eq` rules out: two distinct absorption histories that the chaining value cannot tell
apart. -/
def mdPeelGame {State : Type} (D : SpongeDeployment State) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (List (List ℤ) × ℕ) × (List (List ℤ) × ℕ)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t q =>
    ¬ ((D.machine t).init q.1.2 = (D.machine t).init q.2.2 ∧ q.1.1 = q.2.1) ∧
      List.foldl (D.machine t).step ((D.machine t).init q.1.2) q.1.1
        = List.foldl (D.machine t).step ((D.machine t).init q.2.2) q.2.1
  winsDec := fun _ t q => by
    letI := D.stateDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (2/4).** -/
theorem mdPeelGame_wins_iff {State : Type} (D : SpongeDeployment State) (n : ℕ) (t : D.Tag)
    (q : (List (List ℤ) × ℕ) × (List (List ℤ) × ℕ)) :
    (mdPeelGame D).wins n t q ↔
      (¬ ((D.machine t).init q.1.2 = (D.machine t).init q.2.2 ∧ q.1.1 = q.2.1) ∧
        List.foldl (D.machine t).step ((D.machine t).init q.1.2) q.1.1
          = List.foldl (D.machine t).step ((D.machine t).init q.2.2) q.2.1) :=
  Iff.rfl

/-- **THE FINAL-STATE COLLISION ATTACK GAME (`finalState_inj`'s event).** The adversary outputs two
input lists and WINS iff they are DISTINCT yet drive the sponge to the SAME final state — the
full-state collision `finalState_inj` rules out. -/
def finalStateCollisionGame {State : Type} (D : SpongeDeployment State) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List ℤ × List ℤ
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ (D.machine t).finalState p.1 = (D.machine t).finalState p.2
  winsDec := fun _ t p => by
    letI := D.stateDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (3/4).** -/
theorem finalStateCollisionGame_wins_iff {State : Type} (D : SpongeDeployment State) (n : ℕ)
    (t : D.Tag) (p : List ℤ × List ℤ) :
    (finalStateCollisionGame D).wins n t p ↔
      (p.1 ≠ p.2 ∧ (D.machine t).finalState p.1 = (D.machine t).finalState p.2) :=
  Iff.rfl

/-- **⚑ THE SPONGE DIGEST COLLISION ATTACK GAME (`spongeCR_of_reduction`'s event — the headline).**
The adversary outputs two input lists and WINS iff they are DISTINCT yet `hash_many` maps them to the
SAME digest. This is `Poseidon2SpongeCR` broken; it is the event the whole full-state commitment tower
conditions on being impossible, and the object `realizedSpongeOfReduction` packages. -/
def spongeCollisionGame {State : Type} (D : SpongeDeployment State) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List ℤ × List ℤ
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ (D.machine t).spongeOf p.1 = (D.machine t).spongeOf p.2
  winsDec := fun _ t p => by infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (4/4)** — a sponge-attack win is, by `Iff.rfl`, a genuine
collision of the deployed variable-length digest. -/
theorem spongeCollisionGame_wins_iff {State : Type} (D : SpongeDeployment State) (n : ℕ) (t : D.Tag)
    (p : List ℤ × List ℤ) :
    (spongeCollisionGame D).wins n t p ↔
      (p.1 ≠ p.2 ∧ (D.machine t).spongeOf p.1 = (D.machine t).spongeOf p.2) :=
  Iff.rfl

/-! ## §4 — THE REDUCTION: the MD peel, read as an EXTRACTOR.

`peel` walks the two `foldl step` chains from the LAST block inward and returns the FIRST place they
diverge, as an explicit `(state, block)` pair collision. It is `foldl_step_eq`'s induction turned
inside out: where that theorem CONSUMES `CompressionCR` to conclude the chains agree, `peel` PRODUCES
the compression collision that a disagreement forces. It uses the adversary's actual output, is
structurally recursive, and appeals to no choice principle — the only case it cannot handle is the
`init`-vs-`step` boundary, which the STRUCTURAL `InitStepSeparated` rules out in `peel_spec`. -/

/-- **THE EXTRACTOR.** `peel M junk m n rcs rds` takes the two block lists REVERSED (so the last
absorbed block is at the head) and returns the first divergence: the two chaining states with the
blocks they absorbed. `junk` is returned on the branches `peel_spec` proves unreachable (both lists
empty — no ambiguity to extract; one empty — the `init`-vs-`step` boundary `InitStepSeparated`
excludes). -/
def peel {State : Type} [DecidableEq State] (M : SpongeMachine State) (junk : State) (m n : ℕ) :
    List (List ℤ) → List (List ℤ) → (State × List ℤ) × (State × List ℤ)
  | [], [] => ((junk, []), (junk, []))
  | _ :: _, [] => ((junk, []), (junk, []))
  | [], _ :: _ => ((junk, []), (junk, []))
  | c :: rcs, e :: rds =>
      if (List.foldl M.step (M.init m) rcs.reverse, c)
          = (List.foldl M.step (M.init n) rds.reverse, e) then
        peel M junk m n rcs rds
      else
        ((List.foldl M.step (M.init m) rcs.reverse, c),
         (List.foldl M.step (M.init n) rds.reverse, e))

/-- The extractor's step equation (the only branch that does work). -/
theorem peel_cons_cons {State : Type} [DecidableEq State] (M : SpongeMachine State) (junk : State)
    (m n : ℕ) (c e : List ℤ) (rcs rds : List (List ℤ)) :
    peel M junk m n (c :: rcs) (e :: rds)
      = if (List.foldl M.step (M.init m) rcs.reverse, c)
            = (List.foldl M.step (M.init n) rds.reverse, e) then
          peel M junk m n rcs rds
        else
          ((List.foldl M.step (M.init m) rcs.reverse, c),
           (List.foldl M.step (M.init n) rds.reverse, e)) := rfl

/-- **⚑ THE EXTRACTOR IS CORRECT — and this IS `foldl_step_eq`, run backwards.** Two `foldl step`
chains that land on the same state without being the same chain must diverge somewhere, and `peel`
RETURNS that divergence as a genuine compression collision: distinct `(state, block)` pairs, equal
next state. The structural `InitStepSeparated` (the length-prefix domain separation) discharges the
asymmetric base cases — exactly where it earns its keep in the original induction. No crypto content
is assumed here; the crypto content is what the collision is HANDED to. -/
theorem peel_spec {State : Type} [DecidableEq State] (M : SpongeMachine State) (junk : State)
    (hSep : InitStepSeparated M) (m n : ℕ) :
    ∀ rcs rds : List (List ℤ),
      List.foldl M.step (M.init m) rcs.reverse = List.foldl M.step (M.init n) rds.reverse →
      ¬ (M.init m = M.init n ∧ rcs = rds) →
      (peel M junk m n rcs rds).1 ≠ (peel M junk m n rcs rds).2 ∧
        M.step (peel M junk m n rcs rds).1.1 (peel M junk m n rcs rds).1.2
          = M.step (peel M junk m n rcs rds).2.1 (peel M junk m n rcs rds).2.2 := by
  intro rcs
  induction rcs with
  | nil =>
      intro rds h hne
      cases rds with
      | nil =>
          exact absurd ⟨h, rfl⟩ hne
      | cons e rds' =>
          exfalso
          simp only [List.reverse_nil, List.foldl_nil, List.reverse_cons, List.foldl_concat] at h
          exact hSep m _ e h
  | cons c rcs' ih =>
      intro rds h hne
      cases rds with
      | nil =>
          exfalso
          simp only [List.reverse_nil, List.foldl_nil, List.reverse_cons, List.foldl_concat] at h
          exact hSep n _ c h.symm
      | cons e rds' =>
          simp only [List.reverse_cons, List.foldl_concat] at h
          by_cases hq : (List.foldl M.step (M.init m) rcs'.reverse, c)
              = (List.foldl M.step (M.init n) rds'.reverse, e)
          · rw [peel_cons_cons, if_pos hq]
            obtain ⟨hs, hc⟩ := Prod.mk.injEq .. ▸ hq
            refine ih rds' hs ?_
            rintro ⟨hi, hr⟩
            exact hne ⟨hi, by rw [hr, hc]⟩
          · rw [peel_cons_cons, if_neg hq]
            exact ⟨hq, h⟩

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES (MD peel).** An adversary exhibiting an ambiguous
absorption history becomes a compression-collision finder: hand its two block lists to `peel`. -/
noncomputable def mdPeelToCompressionFinder {State : Type} (D : SpongeDeployment State)
    (A : Adversary (mdPeelGame D)) : Adversary (compressionCollisionGame D) where
  run := fun l t =>
    @peel State D.stateDecEq (D.machine t) D.stateNonempty.some
      (A.run l t).1.2 (A.run l t).2.2 (A.run l t).1.1.reverse (A.run l t).2.1.reverse

/-- **WIN-PRESERVATION (MD peel).** Wherever the adversary wins, the extracted pair is a GENUINE
chaining collision of the deployed compression. -/
theorem mdPeel_wins_imp {State : Type} (D : SpongeDeployment State)
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t)) (A : Adversary (mdPeelGame D)) (l : ℕ)
    (t : D.Tag) (hwin : (mdPeelGame D).wins l t (A.run l t)) :
    (compressionCollisionGame D).wins l t ((mdPeelToCompressionFinder D A).run l t) := by
  obtain ⟨hne, hfold⟩ := hwin
  have h1 : List.foldl (D.machine t).step ((D.machine t).init (A.run l t).1.2)
      ((A.run l t).1.1.reverse).reverse
        = List.foldl (D.machine t).step ((D.machine t).init (A.run l t).2.2)
          ((A.run l t).2.1.reverse).reverse := by
    rw [List.reverse_reverse, List.reverse_reverse]
    exact hfold
  have h2 : ¬ ((D.machine t).init (A.run l t).1.2 = (D.machine t).init (A.run l t).2.2
      ∧ (A.run l t).1.1.reverse = (A.run l t).2.1.reverse) := by
    rintro ⟨hi, hr⟩
    exact hne ⟨hi, List.reverse_injective hr⟩
  exact @peel_spec State D.stateDecEq (D.machine t) D.stateNonempty.some (hSep t)
    (A.run l t).1.2 (A.run l t).2.2 _ _ h1 h2

/-- **THE ADVANTAGE INEQUALITY (MD peel).** Both play over the SAME sampled tag space, and every tag
the adversary wins the extracted finder wins. -/
theorem mdPeel_adv_le {State : Type} (D : SpongeDeployment State)
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t)) (A : Adversary (mdPeelGame D)) (l : ℕ) :
    gameAdv (mdPeelGame D) A l
      ≤ gameAdv (compressionCollisionGame D) (mdPeelToCompressionFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact mdPeel_wins_imp D hSep A l t ht

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES (final state).** A final-state collider becomes a
compression-collision finder: chunk its two inputs (`inputs.chunks(rate)`, the real wiring) and hand
the two block lists to `peel`. -/
noncomputable def finalStateToCompressionFinder {State : Type} (D : SpongeDeployment State)
    (A : Adversary (finalStateCollisionGame D)) : Adversary (compressionCollisionGame D) where
  run := fun l t =>
    @peel State D.stateDecEq (D.machine t) D.stateNonempty.some
      (A.run l t).1.length (A.run l t).2.length
      ((D.machine t).chunksOf (A.run l t).1).reverse ((D.machine t).chunksOf (A.run l t).2).reverse

/-- **WIN-PRESERVATION (final state).** A final-state collision on DISTINCT inputs has distinct block
lists (`chunksOf` is flatten-invertible — the structural alignment step), so `peel` finds a genuine
chaining collision. -/
theorem finalState_wins_imp {State : Type} (D : SpongeDeployment State)
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (A : Adversary (finalStateCollisionGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (finalStateCollisionGame D).wins l t (A.run l t)) :
    (compressionCollisionGame D).wins l t ((finalStateToCompressionFinder D A).run l t) := by
  obtain ⟨hne, hfs⟩ := hwin
  have h1 : List.foldl (D.machine t).step ((D.machine t).init (A.run l t).1.length)
      (((D.machine t).chunksOf (A.run l t).1).reverse).reverse
        = List.foldl (D.machine t).step ((D.machine t).init (A.run l t).2.length)
          (((D.machine t).chunksOf (A.run l t).2).reverse).reverse := by
    rw [List.reverse_reverse, List.reverse_reverse]
    exact hfs
  have h2 : ¬ ((D.machine t).init (A.run l t).1.length = (D.machine t).init (A.run l t).2.length
      ∧ ((D.machine t).chunksOf (A.run l t).1).reverse
          = ((D.machine t).chunksOf (A.run l t).2).reverse) := by
    rintro ⟨_, hr⟩
    have hch := List.reverse_injective hr
    apply hne
    have := congrArg List.flatten hch
    rwa [(D.machine t).chunksOf_flatten, (D.machine t).chunksOf_flatten] at this
  exact @peel_spec State D.stateDecEq (D.machine t) D.stateNonempty.some (hSep t)
    (A.run l t).1.length (A.run l t).2.length _ _ h1 h2

/-- **THE ADVANTAGE INEQUALITY (final state).** -/
theorem finalState_adv_le {State : Type} (D : SpongeDeployment State)
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (A : Adversary (finalStateCollisionGame D)) (l : ℕ) :
    gameAdv (finalStateCollisionGame D) A l
      ≤ gameAdv (compressionCollisionGame D) (finalStateToCompressionFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact finalState_wins_imp D hSep A l t ht

/-- **THE TRUNCATION LEG.** A sponge DIGEST collider is a FINAL-STATE collider — under the honest
truncation residual `SqueezeBindsReachable`, which is the SEPARATE named carrier `SpongeReduction`
already isolates. Identity on data; the content is that the squeeze binds. -/
def spongeToFinalStateAdv {State : Type} (D : SpongeDeployment State)
    (A : Adversary (spongeCollisionGame D)) : Adversary (finalStateCollisionGame D) where
  run := A.run

/-- **WIN-PRESERVATION (truncation leg).** -/
theorem spongeToFinalState_wins_imp {State : Type} (D : SpongeDeployment State)
    (hSq : ∀ t : D.Tag, SqueezeBindsReachable (D.machine t))
    (A : Adversary (spongeCollisionGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (spongeCollisionGame D).wins l t (A.run l t)) :
    (finalStateCollisionGame D).wins l t ((spongeToFinalStateAdv D A).run l t) := by
  obtain ⟨hne, hdig⟩ := hwin
  exact ⟨hne, hSq t _ _ hdig⟩

/-- **THE ADVANTAGE INEQUALITY (truncation leg).** -/
theorem spongeToFinalState_adv_le {State : Type} (D : SpongeDeployment State)
    (hSq : ∀ t : D.Tag, SqueezeBindsReachable (D.machine t))
    (A : Adversary (spongeCollisionGame D)) (l : ℕ) :
    gameAdv (spongeCollisionGame D) A l
      ≤ gameAdv (finalStateCollisionGame D) (spongeToFinalStateAdv D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact spongeToFinalState_wins_imp D hSq A l t ht

/-- **⚑ THE HEADLINE EXTRACTOR.** A sponge DIGEST collider becomes a compression-collision finder:
truncation residual lifts the digest collision to a final-state collision, `peel` peels that into a
chaining collision. This is `spongeCR_of_reduction`'s whole argument, run as an algorithm. -/
noncomputable def spongeToCompressionFinder {State : Type} (D : SpongeDeployment State)
    (A : Adversary (spongeCollisionGame D)) : Adversary (compressionCollisionGame D) :=
  finalStateToCompressionFinder D (spongeToFinalStateAdv D A)

/-- **⚑ WIN-PRESERVATION — and this IS `spongeCR_of_reduction`, at the game level.** -/
theorem sponge_wins_imp {State : Type} (D : SpongeDeployment State)
    (hSq : ∀ t : D.Tag, SqueezeBindsReachable (D.machine t))
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (A : Adversary (spongeCollisionGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (spongeCollisionGame D).wins l t (A.run l t)) :
    (compressionCollisionGame D).wins l t ((spongeToCompressionFinder D A).run l t) :=
  finalState_wins_imp D hSep (spongeToFinalStateAdv D A) l t
    (spongeToFinalState_wins_imp D hSq A l t hwin)

/-- **THE ADVANTAGE INEQUALITY (headline).** The sponge-collision adversary's advantage is at most the
extracted chaining-collision finder's, at every parameter — a genuine reduction inequality over real
game advantages, composed through the truncation leg. -/
theorem sponge_adv_le {State : Type} (D : SpongeDeployment State)
    (hSq : ∀ t : D.Tag, SqueezeBindsReachable (D.machine t))
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (A : Adversary (spongeCollisionGame D)) (l : ℕ) :
    gameAdv (spongeCollisionGame D) A l
      ≤ gameAdv (compressionCollisionGame D) (spongeToCompressionFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact sponge_wins_imp D hSq hSep A l t ht

/-! ## §5 — the RE-GROUNDED CONSUMERS.

The Boolean keystones become advantage bounds, derived FROM the compression-collision floor VIA the
reduction. The old statements are kept in `SpongeReduction`; these are their honest siblings. -/

/-- **⚑ RE-GROUNDED `SpongeReduction.foldl_step_eq`.** Under the compression-collision floor at the
game the reduction actually attacks, an adversary exhibiting an ambiguous absorption history has
NEGLIGIBLE advantage. The Boolean "equal chaining value ⟹ equal block lists" becomes "equal EXCEPT
with negligible probability" — which is what a real fixed-width permutation can deliver, and what the
FALSE injective floor was standing in for. `hSep` stays a HYPOTHESIS and stays STRUCTURAL: it is a
property of the real `init`/`perm`, not a crypto carrier.

⚑ **`hEff` IS UNDISCHARGED AND THAT IS THE HONEST STATE** — the standard "the reduction is efficient"
side condition, a PARAMETER because this tree has no cost model (`FloorGames` §8). The floor's honesty
is exactly its `Eff`'s, and §7 prices both poles: `⊤` makes it FALSE at a fixed-width state, `⊥`
vacuous. -/
theorem foldl_step_eq_advantage_bound {State : Type} (D : SpongeDeployment State)
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (Eff : Adversary (compressionCollisionGame D) → Prop) (A : Adversary (mdPeelGame D))
    (hEff : Eff (mdPeelToCompressionFinder D A))
    (hcol : Hard (compressionCollisionGame D) Eff) :
    Negl (gameAdv (mdPeelGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (mdPeelGame D) A l).1) (mdPeel_adv_le D hSep A)
    (hcol _ hEff)

/-- **⚑ RE-GROUNDED `SpongeReduction.finalState_inj`.** Two distinct inputs drive the sponge to the
same FULL final state only with negligible probability: such a collider is, via `chunksOf`'s
flatten-invertibility and `peel`, a chaining-collision finder. The `Eff` obligation is the same
undischarged side condition — named, not hidden. -/
theorem finalState_inj_advantage_bound {State : Type} (D : SpongeDeployment State)
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (Eff : Adversary (compressionCollisionGame D) → Prop)
    (A : Adversary (finalStateCollisionGame D))
    (hEff : Eff (finalStateToCompressionFinder D A))
    (hcol : Hard (compressionCollisionGame D) Eff) :
    Negl (gameAdv (finalStateCollisionGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (finalStateCollisionGame D) A l).1)
    (finalState_adv_le D hSep A) (hcol _ hEff)

/-- **⚑⚑ RE-GROUNDED `SpongeReduction.spongeCR_of_reduction` — THE HEADLINE, HONESTLY.**

The whole full-state commitment tower's `spongeCR` carrier, re-grounded. The Boolean
`Poseidon2SpongeCR M.spongeOf` — "the variable-length digest is injective" — was FALSE at deployed
parameters twice over: at the sponge level (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`) and,
after the demotion, at the compression level (§1 here). What survives, and what a real Poseidon2 can
actually deliver, is this: a digest-collision adversary whose extracted chaining-collision finder is in
the floor's adversary class has NEGLIGIBLE advantage. The three carriers keep their honest roles —
`hSq` the truncation residual, `hSep` the structural length-prefix separation, and the collision floor
the ONE crypto assumption, now stated over a real game instead of an empty injectivity.

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about the
sponge game, the hypothesis about the compression game, and `sponge_adv_le` is the only bridge (§6's
canary compiles that fact).

⚑ `hEff` is UNDISCHARGED. See §7 for both of its poles, priced. -/
theorem spongeCR_of_reduction_advantage_bound {State : Type} (D : SpongeDeployment State)
    (hSq : ∀ t : D.Tag, SqueezeBindsReachable (D.machine t))
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (Eff : Adversary (compressionCollisionGame D) → Prop) (A : Adversary (spongeCollisionGame D))
    (hEff : Eff (spongeToCompressionFinder D A))
    (hcol : Hard (compressionCollisionGame D) Eff) :
    Negl (gameAdv (spongeCollisionGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (spongeCollisionGame D) A l).1)
    (sponge_adv_le D hSq hSep A) (hcol _ hEff)

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at some OTHER finder.)** Strip the
reduction — try to conclude the sponge-collision adversary's negligibility from the compression floor
applied at some OTHER finder `B`, NOT the one extracted from it — and the proof does not go through:
the floor bounds `B`, and only `sponge_adv_le` connects the EXTRACTED finder to the sponge game. Under
the OLD free hypothesis (`hC : CompressionCR M`, hypothesis and conclusion sharing the same free `M`)
this tooth was unwritable. It compiles now, and reds if a future edit reconnects the games. -/
example {State : Type} (D : SpongeDeployment State)
    (Eff : Adversary (compressionCollisionGame D) → Prop) (A : Adversary (spongeCollisionGame D))
    (B : Adversary (compressionCollisionGame D)) (hB : Eff B)
    (hcol : Hard (compressionCollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (spongeCollisionGame D) A) := hcol B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the collision floor at the EXTRACTED finder the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floor {State : Type} (D : SpongeDeployment State)
    (hSq : ∀ t : D.Tag, SqueezeBindsReachable (D.machine t))
    (hSep : ∀ t : D.Tag, InitStepSeparated (D.machine t))
    (Eff : Adversary (compressionCollisionGame D) → Prop) (A : Adversary (spongeCollisionGame D))
    (hEff : Eff (spongeToCompressionFinder D A))
    (hcol : Hard (compressionCollisionGame D) Eff) :
    Negl (gameAdv (spongeCollisionGame D) A) :=
  spongeCR_of_reduction_advantage_bound D hSq hSep Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED: both poles proved at THIS carrier.

The sweep's deep result (`FloorGames` §2) says a game floor at the unrestricted class IS the existence
floor. Here is that theorem instantiated at the deployed compression, so a reader can price any `Eff`
exactly rather than take the residual on faith. -/

/-- **⚑ (TOOTH — the floor is FALSE at `Eff := ⊤` for a range-bounded compression.)** The real
content, and the reason `Eff` is not decoration: a range-bounded compression HAS a chaining collision
at every tag (§1's counting core), so the collision game is always solvable, so the floor at the
unrestricted adversary class is FALSE — and every consumer would be vacuous there. `Classical.choice`
is the adversary and no restatement of the win relation can see it coming. This is the price of
`hEff`, stated as a theorem instead of a promise. -/
theorem compression_floor_top_false_of_finite_range {State : Type} (D : SpongeDeployment State)
    (hfin : ∀ t : D.Tag,
      (Set.range (fun p : State × List ℤ => (D.machine t).step p.1 p.2)).Finite) :
    ¬ Hard (compressionCollisionGame D) (fun _ => True) := by
  haveI := D.stateNonempty
  refine not_hard_top_of_always_solvable (compressionCollisionGame D)
    (fun _ => ⟨((D.stateNonempty.some, []), (D.stateNonempty.some, []))⟩) (fun _ t => ?_)
  exact exists_step_collision_of_finite_range (D.machine t) (hfin t)

/-- **⚑ (TOOTH — the DEPLOYED form of the same, and it needs NO parameters.)** A real sponge state is
a fixed-width array of felts: a `Finite` type. That single instance is the whole hypothesis. So
`Eff := ⊤` fails at every real Poseidon2 deployment — not at a contrived one, not at a bound someone
chose, at the ONLY thing `SpongeReduction`'s abstraction says about the state. -/
theorem compression_floor_top_false_of_finite_state {State : Type} [Finite State]
    (D : SpongeDeployment State) : ¬ Hard (compressionCollisionGame D) (fun _ => True) :=
  compression_floor_top_false_of_finite_range D (fun _ => Set.toFinite _)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty adversary class the floor holds
for ANY deployment, including a completely broken permutation. Recorded HONESTLY: a satisfiability
witness is worth nothing without the refutation beside it, and these two poles together are what make
`Eff` a dial rather than a costume. -/
theorem compression_floor_bot_vacuous {State : Type} (D : SpongeDeployment State) :
    Hard (compressionCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floor is REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** sponge machine: its "permutation" is the constant `0`, so every `(state, block)` pair
chains to the same next state. -/
def brokenMachine : SpongeMachine ℕ where
  perm := fun _ => 0
  init := fun n => n + 1
  absorb := fun s _ => s
  squeeze := fun s => (s : ℤ)
  rate := 4
  rate_pos := by decide

/-- A **broken** deployment over `brokenMachine`, at a single tag. -/
def brokenSponge : SpongeDeployment ℕ where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  machine := fun _ => brokenMachine
  stateDecEq := inferInstance
  stateNonempty := inferInstance
  deployedTag := ()

/-- **(TOOTH — the floor is REFUTABLE.)** The broken deployment's collision game is solvable at every
tag (`(0, []) ≠ (1, [])`, both chain to `0`), so it has no unrestricted-class floor. So the floor is a
GENUINE constraint — a broken permutation refutes it — not vacuously true. -/
theorem brokenSponge_floor_top_false :
    ¬ Hard (compressionCollisionGame brokenSponge) (fun _ => True) :=
  not_hard_top_of_always_solvable (compressionCollisionGame brokenSponge)
    (fun _ => ⟨(((0 : ℕ), ([] : List ℤ)), ((0 : ℕ), ([] : List ℤ)))⟩)
    (fun _ _ => ⟨(((0 : ℕ), ([] : List ℤ)), ((1 : ℕ), ([] : List ℤ))), by decide, rfl⟩)

/-- **(TOOTH — the broken deployment also refutes `CompressionCR` as named.)** `brokenMachine` is not
a fixed-width abstraction dodge: it FALSIFIES the injective floor outright, so `CompressionCR` is a
meaningful named proposition and not a relabelled `True`. -/
theorem brokenMachine_not_compressionCR : ¬ CompressionCR brokenMachine := by
  intro hCR
  have := (hCR 0 1 [] [] rfl).1
  exact absurd this (by decide)

/-! ### The floor is SATISFIABLE (the connection to the keyed-family treatment). -/

/-- **(TOOTH — the keyed family is SATISFIABLE on an injective deployment.)** A deployment whose
per-tag compression is injective discharges `CollisionResistant (compressionFamily D)` — the honest
floor is REALIZABLE, unlike the injective `CompressionCR` at a fixed-width state. ⚑ Recorded with its
price: this is the `⊤`-class object, which §7's first tooth proves FALSE at a range-bounded (i.e.
real) compression. An injective compression is exactly the `Reference.refMachine` shape — a state that
GROWS with the input — and the satisfiability is honest only as a non-emptiness check, never as
evidence the deployed permutation satisfies it. -/
theorem compressionFamily_CR_of_injective {State : Type} (D : SpongeDeployment State)
    (hinj : ∀ t : D.Tag, Function.Injective (fun p : State × List ℤ => (D.machine t).step p.1 p.2)) :
    CollisionResistant (compressionFamily D) :=
  injective_family_CR (compressionFamily D) (fun _ t => hinj t)

#assert_all_clean [
  compressionCR_false_of_finite_range,
  compressionCR_false_of_finite_state,
  exists_step_collision_of_finite_range,
  exists_step_collision_of_finite_state,
  deployed_step_is_family_instance,
  compressionFamily_CR_of_compressionCR,
  compressionCollisionGame_wins_iff,
  mdPeelGame_wins_iff,
  finalStateCollisionGame_wins_iff,
  spongeCollisionGame_wins_iff,
  peel_cons_cons,
  peel_spec,
  mdPeel_wins_imp,
  mdPeel_adv_le,
  finalState_wins_imp,
  finalState_adv_le,
  spongeToFinalState_wins_imp,
  spongeToFinalState_adv_le,
  sponge_wins_imp,
  sponge_adv_le,
  foldl_step_eq_advantage_bound,
  finalState_inj_advantage_bound,
  spongeCR_of_reduction_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  compression_floor_top_false_of_finite_range,
  compression_floor_top_false_of_finite_state,
  compression_floor_bot_vacuous,
  brokenSponge_floor_top_false,
  brokenMachine_not_compressionCR,
  compressionFamily_CR_of_injective
]

end Dregg2.Crypto.SpongeCompressionRegrounded
