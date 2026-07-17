/-
# `Dregg2.Crypto.HermineHashCRRegrounded` — the Hermine commit-reveal `HashCR` consumers RE-GROUNDED
off the VACUOUS injective floor onto the PROPER keyed `CollisionResistant` floor.

## The bug this closes (the commit-reveal half of the 07-13 floor sweep)

`HermineHintMLWE.HashCR cr := ∀ i w w', cr.H i w = cr.H i w' → w = w'` is stated as **injectivity** of
the commit map, and `HashFloorHonesty.hashCR_false_of_compressing` PROVES it FALSE for any COMPRESSING
commit-reveal (`|C| < |W|` — pigeonhole forces two reveals to one commitment). So every Hermine
binding consumer conditioned on it — `commitment_binding`, `equivocation_breaks_hashcr`,
`concurrent_forgery_breaks_hashcr_or_msis`, `concurrent_unforgeable_reduces`, and the DEPLOYED-reachable
`RevocationSoundness` / `IdentityCommitment` reuses of the SAME `CommitReveal`/`HashCR` — is VACUOUSLY
TRUE at real parameters. `HashFloorHonesty` landed the honest floor (`CollisionResistant`) and the
advantage template; `FloorRegroundedConsumers` moved the STARK/FRI side. This file moves the Hermine
COMMIT-REVEAL side.

## The re-grounding

* **`commitRevealFamily`** — the concrete bridge: a Hermine `CommitReveal Idx W C` at a fixed index `i`
  becomes a `KeyedHashFamily` (`Input = W`, `Out = C`, `H _ _ w = cr.H i w`). This is the keyed hash the
  honest collision game lives over.
* **`commitRevealFamily_CR_of_hashcr`** — the OLD-floor ⟹ NEW-floor bridge: if the injective `HashCR cr`
  held it would discharge `CollisionResistant (commitRevealFamily cr i)` (via `injective_family_CR`), so
  the old floor was STRICTLY STRONGER than needed — and, being false for a compressing commitment, empty.
* **`hermine_commitment_binding_advantage_bound`** — the advantage-bounded sibling of
  `HermineHintMLWE.commitment_binding`: an equivocating opener (per key, two DISTINCT reveals colliding
  under the commit hash — exactly the reduction `HermineHintMLWE.equivocation_breaks_hashcr` witnesses) IS
  a `CollisionFinder`, so under the proper floor its advantage is `Negl` — "opens ⟹ equal" becomes
  "opens ⟹ equal EXCEPT with negligible probability". Discharged by `thread_advantage_bound`.

## ⚑ The concurrent-forgery keystone, ROUTED THROUGH THE REAL DICHOTOMY (the 2026-07-17 repair)

`hermine_concurrent_forgery_advantage_bound` is the advantage-bounded sibling of
`concurrent_forgery_breaks_hashcr_or_msis` / `concurrent_unforgeable_reduces`. Until 07-17 it carried a
FREE ensemble unconnected to any forger:

    (adv : S → Ensemble) (s : S) (hmsis : MSISHardQuantShape adv) : Negl (… + adv s n)

whose MSIS leg was `hmsis s` — a `P → P` instantiation of the content-free `MSISHardQuantShape`
(`ProbCrypto`; `HardQuantVacuity` FINDING-1 / `VACUITY-SWEEP.md` documented this exact site). It assumed
the MSIS hardness it should DERIVE from the forger. The HashCR leg was already sound; only the MSIS leg
was rotten.

Now the reduction is a chain of proof terms, MIRRORING the VRF repair (`VrfRegrounded`):

  * **`concurrentForgeryGame`** — a first-class λ-indexed game: the adversary is handed a sampled
    instance (`A`, key `t`, commit map, target commitment `cm`) and WINS iff it opens `cm` with two
    reveals `w`, `w'` and outputs two accepting SelfTargetMSIS solutions with `c ≠ c'`. The forgery is IN
    the win relation; nothing here is a docstring.
  * **`forgeryToMsisSolver`** — the extractor as a map of adversaries: the difference `(z − z', −(c − c'))`
    of `selftarget_extract_nonzero`, written as a function into `msisGame (cfMsisFamily F)`.
  * **`forgeryToEquivFinder`** — the equivocation adversary as a map: the two reveals `(w, w')` into the
    commit-collision game `cfEquivGame F`.
  * **`forgery_wins_imp`** — the dichotomy `concurrent_forgery_breaks_hashcr_or_msis` at the game level:
    every instance the forger wins, EITHER the extracted vector is an `IsMSISSolution` (bound: `w = w'`)
    OR the two reveals are a genuine commit collision (equivocated: `w ≠ w'`).
  * **`forgery_adv_le`** — the UNION BOUND: `gameAdv forgery ≤ gameAdv msis (extracted) + gameAdv equiv
    (extracted)`, over the SHARED sampled-instance space, by `winProb_le_add_of_imp`.
  * **`hermine_concurrent_forgery_advantage_bound`** — the floors bite on the EXTRACTED solver and
    finder, at the games the reduction actually attacks. The Boolean dichotomy `¬HashCR ∨ MSIS-solution`
    becomes the additive negligible advantage — and, unlike its predecessor, this statement is FALSE if
    you delete the reduction: §5's canary compiles that fact.

⚑ **The `hEff`/`hEffH` obligations are UNDISCHARGED and that is the honest state** — the standard "the
reduction is efficient" side conditions, a PARAMETER because this tree has no cost model (`FloorGames`
§8). Both floors' honesty is exactly their `Eff`'s: `⊤` makes them FALSE at compressing parameters,
`⊥` vacuous. §6.

## Non-fake

The floor is SATISFIABLE (`commitRevealFamily_CR_of_hashcr` on the binding `HermineHintMLWE.exCR`
discharges it) and LOAD-BEARING (`badCR_family_not_CR`: the COLLIDING commit-reveal `HermineHintMLWE.badCR`
has an equivocator winning on every key, advantage `1`, so its family is NOT CR — the siblings cannot be
discharged there). The concrete `crEquivocator` is a genuine collision finder, not a relabel. Old
injective-floor consumers KEPT untouched; siblings ADDED. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`.

## Coordination

This is the COMMIT-REVEAL binding lane. The STARK/FRI/Merkle hash consumers are
`Circuit.FloorRegroundedConsumers` (sibling lane); the decisional/lossy-MLWE and `MSISHard`-Boolean crypto
floors are `FloorBridge`/`CryptoFloorTeeth` (another sibling). It stays in the Hermine `CommitReveal`
subtree — no consumer moved here lives elsewhere.
-/
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Crypto.HermineHintMLWE
import Dregg2.Crypto.FloorGames

namespace Dregg2.Crypto.HermineHashCRRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero negl_add not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv injective_family_CR)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR badCR exCR exCR_hashcr)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit msisGame MSISFamily MSISHardQuant Hard
   hard_bot_vacuous msisHardQuant_top_false_of_compressing
   hashGame finderToAdv HashCRHardQuant collisionAdv_eq_gameAdv
   collisionResistant_iff_hashCRHardQuant_top collisionResistant_false_of_compressing)
open Dregg2.Crypto.HermineSelfTargetMSIS
  (IsSelfTargetMSISSolution augmented augmented_apply selftarget_extract_nonzero instShortNormProd)
open scoped Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.Lattice

set_option autoImplicit false

/-! ## §1 — the concrete bridge: a Hermine commit-reveal becomes a keyed hash family. -/

/-- **THE COMMIT-REVEAL KEYED FAMILY.** A Hermine `CommitReveal Idx W C` at a fixed index `i` as a
`KeyedHashFamily`: reveals `W` are the inputs, commitments `C` the outputs, and the keyed hash is
`H _ _ w = cr.H i w` (a trivial `Unit` key — the deployed effective key is the domain-separation
index/tag). This is the keyed hash the proper collision game runs over. -/
def commitRevealFamily {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) : KeyedHashFamily where
  Key := fun _ => Unit
  Input := W
  Out := C
  H := fun _ _ w => cr.H i w
  keyFintype := fun _ => inferInstance
  keyNonempty := fun _ => inferInstance
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE OLD-FLOOR ⟹ NEW-FLOOR BRIDGE.** If the injective `HashCR cr` held (per-index injectivity of the
commit map), it would discharge the proper `CollisionResistant (commitRevealFamily cr i)` (no collisions ⟹
every finder's advantage `0`, via `injective_family_CR`). So the OLD injective floor is STRICTLY STRONGER
than the honest computational floor — and, being FALSE for a compressing commitment
(`HashFloorHonesty.hashCR_false_of_compressing`), it was an empty hypothesis; the proper floor is the
satisfiable object the same binding reductions actually need. -/
theorem commitRevealFamily_CR_of_hashcr {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (hcr : HashCR cr) :
    CollisionResistant (commitRevealFamily cr i) :=
  injective_family_CR (commitRevealFamily cr i) (fun _ _ w w' h => hcr i w w' h)

/-! ## §2 — the advantage-bounded binding keystone (`commitment_binding`, re-grounded).

⚑ **THE `CollisionResistant`-shaped keystone is ITSELF false at deployed parameters** (FINDING-2 of the
07-17 sweep). `FloorGames.collisionResistant_iff_hashCRHardQuant_top` proves `CollisionResistant F ↔
HashCRHardQuant F ⊤`, and `collisionResistant_false_of_compressing` proves that floor FALSE for ANY
compressing `F` — every real commit hash. So `hermine_commitment_binding_advantage_bound` (kept below,
untouched, and consumed by `WireAke`/`IdentityCommitment`/`XmVrf`/`RandomnessBeacon` re-groundings) is a
true implication off a hypothesis that transports NO security. `_eff` below is the honest keystone: the
SAME game over the SAME family at an EXPLICIT adversary class `Eff`, with the `Eff` obligation in the open
at the use site (`FloorGames` §8 — this tree has no cost model). -/

/-- **RE-GROUNDED `HermineHintMLWE.commitment_binding` (bare-CR form — kept for the downstream consumers).**
Under the proper keyed floor, the commitment-equivocation adversary (per key, two DISTINCT reveals of one
commitment colliding under the commit hash — a collision by `HermineHintMLWE.equivocation_breaks_hashcr`)
has negligible advantage. ⚠ Its hypothesis `CollisionResistant F` IS `HashCRHardQuant F ⊤`
(`collisionResistant_iff_hashCRHardQuant_top`), FALSE at deployed compressing parameters — use
`hermine_commitment_binding_advantage_bound_eff` for the security-transporting form. Proof:
`thread_advantage_bound` (the single `CollisionResistant` leaf). -/
theorem hermine_commitment_binding_advantage_bound {F : KeyedHashFamily}
    (hCR : CollisionResistant F) (equivocator : CollisionFinder F) :
    Negl (collisionAdv F equivocator) := by
  thread_advantage_bound

/-- **⚑ RE-GROUNDED `HermineHintMLWE.commitment_binding` — the `Eff`-carrying keystone.** Under the hash-CR
floor at an EXPLICIT adversary class `Eff`, a commitment-equivocation finder whose game adversary is in the
class (`hEff`) has negligible advantage: the `CollisionFinder` advantage the old consumers state IS the
game advantage the honest floor bounds (`collisionAdv_eq_gameAdv`). The Boolean "two openings ⟹ equal"
becomes "⟹ equal EXCEPT with negligible probability", off a floor a real commit hash could satisfy.

⚑ **THE `hEff` OBLIGATION IS UNDISCHARGED AND THAT IS THE HONEST STATE** — the standard "the reduction is
efficient" side condition, a PARAMETER because this tree has no cost model (`FloorGames` §8). The floor is
priced at both poles below: `⊤` FALSE at compressing parameters, `⊥` vacuous. This is the generic keystone
the `IdentityCommitment` / `XmVrf` / `RandomnessBeacon` re-groundings route their own `_eff` siblings
through. -/
theorem hermine_commitment_binding_advantage_bound_eff {F : KeyedHashFamily}
    (Eff : Adversary (hashGame F) → Prop) (equivocator : CollisionFinder F)
    (hEff : Eff (finderToAdv equivocator)) (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F equivocator) := by
  rw [collisionAdv_eq_gameAdv]
  exact hD _ hEff

/-- **(TOOTH — `Eff := ⊤` is FALSE at a compressing family.)** At the unrestricted class the honest floor
IS `CollisionResistant F` (`collisionResistant_iff_hashCRHardQuant_top`), which is FALSE for any compressing
commit hash (`collisionResistant_false_of_compressing`). This is the price of `hEff`, stated as a theorem:
the class cannot be left implicit, because the implicit `⊤` is the empty hypothesis the whole sweep exists
to name. -/
theorem hermine_binding_eff_top_false_of_compressing {F : KeyedHashFamily} (hin : Nonempty F.Input)
    (hcol : ∀ l (k : F.Key l), ∃ x y : F.Input, x ≠ y ∧ F.H l k x = F.H l k y) :
    ¬ HashCRHardQuant F (fun _ => True) :=
  fun h => collisionResistant_false_of_compressing F hin hcol
    ((collisionResistant_iff_hashCRHardQuant_top F).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY family,
including a broken one. Recorded HONESTLY: a satisfiability witness is worth nothing without the refutation
beside it, and the two poles together are what make `Eff` a dial, not a costume. -/
theorem hermine_binding_eff_bot_vacuous {F : KeyedHashFamily} :
    HashCRHardQuant F (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the keystone does NOT follow from the floor applied at another adversary.)** Strip the
reduction — try to conclude the equivocator's negligibility from the floor applied at some OTHER adversary
`B`, NOT the one extracted from the equivocator — and the proof does not go through: `hD B hB` bounds the
game advantage of `B`, a DIFFERENT ensemble than `collisionAdv F equivocator`, and only
`collisionAdv_eq_gameAdv` at the extracted finder connects them. -/
example {F : KeyedHashFamily} (Eff : Adversary (hashGame F) → Prop)
    (equivocator : CollisionFinder F) (B : Adversary (hashGame F)) (hB : Eff B)
    (hD : HashCRHardQuant F Eff) : True := by
  fail_if_success
    (have : Negl (collisionAdv F equivocator) := hD B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** With the floor at the EXTRACTED finder the
keystone fires. A gate that refuses everything is a broken keystone, not a fixed one. -/
theorem hermine_binding_eff_fires {F : KeyedHashFamily} (Eff : Adversary (hashGame F) → Prop)
    (equivocator : CollisionFinder F) (hEff : Eff (finderToAdv equivocator))
    (hD : HashCRHardQuant F Eff) :
    Negl (collisionAdv F equivocator) :=
  hermine_commitment_binding_advantage_bound_eff Eff equivocator hEff hD

/-! ## §3 — the concurrent forger, as a first-class λ-indexed game.

A concurrent rushing forger is a validator that opens a common commitment `cm` and hands back two
accepting SelfTargetMSIS solutions with `c ≠ c'`. This section makes that adversary a `Game`, played over
a SAMPLED instance, exactly as `VrfRegrounded.vrfUniqGame` makes a uniqueness-breaker one. The two games
the reduction attacks — the MSIS game of the augmented map, and the commit-collision game — are derived
from the SAME family, so all three share an instance space and the union bound below is over one `Ω`. -/

/-- **THE CONCURRENT-FORGERY FAMILY.** At each security parameter `l`: the ring `R_q`, the response module
`M`, the commitment module `N`, the commitment-hash codomain `C`, their algebraic structure and shortness
seminorms, a FINITE space of sampled instances, and per instance the public map `A`, public key `t`, the
commit map `commit : N → C` (`= cr.H i`, the commit-reveal at its fixed index), and the target commitment
`cmt = cm` that both reveals must open. `β` is the shortness bound. This carries the deployed data of the
straight-line rushing composition and nothing else. -/
structure ConcurrentForgeryFamily where
  /-- The ring `R_q` at parameter `l` (challenges live here). -/
  Rq : ℕ → Type
  /-- The response module at parameter `l`. -/
  M : ℕ → Type
  /-- The commitment module at parameter `l` (the reveals `w`). -/
  N : ℕ → Type
  /-- The commit-hash codomain at parameter `l` (commitments `cm`). -/
  C : ℕ → Type
  /-- `Rq l` is a commutative ring. -/
  rqRing : ∀ l, CommRing (Rq l)
  /-- The shortness seminorm on challenges. -/
  rqNrm : ∀ l, letI := rqRing l; ShortNorm (Rq l)
  /-- Decidable equality on challenges (the game checks `c ≠ c'`). -/
  rqDec : ∀ l, DecidableEq (Rq l)
  /-- `M l` is an abelian group. -/
  mGrp : ∀ l, AddCommGroup (M l)
  /-- `M l` is an `Rq l`-module. -/
  mMod : ∀ l, letI := rqRing l; letI := mGrp l; Module (Rq l) (M l)
  /-- The shortness seminorm on responses. -/
  mNrm : ∀ l, letI := mGrp l; ShortNorm (M l)
  /-- Decidable equality on responses. -/
  mDec : ∀ l, DecidableEq (M l)
  /-- `N l` is an abelian group. -/
  nGrp : ∀ l, AddCommGroup (N l)
  /-- `N l` is an `Rq l`-module. -/
  nMod : ∀ l, letI := rqRing l; letI := nGrp l; Module (Rq l) (N l)
  /-- The shortness seminorm on commitments (SelfTargetMSIS bounds `‖w‖`). -/
  nNrm : ∀ l, letI := nGrp l; ShortNorm (N l)
  /-- Decidable equality on commitments (the verify equation and the openings check equality in `N`). -/
  nDec : ∀ l, DecidableEq (N l)
  /-- Decidable equality on commitment hashes (the openings check equality in `C`). -/
  cDec : ∀ l, DecidableEq (C l)
  /-- The instance space (key/commitment sampling randomness). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The public map `A` at parameter `l` on instance `i`. -/
  A : ∀ l, Inst l →
    (letI := rqRing l; letI := mGrp l; letI := mMod l; letI := nGrp l; letI := nMod l;
     M l →ₗ[Rq l] N l)
  /-- The public key `t` at parameter `l` on instance `i`. -/
  t : ∀ l, Inst l → N l
  /-- The commit map `commit w = cr.H i w` at the fixed index of instance `i`. -/
  commit : ∀ l, Inst l → N l → C l
  /-- The target commitment `cm` both reveals must open. -/
  cmt : ∀ l, Inst l → C l
  /-- The shortness bound. -/
  β : ℕ → ℕ

/-- The forger's claim: two reveals, two challenges, two responses. -/
abbrev ConcurrentForgeryFamily.Claim (F : ConcurrentForgeryFamily) (l : ℕ) : Type :=
  (F.N l × F.N l) × (F.Rq l × F.Rq l) × (F.M l × F.M l)

/-- **THE CONCURRENT-FORGERY GAME.** The adversary is given a sampled instance and WINS iff it opens the
target commitment `cm` with two reveals `w`, `w'` and outputs two accepting SelfTargetMSIS solutions with
DISTINCT challenges `c ≠ c'`. Winning this game is a rushing validator double-claiming under commit-reveal;
the SelfTargetMSIS relation and the two openings are IN the win predicate, read directly off the family. -/
def concurrentForgeryGame (F : ConcurrentForgeryFamily) : Game where
  Inst := F.Inst
  Ans := fun l => (F.N l × F.N l) × (F.Rq l × F.Rq l) × (F.M l × F.M l)
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i c =>
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l; letI := F.nNrm l
    F.commit l i c.1.1 = F.cmt l i ∧ F.commit l i c.1.2 = F.cmt l i ∧
      c.2.1.1 ≠ c.2.1.2 ∧
      IsSelfTargetMSISSolution (F.A l i) (F.t l i) (F.β l) c.2.2.1 c.2.1.1 c.1.1 ∧
      IsSelfTargetMSISSolution (F.A l i) (F.t l i) (F.β l) c.2.2.2 c.2.1.2 c.1.2
  winsDec := fun l i c => by
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.rqDec l
    letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l; letI := F.mDec l
    letI := F.nGrp l; letI := F.nMod l; letI := F.nNrm l; letI := F.nDec l
    letI := F.cDec l
    unfold IsSelfTargetMSISSolution Dregg2.Crypto.HermineThreshold.verify
    infer_instance

/-- **THE MSIS INSTANCE THE REDUCTION ATTACKS.** The augmented map `[A | t]` over the augmented solution
space `M × R_q`, at the extracted bound `(β + β) + (β + β)` — exactly the map, space and bound
`selftarget_extract_nonzero` produces a solution for. The MSIS floor bites at THIS family, not at an
abstract index set. -/
def cfMsisFamily (F : ConcurrentForgeryFamily) : MSISFamily where
  Rq := F.Rq
  M := fun l => F.M l × F.Rq l
  N := F.N
  rqRing := F.rqRing
  mGrp := fun l => letI := F.rqRing l; letI := F.mGrp l; inferInstance
  mMod := fun l => letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; inferInstance
  mNrm := fun l => letI := F.mGrp l; letI := F.mNrm l; letI := F.rqRing l; letI := F.rqNrm l;
    instShortNormProd
  nGrp := F.nGrp
  nMod := F.nMod
  mDec := fun l => letI := F.mDec l; letI := F.rqDec l; inferInstance
  nDec := F.nDec
  Inst := F.Inst
  instFin := F.instFin
  instNe := F.instNe
  A := fun l i =>
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l
    augmented (F.A l i) (F.t l i)
  β := fun l => (F.β l + F.β l) + (F.β l + F.β l)

/-- **THE COMMIT-COLLISION GAME THE OTHER HORN ATTACKS.** Instances are the SAME sampled instances as the
forgery game; the adversary outputs two reveals and WINS iff they are a genuine collision of the commit
map — distinct reveals, equal commitments. This is the λ-indexed collision game of `F.commit` at each
sampled index; the equivocation horn of the dichotomy lands here. -/
def cfEquivGame (F : ConcurrentForgeryFamily) : Game where
  Inst := F.Inst
  Ans := fun l => F.N l × F.N l
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i p => p.1 ≠ p.2 ∧ F.commit l i p.1 = F.commit l i p.2
  winsDec := fun l i p => by
    letI := F.nDec l; letI := F.cDec l
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the commit-collision game's win relation is a genuine collision
of the real commit map. -/
theorem cfEquivGame_wins_iff (F : ConcurrentForgeryFamily) (l : ℕ) (i : F.Inst l) (p : F.N l × F.N l) :
    (cfEquivGame F).wins l i p ↔ (p.1 ≠ p.2 ∧ F.commit l i p.1 = F.commit l i p.2) :=
  Iff.rfl

/-- **THE MSIS HORN, AS A MAP OF ADVERSARIES.** A concurrent forger becomes an MSIS solver by SUBTRACTING
its two claims: `(z − z', −(c − c'))`. This is not a re-indexing and not a rename — it is the extractor of
`selftarget_extract_nonzero`, written as a function into the augmented MSIS game. -/
def forgeryToMsisSolver (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F)) :
    Adversary (msisGame (cfMsisFamily F)) where
  run := fun l i =>
    letI := F.rqRing l; letI := F.mGrp l
    let c : F.Claim l := A.run l i
    (c.2.2.1 - c.2.2.2, -(c.2.1.1 - c.2.1.2))

/-- **THE EQUIVOCATION HORN, AS A MAP OF ADVERSARIES.** A concurrent forger becomes a commit-collision
finder by handing back its two reveals `(w, w')` — the equivocating opening of the dichotomy. -/
def forgeryToEquivFinder (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F)) :
    Adversary (cfEquivGame F) where
  run := fun l i => let c : F.Claim l := A.run l i; (c.1.1, c.1.2)

/-! ## §4 — the dichotomy, at the probabilistic level.

`HermineHintMLWE.concurrent_forgery_breaks_hashcr_or_msis` is a Boolean disjunction; here it becomes an
implication of Bool win-events, and then — via a union bound over the shared sampled-instance space — the
additive advantage inequality the floors bite through. -/

/-- **THE UNION BOUND.** If every winning outcome of `f` wins `g` OR wins `h`, then `winProb f ≤ winProb g
+ winProb h` — the favorable set of `f` injects into the union of the other two, `card_union_le` closes
it. The probability-level lift of a two-horned dichotomy (`winProb_le_of_imp` is its one-horned sibling). -/
theorem winProb_le_add_of_imp {Ω : Type*} [Fintype Ω] {f g h : Ω → Bool}
    (himp : ∀ o, f o = true → g o = true ∨ h o = true) :
    winProb f ≤ winProb g + winProb h := by
  classical
  rw [winProb, winProb, winProb, ← add_div]
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · simp [h0]
  · gcongr
    have hsub : (Finset.univ.filter (fun o : Ω => f o = true))
        ⊆ (Finset.univ.filter (fun o : Ω => g o = true))
          ∪ (Finset.univ.filter (fun o : Ω => h o = true)) := by
      intro o ho
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
      rw [Finset.mem_union]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact himp o ho
    calc ((Finset.univ.filter (fun o : Ω => f o = true)).card : ℝ)
        ≤ (((Finset.univ.filter (fun o : Ω => g o = true))
            ∪ (Finset.univ.filter (fun o : Ω => h o = true))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((Finset.univ.filter (fun o : Ω => g o = true)).card : ℝ)
            + ((Finset.univ.filter (fun o : Ω => h o = true)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _

/-- **⚑ THE DICHOTOMY IS WIN-PRESERVING — and this is `concurrent_forgery_breaks_hashcr_or_msis`, on a
claim.** Stated over an explicit claim `c : F.Claim l` (so the projections are on a concrete product):
wherever the forger wins: EITHER `w = w'` (bound), and the extracted vector `(z − z', −(c − c'))` IS an
`IsMSISSolution` of the augmented map (`selftarget_extract_nonzero`); OR `w ≠ w'` (equivocated), and the
two reveals ARE a collision of the commit map (both open `cm`). The lattice/hash content lives in proof
terms, not in a sentence about them. -/
theorem claim_wins_imp (F : ConcurrentForgeryFamily) (l : ℕ) (i : F.Inst l) (c : F.Claim l)
    (hwin : (concurrentForgeryGame F).wins l i c) :
    (letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
     letI := F.nGrp l; letI := F.nMod l;
     IsMSISSolution (augmented (F.A l i) (F.t l i)) ((F.β l + F.β l) + (F.β l + F.β l))
       (c.2.2.1 - c.2.2.2, -(c.2.1.1 - c.2.1.2)))
      ∨ (c.1.1 ≠ c.1.2 ∧ F.commit l i c.1.1 = F.commit l i c.1.2) := by
  letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
  letI := F.nGrp l; letI := F.nMod l; letI := F.nNrm l
  obtain ⟨ho, ho', hne, hf, hf'⟩ := hwin
  by_cases hww : c.1.1 = c.1.2
  · -- BOUND to one commitment: the shared reveal feeds SelfTargetMSIS → a real MSIS solution.
    refine Or.inl ?_
    obtain ⟨hz, hc1, _hw, hv⟩ := hf
    obtain ⟨hz', hc1', _hw', hv'⟩ := hf'
    rw [← hww] at hv'
    exact selftarget_extract_nonzero (F.A l i) (F.t l i) c.1.1
      c.2.1.1 c.2.1.2 c.2.2.1 c.2.2.2 (F.β l) (F.β l) hz hz' hc1 hc1' hne hv hv'
  · -- EQUIVOCATED: two distinct reveals of one commitment — a commit collision.
    exact Or.inr ⟨hww, ho.trans ho'.symm⟩

/-- **⚑ THE DICHOTOMY AT THE GAME LEVEL.** `claim_wins_imp` applied at the forger's actual output: every
instance the forger wins, EITHER the extracted MSIS solver wins the augmented MSIS game OR the extracted
commit-collision finder wins the equivocation game. The two derived runs are DEFINITIONALLY the extractor
and the reveal-pair, so this is `claim_wins_imp` transported by `rfl`. -/
theorem forgery_wins_imp (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F))
    (l : ℕ) (i : F.Inst l) (hwin : (concurrentForgeryGame F).wins l i (A.run l i)) :
    (msisGame (cfMsisFamily F)).wins l i ((forgeryToMsisSolver F A).run l i) ∨
      (cfEquivGame F).wins l i ((forgeryToEquivFinder F A).run l i) :=
  claim_wins_imp F l i (A.run l i) hwin

/-- **THE ADVANTAGE INEQUALITY.** The forger's advantage is at most the SUM of the extracted MSIS solver's
and the extracted collision finder's advantages, at every parameter — the three play over the SAME sampled
instance space, and every instance the forger wins one of the two derived adversaries wins. A genuine
union-bound reduction inequality over real game advantages. -/
theorem forgery_adv_le (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F)) (l : ℕ) :
    gameAdv (concurrentForgeryGame F) A l ≤
      gameAdv (msisGame (cfMsisFamily F)) (forgeryToMsisSolver F A) l +
        gameAdv (cfEquivGame F) (forgeryToEquivFinder F A) l := by
  refine @winProb_le_add_of_imp _ (F.instFin l) _ _ _ (fun i hi => ?_)
  rw [Adversary.hit_eq_true] at hi
  rcases forgery_wins_imp F A l i hi with hm | he
  · exact Or.inl ((Adversary.hit_eq_true (forgeryToMsisSolver F A) l i).mpr hm)
  · exact Or.inr ((Adversary.hit_eq_true (forgeryToEquivFinder F A) l i).mpr he)

/-- **⚑ RE-GROUNDED HERMINE CONCURRENT-FORGERY BOUND — from MSIS hardness AND commit-collision resistance,
VIA the reduction.**

Under the MSIS floor at the augmented family the reduction attacks AND the collision floor at the commit
map, a concurrent forger whose extracted solver and finder are in the floors' adversary classes has
NEGLIGIBLE advantage: a rushing validator double-claims only with negligible probability. The Boolean
dichotomy `¬HashCR ∨ MSIS-solution` becomes the additive negligible advantage — and, unlike its
predecessor, this statement is FALSE if you delete the reduction: the conclusion is about the forgery
game, the hypotheses about the MSIS and collision games, and `forgery_adv_le` is the only bridge.

⚑ **THE `hEff`/`hEffH` OBLIGATIONS ARE UNDISCHARGED AND THAT IS THE HONEST STATE.** They say the extracted
solver/finder are in the classes the floors quantify over — the standard "the reduction is efficient".
They are PARAMETERS here, in the open, at the use site, because this tree has no cost model
(`FloorGames` §8). Both floors are priced exactly by §6: `⊤` makes them FALSE at compressing parameters,
`⊥` vacuous. -/
theorem hermine_concurrent_forgery_advantage_bound (F : ConcurrentForgeryFamily)
    (Eff : Adversary (msisGame (cfMsisFamily F)) → Prop)
    (EffH : Adversary (cfEquivGame F) → Prop)
    (A : Adversary (concurrentForgeryGame F))
    (hEff : Eff (forgeryToMsisSolver F A))
    (hEffH : EffH (forgeryToEquivFinder F A))
    (hmsis : MSISHardQuant (cfMsisFamily F) Eff)
    (hcol : Hard (cfEquivGame F) EffH) :
    Negl (gameAdv (concurrentForgeryGame F) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (concurrentForgeryGame F) A l).1)
    (forgery_adv_le F A) (negl_add (hmsis _ hEff) (hcol _ hEffH))

/-! ## §5 — the CANARY: break the reduction and the keystone goes RED.

The sweep's lesson is that a floor consumer must be checked by asking whether it survives the WRONG
hypothesis. Under the OLD statement — `(adv) (s) (hmsis : MSISHardQuantShape adv) : Negl (… + adv s n)` —
the MSIS leg was `hmsis s`, so a canary that conclude negligibility from a floor applied at some OTHER
solver was unwritable: hypothesis and conclusion mentioned the same free `adv s`. Here they cannot. -/

/-- **(CANARY — the keystone does NOT follow from the floors applied at OTHER adversaries.)** Strip the
reduction — try to conclude the forger's negligibility from the MSIS and collision floors applied at some
OTHER solver `B` and finder `E`, NOT the ones extracted from the forger — and the proof does not go
through: the floors bound `B` and `E`, and only `forgery_adv_le` connects the EXTRACTED pair to the
forgery game. `negl_add (hmsis B hB) (hcol E hE)` proves `Negl` of the WRONG advantage sum, so it cannot
close `Negl (gameAdv (concurrentForgeryGame F) A)`. This tooth was impossible to write under the old free
hypothesis; it compiles now, and reds if a future edit reconnects the games. -/
example (F : ConcurrentForgeryFamily) (Eff : Adversary (msisGame (cfMsisFamily F)) → Prop)
    (EffH : Adversary (cfEquivGame F) → Prop) (A : Adversary (concurrentForgeryGame F))
    (B : Adversary (msisGame (cfMsisFamily F))) (hB : Eff B)
    (E : Adversary (cfEquivGame F)) (hE : EffH E)
    (hmsis : MSISHardQuant (cfMsisFamily F) Eff) (hcol : Hard (cfEquivGame F) EffH) : True := by
  fail_if_success
    (have : Negl (gameAdv (concurrentForgeryGame F) A) := negl_add (hmsis B hB) (hcol E hE))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floors DO discharge it.** A gate that refuses everything is a broken
keystone, not a fixed one. With the MSIS floor at the augmented game and the collision floor at the commit
map — both at the EXTRACTED adversaries — the keystone fires and concludes negligibility of the forger's
advantage. Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floors (F : ConcurrentForgeryFamily)
    (Eff : Adversary (msisGame (cfMsisFamily F)) → Prop)
    (EffH : Adversary (cfEquivGame F) → Prop) (A : Adversary (concurrentForgeryGame F))
    (hEff : Eff (forgeryToMsisSolver F A)) (hEffH : EffH (forgeryToEquivFinder F A))
    (hmsis : MSISHardQuant (cfMsisFamily F) Eff) (hcol : Hard (cfEquivGame F) EffH) :
    Negl (gameAdv (concurrentForgeryGame F) A) :=
  hermine_concurrent_forgery_advantage_bound F Eff EffH A hEff hEffH hmsis hcol

/-! ## §6 — non-vacuity of the derived floors (genuine constraints, priced honestly). -/

/-- **(TOOTH — the MSIS floor is SATISFIABLE.)** At the empty adversary class the floor holds for any
family. Recorded HONESTLY, and it is not evidence of anything: `hard_bot_vacuous` is exactly the statement
that this satisfiability is vacuous — the value of a satisfiability witness is nothing without the
refutation beside it. -/
theorem cf_msis_floor_satisfiable_vacuously (F : ConcurrentForgeryFamily) :
    MSISHardQuant (cfMsisFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the commit-collision floor is SATISFIABLE, vacuously.)** Likewise for the equivocation
horn's game — the empty class holds for any commit map, including a completely broken one. -/
theorem cf_equiv_floor_satisfiable_vacuously (F : ConcurrentForgeryFamily) :
    Hard (cfEquivGame F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the MSIS floor is FALSE at the unrestricted class, when the augmented map is compressing.)**
The real content: if a short nonzero kernel vector of `[A | t]` exists at every sampled instance — which
pigeonhole forces at deployed parameters, and which is WHY MSIS is a hard search problem — then the floor
at `Eff := ⊤` is FALSE, and the keystone is vacuous there. This is the price of `hEff`, stated as a
theorem instead of a promise. -/
theorem cf_msis_floor_top_false_of_compressing (F : ConcurrentForgeryFamily)
    (hsolv : ∀ l (i : F.Inst l),
      ∃ z, (letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l
            letI := F.mNrm l; letI := F.nGrp l; letI := F.nMod l
            IsMSISSolution (augmented (F.A l i) (F.t l i)) ((F.β l + F.β l) + (F.β l + F.β l)) z)) :
    ¬ MSISHardQuant (cfMsisFamily F) (fun _ => True) :=
  msisHardQuant_top_false_of_compressing (cfMsisFamily F) hsolv

/-! ## §7 — non-vacuity: the keyed collision floor is satisfiable AND load-bearing on Hermine
commit-reveals (the HashCR-leg siblings, untouched by the repair). -/

/-- A concrete commit-reveal equivocator: on every key it opens the two reveals `w`, `w'`. It is a genuine
collision finder — it wins exactly when `w ≠ w'` yet `cr.H i w = cr.H i w'`. -/
def crEquivocator {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (w w' : W) :
    CollisionFinder (commitRevealFamily cr i) where
  find := fun _ _ => (w, w')

/-- **(TOOTH — the floor is SATISFIABLE on a Hermine commit-reveal.)** The binding instance
`HermineHintMLWE.exCR` (`H i w = (i, w)`, injective) satisfies the proper keyed floor — the sibling
hypotheses are inhabited, unlike the vacuous injective floor. -/
theorem exCR_family_CR : CollisionResistant (commitRevealFamily exCR 3) :=
  commitRevealFamily_CR_of_hashcr exCR 3 exCR_hashcr

/-- **(TOOTH — the floor is LOAD-BEARING on a Hermine commit-reveal.)** The COLLIDING commit-reveal
`HermineHintMLWE.badCR` (`H _ _ = 0`, every reveal opens every commitment) has the `crEquivocator 5 7 8`
winning on EVERY key (`7 ≠ 8` yet both hash to `0`), so its advantage is the constant `1` and the family
is NOT collision-resistant. So the siblings cannot be discharged on a broken commit-reveal — the proper
floor is a genuine constraint, and the re-grounded binding is non-vacuous. -/
theorem badCR_family_not_CR : ¬ CollisionResistant (commitRevealFamily badCR 5) := by
  intro hCR
  have hadv : collisionAdv (commitRevealFamily badCR 5) (crEquivocator badCR 5 (7 : ℤ) 8)
      = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (commitRevealFamily badCR 5).Key n =>
        (crEquivocator badCR 5 (7 : ℤ) 8).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, badCR]
    show @winProb ((commitRevealFamily badCR 5).Key n) ((commitRevealFamily badCR 5).keyFintype n)
        (fun k => (crEquivocator badCR 5 (7 : ℤ) 8).wins n k) = 1
    rw [hall]
    exact @winProb_top ((commitRevealFamily badCR 5).Key n) ((commitRevealFamily badCR 5).keyFintype n)
      ((commitRevealFamily badCR 5).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR (crEquivocator badCR 5 7 8))

#assert_all_clean [
  commitRevealFamily_CR_of_hashcr,
  hermine_commitment_binding_advantage_bound,
  hermine_commitment_binding_advantage_bound_eff,
  hermine_binding_eff_top_false_of_compressing,
  hermine_binding_eff_bot_vacuous,
  hermine_binding_eff_fires,
  cfEquivGame_wins_iff,
  winProb_le_add_of_imp,
  claim_wins_imp,
  forgery_wins_imp,
  forgery_adv_le,
  hermine_concurrent_forgery_advantage_bound,
  the_repaired_bound_fires_on_the_right_floors,
  cf_msis_floor_satisfiable_vacuously,
  cf_equiv_floor_satisfiable_vacuously,
  cf_msis_floor_top_false_of_compressing,
  exCR_family_CR,
  badCR_family_not_CR
]

end Dregg2.Crypto.HermineHashCRRegrounded
