/-
# `Dregg2.Crypto.RandomnessBeaconRegrounded` — the POST-QUANTUM randomness beacon (abstract model AND the
deployed `crypto-hashrand` refinement) RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the
PROPER keyed `CollisionResistant` floor.

## The gap this closes (the beacon leg of the forward-scaffolding floor sweep)

`RandomnessBeacon.unbiasable_of_hashcr` / `prediction_matching_two_reveals_breaks_hashcr` /
`commit_binds_contribution`, and their deployed refinements `HashRandRefinement.hashrand_unbiasable` /
`hashrand_commit_binds`, are the UNBIASABILITY + UNPREDICTABILITY floors of the hash-based beacon. Each is
conditioned on `HermineHintMLWE.HashCR cr` — the injective floor `HashFloorHonesty.hashCR_false_of_compressing`
PROVES FALSE for any compressing commit (`beaconViaHash cr i adv c = cr.H i (c, adv)` and the deployed
`combine = H("output", sorted[(i,cᵢ)])` both map a long framed pre-image to a fixed-width digest, so they
ARE compressing). So the beacon's safety lemmas are VACUOUSLY TRUE at real parameters.

This file instantiates the generic commit-reveal regrounding (`HermineHashCRRegrounded`) for the beacon's own
combine/commit hashes — the abstract model AND the deployed `crypto-hashrand` surface — so unbiasability and
unpredictability no longer ride an empty hypothesis. Mirror of `IdentityCommitmentRegrounded`.

## The re-grounding

* **`beaconHashFamily cr i`** — the beacon's combine/commit hash `cr.H i` as the keyed hash family
  `commitRevealFamily cr i`. **`hashRandCommitFamily X` / `hashRandOutputFamily X`** — the deployed
  `crypto-hashrand` commit hash `H(Role.commit, ·)` and combine hash `H(Role.output, ·)` as families.
* **`beacon_binding_advantage_bound`** — the advantage-bounded sibling of `unbiasable_of_hashcr` /
  `prediction_matching_two_reveals_breaks_hashcr`: a BIAS / early-prediction adversary (per key, two distinct
  reveals colliding to one beacon output — a hash collision, by `bias_breaks_honest_slot_cr`) IS a
  `CollisionFinder`, so under the proper floor its advantage is `Negl`. "distinct honest reveal ⟹ distinct
  output" becomes "⟹ distinct output EXCEPT with negligible probability".
* **`hashrand_commit_binding_advantage_bound` / `hashrand_output_binding_advantage_bound`** — the same, on the
  DEPLOYED `crypto-hashrand` commit/combine hashes: an equivocating committer / a bias adversary has
  negligible advantage under the proper floor. Both discharged by `thread_advantage_bound`.

## Non-fake

Each floor is SATISFIABLE (`beacon_exBeaconHash_CR` on the injective `exBeaconHash`;
`hashRand_goodCR_commit_CR` / `_output_CR` on the injective deployed `goodCR`) and LOAD-BEARING
(`beacon_badBeaconOut_not_CR` on the colliding `badBeaconOut`; `hashRand_badCR_output_not_CR` on the deployed
colliding `badCR`). Old injective-floor consumers KEPT untouched; siblings ADDED. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`, no `native_decide`.

## Coordination

Beacon commit-reveal leg. Generic template = `HermineHashCRRegrounded`; the PQ sortition VRF (also `HashCR`)
= `XmVrfRefinementRegrounded`; the wire channel binding = `WireAkeRegrounded`. Stays in the beacon subtree.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.HashRandRefinement

namespace Dregg2.Crypto.RandomnessBeaconRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv idFamily idFamily_CR)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.HermineHashCRRegrounded
  (commitRevealFamily commitRevealFamily_CR_of_hashcr hermine_commitment_binding_advantage_bound
   hermine_commitment_binding_advantage_bound_eff crEquivocator)
open Dregg2.Crypto.FloorGames
  (Adversary hashGame finderToAdv HashCRHardQuant collisionResistant_iff_hashCRHardQuant_top
   hard_bot_vacuous)
open Dregg2.Crypto.HashRandRefinement (HashRand Role)

set_option autoImplicit false

/-! ## §1 — the beacon combine/commit hashes as keyed families. -/

/-- **THE BEACON KEYED FAMILY.** The abstract beacon's combine/commit hash `cr.H i` over the framed
`(contribution, adversary aggregate)` pre-images, as `commitRevealFamily cr i` — the keyed hash the honest
collision game runs over. -/
def beaconHashFamily {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) : KeyedHashFamily :=
  commitRevealFamily cr i

/-- **THE DEPLOYED `crypto-hashrand` COMMIT FAMILY.** `H(Role.commit, frameCommit i c)` as a keyed family. -/
def hashRandCommitFamily {Party Ct Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : HashRand Party Ct Pre Digest) : KeyedHashFamily :=
  commitRevealFamily X.cr Role.commit

/-- **THE DEPLOYED `crypto-hashrand` OUTPUT FAMILY.** `H(Role.output, frameOutput cs)` as a keyed family. -/
def hashRandOutputFamily {Party Ct Pre Digest : Type} [DecidableEq Pre] [DecidableEq Digest]
    (X : HashRand Party Ct Pre Digest) : KeyedHashFamily :=
  commitRevealFamily X.cr Role.output

/-! ## §2 — the advantage-bounded beacon keystones (unbiasability / unpredictability, re-grounded). -/

/-- **RE-GROUNDED `RandomnessBeacon.unbiasable_of_hashcr` / `prediction_matching_two_reveals_breaks_hashcr`.**
Under the proper keyed floor, the bias / early-prediction adversary (per key, two distinct reveals colliding
to one beacon output — a collision by `bias_breaks_honest_slot_cr`) has negligible advantage. "distinct
honest reveal ⟹ distinct output" becomes "⟹ distinct output EXCEPT with negligible probability": no coalition
can steer or predict the beacon except with negligible advantage. Proof: `thread_advantage_bound`. -/
theorem beacon_binding_advantage_bound {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx)
    (hCR : CollisionResistant (beaconHashFamily cr i))
    (biasAdversary : CollisionFinder (beaconHashFamily cr i)) :
    Negl (collisionAdv (beaconHashFamily cr i) biasAdversary) :=
  hermine_commitment_binding_advantage_bound hCR biasAdversary

/-- **RE-GROUNDED `HashRandRefinement.hashrand_commit_binds`.** Under the proper keyed floor, the deployed
`crypto-hashrand` commit-equivocation adversary (two distinct contributions opening one commitment) has
negligible advantage — the honest party is pinned to one contribution except with negligible probability,
grounding UNPREDICTABILITY. Proof: `thread_advantage_bound`. -/
theorem hashrand_commit_binding_advantage_bound {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (hCR : CollisionResistant (hashRandCommitFamily X))
    (equivocator : CollisionFinder (hashRandCommitFamily X)) :
    Negl (collisionAdv (hashRandCommitFamily X) equivocator) :=
  hermine_commitment_binding_advantage_bound hCR equivocator

/-- **RE-GROUNDED `HashRandRefinement.hashrand_unbiasable` / `hashrand_bias_breaks_hashcr`.** Under the proper
keyed floor, the deployed `crypto-hashrand` bias adversary (two distinct contributions colliding to one
combine output) has negligible advantage — the honest contribution moves the beacon except with negligible
probability, grounding UNBIASABILITY. Proof: `thread_advantage_bound`. -/
theorem hashrand_output_binding_advantage_bound {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (hCR : CollisionResistant (hashRandOutputFamily X))
    (biasAdversary : CollisionFinder (hashRandOutputFamily X)) :
    Negl (collisionAdv (hashRandOutputFamily X) biasAdversary) :=
  hermine_commitment_binding_advantage_bound hCR biasAdversary

/-! ## §2b — ⚑ the `Eff`-CARRYING beacon keystones (FINDING-2 of the 07-17 sweep).

Each bare-CR sibling above rests on `CollisionResistant _` = `HashCRHardQuant _ ⊤`
(`collisionResistant_iff_hashCRHardQuant_top`), FALSE for the compressing combine/commit hashes — so it
transports no security. Each `_eff` conditions on the SAME collision game at an EXPLICIT class `Eff`, with
the finder's `hEff` obligation in the open (`FloorGames` §8 — no cost model). Poles priced in §4. -/

/-- **⚑ RE-GROUNDED beacon unbiasability/unpredictability — the `Eff`-carrying form.** A bias / early-prediction
finder in the class `Eff` has negligible advantage: no coalition steers or predicts the beacon except with
negligible probability. -/
theorem beacon_binding_advantage_bound_eff {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx)
    (Eff : Adversary (hashGame (beaconHashFamily cr i)) → Prop)
    (biasAdversary : CollisionFinder (beaconHashFamily cr i))
    (hEff : Eff (finderToAdv biasAdversary))
    (hD : HashCRHardQuant (beaconHashFamily cr i) Eff) :
    Negl (collisionAdv (beaconHashFamily cr i) biasAdversary) :=
  hermine_commitment_binding_advantage_bound_eff Eff biasAdversary hEff hD

/-- **⚑ RE-GROUNDED `HashRandRefinement.hashrand_commit_binds` — the `Eff`-carrying form.** A deployed
`crypto-hashrand` commit-equivocation finder in `Eff` has negligible advantage — the honest party is pinned
to one contribution except with negligible probability (UNPREDICTABILITY). -/
theorem hashrand_commit_binding_advantage_bound_eff {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (Eff : Adversary (hashGame (hashRandCommitFamily X)) → Prop)
    (equivocator : CollisionFinder (hashRandCommitFamily X))
    (hEff : Eff (finderToAdv equivocator))
    (hD : HashCRHardQuant (hashRandCommitFamily X) Eff) :
    Negl (collisionAdv (hashRandCommitFamily X) equivocator) :=
  hermine_commitment_binding_advantage_bound_eff Eff equivocator hEff hD

/-- **⚑ RE-GROUNDED `HashRandRefinement.hashrand_unbiasable` — the `Eff`-carrying form.** A deployed
`crypto-hashrand` bias finder in `Eff` has negligible advantage — the honest contribution moves the beacon
except with negligible probability (UNBIASABILITY). -/
theorem hashrand_output_binding_advantage_bound_eff {Party Ct Pre Digest : Type}
    [DecidableEq Pre] [DecidableEq Digest] (X : HashRand Party Ct Pre Digest)
    (Eff : Adversary (hashGame (hashRandOutputFamily X)) → Prop)
    (biasAdversary : CollisionFinder (hashRandOutputFamily X))
    (hEff : Eff (finderToAdv biasAdversary))
    (hD : HashCRHardQuant (hashRandOutputFamily X) Eff) :
    Negl (collisionAdv (hashRandOutputFamily X) biasAdversary) :=
  hermine_commitment_binding_advantage_bound_eff Eff biasAdversary hEff hD

/-! ## §3 — non-vacuity: satisfiable AND load-bearing, on the abstract beacon and the deployed surface. -/

/-- **(TOOTH — the beacon floor is SATISFIABLE.)** The injective combine hash `exBeaconHash` satisfies the
proper keyed floor. -/
theorem beacon_exBeaconHash_CR :
    CollisionResistant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.exBeaconHash 0) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.RandomnessBeacon.exBeaconHash 0
    Dregg2.Crypto.RandomnessBeacon.exBeaconHash_hashcr

/-- **(TOOTH — the beacon floor is LOAD-BEARING.)** The colliding combine hash `badBeaconOut` (`H _ _ = 0`,
every reveal absorbed to one output) has the bias equivocator `crEquivocator badBeaconOut 0 (5,1) (6,1)`
winning on every key (advantage `1`), so its family is NOT CR — the proper floor is a genuine constraint. -/
theorem beacon_badBeaconOut_not_CR :
    ¬ CollisionResistant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.badBeaconOut 0) := by
  intro hCR
  set bad := Dregg2.Crypto.RandomnessBeacon.badBeaconOut with hbad
  have hadv : collisionAdv (beaconHashFamily bad 0)
      (crEquivocator bad 0 ((5, 1) : ℤ × ℤ) (6, 1)) = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (beaconHashFamily bad 0).Key n =>
        (crEquivocator bad 0 ((5, 1) : ℤ × ℤ) (6, 1)).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, hbad,
        Dregg2.Crypto.RandomnessBeacon.badBeaconOut]
    show @winProb ((beaconHashFamily bad 0).Key n) ((beaconHashFamily bad 0).keyFintype n)
        (fun k => (crEquivocator bad 0 ((5, 1) : ℤ × ℤ) (6, 1)).wins n k) = 1
    rw [hall]
    exact @winProb_top ((beaconHashFamily bad 0).Key n) ((beaconHashFamily bad 0).keyFintype n)
      ((beaconHashFamily bad 0).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR (crEquivocator bad 0 (5, 1) (6, 1)))

/-- **(TOOTH — the deployed commit floor is SATISFIABLE.)** The injective deployed hash `goodCR` satisfies
the proper keyed floor at `Role.commit`. -/
theorem hashRand_goodCR_commit_CR :
    CollisionResistant (hashRandCommitFamily Dregg2.Crypto.HashRandRefinement.goodX) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.HashRandRefinement.goodX.cr Role.commit
    Dregg2.Crypto.HashRandRefinement.goodCR_hashcr

/-- **(TOOTH — the deployed output floor is SATISFIABLE.)** The injective deployed hash `goodCR` satisfies
the proper keyed floor at `Role.output`. -/
theorem hashRand_goodCR_output_CR :
    CollisionResistant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.goodX) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.HashRandRefinement.goodX.cr Role.output
    Dregg2.Crypto.HashRandRefinement.goodCR_hashcr

/-- **(TOOTH — the deployed output floor is LOAD-BEARING.)** The deployed colliding combine `badCR`
(`H _ _ = 0`) has a bias equivocator winning on every key (advantage `1`), so its output family is NOT CR —
the deployed unbiasability's floor is a genuine constraint. -/
theorem hashRand_badCR_output_not_CR :
    ¬ CollisionResistant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX) := by
  intro hCR
  set bad := Dregg2.Crypto.HashRandRefinement.badX.cr with hbad
  have hadv : collisionAdv (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX)
      (crEquivocator bad Role.output (Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ)) (Sum.inl (2, 2)))
      = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).Key n =>
        (crEquivocator bad Role.output (Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ))
          (Sum.inl (2, 2))).wins n k) = fun _ => true := by
      funext k
      simp [CollisionFinder.wins, crEquivocator, commitRevealFamily, hbad,
        Dregg2.Crypto.HashRandRefinement.badX, Dregg2.Crypto.HashRandRefinement.badCR]
    show @winProb ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).Key n)
        ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).keyFintype n)
        (fun k => (crEquivocator bad Role.output (Sum.inl (1, 1) : (ℕ × ℕ) ⊕ Multiset (ℕ × ℕ))
          (Sum.inl (2, 2))).wins n k) = 1
    rw [hall]
    exact @winProb_top ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).Key n)
      ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).keyFintype n)
      ((hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR
    (crEquivocator bad Role.output (Sum.inl (1, 1)) (Sum.inl (2, 2))))

/-- **THE RE-GROUNDED BEACON BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective identity family, the
bias-equivocation advantage is negligible — the beacon safety runs end-to-end to a genuine `Negl`. -/
theorem beacon_binding_fires (biasAdversary : CollisionFinder idFamily) :
    Negl (collisionAdv idFamily biasAdversary) :=
  hermine_commitment_binding_advantage_bound idFamily_CR biasAdversary

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing beacon combine hash.)** The bare-CR floor at the
colliding `badBeaconOut` is refuted (`beacon_badBeaconOut_not_CR`), and it IS `HashCRHardQuant _ ⊤` — so
the `⊤` class is FALSE. The price of `hEff`, as a theorem. -/
theorem beacon_eff_top_false :
    ¬ HashCRHardQuant (beaconHashFamily Dregg2.Crypto.RandomnessBeacon.badBeaconOut 0) (fun _ => True) :=
  fun h => beacon_badBeaconOut_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — `Eff := ⊤` is FALSE at the compressing deployed combine hash.)** Same, on the deployed
`crypto-hashrand` colliding `badX` output hash (`hashRand_badCR_output_not_CR`). -/
theorem hashRand_output_eff_top_false :
    ¬ HashCRHardQuant (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.badX) (fun _ => True) :=
  fun h => hashRand_badCR_output_not_CR ((collisionResistant_iff_hashCRHardQuant_top _).mpr h)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the beacon floor holds for ANY
combine/commit hash. -/
theorem beacon_eff_bot_vacuous {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) :
    HashCRHardQuant (beaconHashFamily cr i) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — beacon safety does NOT follow from the floor at another adversary.)** From the floor at some
OTHER adversary `B` the bias-equivocator's negligibility does not follow: `hD B hB` bounds a DIFFERENT
ensemble. -/
example {Idx W C : Type} [DecidableEq W] [DecidableEq C] (cr : CommitReveal Idx W C) (i : Idx)
    (Eff : Adversary (hashGame (beaconHashFamily cr i)) → Prop)
    (biasAdversary : CollisionFinder (beaconHashFamily cr i))
    (B : Adversary (hashGame (beaconHashFamily cr i))) (hB : Eff B)
    (hD : HashCRHardQuant (beaconHashFamily cr i) Eff) : True := by
  fail_if_success
    (have : Negl (collisionAdv (beaconHashFamily cr i) biasAdversary) := hD B hB)
  trivial

/-- **THE `Eff` BEACON BINDING FIRES AT A REAL FLOOR WITNESS.** On the injective deployed `goodX.cr` the
output `Eff`-floor at `⊤` holds (`hashRand_goodCR_output_CR`), so the deployed unbiasability runs
end-to-end to a genuine `Negl` at an inhabited hypothesis. -/
theorem hashrand_output_eff_fires
    (biasAdversary : CollisionFinder (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.goodX)) :
    Negl (collisionAdv (hashRandOutputFamily Dregg2.Crypto.HashRandRefinement.goodX) biasAdversary) :=
  hashrand_output_binding_advantage_bound_eff Dregg2.Crypto.HashRandRefinement.goodX (fun _ => True)
    biasAdversary trivial ((collisionResistant_iff_hashCRHardQuant_top _).mp hashRand_goodCR_output_CR)

#assert_all_clean [
  beacon_binding_advantage_bound,
  hashrand_commit_binding_advantage_bound,
  hashrand_output_binding_advantage_bound,
  beacon_binding_advantage_bound_eff,
  hashrand_commit_binding_advantage_bound_eff,
  hashrand_output_binding_advantage_bound_eff,
  beacon_exBeaconHash_CR,
  beacon_badBeaconOut_not_CR,
  hashRand_goodCR_commit_CR,
  hashRand_goodCR_output_CR,
  hashRand_badCR_output_not_CR,
  beacon_binding_fires,
  beacon_eff_top_false,
  hashRand_output_eff_top_false,
  beacon_eff_bot_vacuous,
  hashrand_output_eff_fires
]

end Dregg2.Crypto.RandomnessBeaconRegrounded
