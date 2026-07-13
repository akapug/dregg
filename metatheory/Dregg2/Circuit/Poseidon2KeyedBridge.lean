/-
# `Dregg2.Circuit.Poseidon2KeyedBridge` — bridging the DEPLOYED UNKEYED Poseidon2 sponge to the
KEYED `CollisionResistant` game (the honest keyed-from-unkeyed-via-domain-separation model).

## The obligation this closes

`HashFloorHonesty.lean` replaced the VACUOUS injective hash floor (`Poseidon2Binding.Poseidon2SpongeCR`,
false at real BabyBear params by pigeonhole) with a PROPER computational floor: `CollisionResistant F`
over a **KEYED** hash family `F`, and `FloorRegroundedConsumers.lean` re-seated every STARK/FRI/binding
consumer (`OodCommitmentBinding`, `FriSoundness.oracle_binding`, `AirSoundness.committed_trace_pinned`,
`FinBindsKernel`) onto that keyed floor as advantage bounds.

Keying is LOAD-BEARING: an UNKEYED fixed hash lets an adversary hardcode a known collision (advantage
`1`), collapsing the floor. BUT the DEPLOYED Poseidon2 (`p3-poseidon2-circuit-air` BabyBear width-16,
`Poseidon2Binding.babyBearD4W16`) is a FIXED, UNKEYED sponge `List ℤ → ℤ`. So there is a genuine
"bridge to the real object" gap: the consumers rest on `CollisionResistant F` for an ABSTRACT keyed
family `F`, while the prover computes a fixed unkeyed function. This file connects the two.

## The standard bridge: domain separation IS the key

The deployed sponge's effective "key" is its **domain-separation tag** — the per-use prefix
(`PaddingFreeSponge` over the round-constant/rate-capacity regime, absorbed ahead of the message) that
the deployment uses to separate the Merkle-node hash from the leaf hash from the log hash from the OOD
commitment. Modelling that tag as the key of a keyed family is the standard way a real FIXED hash
receives a keyed collision-resistance treatment (the keyed-from-unkeyed / domain-separation model). The
keyed CR game then FAITHFULLY MODELS the deployed hash: its win event at the deployed tag is
DEFINITIONALLY a collision of the deployed unkeyed function `xs ↦ sponge (tag ++ xs)`.

  * **§1** — `DomainSeparatedSponge`: the deployed unkeyed sponge + its finite domain-separation tag
    space + the tag-absorption encoding + the specific deployed tag the prover uses.
  * **§2** — `poseidon2KeyedFamily`: that bundle lifted to a `HashFloorHonesty.KeyedHashFamily`, keyed
    by the domain-separation tag. FAITHFULNESS (`deployed_hash_is_family_instance`,
    `wins_iff_deployed_collision`): the deployed fixed hash IS the family instance at the deployed tag,
    and a keyed-game win at any tag is exactly a deployed-hash collision — the game models the real
    object, no idealization.
  * **§3** — the NAMED domain-separation floor `DomainSeparatedCR D := CollisionResistant
    (poseidon2KeyedFamily D)`. GENUINE, per [[feedback-prove-the-floor-false]]: SATISFIABLE (a
    domain-separated family over an injective sponge is CR — `domainSeparatedCR_of_injective_sponge`,
    witnessed concretely by `Reference.refSponge` at the REAL `babyBearD4W16` params) and REFUTABLE (a
    broken domain separation — the tag-ignoring constant sponge — has advantage `1`,
    `brokenDomainSep_not_CR`). NOT an injectivity/existence-refutation: the win event is *finding* a
    collision over a random tag, not the mere *existence* of one.
  * **§4** — the connection: under `DomainSeparatedCR D`, the `FloorRegroundedConsumers` advantage
    bounds fire at `F := poseidon2KeyedFamily D`, so the deployed circuit's keyed-CR floor is BRIDGED to
    the real deployed hash — `FinBindsKernel`'s root binder, the OOD/Merkle/trace binders, and the apex
    two-hash forgery advantage all rest on the deployed sponge's domain-separation CR.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; NO `sorryAx`/`sorry`, NO fresh `axiom`. The
named floor `DomainSeparatedCR` is a HYPOTHESIS (never an `axiom`), satisfiable AND refutable, so the
bridge theorems are genuine implications, not vacuous. The keyed family reuses
`HashFloorHonesty.KeyedHashFamily`/`CollisionResistant` and the deployed sponge is the
`Poseidon2Binding` `List ℤ → ℤ` object.
-/
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Circuit.FloorRegroundedConsumers
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Poseidon2KeyedBridge

open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder CollisionResistant collisionAdv injective_family_CR
   brokenFamily_not_CR idFamily_CR)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot)
open Dregg2.Crypto.ConcreteSecurity (Ensemble Negl negl_zero not_negl_one)

set_option autoImplicit false

/-! ## §1 — the deployed unkeyed sponge with its domain-separation structure.

The deployed Poseidon2 (`Poseidon2Binding.babyBearD4W16`) is a fixed sponge `sponge : List ℤ → ℤ`. Its
effective KEY is the domain-separation tag: a finite set of per-use prefixes the deployment absorbs
ahead of the message. `deployedTag` is the specific tag the prover computes at a given use-site (so the
deployed FIXED function is `xs ↦ sponge (tagCode deployedTag ++ xs)`). -/

/-- The deployed unkeyed Poseidon2 sponge together with its domain-separation structure. `sponge` is the
`Poseidon2Binding` `List ℤ → ℤ` object (the real `babyBearD4W16` PaddingFreeSponge); `Tag` is the
finite, inhabited domain-separation tag space; `tagCode` is how a tag is absorbed as a prefix;
`deployedTag` is the specific tag the deployment uses. -/
structure DomainSeparatedSponge where
  /-- The deployed unkeyed Poseidon2 sponge (`Poseidon2Binding`'s `List ℤ → ℤ`). -/
  sponge : List ℤ → ℤ
  /-- The domain-separation tag space (the effective key). -/
  Tag : Type
  /-- The tag space is finite (the CR game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- How a domain-separation tag is absorbed: as a field-element prefix ahead of the message. -/
  tagCode : Tag → List ℤ
  /-- The specific domain-separation tag the deployment computes at this use-site. -/
  deployedTag : Tag

/-- The deployed sponge domain-separated by a SPECIFIC tag: `xs ↦ sponge (tagCode t ++ xs)` — a fixed
unkeyed function per tag. -/
def DomainSeparatedSponge.hashAt (D : DomainSeparatedSponge) (t : D.Tag) (xs : List ℤ) : ℤ :=
  D.sponge (D.tagCode t ++ xs)

/-- The DEPLOYED fixed unkeyed function the prover actually computes: the sponge over the deployed tag's
prefix concatenated with the message. This is the real object the bridge points at. -/
def DomainSeparatedSponge.deployedHash (D : DomainSeparatedSponge) (xs : List ℤ) : ℤ :=
  D.hashAt D.deployedTag xs

/-! ## §2 — the deployed sponge lifted to a KEYED family (domain separation = the key). -/

/-- **`poseidon2KeyedFamily D`** — the deployed unkeyed Poseidon2 sponge lifted to a
`HashFloorHonesty.KeyedHashFamily`, keyed by its domain-separation tag: `H n t xs = sponge (tagCode t ++
xs)`. Input domain `List ℤ` (the sponge domain), output `ℤ` (the BabyBear field element). This is the
object `FloorRegroundedConsumers`'s `CollisionResistant F` floor is realized at for the real hash. -/
def poseidon2KeyedFamily (D : DomainSeparatedSponge) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List ℤ
  Out := ℤ
  H := fun _ t xs => D.sponge (D.tagCode t ++ xs)
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS (1/2).** The deployed FIXED unkeyed hash IS the keyed family's instance at the
deployed tag — no idealization, a definitional equality. So the keyed CR game (over the family) is a
game about the very function the prover computes. -/
theorem deployed_hash_is_family_instance (D : DomainSeparatedSponge) (n : ℕ) :
    D.deployedHash = (poseidon2KeyedFamily D).H n D.deployedTag := rfl

/-- **FAITHFULNESS (2/2).** A keyed-game WIN at tag `t` is DEFINITIONALLY a collision of the deployed
unkeyed function `xs ↦ sponge (tagCode t ++ xs)`: the finder outputs two DISTINCT inputs that the
domain-separated sponge maps to the same field element. The game measures *finding* a real collision,
not the *existence* of one — this is what makes modelling the fixed hash by the keyed game honest. -/
theorem wins_iff_deployed_collision (D : DomainSeparatedSponge) (A : CollisionFinder (poseidon2KeyedFamily D))
    (n : ℕ) (t : D.Tag) :
    A.wins n t = true ↔
      (A.find n t).1 ≠ (A.find n t).2 ∧
        D.hashAt t (A.find n t).1 = D.hashAt t (A.find n t).2 := by
  simp only [CollisionFinder.wins, Bool.and_eq_true, decide_eq_true_eq, poseidon2KeyedFamily,
    DomainSeparatedSponge.hashAt]

/-! ## §3 — the NAMED domain-separation floor: SATISFIABLE + REFUTABLE (a genuine floor). -/

/-- **`DomainSeparatedCR D`** — the deployed Poseidon2's domain-separation collision-resistance: the
keyed family (keyed by the domain-separation tag) is `CollisionResistant`. This is the honest deployed-hash
assumption — the keyed-from-unkeyed-via-domain-separation model. It is a HYPOTHESIS (never an `axiom`),
and a GENUINE floor: satisfiable (§ `domainSeparatedCR_of_injective_sponge`) and refutable (§
`brokenDomainSep_not_CR`). -/
def DomainSeparatedCR (D : DomainSeparatedSponge) : Prop :=
  CollisionResistant (poseidon2KeyedFamily D)

/-- Each keyed instance `xs ↦ sponge (tagCode t ++ xs)` is injective when the underlying sponge is
(domain-separation prefixing is injective — `List.append_right_injective`). -/
theorem family_H_injective_of_injective_sponge {D : DomainSeparatedSponge}
    (hs : Function.Injective D.sponge) (n : ℕ) (t : D.Tag) :
    Function.Injective ((poseidon2KeyedFamily D).H n t) :=
  hs.comp (List.append_right_injective (D.tagCode t))

/-- **(SATISFIABILITY.)** A domain-separated family over an INJECTIVE deployed sponge is
collision-resistant: no finder ever wins, advantage `0`. So the floor is REALIZABLE — a domain-separated
hash satisfies it under the standard model, exactly as a Poseidon2 with proper domain separation is
assumed to. (`Function.Injective sponge` is the idealized-hash shape; it is unsatisfiable at real
BabyBear params — `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` — which is why the DEPLOYED floor
must be the computational `DomainSeparatedCR`, satisfied here by a stand-in to prove non-vacuity.) -/
theorem domainSeparatedCR_of_injective_sponge {D : DomainSeparatedSponge}
    (hs : Function.Injective D.sponge) : DomainSeparatedCR D :=
  injective_family_CR (poseidon2KeyedFamily D) (family_H_injective_of_injective_sponge hs)

/-- **The link to the `Poseidon2Binding.Poseidon2SpongeCR` object.** The old (idealized, false-at-real-
params) injective floor `Poseidon2SpongeCR sponge` on the deployed sponge DISCHARGES the honest
`DomainSeparatedCR` floor — the honest keyed floor is strictly WEAKER than (implied by) the old broken
one, and unlike it is satisfiable at real params. So nothing is lost re-grounding onto `DomainSeparatedCR`. -/
theorem domainSeparatedCR_of_poseidon2SpongeCR {D : DomainSeparatedSponge}
    (hCR : Poseidon2Binding.Poseidon2SpongeCR D.sponge) : DomainSeparatedCR D :=
  domainSeparatedCR_of_injective_sponge (fun _ _ h => hCR _ _ h)

/-! ### The refutation: a BROKEN domain separation. -/

/-- A **broken** domain separation: the sponge IGNORES its input entirely (constant `0`), so the
domain-separation tag separates nothing — every pair of distinct inputs collides at every tag. -/
def brokenDomainSep : DomainSeparatedSponge where
  sponge := fun _ => 0
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  tagCode := fun _ => []
  deployedTag := ()

/-- A finder that outputs the distinct pair `([0], [1])` — a genuine collision under the broken sponge. -/
def brokenFinder : CollisionFinder (poseidon2KeyedFamily brokenDomainSep) where
  find := fun _ _ => (([0], [1]) : List ℤ × List ℤ)

theorem brokenFinder_wins (n : ℕ) (k : (poseidon2KeyedFamily brokenDomainSep).Key n) :
    brokenFinder.wins n k = true := by
  simp [CollisionFinder.wins, brokenFinder, poseidon2KeyedFamily, brokenDomainSep]

/-- **(REFUTABILITY.)** The broken domain separation is NOT collision-resistant: the constant finder
wins on every tag, so its advantage is the constant `1`, not negligible. So `DomainSeparatedCR` is
LOAD-BEARING — a broken domain separation refutes it — not vacuously true. -/
theorem brokenDomainSep_not_CR : ¬ DomainSeparatedCR brokenDomainSep := by
  intro hCR
  have hadv : collisionAdv (poseidon2KeyedFamily brokenDomainSep) brokenFinder = fun _ => (1 : ℝ) := by
    funext n
    have hall : (fun k : (poseidon2KeyedFamily brokenDomainSep).Key n => brokenFinder.wins n k)
        = (fun _ => true) := by
      funext k; exact brokenFinder_wins n k
    show @winProb ((poseidon2KeyedFamily brokenDomainSep).Key n)
        ((poseidon2KeyedFamily brokenDomainSep).keyFintype n)
        (fun k => brokenFinder.wins n k) = 1
    rw [hall]
    exact @winProb_top ((poseidon2KeyedFamily brokenDomainSep).Key n)
      ((poseidon2KeyedFamily brokenDomainSep).keyFintype n)
      ((poseidon2KeyedFamily brokenDomainSep).keyNonempty n)
  exact not_negl_one (hadv ▸ hCR brokenFinder)

/-! ### A SATISFYING witness at the REAL params (non-vacuity of the whole bridge). -/

/-- A concrete domain-separated deployment over `Poseidon2Binding.Reference.refSponge` (the provably-
injective stand-in Poseidon2, tagged with the REAL `babyBearD4W16` params) — a genuine domain-separation
prefix `[7]` ahead of the message. This inhabits `DomainSeparatedSponge` and satisfies `DomainSeparatedCR`,
so the bridge and every consumer connection below FIRE on a concrete instance. -/
def refDomainSep : DomainSeparatedSponge where
  sponge := Poseidon2Binding.Reference.refSponge
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  tagCode := fun _ => [7]
  deployedTag := ()

theorem refDomainSep_CR : DomainSeparatedCR refDomainSep :=
  domainSeparatedCR_of_poseidon2SpongeCR Poseidon2Binding.Reference.refSponge_CR

/-! ## §4 — the connection: the deployed consumers rest on the deployed hash's domain-separation CR.

Under `DomainSeparatedCR D` (the deployed sponge's domain-separation floor), every
`FloorRegroundedConsumers` advantage bound fires at `F := poseidon2KeyedFamily D`. So the STARK/FRI/
binding consumers — `FinBindsKernel`'s full-state root binder, the OOD/Merkle-opening/trace-digest
binders, the multi-round FRI/STARK fold, and the apex two-hash forgery advantage — are now bridged to
the REAL deployed Poseidon2 (its domain-separated keyed family), not an abstract `F`. -/

/-- **`FinBindsKernel` root binder, bridged.** The full-state-root-equivocation adversary (two distinct
kernel states committing to one root — `FinBindsKernel.recStateCommit_binds_kernel_fin`'s collision) has
negligible advantage under the DEPLOYED sponge's domain-separation floor. -/
theorem deployed_recStateCommit_advantage_bound (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (rootEquivocator : CollisionFinder (poseidon2KeyedFamily D)) :
    Negl (collisionAdv (poseidon2KeyedFamily D) rootEquivocator) :=
  FloorRegroundedConsumers.recStateCommit_root_advantage_bound hD rootEquivocator

/-- **OOD / Merkle-opening binder, bridged.** The opening-equivocation adversary has negligible advantage
under the deployed domain-separation floor. -/
theorem deployed_oodCommitmentOpening_advantage_bound (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (opener : CollisionFinder (poseidon2KeyedFamily D)) :
    Negl (collisionAdv (poseidon2KeyedFamily D) opener) :=
  FloorRegroundedConsumers.oodCommitmentOpening_advantage_bound hD opener

/-- **FRI oracle binder, bridged.** -/
theorem deployed_friOracle_binding_advantage_bound (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (oracleEquivocator : CollisionFinder (poseidon2KeyedFamily D)) :
    Negl (collisionAdv (poseidon2KeyedFamily D) oracleEquivocator) :=
  FloorRegroundedConsumers.friOracle_binding_advantage_bound hD oracleEquivocator

/-- **AIR trace-digest binder, bridged.** -/
theorem deployed_committedTrace_pinned_advantage_bound (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (traceEquivocator : CollisionFinder (poseidon2KeyedFamily D)) :
    Negl (collisionAdv (poseidon2KeyedFamily D) traceEquivocator) :=
  FloorRegroundedConsumers.committedTrace_pinned_advantage_bound hD traceEquivocator

/-- **Multi-round FRI/STARK fold, bridged.** The total binding-failure advantage across the `rounds`
Merkle checks is a finite sum of per-round collision advantages, negligible under the deployed floor. -/
theorem deployed_friStark_fold_advantage_bound (D : DomainSeparatedSponge) (rounds : Finset ℕ)
    (roundEquivocator : ℕ → CollisionFinder (poseidon2KeyedFamily D)) (hD : DomainSeparatedCR D) :
    Negl (fun n => ∑ r ∈ rounds, collisionAdv (poseidon2KeyedFamily D) (roundEquivocator r) n) :=
  FloorRegroundedConsumers.friStark_fold_advantage_bound rounds roundEquivocator hD

/-- **APEX two-hash forgery advantage, bridged.** The light-client forgery advantage — trace-commitment
equivocation PLUS OOD-commitment equivocation — is negligible under the DEPLOYED sponge's domain-
separation floor. The deployed apex is now welded to the real hash. -/
theorem deployed_lightclientUnfoolable_advantage_bound (D : DomainSeparatedSponge) (hD : DomainSeparatedCR D)
    (traceEquivocator oodEquivocator : CollisionFinder (poseidon2KeyedFamily D)) :
    Negl (fun n => collisionAdv (poseidon2KeyedFamily D) traceEquivocator n
        + collisionAdv (poseidon2KeyedFamily D) oodEquivocator n) :=
  FloorRegroundedConsumers.lightclientUnfoolable_advantage_bound hD traceEquivocator oodEquivocator

/-! ### The bridge FIRES on a concrete deployment (non-vacuity of the connection). -/

/-- The apex two-hash bridge fires on the concrete `refDomainSep` deployment at the real `babyBearD4W16`
params — the hypothesis `DomainSeparatedCR refDomainSep` is INHABITED (`refDomainSep_CR`), so the bridge
is a genuine implication, not a vacuous one. -/
example (traceEquivocator oodEquivocator : CollisionFinder (poseidon2KeyedFamily refDomainSep)) :
    Negl (fun n => collisionAdv (poseidon2KeyedFamily refDomainSep) traceEquivocator n
        + collisionAdv (poseidon2KeyedFamily refDomainSep) oodEquivocator n) :=
  deployed_lightclientUnfoolable_advantage_bound refDomainSep refDomainSep_CR traceEquivocator oodEquivocator

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms deployed_hash_is_family_instance
#assert_axioms wins_iff_deployed_collision
#assert_axioms domainSeparatedCR_of_injective_sponge
#assert_axioms domainSeparatedCR_of_poseidon2SpongeCR
#assert_axioms brokenDomainSep_not_CR
#assert_axioms refDomainSep_CR
#assert_axioms deployed_recStateCommit_advantage_bound
#assert_axioms deployed_lightclientUnfoolable_advantage_bound
#assert_axioms deployed_friStark_fold_advantage_bound

end Dregg2.Circuit.Poseidon2KeyedBridge
