/-
# AutomataflRevealJoin — the exact Leg-S recursive join, and its honest boundary.

`AutomataflRevealEmit` publishes a constrained contiguous copy of the two opened
commitments at PI `[39,41)`. This is not a decorative ABI: it is the exact shape
accepted by Rust's deployed `AppRootBinding`, with `app_root_pi_offset = 39`,
`app_root_len = 2`, and `field_key = 2`. The wide custom leg exposes the AFTER
state's eight flat fields; Automatafl registers `a_commit` and `b_commit` at
registers 5 and 6, hence octet lanes `5 - state.FIELD_BASE = 2` and `3`.

The capstone composes three equalities:

1. Leg S constrains each opening commitment to its contiguous join PI;
2. the deployed app-root weld equates that two-felt PI slice to the reveal
   receipt's AFTER commitment fields; and
3. the reveal transition preserves those fields from the preceding committed
   state.

The theorem describes a real join shape, not a currently safe caller. Three exact
deployment blockers remain:

* the live surface commits with a truncated ~63-bit BLAKE3 `u64`, whereas Leg S
  opens one ~31-bit BabyBear Poseidon2 lane; the app-root octet exposes only the
  low-32-bit lane of each `field_from_u64` value;
* the old-board pack is nine felts derived from heap-resident board cells, while
  the current app-root carrier exposes only eight flat field lanes; and
* the live playable game is 5×5 while this descriptor is fixed at 11×11.

Therefore this file deliberately does not register a descriptor or invent a
caller. A real caller needs a multi-felt reveal commitment with a matching host
encoding, the old-pack equality carrier, and an n=11 game (or a live-N/n-parametric
Leg S).
-/
import Dregg2.Circuit.Emit.AutomataflRevealRefine
import Dregg2.Circuit.Emit.EffectVmEmitRotationV3

namespace Dregg2.Circuit.Emit.AutomataflRevealJoin

open Dregg2.Circuit.DescriptorIR2 (VmTrace)
open Dregg2.Circuit.Emit.AutomataflRevealEmit
open Dregg2.Circuit.Emit.AutomataflRevealRefine
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitRotationV3 (CUSTOM_APP_FIELD_OCTET_LEN)

set_option autoImplicit false

/-! ## The deployed app-root binding shape. -/

/-- Lean mirror of the three values consumed by Rust `AppRootBinding`. -/
structure AppRootBindingSpec where
  appPiOffset : Nat
  appRootLen : Nat
  fieldKey : Nat
deriving DecidableEq

def COMMIT_FIELD_KEY : Nat := 2
def A_COMMIT_REGISTER : Nat := 5
def B_COMMIT_REGISTER : Nat := 6

def legSCommitBinding : AppRootBindingSpec :=
  { appPiOffset := JOIN_COMMIT_PI_BASE
  , appRootLen := 2
  , fieldKey := COMMIT_FIELD_KEY }

def AppRootBindingWellFormed (b : AppRootBindingSpec) : Prop :=
  b.appRootLen > 0 ∧ b.appPiOffset ≥ DOOR_PI_COUNT ∧
    b.fieldKey + b.appRootLen ≤ CUSTOM_APP_FIELD_OCTET_LEN

theorem legSCommitBinding_wellFormed : AppRootBindingWellFormed legSCommitBinding := by
  norm_num [AppRootBindingWellFormed, legSCommitBinding, JOIN_COMMIT_PI_BASE,
    DOOR_PI_COUNT, COMMIT_FIELD_KEY, CUSTOM_APP_FIELD_OCTET_LEN]

#guard state.FIELD_BASE + COMMIT_FIELD_KEY == A_COMMIT_REGISTER
#guard state.FIELD_BASE + COMMIT_FIELD_KEY + 1 == B_COMMIT_REGISTER
#guard legSCommitBinding.appPiOffset == 39
#guard legSCommitBinding.appRootLen == 2
#guard legSCommitBinding.fieldKey == 2

/-! ## Equality carriers and the non-decorative join. -/

/-- The eight lane-0 field felts exposed from a committed cell state. -/
abbrev FieldOctet := Fin CUSTOM_APP_FIELD_OCTET_LEN → ℤ

/-- The exact equality established by the recursive app-root binding node for the
contiguous two-felt Leg-S commitment slice. -/
def AppRootWeldsCommitPair (t : VmTrace) (after : FieldOctet) : Prop :=
  ∀ s : Fin 2,
    t.pub (JOIN_COMMIT_PI_BASE + s.val) =
      after ⟨COMMIT_FIELD_KEY + s.val, by
        have hs := s.isLt
        simp only [CUSTOM_APP_FIELD_OCTET_LEN, COMMIT_FIELD_KEY]
        omega⟩

/-- The reveal method leaves both commitment fields unchanged from the preceding
commit receipt to the reveal receipt. -/
def RevealPreservesCommitPair (before after : FieldOctet) : Prop :=
  ∀ s : Fin 2,
    after ⟨COMMIT_FIELD_KEY + s.val, by
      have hs := s.isLt
      simp only [CUSTOM_APP_FIELD_OCTET_LEN, COMMIT_FIELD_KEY]
      omega⟩ =
    before ⟨COMMIT_FIELD_KEY + s.val, by
      have hs := s.isLt
      simp only [CUSTOM_APP_FIELD_OCTET_LEN, COMMIT_FIELD_KEY]
      omega⟩

/-- **Commit-pair join capstone.** The opened Poseidon commitments are not merely
published by Leg S: after the app-root weld and reveal immutability equality, they
are exactly the two commitments held in the preceding committed cell state. -/
theorem legS_commit_pair_bound_to_preceding {hash : List ℤ → ℤ} {t : VmTrace}
    {before after : FieldOctet} (hS : LegSSemantics hash t)
    (hWeld : AppRootWeldsCommitPair t after)
    (hPreserve : RevealPreservesCommitPair before after) :
    ∀ s : Fin 2,
      (publicOpening t s.val).commit =
        before ⟨COMMIT_FIELD_KEY + s.val, by
          have hs := s.isLt
          simp only [CUSTOM_APP_FIELD_OCTET_LEN, COMMIT_FIELD_KEY]
          omega⟩ := by
  intro s
  exact (hS.2.1 s.val s.isLt).trans ((hWeld s).trans (hPreserve s))

/-! ## The board-pack carrier: theorem present, deployed wire absent. -/

abbrev OldBoardPack := Fin PACK_FELTS → ℤ

/-- The missing equality wire a preceding-state board-pack carrier must establish.
It is intentionally stated at the exact PI indices, so a future heap opening or
recursive join has one target rather than a prose obligation. -/
def OldBoardPackEqualityCarrier (t : VmTrace) (beforePack : OldBoardPack) : Prop :=
  ∀ j : Fin PACK_FELTS, t.pub (PACK_PI_BASE + j.val) = beforePack j

structure FullyJoinedLegS (hash : List ℤ → ℤ) (t : VmTrace)
    (before : FieldOctet) (beforePack : OldBoardPack) : Prop where
  openingA : Opens hash 0 (publicOpening t 0)
  openingB : Opens hash 1 (publicOpening t 1)
  commitsBefore : ∀ s : Fin 2,
    (publicOpening t s.val).commit =
      before ⟨COMMIT_FIELD_KEY + s.val, by
        have hs := s.isLt
        simp only [CUSTOM_APP_FIELD_OCTET_LEN, COMMIT_FIELD_KEY]
        omega⟩
  oldPackBefore : ∀ j : Fin PACK_FELTS,
    t.pub (PACK_PI_BASE + j.val) = beforePack j

/-- Strongest honest full join: Leg-S SAT semantics plus the deployed-shaped commit
weld and the exact (currently missing) old-pack carrier imply both openings are bound
to the complete preceding committed view. -/
theorem legS_fully_joined_of_carriers {hash : List ℤ → ℤ} {t : VmTrace}
    {before after : FieldOctet} {beforePack : OldBoardPack}
    (hS : LegSSemantics hash t) (hWeld : AppRootWeldsCommitPair t after)
    (hPreserve : RevealPreservesCommitPair before after)
    (hPack : OldBoardPackEqualityCarrier t beforePack) :
    FullyJoinedLegS hash t before beforePack := by
  exact
    { openingA := hS.2.2.1
    , openingB := hS.2.2.2
    , commitsBefore := legS_commit_pair_bound_to_preceding hS hWeld hPreserve
    , oldPackBefore := hPack }

/-! ## Deployment refusal teeth. -/

/-- Cardinality of the one-felt Leg-S commitment codomain. -/
def BABYBEAR_CARD : Nat := 2013265921

/-- The live host seal is `max(1, low_u64(BLAKE3(...)) >> 1)`: at most 63 bits,
before `field_from_u64` stores it. -/
def LIVE_HOST_SEAL_BITS : Nat := 63

/-- What the deployed flat-field app-root octet sees from a numeric host seal:
the low 32 bits, reduced into one BabyBear lane. The high 31 bits of the live
63-bit seal do not ride this carrier. -/
def liveHostSealLane0 (hostCommitment : Nat) : ℤ :=
  ((hostCommitment % (2^32)) % BABYBEAR_CARD : Nat)

/-- The exact additional equality an honest live caller would need. It is not
currently established: `hostSeal` is truncated BLAKE3, while the opening commit
is one-lane Poseidon2. -/
def LiveHostSealMatchesLegS (t : VmTrace) (hostSeal : Fin 2 → Nat) : Prop :=
  ∀ s : Fin 2, (publicOpening t s.val).commit = liveHostSealLane0 (hostSeal s)

/-- RED encoding tooth: the deployed app-root lane cannot faithfully carry the
live 63-bit seal even before accounting for the BLAKE3/Poseidon algorithm mismatch. -/
theorem live_host_seal_lane0_is_not_injective :
    (1 : Nat) ≠ 1 + 2^32 ∧ liveHostSealLane0 1 = liveHostSealLane0 (1 + 2^32) := by
  decide

/-- The one-felt codomain lies between `2^30` and `2^31`; generic birthday
search is therefore between `2^15` and `2^16` samples (about `2^15.5`), not a
deployment-grade collision floor. `Hash4NoCollision` remains only a conditional
idealization; the unconditional Leg-S result is the collision extractor. -/
theorem one_felt_commitment_cardinality_window :
    2^30 < BABYBEAR_CARD ∧ BABYBEAR_CARD < 2^31 := by
  decide

/-- Width tooth explaining why the current flat-field carrier cannot itself carry
the board pack. This does not claim that a future heap-opening carrier is impossible;
it pins precisely why the currently deployed app-root weld is insufficient. -/
theorem current_field_octet_too_short_for_old_pack :
    CUSTOM_APP_FIELD_OCTET_LEN < PACK_FELTS := by
  decide

/-- The live Rust offering is still 5×5. Registering this fixed-n11 leaf for that
caller would flatten different coordinates and commit a different board shape. -/
def LIVE_GAME_N : Nat := 5

theorem fixed_n11_descriptor_is_not_live_game_shape : LIVE_GAME_N ≠ N := by
  decide

#assert_axioms legSCommitBinding_wellFormed
#assert_axioms legS_commit_pair_bound_to_preceding
#assert_axioms legS_fully_joined_of_carriers
#assert_axioms live_host_seal_lane0_is_not_injective
#assert_axioms one_felt_commitment_cardinality_window
#assert_axioms current_field_octet_too_short_for_old_pack
#assert_axioms fixed_n11_descriptor_is_not_live_game_shape

#print axioms legS_commit_pair_bound_to_preceding
#print axioms legS_fully_joined_of_carriers

end Dregg2.Circuit.Emit.AutomataflRevealJoin
