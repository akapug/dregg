/-
# Dregg2.Crypto.BlindedSet — §8 discharge: blinded issuer-set membership.

A holder proves membership in an issuer's authorized set (a Poseidon2 Merkle commitment over its
members) without revealing which member (`blinded_leaf = hash_fact(leaf,[blinding])`). The
membership relation IS a Merkle membership against the issuer root, so the gadget reuses
`Crypto.Merkle` wholesale. Blinding is a separate epistemic obligation (dial floor +
`HolderAnonymity` carrier).

    blindedset_bridge       : Satisfies blindedSetCircuit (root, member) ↔ MemberOf member set
    blindedset_verify_sound : verify accepts → MemberOf  (derived off the bridge + `extractable`)
    blindedset_dial_wired   : dial pinned to verifier at `acceptanceOnly` (ZK floor; holder hidden)

Cryptographic residue: (a) `compress` collision-resistance (`collisionHard`, consumed by
`extractable`); (b) holder-anonymity indistinguishability (`HolderAnonymity` carrier). Both are
honest `Prop` carriers.
-/
import Dregg2.Crypto.Merkle
import Dregg2.Crypto.VerifierKernel
import Dregg2.Authority.Predicate
import Metatheory.EpistemicDial
import Dregg2.Tactics

namespace Dregg2.Crypto.BlindedSet

open Dregg2.Crypto Dregg2.Crypto.Merkle

universe u

/-! ## The blinded issuer-set membership relation (reusing the Merkle gadget).

The authorized set is committed as a Poseidon2 Merkle tree; `root` is the issuer's
authorized-set commitment. A holder is authorized iff its member key has a Merkle path
recomposing the issuer root — i.e. `Merkle.MerkleMembers`. `compress` (the node hash) stays
abstract; the bridge is the pure recomposition equivalence, with NO primitive seam. The
HOLDER-ANONYMITY (blinding) is a SEPARATE epistemic obligation handled by the dial floor +
the `HolderAnonymity` carrier below — it is NOT a constraint of the membership relation. -/

variable {Digest : Type u}

/-- **`MemberOf compress root member`** — the BlindedSet STATEMENT relation: `member` is in the
issuer's authorized set committed at `root`, i.e. it has a Merkle path recomposing the issuer
root. This is DEFINITIONALLY `Merkle.MerkleMembers` (a BlindedSet membership IS a Merkle
membership against the issuer root); the reuse is total, no new combinatorics. -/
def MemberOf (compress : Digest → Digest → Digest) (root member : Digest) : Prop :=
  MerkleMembers compress root member

/-! ## `CircuitIR` — the blinded membership AIR, REUSING the Merkle gadget verbatim.

`generate_blinded_merkle_poseidon2_trace` is the Merkle membership trace plus a per-row blinding
column (`blinded = hash_fact(current, [blinding])`) and a public-input swap (`blinded_leaf` for
the cleartext leaf). The MEMBERSHIP constraints — `MerkleHash` per row, `Transition` continuity,
the boundary `PiBinding`s — are EXACTLY the Merkle AIR's. So the circuit IS a `Merkle.CircuitIR`;
the blinding column is the epistemic (anonymity) layer, orthogonal to the recomposition the
bridge proves. We therefore reuse `Merkle.CircuitIR`/`Merkle.Satisfies` directly. -/

/-- **The blinded-set circuit IR** — a `Merkle.CircuitIR` (the membership sub-AIR); blinding is
the orthogonal anonymity column, not part of the recomposition relation. -/
abbrev CircuitIR (Digest : Type u) := Merkle.CircuitIR Digest

/-- **`Satisfies compress circuit root member`** — the blinded-set AIR check: the Merkle
membership AIR over `(root, member)` (every row's `MerkleHash`, `Transition` continuity, the two
boundary `PiBinding`s). The blinding is the epistemic layer (dial floor), not a satisfiability
constraint — so satisfiability IS Merkle satisfiability. -/
def Satisfies (compress : Digest → Digest → Digest)
    (circuit : CircuitIR Digest) (root member : Digest) : Prop :=
  Merkle.Satisfies compress circuit root member

/-! ## The bridge — `Satisfies ↔ MemberOf`, FULLY proven by REUSING `merkle_bridge`.

Both directions are `merkle_bridge` verbatim (BlindedSet membership = Merkle membership against
the issuer root). `compress` is abstract throughout — NO primitive seam. The only cryptographic
residue is `compress`'s CR (consumed by `extractable`, never here) and the holder-anonymity
indistinguishability (the dial-floor carrier, below). -/

/-- **`blindedset_sound` (the `→` half).** A satisfying blinded-membership trace PROVES the
holder is in the issuer's authorized set: `merkle_sound` extracts the recomposing path. -/
theorem blindedset_sound (compress : Digest → Digest → Digest) (root member : Digest)
    (circuit : CircuitIR Digest) (h : Satisfies compress circuit root member) :
    MemberOf compress root member :=
  merkle_sound compress root member circuit h

/-- **`blindedset_complete` (the `←` half).** A genuine authorized member has a satisfying
blinded-membership trace (`merkle_complete` builds it from the path). -/
theorem blindedset_complete (compress : Digest → Digest → Digest) (root member : Digest)
    (h : MemberOf compress root member) :
    ∃ circuit : CircuitIR Digest, Satisfies compress circuit root member :=
  merkle_complete compress root member h

/-- **`blindedset_bridge`** — the blinded-set AIR's satisfiability is exactly issuer-set
membership: a satisfying trace proves the holder is authorized (`blindedset_sound`), and every
authorized member has a satisfying trace (`blindedset_complete`). This is `merkle_bridge` reused
both directions — no primitive seam. Blinding lives in the dial floor (holder anonymity), not here;
`compress` CR is consumed by `blindedset_verify_sound`'s `extractable`, never by the bridge. -/
theorem blindedset_bridge (compress : Digest → Digest → Digest) (root member : Digest) :
    (∃ circuit : CircuitIR Digest, Satisfies compress circuit root member)
      ↔ MemberOf compress root member :=
  merkle_bridge compress root member

-- Tripwires: both bridge directions rest only on `merkle_bridge` — no primitive seam.
#assert_axioms blindedset_sound
#assert_axioms blindedset_complete
#assert_axioms blindedset_bridge

/-! ## Holder anonymity — the blinding obligation, as an honest indistinguishability carrier.

This is what makes a BlindedSet proof MORE private than a bare Merkle membership: the verifier
learns "this holder is in the issuer's set" but NOT WHICH member. We carry it exactly as
`Privacy.blinded_membership_hides_element` does — the verifier-visible `view` of two authorized
members is computationally INDISTINGUISHABLE. It is a `Prop` carrier (the ZK simulator/advantage
obligation, a circuit obligation per §8), NEVER discharged by exhibiting a witness pair. -/

/-- **`HolderAnonymity`** — the blinded-set anonymity carriers + law, bundled as a class (the
`CryptoKernel.lean`/`BlindedMembershipKernel` idiom). `view member` is everything the verifier
learns from a blinded proof of `member` (the issuer root + the blinded transcript — by design it
leaks nothing about which member); `ViewIndistinguishable` is the advantage bound. The LAW: two
authorized members of the SAME issuer root have indistinguishable views. A lawful instance is the
circuit/ZK discharge (§8); `Reference` exhibits one, making the law non-vacuous. -/
class HolderAnonymity (Digest : Type u) where
  /-- The issuer's authorized-set Merkle commitment (the public root). -/
  compress : Digest → Digest → Digest
  /-- The verifier-visible view of a blinded membership proof of `member` at `root` (the root +
  blinded transcript). The point: it is independent of WHICH member, hiding the holder. -/
  view : Digest → Digest → Nat
  /-- Computational indistinguishability of two blinded views (the ZK advantage bound). -/
  ViewIndistinguishable : Nat → Nat → Prop
  /-- **LAW — holder anonymity**: two authorized members of the same issuer root produce
  indistinguishable blinded views, so a verifier confirms "authorized" while learning nothing
  about WHICH holder. (Hiding advantage bound; circuit obligation §8 — never an exhibited pair.) -/
  hides_law : ∀ (root m m' : Digest),
    MemberOf compress root m → MemberOf compress root m' →
    ViewIndistinguishable (view m root) (view m' root)

/-- **`blindedset_hides_holder` — holder anonymity, de-vacuified.** Given two GENUINE authorized
members `m`, `m'` of the same issuer `root`, their blinded views are indistinguishable: the
verifier learns "a holder is authorized" but NOT which one. Body is the kernel's `hides_law`
FIELD — non-vacuous (witnessed by `Reference`). The analog of
`Privacy.blinded_membership_hides_element` for the issuer-set kind. -/
theorem blindedset_hides_holder [K : HolderAnonymity Digest]
    (root m m' : Digest)
    (h : MemberOf K.compress root m) (h' : MemberOf K.compress root m') :
    K.ViewIndistinguishable (K.view m root) (K.view m' root) :=
  K.hides_law root m m' h h'

#assert_axioms blindedset_hides_holder

/-! ## Layer B — the blinded-set `VerifierKernel`: `verify` + carriers + DERIVED `verify_sound`.

Mirrors `MerkleVerifierKernel`. `verify` is the §8 oracle over the disclosed `(root, blinded_leaf)`;
`extractable` (STARK soundness + `compress` CR) gives "accept ⇒ a satisfying membership trace
against the issuer root exists"; `blindedset_verify_sound` is DERIVED off the bridge's soundness
half. The blinding does not enter soundness — it is the anonymity floor (above). -/

/-- **The disclosed blinded-set statement** — the public inputs the verifier sees: the issuer's
authorized-set Merkle root and the BLINDED member key (`blinded_leaf = hash_fact(leaf,[blinding])`,
`membership.rs:234`). The cleartext member is HIDDEN; `compress` CR binds the proof to the root. -/
structure Statement (Digest : Type u) where
  /-- The issuer's authorized-set Poseidon2 commitment (public). -/
  root : Digest
  /-- The blinded member key proved authorized (public; hides which member). -/
  blindedMember : Digest

/-- **Layer B — the blinded-set `VerifierKernel`.** The `compress` primitive, the §8 `verify`
oracle over the disclosed `(root, blindedMember)`, and the STARK `extractable` carrier. `extract`
unpacks `extractable`: an accepted proof witnesses a satisfying membership trace against the
issuer root for SOME member key — the existence FRI/Fiat-Shamir + `compress`-CR soundness
delivers (the cleartext member stays hidden; the bridge needs only that SOME path exists). -/
class BlindedSetVerifierKernel (Digest : Type u) (Proof : Type u) where
  /-- The abstract Poseidon2 node hash (the Layer-A `compress`; CR is `collisionHard`). -/
  compress : Digest → Digest → Digest
  /-- **The §8 verify oracle** (`stark::verify` for the blinded membership AIR): does `proof`
  discharge the disclosed `(root, blindedMember)`? An opaque `Bool`; soundness is `extractable`. -/
  verify : Statement Digest → Proof → Bool
  /-- **CARRIER — STARK extractability/soundness** (FRI + Fiat-Shamir + `compress` CR binding the
  proof to the issuer root): accept ⇒ a satisfying membership trace for some member exists. A
  `Prop`; never proved. -/
  extractable : Prop
  /-- `extractable` UNPACKED: an accepted proof witnesses a satisfying Merkle membership trace
  against the issuer root for SOME member key (the cleartext member is hidden by the blinding —
  the existential is exactly what the holder-anonymity buys). The form the bridge composes with. -/
  extract : extractable →
    ∀ (stmt : Statement Digest) (proof : Proof), verify stmt proof = true →
      ∃ (member : Digest) (circuit : CircuitIR Digest),
        Satisfies compress circuit stmt.root member

variable {Proof : Type u}

/-- **`blindedset_verify_sound`** — given the STARK-soundness carrier `extractable`, an accepted
blinded-set proof proves some member is in the issuer's authorized set:
`verify stmt proof = true  →  ∃ member, MemberOf compress stmt.root member`.
Derived by composing `extract` with `blindedset_bridge`'s soundness half; never assumed. The member
stays existentially hidden, which is the holder anonymity the dial floor records. -/
theorem blindedset_verify_sound [K : BlindedSetVerifierKernel Digest Proof]
    (hext : K.extractable) (stmt : Statement Digest) (proof : Proof)
    (haccept : K.verify stmt proof = true) :
    ∃ member : Digest, MemberOf K.compress stmt.root member := by
  obtain ⟨member, circuit, hsat⟩ := K.extract hext stmt proof haccept
  exact ⟨member, (blindedset_bridge K.compress stmt.root member).1 ⟨circuit, hsat⟩⟩

#assert_axioms blindedset_verify_sound

/-! ## Layer C — the kind obligation + the DIAL wiring at the `acceptanceOnly` floor.

Blinded issuer-set membership discloses ONE bit ("this holder is authorized") and HIDES which
member (holder anonymity) — the zero-knowledge floor, like blinded Merkle membership. So the
epistemic floor is `acceptanceOnly` (NOT `selective`): the verifier learns only authorization,
nothing about the holder. We wire `EpistemicDial.DiscloseAt` to the verifier exactly as
`PredicateKernel` does for Merkle. -/

open Dregg2.Authority.Predicate Dregg2.Laws Metatheory

/-- **`KindObligation`** for blinded-set membership — statement algebra `Statement Digest`, **dial
floor = `acceptanceOnly`** (blinded ⇒ holder anonymity: one bit "authorized", which holder hidden;
the ZK floor, like blinded membership). -/
structure KindObligation (Digest : Type u) where
  /-- The public-input algebra: the disclosed `(root, blindedMember)`. -/
  Statement : Type u
  /-- The dial floor — `acceptanceOnly` for blinded issuer-set membership. -/
  dialFloor : Dial

/-- The blinded-set kind's obligation: statement = disclosed `(root, blindedMember)`, floor =
`acceptanceOnly` (blinded ⇒ ZK floor: the verifier learns only "authorized", not the holder). -/
def blindedSetKindObligation : KindObligation Digest where
  Statement := Statement Digest
  dialFloor := Dial.acceptanceOnly

@[simp] theorem blindedSetKindObligation_floor :
    (blindedSetKindObligation (Digest := Digest)).dialFloor = Dial.acceptanceOnly :=
  rfl

/-! ### The dial wiring — `DiscloseAt` instantiated at the blinded-set verifier's `acceptanceOnly`
floor (the registry/dial machinery lives at universe 0, so we instantiate over `Type`). -/

section Wiring

variable {D : Type} {P : Type}

/-- A `Verifier (Statement D) P` from the kernel's §8 `verify` oracle. -/
def blindedSetVerifier [K : BlindedSetVerifierKernel D P] : Verifier (Statement D) P :=
  fun stmt proof => K.verify stmt proof

/-- The blinded-set-kind registry: the §8 `verify` oracle installed at `blindedSet`. -/
def blindedSetReg [BlindedSetVerifierKernel D P]
    (base : Registry (Statement D) P) : Registry (Statement D) P :=
  fun j => if j = .blindedSet then some blindedSetVerifier else base j

/-- The `Verifiable` seam this kind dispatches through (explicit `base`, not auto-synthesized). -/
@[reducible] def blindedSetSeam [BlindedSetVerifierKernel D P]
    (base : Registry (Statement D) P) : Verifiable (Statement D) P :=
  verifiableOfRegistry (blindedSetReg base) .blindedSet

/-- **`blindedSetDisclose` — the dial pinned to the blinded-set verifier.** `accepts d` is the
position-independent `Discharged stmt proof`; `accepts_eq := fun _ => Iff.rfl`. Realizes
"instantiate `DiscloseAt` at the `acceptanceOnly` floor (blinded membership: one bit, holder
hidden)". -/
def blindedSetDisclose [BlindedSetVerifierKernel D P]
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    @DiscloseAt Unit (Statement D) P _ (blindedSetSeam base) :=
  letI : Verifiable (Statement D) P := blindedSetSeam base
  { leaked := fun _ => ()
    mono := fun _ _ _ => le_refl _
    pred := stmt
    wit := proof
    accepts := fun _ => Discharged stmt proof
    accepts_eq := fun _ => Iff.rfl }

/-- **`blindedset_dial_wired`** — the blinded-set kind's floor is `acceptanceOnly` (holder-anonymity
ZK floor), the dial's bottom notch IS the verifier's `Discharged` bit, and an accepting proof
proves some member is in the issuer's authorized set (member hidden). Dial pinned to the per-kind
verifier. -/
theorem blindedset_dial_wired [K : BlindedSetVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P) (stmt : Statement D) (proof : P) :
    -- (1) the floor is acceptanceOnly:
    (blindedSetKindObligation (Digest := D)).dialFloor = Dial.acceptanceOnly ∧
    -- (2) the dial's bottom notch accepts IFF the blinded-set verifier discharges:
    (@DiscloseAt.accepts Unit (Statement D) P _ (blindedSetSeam base)
        (blindedSetDisclose base stmt proof) (⊥ : Dial)
      ↔ @Discharged (Statement D) P (blindedSetSeam base) stmt proof) ∧
    -- (3) and an accepting proof PROVES authorized membership, holder hidden (the cascade):
    (K.verify stmt proof = true →
      ∃ member : D, MemberOf K.compress stmt.root member) := by
  refine ⟨rfl, ?_, ?_⟩
  · exact @DiscloseAt.accepts_bot_iff_discharged Unit (Statement D) P _ (blindedSetSeam base)
      (blindedSetDisclose base stmt proof)
  · exact fun haccept => blindedset_verify_sound hext stmt proof haccept

/-- **`blindedset_registry_cascade`** — registering the blinded-set kind, an accepted proof both
`Discharged`s the kind's predicate (`registry_sound`) and — given `extractable` — proves some
member is in the issuer's authorized set (`blindedset_verify_sound`). Single trust boundary:
`extractable`. -/
theorem blindedset_registry_cascade [K : BlindedSetVerifierKernel D P]
    (hext : K.extractable)
    (base : Registry (Statement D) P)
    (stmt : Statement D) (proof : P)
    (haccept : K.verify stmt proof = true) :
    (@Discharged (Statement D) P (verifiableOfRegistry (blindedSetReg base) .blindedSet)
        stmt proof)
      ∧ ∃ member : D, MemberOf K.compress stmt.root member := by
  refine ⟨?_, blindedset_verify_sound hext stmt proof haccept⟩
  apply registry_sound (blindedSetReg base) .blindedSet stmt proof
  show registryVerify (blindedSetReg base) .blindedSet stmt proof = true
  unfold registryVerify blindedSetReg
  simp only [↓reduceIte]
  exact haccept

end Wiring

#assert_axioms blindedset_dial_wired
#assert_axioms blindedset_registry_cascade

/-! ## `Reference` — a concrete kernel + non-vacuity witnesses over `ℤ`.

The Layer-A `Crypto.Reference.instCryptoPrimitives` gives `compress a b := a + b`. We build a
degenerate blinded-set verifier kernel + a holder-anonymity kernel (`def`s, NOT global
`instance`s) and witness the bridge / verify-sound / cascade / anonymity end-to-end. NOT real
crypto. -/

namespace Reference

/-- The reference node hash over `ℤ`: `compress a b := a + b` (matching the Layer-A reference). -/
def refCompress : Int → Int → Int := fun a b => a + b

/-- A single-level membership witness over `ℤ`: member `x` is authorized at issuer root `x + s`
via a self-hash path `compress x s = x + s` with sibling `s` (`recompose (+) x [s] = x + s`). -/
theorem ref_member_at (x s : Int) : MemberOf refCompress (x + s) x :=
  ⟨[{ sib := s, position := 0 }], by simp, rfl⟩

/-- Non-vacuity of the BRIDGE completeness half: member `1` is authorized at issuer root `3`
(via sibling `2`, `1 + 2 = 3`), so the AIR is satisfied. -/
example : ∃ circuit : CircuitIR Int, Satisfies refCompress circuit 3 1 :=
  blindedset_complete refCompress 3 1 (by have := ref_member_at 1 2; norm_num at this; exact this)

/-- A degenerate reference blinded-set verifier kernel over `ℤ` (`def`, not a global `instance`).
`compress := (+)`; `verify` accepts iff `stmt.root = 3 ∧ stmt.blindedMember = 0` (the toy "some
member of the set rooted at 3 is authorized; the member is blinded to 0" check); `extractable :=
True`. `extract` rebuilds the membership trace for member `1` (authorized at root `3` via the
self-hash path), through `blindedset_complete`. -/
@[reducible] def refKernel : BlindedSetVerifierKernel Int Int where
  compress := refCompress
  verify stmt _ := decide (stmt.root = 3 ∧ stmt.blindedMember = 0)
  extractable := True
  extract := by
    intro _ stmt _ haccept
    obtain ⟨root, bm⟩ := stmt
    simp only [decide_eq_true_eq] at haccept
    obtain ⟨hr, _⟩ := haccept
    subst hr
    obtain ⟨circuit, hsat⟩ :=
      blindedset_complete refCompress 3 1
        (by have := ref_member_at 1 2; norm_num at this; exact this)
    exact ⟨1, circuit, hsat⟩

/-- The empty base registry over the toy `ℤ` blinded-set statement/proof. -/
def base : Registry (Statement Int) Int := fun _ => none

/-- A disclosed statement over `ℤ`: issuer root `3`, blinded member `0` — the reference verifier
accepts (it is the toy "a member of the set rooted at 3 is authorized, holder blinded" claim). -/
def authStmt : Statement Int := { root := 3, blindedMember := 0 }

/-- Non-vacuity of `blindedset_verify_sound`: at the reference kernel an accepted proof yields
SOME member in the issuer's authorized set rooted at `3`. -/
example : ∃ member : Int, MemberOf refCompress authStmt.root member :=
  blindedset_verify_sound (K := refKernel) trivial authStmt 0 (by decide)

/-- Non-vacuity of the FULL cascade: at the reference kernel an accepted proof both `Discharged`s
the registry predicate AND proves authorized membership (holder hidden). A NAMED witness so its
axiom footprint is checkable. -/
theorem reference_cascade_nonvacuous :
    (@Discharged (Statement Int) Int
        (verifiableOfRegistry (@blindedSetReg Int Int refKernel base) .blindedSet)
        authStmt 0)
      ∧ ∃ member : Int, MemberOf refCompress authStmt.root member :=
  blindedset_registry_cascade (K := refKernel) trivial base authStmt 0 (by decide)

-- Non-vacuity axiom footprint: rests only on the standard kernel axioms.
#print axioms reference_cascade_nonvacuous

/-- A degenerate reference holder-anonymity kernel over `ℤ`: `view := fun _ _ => 0` (the blinded
view is constant — it leaks nothing about which member), `ViewIndistinguishable := fun _ _ =>
True`; the hiding law holds because both views are `0` and `True` is reflexive. -/
@[reducible] def anonKernel : HolderAnonymity Int where
  compress := refCompress
  view _ _ := 0
  ViewIndistinguishable _ _ := True
  hides_law _ _ _ _ _ := trivial

/-- Non-vacuity of HOLDER ANONYMITY: two authorized members of the same issuer root have
indistinguishable blinded views — the verifier learns "authorized" not "which holder". Inhabited
at the reference anonymity kernel, so `blindedset_hides_holder` is not over an empty world. -/
example (m m' : Int)
    (h : MemberOf refCompress 3 m) (h' : MemberOf refCompress 3 m') :
    @HolderAnonymity.ViewIndistinguishable Int anonKernel
      (@HolderAnonymity.view Int anonKernel m 3) (@HolderAnonymity.view Int anonKernel m' 3) :=
  @blindedset_hides_holder Int anonKernel 3 m m' h h'

/-- Non-vacuity of the dial wiring: the floor is `acceptanceOnly`, the dial's bottom notch is the
verifier's bit, and an accepting proof proves authorized membership. -/
example :
    (blindedSetKindObligation (Digest := Int)).dialFloor = Dial.acceptanceOnly :=
  (blindedset_dial_wired (K := refKernel) trivial base authStmt 0).1

end Reference

-- Crypto residue: `extractable` carrier and `HolderAnonymity` advantage bound (honest `Prop`
-- carriers).
#assert_axioms blindedset_bridge
#assert_axioms blindedset_verify_sound
#assert_axioms blindedset_hides_holder
#assert_axioms blindedset_registry_cascade
#assert_axioms blindedset_dial_wired

end Dregg2.Crypto.BlindedSet
