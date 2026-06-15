/-
# Dregg2.AttestCube — the per-turn ATTESTATION CUBE (dregg4: Disclosure × Transferability × Agreement).

This module ASSEMBLES three independently-proved dials into one per-turn attestation point
and proves the cube's coherence 2-cells + its load-bearing impossibility corner. It builds
NOTHING from scratch — every dial is a finished object elsewhere; here they become one type.

The three axes (each a proved structure in its own module):

  * **Disclosure** = `Metatheory.Dial` — a bounded chain `acceptanceOnly < selective <
    fullDisclosure` (`Metatheory/EpistemicDial.lean`, proved `LinearOrder` + `BoundedOrder`).
    *How much* a verifier learns.
  * **Transferability** = `Dregg2.Authority.DV.TransferDial Verifier` —
    `transferable` (convince everyone, non-repudiable) vs `designated V₀` (convince only `V₀`,
    deniable) (`Dregg2/Authority/DesignatedVerifier.lean`). *To whom* the proof is convincing.
  * **Agreement** = `Dregg2.Finality.Tier` — `causal < ackThreshold < bft < constitutional`
    (`Dregg2/Finality.lean`, proved `LinearOrder`). *How finalized* the turn is.

The realized vision (per `docs/guides/authority.md` §"The caveat / attestation dial-cube" and the
dregg4 DREGG4-UNIFICATION §6.1 / DREGG4-HYPERSYSTEM §8.1 attestation-cube):

  1. `Turn.Attest` — one cube point carrying all three coordinates (§6.1 the cube IS the
     per-turn attestation type).
  2. The two coherence **2-cells**:
       (a) `disclosure_transfer_orthogonal` — Disclosure ⟂ Transferability: the product is
           genuine, every (disclosure, transferability) pair is realized, no pullback collapse.
       (b) `agreement_directed` — the Agreement coordinate only moves UP along a turn's
           finalization run (reuses `Finality.no_downgrade`; §8.1 directed agreement edge).
  3. The impossibility surface `deniable_bft_quorum_empty` — the corner
     "deniable transferability ∧ BFT-quorum agreement" is EMPTY *under the bridge that BFT
     finality requires the authorization be quorum-verifiable* (= transferable to the committee).
     This is the cube's load-bearing corner: you cannot have a deniable authorization that a
     BFT committee each independently verifies. The bare product corner is INHABITED (the cube is
     not collapsed) — `deniable_bft_inhabited_bare`; the EMPTINESS is the *semantic* obstruction,
     conditional on the honest bridge, not a type-level collapse.
  4. Non-vacuity #guards: the cube is genuinely 3-dimensional — two points differing in EACH
     coordinate (`cubeIsThreeDimensional`), assembled on the reference DV-kernel.

Everything here is additive: it imports the three modules and re-uses their proved theorems; it
edits none of them. Kernel-clean (`{propext, Classical.choice, Quot.sound}`), pinned below.
-/
import Dregg2.Finality
import Dregg2.Authority.DesignatedVerifier
import Metatheory.EpistemicDial

namespace Dregg2.AttestCube

open Dregg2.Finality (Tier)
open Dregg2.Authority.DV (DVKernel TransferDial DialHolds Transferable DesignatedFor DischargedFor
  designated_excludes_public designated_not_transferable)
open Metatheory (Dial)

/-! ## §1. The cube point — `Turn.Attest` (DREGG4-UNIFICATION §6.1).

One per-turn attestation is a point in the cube: a coordinate on each of the three independent
dials. The transferability axis is parameterised by the verifier set `V` (the dial itself is). -/

/-- **`Turn.Attest V` — a single per-turn attestation point in the cube.** Three coordinates,
one per proved dial:

  * `disclosure : Dial` — how much a verifier learns (`acceptanceOnly … fullDisclosure`);
  * `transferability : TransferDial V` — to whom the proof is convincing (`transferable` |
    `designated V₀`);
  * `agreement : Tier` — how finalized the turn is (`causal … constitutional`).

The cube is `Dial × TransferDial V × Tier`; this structure NAMES that product as the attestation
type a turn carries. The three axes are independent (the orthogonality 2-cell below witnesses the
product is genuine), so a `Turn.Attest` is free to take any value on each axis. -/
structure Turn.Attest (V : Type) where
  /-- Disclosure coordinate: the epistemic dial position (`Metatheory.Dial`). -/
  disclosure : Dial
  /-- Transferability coordinate: the DV transferability dial (`DV.TransferDial`). -/
  transferability : TransferDial V
  /-- Agreement coordinate: the finality tier (`Finality.Tier`). -/
  agreement : Tier
  deriving Repr

namespace Turn.Attest

variable {V : Type}

/-- The cube point as the bare triple — the cube IS this product, nothing more, nothing less. -/
def toTriple (a : Turn.Attest V) : Dial × TransferDial V × Tier :=
  ⟨a.disclosure, a.transferability, a.agreement⟩

/-- Build a cube point from a triple (the inverse of `toTriple`). -/
def ofTriple (t : Dial × TransferDial V × Tier) : Turn.Attest V :=
  ⟨t.1, t.2.1, t.2.2⟩

@[simp] theorem ofTriple_toTriple (a : Turn.Attest V) : ofTriple a.toTriple = a := rfl
@[simp] theorem toTriple_ofTriple (t : Dial × TransferDial V × Tier) : (ofTriple t).toTriple = t :=
  rfl

end Turn.Attest

/-! ## §2. Coherence 2-cell (a) — Disclosure ⟂ Transferability (DREGG4-HYPERSYSTEM §8.1).

The first coherence 2-cell: the disclosure axis and the transferability axis are INDEPENDENT —
the product is genuine, not a pullback that secretly collapses one onto the other. Concretely: a
turn's disclosure level does not constrain its transferability and vice-versa. We witness this the
faithful way — by showing the assignment `(d, t) ↦ Attest` is a *bijection* onto the disclosure ×
transferability plane (every pair is realized exactly once), so no value of one axis is forbidden
by the other. (A pullback collapse would make some `(d, t)` unreachable.) -/

/-- The disclosure × transferability *plane* (the agreement coordinate fixed): the projection of a
cube point onto its first two axes. -/
def plane (V : Type) := Dial × TransferDial V

/-- Project a cube point to the disclosure × transferability plane. -/
def Turn.Attest.toPlane {V : Type} (a : Turn.Attest V) : plane V :=
  ⟨a.disclosure, a.transferability⟩

/-- **2-cell (a) — `disclosure_transfer_orthogonal`.** The two axes are independent: the map
`(d, t) ↦ a cube point with those coordinates` lands every disclosure × transferability pair, and
recovers the pair exactly. Formally a *section/retraction* pair onto the plane:

  * `toPlane (mk d t agr) = (d, t)` for every disclosure `d`, transferability `t`, agreement
    `agr` — i.e. **fixing the agreement coordinate, the plane is hit surjectively**: NO `(d, t)`
    is excluded by the other axis (a pullback collapse would forbid some pair).

This is the honest content of "the product is genuine, not a pullback": disclosure does not
constrain transferability and vice-versa — each combination is inhabited at any agreement tier. -/
theorem disclosure_transfer_orthogonal {V : Type} (d : Dial) (t : TransferDial V) (agr : Tier) :
    (Turn.Attest.mk d t agr).toPlane = (d, t) := rfl

/-- **Orthogonality, surjective form.** Every disclosure × transferability pair is the projection
of some cube point — at *any* chosen agreement tier. The plane is covered: the two axes do not
restrict one another. -/
theorem plane_covered {V : Type} (agr : Tier) (p : plane V) :
    ∃ a : Turn.Attest V, a.toPlane = p ∧ a.agreement = agr :=
  ⟨Turn.Attest.mk p.1 p.2 agr, rfl, rfl⟩

/-- **Orthogonality, independence form (the cleanest statement).** Varying transferability while
holding disclosure fixed stays a legal cube point with the SAME disclosure — and symmetrically.
So neither axis is a function of the other: the product is free. -/
theorem axes_independent {V : Type} (d : Dial) (t₁ t₂ : TransferDial V) (agr : Tier) :
    (Turn.Attest.mk d t₁ agr).disclosure = (Turn.Attest.mk d t₂ agr).disclosure
    ∧ (Turn.Attest.mk d t₁ agr).transferability = t₁
    ∧ (Turn.Attest.mk d t₂ agr).transferability = t₂ :=
  ⟨rfl, rfl, rfl⟩

/-! ## §3. Coherence 2-cell (b) — directed Agreement (DREGG4-HYPERSYSTEM §8.1).

The second coherence 2-cell: the agreement coordinate is DIRECTED — along a turn's finalization
run it only moves up. A turn cannot downgrade finality. This is exactly `Finality.no_downgrade`
lifted onto the cube: the agreement axis of `Turn.Attest` is monotone non-decreasing under
re-finalization. We reuse the proved finality-strength transition system verbatim. -/

/-- **2-cell (b) — `agreement_directed`.** Along any run of the finality-strength system
(`Finality.finalitySystem`, where a step may only keep or strengthen the tier), a cube point's
agreement coordinate ends no weaker than it began. The agreement axis is a one-way edge — a turn's
attestation can be *re-finalized upward* (causal → bft → …) but never downgraded. This is
`Finality.no_downgrade` read on the agreement coordinate of `Turn.Attest`. -/
theorem agreement_directed {V : Type} (a₀ a : Turn.Attest V)
    (hrun : Execution.Run Finality.finalitySystem a₀.agreement a.agreement) :
    a₀.agreement ≤ a.agreement :=
  Finality.no_downgrade hrun

/-- **Directed Agreement, single-step form.** One re-finalization event never lowers the agreement
coordinate. The atomic version of the directed edge (each step of the run obeys it). -/
theorem agreement_step_no_downgrade {V : Type} (a₀ a : Turn.Attest V)
    (hstep : Finality.finalitySystem.Step a₀.agreement a.agreement) :
    a₀.agreement ≤ a.agreement :=
  hstep

/-! ## §4. The impossibility surface — the cube's load-bearing corner.

The corner of interest: **deniable transferability ∧ high (BFT) agreement**. Is it inhabited or
empty? The answer is the cube's whole point, and it is subtle — so we state BOTH halves precisely.

  * At the level of the **bare product type**, the corner is INHABITED: nothing in the *types*
    forbids a cube point with `transferability = designated V₀` and `agreement = bft`. The cube is
    NOT collapsed. (`deniable_bft_inhabited_bare`.)
  * The genuine obstruction is **semantic**: a BFT tier means a *quorum/committee* each
    independently verifies the turn's authorization — which, read at full strength, is exactly
    `Transferable` (the authorization proof convinces every relevant verifier). But a
    `designated V₀` authorization is, by `designated_excludes_public`, NOT transferable: there is a
    verifier it does not convince. So **under the bridge "BFT-finality ⇒ the authorization is
    quorum-verifiable (transferable)", the corner is EMPTY** (`deniable_bft_quorum_empty`).

The verdict: the deniable-∧-BFT corner is **EMPTY as an attested region** (you cannot have a
deniable authorization that a BFT committee each verifies) while **inhabited as a bare cube point**
(the dials are genuinely independent coordinates). The impossibility is an obstruction on
*joint realizability under the finality semantics*, not a type collapse — which is the faithful
dregg4 reading of the load-bearing corner. -/

variable {Verifier Statement Proof VSecret : Type}

/-- **The honest bridge: BFT agreement requires a quorum-verifiable authorization.** A turn whose
agreement coordinate is at least `bft` is finalized by a known committee that each ratifies it; the
strongest faithful reading is that the turn's authorization transcript `(stmt, proof)` convinces
*every* verifier in play — i.e. it is `Transferable`. This is a *property of the attested turn*
(supplied by the BFT layer), NOT a Lean axiom: the impossibility below is conditional on it. The
designated-verifier corner contradicts exactly this bridge. -/
def BftQuorumVerifiable [DVKernel Verifier Statement Proof VSecret]
    (a : Turn.Attest Verifier) (stmt : Statement) (proof : Proof) : Prop :=
  Finality.Tier.bft ≤ a.agreement →
    Transferable Verifier (Statement := Statement) (Proof := Proof) (VSecret := VSecret) stmt proof

/-- **`deniable_bft_quorum_empty` — THE impossibility corner (EMPTY under the bridge).** There is
NO attested turn that is simultaneously (i) at the deniable / designated-verifier transferability
endpoint, (ii) at BFT agreement or higher, and (iii) BFT-quorum-verifiable. The three are jointly
unsatisfiable: (ii)+(iii) force the authorization `Transferable`, but (i) — via the proved
`designated_excludes_public` — forces it NOT transferable. You cannot have a BFT-finalized turn
whose authorization is deniable to the very committee that finalized it.

Assembled from `designated_excludes_public` (designated ⇒ ¬transferable) + the bridge. The
transferability coordinate `a.transferability = .designated V₀` is realized by `hholds` (the
transcript sits at that endpoint) — that IS the deniable corner; the agreement coordinate enters
through `hbft` on `a.agreement`. -/
theorem deniable_bft_quorum_empty
    [DVKernel Verifier Statement Proof VSecret]
    (a : Turn.Attest Verifier) (V₀ : Verifier) (stmt : Statement) (proof : Proof)
    -- (i) deniable / designated transferability endpoint, realized by a transcript:
    (hholds : DialHolds (VSecret := VSecret) (Verifier := Verifier) (.designated V₀) stmt proof)
    -- (ii) BFT agreement or higher (the cube point's agreement coordinate):
    (hbft : Finality.Tier.bft ≤ a.agreement)
    -- (iii) the BFT-quorum-verifiable bridge:
    (hquorum : BftQuorumVerifiable (VSecret := VSecret) (Statement := Statement) a stmt proof) :
    False := by
  -- (ii)+(iii): the authorization is transferable …
  have htrans : DialHolds (VSecret := VSecret) (Verifier := Verifier) .transferable stmt proof :=
    hquorum hbft
  -- (i): … but the designated endpoint excludes the transferable endpoint.
  exact (designated_excludes_public (VSecret := VSecret) hholds) htrans

/-- **The contrapositive — `bft_quorum_forbids_deniability`.** A BFT-quorum-verifiable turn at BFT
agreement CANNOT carry a deniable (designated-verifier) authorization: the only transferability
endpoint left is `transferable` (public, non-repudiable). High agreement *forces non-repudiation*.
This is the positive reading of the empty corner. -/
theorem bft_quorum_forbids_deniability
    [DVKernel Verifier Statement Proof VSecret]
    (a : Turn.Attest Verifier) (V₀ : Verifier) (stmt : Statement) (proof : Proof)
    (hbft : Finality.Tier.bft ≤ a.agreement)
    (hquorum : BftQuorumVerifiable (VSecret := VSecret) (Statement := Statement) a stmt proof) :
    ¬ DialHolds (VSecret := VSecret) (Verifier := Verifier) (.designated V₀) stmt proof := by
  intro hholds
  exact deniable_bft_quorum_empty (VSecret := VSecret) a V₀ stmt proof hholds hbft hquorum

/-- **`deniable_bft_inhabited_bare` — the corner IS inhabited as a bare cube point.** Without the
finality-semantics bridge, the type `Turn.Attest` happily holds a point that is BOTH deniable
(`designated V₀`) AND at BFT agreement. The cube is genuinely 3-dimensional — the EMPTINESS above
is a *semantic* obstruction (the quorum-verifiability bridge), NOT a collapse of the product type.
This is the honest counterpoint to `deniable_bft_quorum_empty`. -/
theorem deniable_bft_inhabited_bare {V : Type} (V₀ : V) :
    ∃ a : Turn.Attest V,
      a.transferability = .designated V₀ ∧ a.agreement = Finality.Tier.bft :=
  ⟨Turn.Attest.mk Dial.acceptanceOnly (.designated V₀) Finality.Tier.bft, rfl, rfl⟩

/-! ## §5. Non-vacuity — the cube is genuinely 3-dimensional.

Two cube points differing in EVERY coordinate, exhibited on the reference DV-kernel
(`DesignatedVerifier.lean`'s `Reference.V`). If the type were collapsed (any axis degenerate or two
axes fused), no such pair could exist. We pin it with executable `#guard`s on the coordinates. -/

open Dregg2.Authority.DV.Reference (V)

/-- A `Bool` discriminator on the transferability axis (`TransferDial` carries only `Repr`, not
`DecidableEq`): `true` at the public `transferable` endpoint, `false` at any `designated V₀`. Lets
us separate the two endpoints by a decidable computation — the two settings are literally the two
constructors. -/
def TransferDial.isPublic {W : Type} : TransferDial W → Bool
  | .transferable  => true
  | .designated _  => false

/-- A cube point at the LOW corner of every axis: minimal disclosure (`acceptanceOnly`), public
transferability, weakest agreement (`causal`). -/
def lowPoint : Turn.Attest V :=
  ⟨Dial.acceptanceOnly, .transferable, Finality.Tier.causal⟩

/-- A cube point at a HIGH corner of every axis: full disclosure, designated (the OTHER
transferability endpoint), strongest agreement (`constitutional`). Differs from `lowPoint` in ALL
THREE coordinates. -/
def highPoint : Turn.Attest V :=
  ⟨Dial.fullDisclosure, .designated V.v0, Finality.Tier.constitutional⟩

/-- **`cubeIsThreeDimensional` — the cube is not collapsed.** `lowPoint` and `highPoint` differ in
EACH of the three coordinates: disclosure (`acceptanceOnly ≠ fullDisclosure`), transferability
(`transferable ≠ designated`), and agreement (`causal ≠ constitutional`). A degenerate / fused cube
could not exhibit a pair separated on every axis. The three dials are genuinely independent
coordinates. -/
theorem cubeIsThreeDimensional :
    lowPoint.disclosure ≠ highPoint.disclosure
    ∧ lowPoint.transferability ≠ highPoint.transferability
    ∧ lowPoint.agreement ≠ highPoint.agreement := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · -- transferability: `transferable ≠ designated v0` (no DecidableEq on TransferDial V) — discharge
    -- through the `isPublic` discriminator, which separates the two endpoints decidably.
    intro h
    have : TransferDial.isPublic lowPoint.transferability
            = TransferDial.isPublic highPoint.transferability := congrArg _ h
    simp [lowPoint, highPoint, TransferDial.isPublic] at this
  · decide

/-- Each coordinate strictly moves along the dial's own order too (low < high on all three),
witnessing the points sit at opposite ends of each chain — not merely distinct. -/
theorem lowPoint_lt_highPoint_per_axis :
    lowPoint.disclosure < highPoint.disclosure
    ∧ lowPoint.agreement < highPoint.agreement := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

-- Executable non-vacuity: the coordinates differ on every axis (disclosure + agreement carry
-- `DecidableEq`/`Repr`; transferability is handled propositionally above).
#guard lowPoint.disclosure ≠ highPoint.disclosure
#guard lowPoint.agreement ≠ highPoint.agreement
#guard decide (lowPoint.disclosure < highPoint.disclosure)
#guard decide (lowPoint.agreement < highPoint.agreement)
-- the two transferability endpoints are the two distinct constructors (public vs designated):
#guard TransferDial.isPublic lowPoint.transferability
#guard TransferDial.isPublic highPoint.transferability == false
#guard TransferDial.isPublic lowPoint.transferability
        != TransferDial.isPublic highPoint.transferability

/-! ## §6. Axiom audit — kernel-clean (`{propext, Classical.choice, Quot.sound}`). -/

#assert_all_clean [disclosure_transfer_orthogonal, plane_covered, axes_independent,
  agreement_directed, agreement_step_no_downgrade,
  deniable_bft_quorum_empty, bft_quorum_forbids_deniability, deniable_bft_inhabited_bare,
  cubeIsThreeDimensional, lowPoint_lt_highPoint_per_axis]

end Dregg2.AttestCube
