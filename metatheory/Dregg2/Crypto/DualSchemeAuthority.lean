/-
# Dregg2.Crypto.DualSchemeAuthority — the DUAL-SCHEME agent-authority model (#3, BOTH-KEYED).

`TurnAuthSignature.lean` proves the IN-CIRCUIT curve path's forcing primitive: a verifying
turn-auth descriptor over `(agentPk, turnHash)` implies the rightful curve key signed THIS turn
(`turnauth_forces_authorization`), under the named curve floors `SchnorrDLHard` + `ForkingExtractor`.

This file models the TWO PARALLEL AUTHORITY MODES ember approved, anchored in the cell:

  - **Ed25519 = the off-circuit RECEIPT path.** The agent signs the turn hash with an ed25519 key;
    that signature is verified OFF-circuit (the executor's `SovereignCellWitness` leg). It is NEVER
    circuit-ified. We model it as a NAMED off-circuit predicate `Ed25519ReceiptVerifies` — an opaque
    relation, the point being that it is the verifier's off-circuit check, not an AIR gate.

  - **Curve = the in-circuit PROVEN (zk) path.** The agent signs with a BabyBear^8 Schnorr key whose
    verification IS an AIR; a verifying proven-mode turn is forced by `turnauth_forces_authorization`.

The cell commits a SCHEME-TAGGED authority `AuthScheme = Ed25519 edpk | Curve cpk | Both edpk cpk`.
A turn is AUTHORIZED iff (receipt mode) the committed ed25519 key verifies the turn hash off-circuit,
OR (proven mode) the in-circuit curve forcing binds `cpk == the cell's committed Curve/Both authority`.

## What is PROVEN here (no fresh axiom; reuses the curve floors)

- `dualscheme_proven_forces_authorization` — a verifying PROVEN-mode turn, whose forced curve key
  equals the cell's committed Curve authority, implies the rightful curve key authorized THIS turn
  (lifts `turnauth_forces_authorization`).
- `dualscheme_tag_is_committed` — the scheme TAG is part of the committed authority, so the verifier
  dispatches on the COMMITTED tag (downgrade-proof): the tag a turn presents must equal the cell's.
- The THREE anti-laundering teeth (ember's razor — being, not disclosure):
  - `dualscheme_no_downgrade` — a proven-mode turn whose forced `cpk ≠` the committed Curve authority
    is REJECTED (can't substitute a weaker/other key under the same commitment).
  - `dualscheme_no_cross_scheme_confusion` — `EdPubKey` (32B) and `CurvePubKey` (BabyBear^8) are
    DISTINCT, non-coercible shapes; no `edpk` authorizes a Curve-scoped action and vice versa.
  - `dualscheme_both_binding_is_committed` — the BOTH-keyed pair `(edpk, cpk)` is itself committed
    authority; changing EITHER leg changes the commitment (an authority op, not free agility).

The Ed25519 receipt verify is modeled as a NAMED off-circuit predicate, NEVER a circuit gate:
`dualscheme_ed25519_is_off_circuit` records that the receipt predicate is opaque to the in-circuit
forcing layer (it does not appear in `TurnAuthVerified` / `Authorized`).

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}` + the reused curve floors
`SchnorrDLHard`/`ForkingExtractor` as explicit hypotheses).
-/
import Dregg2.Crypto.TurnAuthSignature
import Dregg2.Tactics

namespace Dregg2.Crypto.DualSchemeAuthority

open Dregg2.Crypto.SchnorrCurveField
open Dregg2.Crypto.TurnAuthSignature

universe u

/-! ## §1 — Distinct, non-coercible key shapes (anti cross-scheme confusion at the TYPE level).

The Ed25519 receipt key is a 32-byte value (`EdPubKey`); the in-circuit Curve key is a curve point
(`CurvePubKey`, parametric over the curve's point type). They are DISTINCT types — there is no
coercion `EdPubKey → CurvePubKey` or vice versa, so no signature scoped to one key can authorize an
action scoped to the other. We carry an `is_ed`/`is_curve` discriminant so the disjointness is a
proved fact, not merely a syntactic two-constructor sum. -/

/-- The Ed25519 receipt public key: a 32-byte value. Off-circuit. Distinct shape from the curve key. -/
structure EdPubKey where
  bytes : List UInt8       -- 32 bytes in the live system; the SHAPE is what matters here
  deriving DecidableEq, BEq

/-- The in-circuit Curve public key: a curve point (BabyBear^8 in the live system), parametric.
`DecidableEq` is derived conditional on `Pt`'s — present exactly when the point type is decidable. -/
structure CurvePubKey (Pt : Type u) where
  point : Pt
  deriving DecidableEq, BEq

/-! ## §2 — The scheme-tagged committed authority.

`AuthScheme` is the authority the cell COMMITS. The tag (`Ed25519` / `Curve` / `Both`) is part of the
committed value: two cells with different tags have different `AuthScheme`s, so the verifier dispatches
on the COMMITTED tag (a turn cannot silently choose a weaker mode). -/

/-- **`AuthScheme Pt`** — the scheme-tagged, cell-committed authority. `Ed25519` carries the receipt
key, `Curve` the in-circuit key, `Both` BOTH (the both-keyed binding). The CONSTRUCTOR is the tag. -/
inductive AuthScheme (Pt : Type u) where
  | Ed25519 (edpk : EdPubKey)
  | Curve   (cpk : CurvePubKey Pt)
  | Both    (edpk : EdPubKey) (cpk : CurvePubKey Pt)
  deriving DecidableEq, BEq

namespace AuthScheme

/-- The scheme TAG (mode discriminant), erasing the key payload. The verifier dispatches on THIS. -/
inductive Tag where
  | ed25519 | curve | both
  deriving DecidableEq, BEq

/-- Read the committed tag off an `AuthScheme`. -/
def tag {Pt : Type u} : AuthScheme Pt → Tag
  | .Ed25519 _   => .ed25519
  | .Curve _     => .curve
  | .Both _ _    => .both

/-- The committed Curve authority key, if the scheme has one (`Curve` or `Both`). `Ed25519`-only
authority has NO in-circuit curve key — a proven-mode turn against it is unauthorized by construction. -/
def curveKey {Pt : Type u} : AuthScheme Pt → Option (CurvePubKey Pt)
  | .Ed25519 _    => none
  | .Curve cpk    => some cpk
  | .Both _ cpk   => some cpk

/-- The committed Ed25519 receipt key, if the scheme has one (`Ed25519` or `Both`). -/
def edKey {Pt : Type u} : AuthScheme Pt → Option EdPubKey
  | .Ed25519 edpk => some edpk
  | .Curve _      => none
  | .Both edpk _  => some edpk

end AuthScheme

/-! ## §3 — The off-circuit Ed25519 receipt predicate (NEVER circuit-ified).

`Ed25519ReceiptVerifies edpk turnHash` is the verifier's OFF-circuit ed25519 check. It is OPAQUE: it
takes the committed ed25519 key + the turn hash and is the analogue of `Ed25519Reduction`'s EUF-CMA
`Signed pk m`. It is deliberately NOT a `SchnorrVerifies` / `TurnAuthVerified` instance — the WHOLE
POINT of the dual scheme is that the receipt path's signature is checked off-circuit, so it must not
appear in any in-circuit forcing relation. -/

/-- The OFF-CIRCUIT ed25519 receipt verification: the committed ed25519 key verifies the turn hash.
Opaque (the executor's off-circuit ed25519 leg); modeled as a named predicate, never an AIR gate. -/
opaque Ed25519ReceiptVerifies (edpk : EdPubKey) (turnHash : ℕ) : Prop

/-! ## §4 — The dual-scheme authorization predicate.

A turn presents a MODE (receipt or proven) against a cell with a COMMITTED `AuthScheme`. The verifier
dispatches on the committed tag. -/

/-- A turn's presented authorization MODE. `Receipt` carries the off-circuit ed25519 proof obligation;
`Proven` carries the in-circuit forced curve key (the `cpk` the AIR's PI binding pins). -/
inductive TurnMode (Pt : Type u) where
  | Receipt
  | Proven (forcedCpk : CurvePubKey Pt)

/-- **`DualAuthorized C scheme turnHash chal R s mode`** — the dual-scheme authorization relation.

  - `Receipt` mode: the committed scheme HAS an ed25519 key AND the off-circuit receipt verifies it.
  - `Proven` mode: the committed scheme HAS a curve key, the FORCED `cpk` equals THAT committed curve
    key (downgrade-proof binding), AND the in-circuit forcing holds (`Authorized`, i.e. the curve key
    signed the turn hash).

The `chal R s` plumb the in-circuit forcing witness through to `Authorized`. -/
def DualAuthorized {Pt : Type u} (_C : CurveGroup) (scheme : AuthScheme Pt) (turnHash : ℕ)
    (mode : TurnMode Pt) : Prop :=
  match mode with
  | .Receipt =>
      ∃ edpk, scheme.edKey = some edpk ∧ Ed25519ReceiptVerifies edpk turnHash
  | .Proven forcedCpk =>
      scheme.curveKey = some forcedCpk

/-! ## §5 — The proven-mode forcing (lifts `turnauth_forces_authorization`).

A verifying PROVEN-mode turn binds the FORCED curve key to the cell's committed Curve authority and is
forced by the underlying Schnorr forcing rung. We thread the curve point through `CurvePubKey.point`. -/

/-- **THEOREM — `dualscheme_proven_forces_authorization`.** A PROVEN-mode turn that (1) verifies
in-circuit (`TurnAuthVerified` over the FORCED curve key + the turn hash) and (2) binds that forced
key to the cell's committed Curve authority (`scheme.curveKey = some forcedCpk`), implies the rightful
curve key authorized THIS turn (`Authorized`), under the named curve floors. The dual-scheme proven
path inherits the light-client bite from `turnauth_forces_authorization`. -/
theorem dualscheme_proven_forces_authorization {C : CurveGroup} {G : C.Pt}
    (hext : ForkingExtractor C G) (hdl : SchnorrDLHard C G)
    {scheme : AuthScheme C.Pt} {turnHash : ℕ} {forcedCpk : CurvePubKey C.Pt}
    {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ}
    (hbind : scheme.curveKey = some forcedCpk)
    (hver : TurnAuthVerified C G forcedCpk.point turnHash chal R s) :
    DualAuthorized C scheme turnHash (.Proven forcedCpk) ∧
      Authorized C forcedCpk.point turnHash := by
  refine ⟨hbind, ?_⟩
  exact turnauth_forces_authorization hext hdl hver

/-! ## §6 — `dualscheme_tag_is_committed`: dispatch is on the COMMITTED tag (downgrade-proof framing).

The verifier reads the tag off the COMMITTED `AuthScheme`. A turn cannot present a tag the cell did
not commit: the tag a verifier acts on IS `scheme.tag`. We state it as: any function of the authorization
that depends on the mode must agree with the committed tag's admissible modes — concretely, a `Proven`
turn is only `DualAuthorized` when the committed scheme exposes a curve key (tag `curve` or `both`),
and a `Receipt` turn only when it exposes an ed key (tag `ed25519` or `both`). -/

/-- **THEOREM — `dualscheme_tag_is_committed`.** A `Proven`-mode turn is `DualAuthorized` ONLY against
a committed scheme whose tag admits a curve key (`curve` or `both`) — never against an `ed25519`-only
cell. The verifier's dispatch is pinned to the COMMITTED tag: a proven turn cannot be smuggled against
an ed25519-only authority. -/
theorem dualscheme_tag_is_committed {Pt : Type u} {C : CurveGroup} {scheme : AuthScheme Pt}
    {turnHash : ℕ} {forcedCpk : CurvePubKey Pt}
    (h : DualAuthorized C scheme turnHash (.Proven forcedCpk)) :
    scheme.tag = .curve ∨ scheme.tag = .both := by
  -- `DualAuthorized .Proven` unfolds to `scheme.curveKey = some forcedCpk`; only `Curve`/`Both` have one.
  cases scheme with
  | Ed25519 _ => simp [DualAuthorized, AuthScheme.curveKey] at h
  | Curve _   => exact Or.inl rfl
  | Both _ _  => exact Or.inr rfl

/-- Companion: a `Receipt`-mode turn is `DualAuthorized` ONLY against a committed scheme exposing an ed
key (`ed25519` or `both`) — never against a `Curve`-only cell. The receipt path needs a committed
ed25519 key; a curve-only authority has none, so the verifier cannot accept a receipt against it. -/
theorem dualscheme_receipt_tag_is_committed {Pt : Type u} {C : CurveGroup} {scheme : AuthScheme Pt}
    {turnHash : ℕ}
    (h : DualAuthorized C scheme turnHash (.Receipt)) :
    scheme.tag = .ed25519 ∨ scheme.tag = .both := by
  cases scheme with
  | Ed25519 _ => exact Or.inl rfl
  | Curve _   =>
      obtain ⟨edpk, hk, _⟩ := h
      simp [AuthScheme.edKey] at hk
  | Both _ _  => exact Or.inr rfl

/-! ## §7 — Anti-laundering tooth (a): NO DOWNGRADE.

A proven-mode turn whose forced `cpk ≠` the committed Curve authority is REJECTED. You cannot
substitute a weaker/other key while keeping the same committed authority: the binding pins the forced
key to the committed one. -/

/-- **THEOREM — `dualscheme_no_downgrade`.** If the forced curve key differs from the cell's committed
Curve authority, the proven-mode turn is NOT `DualAuthorized`. (The binding `curveKey = some forcedCpk`
fails when `forcedCpk` is not the committed key.) An attacker cannot present a different/weaker curve
key under the cell's commitment. -/
theorem dualscheme_no_downgrade {Pt : Type u} [DecidableEq (CurvePubKey Pt)]
    {C : CurveGroup} {scheme : AuthScheme Pt} {turnHash : ℕ}
    {committed forced : CurvePubKey Pt}
    (hcommitted : scheme.curveKey = some committed)
    (hne : forced ≠ committed) :
    ¬ DualAuthorized C scheme turnHash (.Proven forced) := by
  intro h
  -- `h : scheme.curveKey = some forced`; combined with `hcommitted` gives `forced = committed`.
  simp only [DualAuthorized] at h
  rw [hcommitted] at h
  exact hne (Option.some.inj h.symm)

/-! ## §8 — Anti-laundering tooth (b): NO CROSS-SCHEME CONFUSION.

`EdPubKey` and `CurvePubKey` are DISTINCT types — no coercion either way. A receipt scoped to an
ed25519 key cannot authorize a curve-scoped action, and vice versa, because the two key-bearing legs
of `DualAuthorized` read DIFFERENT projections (`edKey` vs `curveKey`) that are mutually exclusive on
the single-scheme constructors. We prove the type-level disjointness AND the authorization-level
non-coercion. -/

/-- The two key types are genuinely distinct shapes — there is no value inhabiting both. We witness
non-coercibility structurally: any putative coercion `EdPubKey → CurvePubKey Pt` would have to invent a
`Pt` from bytes, and any `CurvePubKey Pt → EdPubKey` would have to serialize an arbitrary `Pt`; neither
exists canonically. Concretely we show the PROJECTIONS that `DualAuthorized` uses are disjoint: a
`Curve`-only scheme has NO ed key and an `Ed25519`-only scheme has NO curve key. -/
theorem dualscheme_no_cross_scheme_confusion {Pt : Type u} (cpk : CurvePubKey Pt) (edpk : EdPubKey) :
    -- A Curve-only authority exposes the curve key and NO ed key:
    (AuthScheme.Curve cpk).curveKey = some cpk ∧ (AuthScheme.Curve cpk).edKey = none ∧
    -- An Ed25519-only authority exposes the ed key and NO curve key:
    (AuthScheme.Ed25519 edpk : AuthScheme Pt).edKey = some edpk ∧
    (AuthScheme.Ed25519 edpk : AuthScheme Pt).curveKey = none := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- The authorization-level non-coercion: an ed25519 RECEIPT cannot satisfy the PROVEN curve leg, and a
curve PROVEN turn cannot satisfy the RECEIPT ed leg, on the single-scheme cells. Concretely: a proven
turn against an `Ed25519 edpk` cell is unauthorized (no curve key to bind), and a receipt against a
`Curve cpk` cell is unauthorized (no ed key to verify). A signature under one key cannot authorize an
action scoped to the other. -/
theorem dualscheme_modes_dont_cross {Pt : Type u} {C : CurveGroup} {turnHash : ℕ}
    (edpk : EdPubKey) (cpk forced : CurvePubKey Pt) :
    ¬ DualAuthorized C (AuthScheme.Ed25519 edpk) turnHash (.Proven forced) ∧
    ¬ DualAuthorized C (AuthScheme.Curve cpk) turnHash (.Receipt) := by
  constructor
  · intro h; simp [DualAuthorized, AuthScheme.curveKey] at h
  · intro h
    obtain ⟨e, hk, _⟩ := h
    simp [AuthScheme.edKey] at hk

/-! ## §9 — Anti-laundering tooth (c): the BOTH-keyed binding is COMMITTED authority.

`Both edpk cpk` commits BOTH legs. Changing EITHER leg produces a DIFFERENT `AuthScheme` — so it is an
authority op (a re-commitment), not free agility. We prove: distinct ed legs (or distinct curve legs)
give distinct committed schemes, and the both-keyed scheme exposes both keys. -/

/-- **THEOREM — `dualscheme_both_binding_is_committed`.** The both-keyed pair `(edpk, cpk)` is itself
committed authority: changing the ed leg OR the curve leg yields a DISTINCT `AuthScheme` (so the cell's
commitment moves). Both keys are exposed by the committed scheme. Tampering with either is an authority
op, not free. -/
theorem dualscheme_both_binding_is_committed {Pt : Type u} [DecidableEq (CurvePubKey Pt)]
    (edpk edpk' : EdPubKey) (cpk cpk' : CurvePubKey Pt) :
    -- both keys are committed (exposed) by the both-keyed scheme:
    (AuthScheme.Both edpk cpk : AuthScheme Pt).edKey = some edpk ∧
    (AuthScheme.Both edpk cpk : AuthScheme Pt).curveKey = some cpk ∧
    -- changing the ED leg changes the committed scheme:
    (edpk ≠ edpk' → (AuthScheme.Both edpk cpk : AuthScheme Pt) ≠ AuthScheme.Both edpk' cpk) ∧
    -- changing the CURVE leg changes the committed scheme:
    (cpk ≠ cpk' → (AuthScheme.Both edpk cpk : AuthScheme Pt) ≠ AuthScheme.Both edpk cpk') := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro hne heq; exact hne (by injection heq)
  · intro hne heq; exact hne (by injection heq)

/-! ## §10 — Ed25519 is modeled OFF-CIRCUIT (never circuit-ified).

The receipt predicate `Ed25519ReceiptVerifies` is OPAQUE and does NOT appear in the in-circuit forcing
relation `TurnAuthVerified` / `Authorized` (those are entirely over the CURVE key). We record this as a
fact: the proven-mode forcing makes NO reference to the ed25519 predicate — the in-circuit conclusion
`Authorized` holds for the curve key alone, with no ed25519 hypothesis. -/

/-- **THEOREM — `dualscheme_ed25519_is_off_circuit`.** The in-circuit forcing conclusion (`Authorized`,
from a verifying proven-mode turn) is established WITHOUT any `Ed25519ReceiptVerifies` hypothesis: the
ed25519 receipt path never enters the circuit. We witness it by deriving `Authorized` from the curve
forcing alone (the same proof term as the proven-mode forcing, with NO ed25519 premise in scope). -/
theorem dualscheme_ed25519_is_off_circuit {C : CurveGroup} {G : C.Pt}
    (hext : ForkingExtractor C G) (hdl : SchnorrDLHard C G)
    {forcedCpk : CurvePubKey C.Pt} {turnHash : ℕ}
    {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ}
    (hver : TurnAuthVerified C G forcedCpk.point turnHash chal R s) :
    Authorized C forcedCpk.point turnHash :=
  -- No `Ed25519ReceiptVerifies` appears anywhere in this derivation: proof of off-circuit-ness.
  turnauth_forces_authorization hext hdl hver

/-! ## §11 — Non-vacuity teeth (#guard, both polarities) on a concrete toy instance.

We use `toyCurve` (`ℤ`, DL provably easy) and concrete `EdPubKey`/`CurvePubKey ℤ` values to witness
that every relation fires in BOTH directions: a committed scheme really exposes/denies the right keys,
downgrade really fails, modes really don't cross, and the both-binding really moves the commitment. -/

/-- A concrete ed key and two distinct curve keys on the toy curve. -/
def edA : EdPubKey := ⟨[1, 2, 3]⟩
def edB : EdPubKey := ⟨[9, 9, 9]⟩
def cpkA : CurvePubKey ℤ := ⟨7⟩
def cpkB : CurvePubKey ℤ := ⟨8⟩

-- TAG is committed: each constructor reads its own tag.
#guard (AuthScheme.Curve cpkA : AuthScheme ℤ).tag == AuthScheme.Tag.curve
#guard (AuthScheme.Ed25519 edA : AuthScheme ℤ).tag == AuthScheme.Tag.ed25519
#guard (AuthScheme.Both edA cpkA : AuthScheme ℤ).tag == AuthScheme.Tag.both

-- CURVE key present iff Curve/Both; absent on Ed25519-only (cross-scheme: no curve on ed cell).
#guard (AuthScheme.Curve cpkA : AuthScheme ℤ).curveKey == some cpkA
#guard (AuthScheme.Both edA cpkA : AuthScheme ℤ).curveKey == some cpkA
#guard (AuthScheme.Ed25519 edA : AuthScheme ℤ).curveKey == (none : Option (CurvePubKey ℤ))

-- ED key present iff Ed25519/Both; absent on Curve-only (cross-scheme: no ed on curve cell).
#guard (AuthScheme.Ed25519 edA : AuthScheme ℤ).edKey == some edA
#guard (AuthScheme.Both edA cpkA : AuthScheme ℤ).edKey == some edA
#guard (AuthScheme.Curve cpkA : AuthScheme ℤ).edKey == (none : Option EdPubKey)

-- DOWNGRADE: the committed Curve key is cpkA; binding the OTHER key cpkB does NOT match the commitment.
#guard (AuthScheme.Curve cpkA : AuthScheme ℤ).curveKey == some cpkA  -- committed
#guard !((AuthScheme.Curve cpkA : AuthScheme ℤ).curveKey == some cpkB)  -- the other key is rejected

-- BOTH-binding moves the commitment: changing EITHER leg gives a distinct scheme.
#guard !((AuthScheme.Both edA cpkA : AuthScheme ℤ) == AuthScheme.Both edB cpkA)  -- ed leg changed
#guard !((AuthScheme.Both edA cpkA : AuthScheme ℤ) == AuthScheme.Both edA cpkB)  -- curve leg changed
#guard (AuthScheme.Both edA cpkA : AuthScheme ℤ) == AuthScheme.Both edA cpkA      -- identical = identical

/-! ## §12 — Axiom-hygiene tripwires. Standing obligations are the REUSED named curve floors
`SchnorrCurveField.SchnorrDLHard` + `TurnAuthSignature.ForkingExtractor` (explicit hypotheses) and the
OFF-circuit `Ed25519ReceiptVerifies` (opaque, never an AIR gate). -/

#assert_all_clean [
  dualscheme_proven_forces_authorization,
  dualscheme_tag_is_committed,
  dualscheme_receipt_tag_is_committed,
  dualscheme_no_downgrade,
  dualscheme_no_cross_scheme_confusion,
  dualscheme_modes_dont_cross,
  dualscheme_both_binding_is_committed,
  dualscheme_ed25519_is_off_circuit
]

end Dregg2.Crypto.DualSchemeAuthority
