/-
# Dregg2.Distributed.ThresholdAdmission — the HOST-POLICY threshold-signature ADMISSION decision
# (`turn/src/executor/membership_verifier.rs::ThresholdSigVerifier::verify`).

`Crypto/BlsThreshold.lean` models the federation's quorum *certificate* and its single-cert
soundness reduction (`accepting_cert_has_quorum`): an accepting `ThresholdCert` ⇒ a genuine weighted
quorum signed the message, relative to the three named pairing-crypto primitives. That layer answers
"does this QC certify *its own* claimed threshold?".

It does NOT answer the question the EXECUTOR actually asks at an `Authorization::Custom { vk_hash }`
discharge: **should this aggregate be ADMITTED as authority for this turn?** The real verifier
(`turn/src/executor/membership_verifier.rs:1236-1312`, the `ThresholdSigVerifier` welded from the
`hints` crate) makes a FIVE-conjunct decision over a HOST-TRUSTED committee policy, and TWO of those
conjuncts have no twin in `BlsThreshold.lean`:

  1. **host-pinned committee** — `policies.committee(commitment)` (`:1266`). The committee VK and the
     `k`-of-`n` floor come from the HOST (the `governance_committee_root` slot), *never* the proof.
     A `commitment` with no registered committee **fails closed** (`ok_or_else(... Rejected)`): an
     unknown / self-declared committee is never trusted.
  2. **threshold-downgrade defense (the host FLOOR)** — `if sig.threshold < floor { reject }`
     (`:1289-1299`), where `floor = committee.threshold_k` comes from the HOST POLICY, not the QC.
     `verify_aggregate` only checks `agg_weight ≥ sig.threshold` — the QC's OWN embedded threshold,
     which a malicious aggregator can set to `1` and present a 1-of-n QC as if it satisfied a k-of-n
     policy. Pinning `sig.threshold ≥ host_k` defeats that. (Exactly as `dregg-federation`'s
     `FederationCommittee::verify` adds `if qc.threshold < self.threshold { reject }` ON TOP of
     `verify_aggregate`.)
  3. **the cryptographic gate** — `hints::verify_aggregate(committee.verifier, sig, message)`
     (`:1305`): the SNARK proof check + final BLS pairing, against the HOST committee VK and the
     executor-supplied signing message. (This IS `ThresholdCert.accepts` of `BlsThreshold.lean`.)
  4. **message-binding** — a QC over a different message fails the BLS pairing (`wrong_message_rejected`).
  5. **wrong-committee** — a QC whose SNARK proof is for a different committee fails against the host
     VK (`wrong_committee_rejected`).

(2) is the security keystone the existing model is BLIND to: `BlsThreshold.accepts` reads the QC's own
`threshold` field, which is exactly the attacker-controlled value the host floor pins from below. This
module is its Lean twin.

## What this models (faithful to `ThresholdSigVerifier::verify`)

  * `HostCommittee` — a host-trusted committee policy: the `BlsThreshold.Committee` (whose VK binds the
     weighted member keys — *which* committee) plus the host floor `floorK` (the minimum `k` of `k`-of-`n`
     the QC must certify). Mirrors `ThresholdSigCommittee` (`:1118-1128`): VK + `threshold_k`, both host.
  * `Policy` — the `commitment → HostCommittee` table (`StaticThresholdSigPolicy`, `:1169`): a partial
     map; a `commitment` absent ⇒ `none` ⇒ fail-closed.
  * `admits` — the FIVE-conjunct admission decision (`verify`, `:1236-1312`): the host resolves the
     committee for `commitment` (fail-closed if absent), pins `sig.threshold ≥ floorK`, AND the QC
     cryptographically accepts under that host committee over `message`. EXACTLY the `if … return Err`
     cascade, conjoined.

## Properties PROVED (both polarities — the assurance the executor leans on)

  * **`admits_genuine_quorum`** — THE SOUNDNESS theorem: an ADMITTED aggregate yields a genuine weighted
     quorum of the HOST committee that signed `message`, reaching the HOST FLOOR (not merely the QC's
     self-declared threshold). This is `BlsThreshold.accepting_cert_has_quorum` LIFTED through the host
     floor: `selectedWeight S ≥ floorK`, i.e. a real `k`-of-`n` quorum, `k = host floor`. REUSED, not
     re-derived.
  * **`under_floor_refused`** (the downgrade-resistance KEYSTONE) — any aggregate whose embedded
     `threshold < floorK` is REFUSED, *regardless of whether it cryptographically verifies*. This is
     the property `BlsThreshold` cannot state (it has no host floor): a perfectly valid 1-of-n QC is
     still refused under a 3-of-n host policy. The malicious-aggregator forge is closed.
  * **`unregistered_refused`** — a `commitment` with no host committee is REFUSED (fail-closed). An
     unknown / self-declared committee is never admitted.
  * **`wrong_committee_refused`** — an aggregate that does NOT cryptographically accept under the HOST
     committee (wrong committee VK, wrong message, forged proof, under-weight) is REFUSED.
  * **`admits_iff`** — the admission decision is EXACTLY the five-conjunct conjunction (extensional
     characterization; no hidden slack, the gate is precisely the Rust cascade).

The cryptographic content (the QC genuinely certifies a weighted quorum signed `m` under THIS
committee) is `BlsThreshold.accepts` + its `SnarkContract`/`BlsContract`, themselves the unpacked
content of the three named pairing primitives (`KzgBinding`/`BlsAggUnforgeable`/`SnarkPolyIOP`). What is
PROVED here, purely, is the HOST-POLICY decision logic ON TOP: floor-pinning, fail-closed
committee-resolution, and the lift of single-cert soundness to host-floor quorum authority.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Differential anchor: the `#[cfg(feature="threshold-sig")] mod threshold_sig` tests
(`membership_verifier.rs:2134-2348`) — `valid_quorum_verifies` / `under_host_floor_rejected` /
`wrong_committee_rejected` / `unregistered_commitment_fails_closed` — re-run here as both-polarity
`#guard`s over a concrete reference policy. Reuses `Crypto.BlsThreshold` (no duplication of the cert
arithmetic); companion to `Distributed.BlsQuorumCert` (the corruption-bound distributed layer).
-/
import Dregg2.Crypto.BlsThreshold
import Dregg2.Tactics

namespace Dregg2.Distributed.ThresholdAdmission

open Dregg2.Crypto.BlsThreshold (Committee ThresholdCert)
open Dregg2.Crypto.BlsThreshold.Committee (totalWeight selectedWeight)
open Dregg2.Crypto.BlsThreshold.ThresholdCert (accepts SnarkContract BlsContract)

universe u

variable {PK : Type u}

/-! ## §1 — the host-trusted committee policy (`ThresholdSigCommittee`, `membership_verifier.rs:1118`).

The host pins BOTH the committee (the VK binding the weighted member keys — `BlsThreshold.Committee`)
AND the floor `floorK` (the minimum `k`-of-`n` a QC must certify). Both come from the host, never the
proof — so a prover can neither swap in their own committee nor lower the threshold. -/

/-- **`HostCommittee`** — a host-trusted threshold-signing committee (`ThresholdSigCommittee`,
`membership_verifier.rs:1118-1128`): the underlying `BlsThreshold.Committee` (the `hints::Verifier` VK,
which binds *which* weighted committee) plus the host-mandated floor `floorK` (the minimum weighted
`k`-of-`n` the aggregate must certify, `threshold_k`). -/
structure HostCommittee (PK : Type u) where
  /-- The committee the host trusts (its VK binds the weighted member public keys). -/
  committee : Committee PK
  /-- The host's minimum `k`-of-`n` floor (`threshold_k`, `:1127`). A QC's own embedded threshold is
  pinned `≥ floorK`, defeating the aggregator-chosen-low-threshold downgrade. -/
  floorK : ℕ

/-- **`Policy`** — the host's `commitment → HostCommittee` table (`StaticThresholdSigPolicy`,
`membership_verifier.rs:1169`). A PARTIAL map: a `commitment` absent from the table resolves to `none`,
which the admission decision treats as fail-closed (an unknown / self-declared committee is never
trusted). Modelled as `Commit → Option (HostCommittee PK)` (the `BTreeMap::get`, `:1192`). -/
structure Policy (Commit : Type) (PK : Type u) where
  /-- Resolve the host-trusted committee for a predicate `commitment` (the `governance_committee_root`),
  or `none` if none is registered. -/
  committee : Commit → Option (HostCommittee PK)

namespace Policy
variable {Commit : Type}

/-- The empty policy (`StaticThresholdSigPolicy::new`, `:1176`) rejects everything: no commitment is
registered, so every admission fails closed. -/
def empty : Policy Commit PK := ⟨fun _ => none⟩

/-- `authorize commit hc` registers `hc` for `commit` (`StaticThresholdSigPolicy::authorize`,
`:1183`); other commitments resolve as before. Decidable-equality on the small commitment type. -/
def authorize [DecidableEq Commit] (P : Policy Commit PK) (commit : Commit)
    (hc : HostCommittee PK) : Policy Commit PK :=
  ⟨fun c => if c = commit then some hc else P.committee c⟩

@[simp] theorem committee_empty (c : Commit) : (empty : Policy Commit PK).committee c = none := rfl

@[simp] theorem committee_authorize_self [DecidableEq Commit] (P : Policy Commit PK)
    (commit : Commit) (hc : HostCommittee PK) :
    (P.authorize commit hc).committee commit = some hc := by
  simp [authorize]

theorem committee_authorize_other [DecidableEq Commit] (P : Policy Commit PK)
    {commit c : Commit} (hc : HostCommittee PK) (hne : c ≠ commit) :
    (P.authorize commit hc).committee c = P.committee c := by
  simp [authorize, hne]

end Policy

/-! ## §2 — THE ADMISSION DECISION (`ThresholdSigVerifier::verify`, `membership_verifier.rs:1236-1312`).

`verify(commitment, message, proof)` is the FIVE-conjunct cascade. We model the aggregate QC as a
`BlsThreshold.ThresholdCert` (the deserialized `hints::Signature`, `:1278`) plus the per-member
`SnarkContract`/`BlsContract` (the unpacked content of the SNARK + BLS gates). The decision is:

  resolve the host committee for `commitment` (FAIL-CLOSED if `none`)            — `:1266`
  ∧ `cert.threshold ≥ host.floorK`        (downgrade defense, the host FLOOR)    — `:1289`
  ∧ `cert.accepts`                        (`verify_aggregate`: weight ∧ SNARK ∧ BLS) — `:1305`

over the HOST committee. We carry the SNARK/BLS *contracts* (what an accepting `verify_aggregate`
yields under the named primitives) alongside, so the soundness lift below can fire. -/

/-- The cryptographic acceptance of an aggregate `cert` *under a specific host committee* over `msg` —
the `hints::verify_aggregate(committee.verifier, sig, msg)` gate (`:1305`), with the SNARK + BLS
contracts (the unpacked content of `SnarkPolyIOP` / `BlsAggUnforgeable` against the HOST VK) carried so
admission yields a genuine quorum. This is precisely `BlsThreshold.accepts` + its contracts, evaluated
against the HOST committee — wrong-committee / wrong-message / forged / under-weight all FALSIFY it. -/
structure CryptoAccepts {PK : Type u} (hc : HostCommittee PK) {msg : ℕ}
    (cert : ThresholdCert hc.committee msg) : Prop where
  /-- `verify_aggregate`'s three gates accept (weight ∧ SNARK ∧ BLS) under the host committee VK. -/
  accepts : cert.accepts
  /-- The SNARK contract (`SnarkPolyIOP` unpacked): the selected set is a sub-committee of the HOST
  committee and the claimed weight is the genuine selected weight. -/
  snark : cert.SnarkContract
  /-- The BLS contract (`BlsAggUnforgeable` unpacked): every selected member signed `msg`. -/
  bls : cert.BlsContract

/-- **`admits`** — the host-policy admission decision (`ThresholdSigVerifier::verify`,
`membership_verifier.rs:1236-1312`). Given the policy `P`, the predicate `commitment`, the message the
turn binds, the host committee `hc` resolved for `commitment`, and the aggregate `cert` over `hc`'s
committee: ADMIT iff `P` registers `hc` at `commitment` AND `cert.threshold ≥ hc.floorK` (the host
FLOOR — downgrade defense) AND `cert` cryptographically accepts under `hc` over `msg`. The whole `if …
return Err` cascade, conjoined; any conjunct false ⇒ refuse (fail-closed). -/
def admits {Commit : Type} {PK : Type u} (P : Policy Commit PK) (commit : Commit) (msg : ℕ)
    (hc : HostCommittee PK) (cert : ThresholdCert hc.committee msg) : Prop :=
  P.committee commit = some hc ∧ cert.threshold ≥ hc.floorK ∧ CryptoAccepts hc cert

/-! ## §3 — THE ADMISSION THEOREMS (both polarities). -/

variable {Commit : Type}

/-- **`admits_iff`** — the admission decision is EXACTLY the three-conjunct conjunction (the resolved
committee, the host-floor pin, and cryptographic acceptance). Extensional: the gate has no hidden
slack — it is precisely the Rust `if … return Err` cascade, nothing more, nothing less. -/
theorem admits_iff {P : Policy Commit PK} {commit : Commit} {msg : ℕ}
    {hc : HostCommittee PK} {cert : ThresholdCert hc.committee msg} :
    admits P commit msg hc cert ↔
      (P.committee commit = some hc ∧ cert.threshold ≥ hc.floorK ∧ CryptoAccepts hc cert) :=
  Iff.rfl

/-- **`admits_genuine_quorum`** — THE SOUNDNESS theorem. An ADMITTED aggregate yields a genuine
weighted quorum of the HOST committee that signed `msg`, reaching the HOST FLOOR `hc.floorK` (not
merely the QC's self-declared `threshold`). This is `BlsThreshold.accepting_cert_has_quorum` LIFTED
through the host floor: the selected sub-committee `S ⊆ host.members` has `selectedWeight S ≥ floorK`
(a real `k`-of-`n` quorum, `k` = the HOST's `k`), `≤ totalWeight`, and every member of `S` signed
`msg`. So admission is authority for a host-mandated quorum, not whatever the aggregator declared. -/
theorem admits_genuine_quorum {P : Policy Commit PK} {commit : Commit} {msg : ℕ}
    {hc : HostCommittee PK} {cert : ThresholdCert hc.committee msg}
    (h : admits P commit msg hc cert) :
    ∃ S : Finset ℕ,
      S ⊆ hc.committee.members ∧
      hc.committee.selectedWeight S ≥ hc.floorK ∧
      hc.committee.selectedWeight S ≤ hc.committee.totalWeight ∧
      (∀ i ∈ S, hc.committee.SignedBy i msg) := by
  obtain ⟨_hreg, hfloor, hca⟩ := h
  -- BlsThreshold gives a quorum reaching the QC's OWN threshold …
  obtain ⟨S, hSsub, hSge, hStot, hSsigned⟩ :=
    Dregg2.Crypto.BlsThreshold.accepting_cert_has_quorum cert hca.accepts hca.snark hca.bls
  -- … and the host floor pins cert.threshold ≥ floorK, so the genuine quorum reaches the HOST floor.
  exact ⟨S, hSsub, le_trans hfloor hSge, hStot, hSsigned⟩

/-- **`under_floor_refused`** (the DOWNGRADE-RESISTANCE keystone, `membership_verifier.rs:1289-1299`).
Any aggregate whose embedded `threshold < hc.floorK` is REFUSED — *regardless of whether it
cryptographically verifies*. This is the property `BlsThreshold` cannot state: a perfectly valid,
SNARK-and-BLS-accepting 1-of-n QC is still refused under a 3-of-n host policy. The malicious-aggregator
forge (set `sig.threshold = 1`, present a 1-of-n as a k-of-n) is closed BY THE HOST FLOOR, not the QC.
Note the absence of any `CryptoAccepts` hypothesis — refusal holds even for a genuine aggregate. -/
theorem under_floor_refused {P : Policy Commit PK} {commit : Commit} {msg : ℕ}
    {hc : HostCommittee PK} {cert : ThresholdCert hc.committee msg}
    (hlow : cert.threshold < hc.floorK) :
    ¬ admits P commit msg hc cert := by
  rintro ⟨_hreg, hfloor, _hca⟩
  exact absurd hfloor (by omega)

/-- **`unregistered_refused`** (fail-closed, `membership_verifier.rs:1266`). If the policy has NO
committee registered for `commit` (`P.committee commit = none`), every aggregate is REFUSED — an
unknown / self-declared committee is never admitted. The `commit` arrives from the cell's
`governance_committee_root`; if the host did not pin a committee there, authority fails closed. -/
theorem unregistered_refused {P : Policy Commit PK} {commit : Commit} {msg : ℕ}
    {hc : HostCommittee PK} {cert : ThresholdCert hc.committee msg}
    (hnone : P.committee commit = none) :
    ¬ admits P commit msg hc cert := by
  rintro ⟨hreg, _, _⟩
  rw [hnone] at hreg
  exact absurd hreg (by simp)

/-- **`wrong_committee_refused`** (`membership_verifier.rs:1305`). An aggregate that does NOT
cryptographically accept under the HOST committee `hc` (wrong committee VK, wrong message, forged
proof, under-weight aggregate — anything that falsifies `verify_aggregate(host.verifier, sig, msg)`) is
REFUSED. The SNARK proof is checked against the HOST VK, so a QC built for a different committee fails
here. -/
theorem wrong_committee_refused {P : Policy Commit PK} {commit : Commit} {msg : ℕ}
    {hc : HostCommittee PK} {cert : ThresholdCert hc.committee msg}
    (hbad : ¬ CryptoAccepts hc cert) :
    ¬ admits P commit msg hc cert := by
  rintro ⟨_, _, hca⟩
  exact hbad hca

/-- **`admits_valid_quorum`** — the POSITIVE direction (`valid_quorum_verifies`,
`membership_verifier.rs:2220`). A genuine aggregate that (1) is registered, (2) meets the host floor,
and (3) cryptographically accepts under the host committee IS admitted. The constructor of `admits`:
all three gates open ⇒ admit. Pairs with the refusals to witness the decision is non-trivial. -/
theorem admits_valid_quorum {P : Policy Commit PK} {commit : Commit} {msg : ℕ}
    {hc : HostCommittee PK} {cert : ThresholdCert hc.committee msg}
    (hreg : P.committee commit = some hc)
    (hfloor : cert.threshold ≥ hc.floorK)
    (hca : CryptoAccepts hc cert) :
    admits P commit msg hc cert :=
  ⟨hreg, hfloor, hca⟩

/-! ## §4 — non-vacuity + the threshold-sig differential (vs `membership_verifier.rs` tests).

A concrete reference: the host registers `fed4` (the 4-member equal-weight committee from
`BlsThreshold.Reference`) at a commitment `gov`, with a floor of 3 — a 3-of-4 host policy. We witness:
ADMIT fires on the genuine 3-of-4 QC; REFUSE fires on a 2-of-4 QC (under floor), on a different
commitment (unregistered), and on a non-accepting aggregate (wrong committee). Mirrors the Rust
`threshold_sig` module tests gate-for-gate. -/

namespace Reference

open Dregg2.Crypto.BlsThreshold.Reference
  (fed4 passingCert passingCert_accepts passingCert_snark passingCert_bls
   subQuorumCert subQuorumCert_snark)

/-- The commitment type: the small finite set of governance roots in play (the
`governance_committee_root`). Two concrete values suffice for the differential. -/
inductive Gov where
  | governed    -- the registered governance commitment
  | unregistered -- a commitment with NO host committee (fail-closed corner)
deriving DecidableEq

/-- The host committee pinned at `governed`: `fed4` with a 3-of-4 floor (`floorK = 3`). Mirrors the
Rust `policy(&committee, 3)` (`membership_verifier.rs:2211`) — the VK is `fed4`, the floor is the
host's `threshold_k = 3`. -/
def hostFed4 : HostCommittee ℕ := ⟨fed4, 3⟩

/-- The host policy: `governed ↦ hostFed4`, everything else unregistered (the `StaticThresholdSigPolicy`
with one `authorize`). -/
def policy : Policy Gov ℕ := (Policy.empty).authorize Gov.governed hostFed4

/-- The genuine 3-of-4 aggregate (`passingCert`) cryptographically accepts under the host `fed4`
committee over `msg = 99`: all three gates open, the SNARK + BLS contracts hold (PROVED, against the
genuine reference `SignedBy`, not `True`-filled). -/
def passingCert_crypto : CryptoAccepts hostFed4 (msg := 99) passingCert where
  accepts := passingCert_accepts
  snark := passingCert_snark
  bls := passingCert_bls

/-- **ADMIT fires** (`valid_quorum_verifies`): the genuine 3-of-4 QC, threshold 3 = the host floor,
registered at `governed`, IS admitted. -/
theorem ref_admits :
    admits policy Gov.governed 99 hostFed4 passingCert :=
  admits_valid_quorum (by simp [policy, hostFed4]) (by decide) passingCert_crypto

/-- The admitted aggregate yields a genuine 3-weight quorum of `fed4` (the host floor `3`) — the
soundness lift FIRES on the reference. -/
theorem ref_admits_genuine_quorum :
    ∃ S : Finset ℕ, S ⊆ fed4.members ∧ fed4.selectedWeight S ≥ 3 ∧
      fed4.selectedWeight S ≤ fed4.totalWeight ∧ (∀ i ∈ S, fed4.SignedBy i 99) :=
  admits_genuine_quorum ref_admits

/-- **REFUSE fires — under floor** (`under_host_floor_rejected`, `membership_verifier.rs:2252`). The
genuine 2-of-4 aggregate (`subQuorumCert`, embedded `threshold = 3` but selected weight only 2 …) — to
witness the DOWNGRADE corner cleanly we take a cert that genuinely certifies threshold 2 and is
refused under the floor-3 policy. We re-use a threshold-2 aggregate: its `threshold = 2 < 3 = floorK`,
so it is refused IRRESPECTIVE of crypto — the downgrade defense. -/
def lowThresholdCert : ThresholdCert fed4 (msg := 99) where
  threshold := 2          -- the aggregator's self-declared (low) threshold
  aggWeight := 2
  selected := {0, 1}
  SnarkOk := True
  BlsAggregateOk := True

/-- The 2-of-4 (`threshold = 2`) aggregate is REFUSED under the floor-3 host policy — the
downgrade-resistance keystone FIRES (no crypto hypothesis needed: even a perfectly valid 2-QC is
refused when the host demands 3). -/
theorem ref_under_floor_refused :
    ¬ admits policy Gov.governed 99 hostFed4 lowThresholdCert :=
  under_floor_refused (hc := hostFed4) (by decide)

/-- **REFUSE fires — unregistered** (`unregistered_commitment_fails_closed`,
`membership_verifier.rs:2284`). The genuine 3-of-4 QC, presented at the `unregistered` commitment, is
refused (fail-closed: no host committee there). -/
theorem ref_unregistered_refused :
    ¬ admits policy Gov.unregistered 99 hostFed4 passingCert :=
  unregistered_refused (by simp [policy, Policy.authorize])

/-- **REFUSE fires — non-accepting aggregate** (the wrong-committee / wrong-message corner,
`membership_verifier.rs:2269`). An aggregate whose BLS contract FAILS (it "selects" the non-signer
member 3, so `SignedBy 3 99` is false — the BLS pairing would reject) does not cryptographically
accept, hence is refused. Witnesses the crypto gate is load-bearing. -/
def forgedCert : ThresholdCert fed4 (msg := 99) where
  threshold := 3
  aggWeight := 4
  selected := {0, 1, 2, 3}    -- includes the non-signer 3 — BLS contract is FALSE
  SnarkOk := True
  BlsAggregateOk := True

/-- The forged aggregate does not cryptographically accept (its BLS contract fails on member 3). -/
theorem forged_not_crypto : ¬ CryptoAccepts hostFed4 (msg := 99) forgedCert := by
  rintro ⟨_, _, hbls⟩
  -- hbls : ∀ i ∈ {0,1,2,3}, SignedBy i 99; but SignedBy 3 99 is 3 ≤ 2, false.
  have h3 : fed4.SignedBy 3 99 := hbls 3 (by decide)
  exact absurd (show (3 : ℕ) ≤ 2 from h3) (by decide)

theorem ref_wrong_committee_refused :
    ¬ admits policy Gov.governed 99 hostFed4 forgedCert :=
  wrong_committee_refused forged_not_crypto

/-! ### §4b — both-polarity `#guard`s pinning the decision to the Rust `threshold_sig` tests.

The admission predicate is a `Prop`, but its three conjuncts over the reference are DECIDABLE facts
(the floor comparison, the registration lookup). We pin those facts as kernel `#guard`s — a false
`#guard` is a BUILD ERROR — mirroring `valid_quorum_verifies` / `under_host_floor_rejected` /
`unregistered_commitment_fails_closed` gate-for-gate. -/

-- POSITIVE: the genuine 3-of-4 cert meets the host floor 3 (the ADMIT precondition).
#guard decide (passingCert.threshold ≥ hostFed4.floorK)
-- NEGATIVE: the 2-threshold cert is BELOW the host floor 3 — the downgrade corner is REFUSED …
#guard !decide (lowThresholdCert.threshold ≥ hostFed4.floorK)
-- … and the floor genuinely exceeds the low cert's self-declared threshold (host > aggregator).
#guard decide (lowThresholdCert.threshold < hostFed4.floorK)
-- The host floor is the POLICY's 3, NOT the QC's 2 (the pin is host-side).
#guard hostFed4.floorK == 3
#guard lowThresholdCert.threshold == 2
-- Registration: `governed` resolves to the host committee; `unregistered` fails closed (none).
#guard (policy.committee Gov.governed).isSome
#guard (policy.committee Gov.unregistered).isNone
-- The resolved floor at `governed` is exactly 3 (the host's k-of-n).
#guard (policy.committee Gov.governed).map (·.floorK) == some 3

end Reference

/-! ## §5 — axiom-hygiene tripwires: the host-policy decision logic pins exactly the whitelist; the
cryptographic content is `Crypto.BlsThreshold`'s NAMED carriers (consumed via `CryptoAccepts`'s
`SnarkContract`/`BlsContract`), never as Lean axioms here. -/

#assert_axioms admits_iff
#assert_axioms admits_genuine_quorum
#assert_axioms under_floor_refused
#assert_axioms unregistered_refused
#assert_axioms wrong_committee_refused
#assert_axioms admits_valid_quorum
#assert_axioms Reference.ref_admits
#assert_axioms Reference.ref_admits_genuine_quorum
#assert_axioms Reference.ref_under_floor_refused
#assert_axioms Reference.ref_unregistered_refused
#assert_axioms Reference.ref_wrong_committee_refused
#assert_axioms Reference.forged_not_crypto

end Dregg2.Distributed.ThresholdAdmission
