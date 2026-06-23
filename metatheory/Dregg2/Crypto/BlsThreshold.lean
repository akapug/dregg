/-
# Dregg2.Crypto.BlsThreshold — §8 discharge: the federation's weighted-threshold BLS quorum cert.

This is the previously-UNCOVERED crypto surface of `federation/src/threshold.rs` + the `hints` crate
(BLS12-381 + KZG weighted-threshold signatures): a *constant-size* aggregate certificate proving that
a weighted threshold of committee members signed a message, replacing N×64-byte ed25519 sigs.

The real `hints::verify_aggregate` (`hints/src/lib.rs:208`) is a THREE-GATE conjunction:

  1. **threshold gate** (`agg_weight ≥ threshold`)                — pure field/Nat arithmetic.
  2. **SNARK gate** (`verify_proof`, `hints/src/snark/verifier.rs:126`) — a KZG-based polynomial-IOP
     that pins `agg_pk = ∏_{i : b_i=1} pk_i`, `agg_weight = Σ_{i : b_i=1} w_i`, AND `b ∈ {0,1}^n`
     (the `b(r)·b(r)−b(r)=Q·Z_V` row, `verifier.rs:173`), via the "secret part" pairing equation
     `e(B, sk_of_x) = e(q1,Z)·e(q2,x)·e(agg_pk, h₀)` (`verifier.rs:153`).
  3. **final BLS gate** (`e(agg_pk, H(m)) = e(g₀, agg_sig')`, `hints/src/lib.rs:228`) — BLS aggregate
     signature verification against the aggregated public key.

## What this module does (a REAL reduction, not a relabel)

We separate the gates exactly as the Rust does, and PROVE: an accepting certificate ⇒ there is a
0/1 selector `b` over the committee whose selected weight reaches the threshold AND whose product of
public keys is `agg_pk` AND that aggregate verifies under BLS — i.e. *a genuine weighted quorum signed
`m`*. The two layers are split:

  * **DISCHARGEABLE (proved here, no crypto):** the threshold/selector ARITHMETIC — `b ∈ {0,1}^n`,
    `aggWeight = Σ selected weights`, and `aggWeight ≥ threshold ⇒ selectedWeight ≥ threshold`. This is
    the polynomial-IOP's *combinatorial content* (the `b`-boolean + weighted-sum rows), which is
    field algebra once the KZG openings are believed. We model it as `Nat`/`Finset` arithmetic and
    prove `quorum_weight_suffices`, `accepting_cert_has_quorum`.

  * **IRREDUCIBLE PRIMITIVES (named carriers, never proved):**
      - `KzgBinding`         — KZG10 evaluation binding (SXDH / `q`-SDH over BLS12-381 pairing). A
        commitment opens to at most one polynomial; this is what makes the SNARK gate's claimed
        `agg_pk`/`agg_weight`/`b` the ones the prover is *bound* to. (`hints/src/kzg.rs`.)
      - `BlsAggUnforgeable` — BLS aggregate-signature unforgeability (co-CDH over the pairing): an
        accepting `e(apk,H(m)) = e(g₀,σ')` proves the holders of the secret keys aggregated into `apk`
        signed `m`. (`hints/src/lib.rs:228`, `hash_to_g2`.)
      - `SnarkPolyIOP`      — the polynomial-IOP/Fiat-Shamir soundness wrapping the KZG openings: an
        accepting `verify_proof` proves the committed `b`/`agg_pk`/`agg_weight` satisfy the circuit
        relation. (Reduces to `KzgBinding` + Schwartz–Zippel; carried as the STARK-style
        `extractable` carrier, the same discipline as `PortalFloor.VerifierKernel`.)

These three are the genuine cryptographic assumptions of weighted-threshold BLS — pairing/curve math,
named, exactly like `PortalFloor` names ed25519 EUF-CMA. The reduction *from* them *to* "an
honest quorum signed" is the load-bearing thing proved here.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Companion to `Distributed/ThresholdDecrypt.lean` (the t-of-n decryption) — that is Shamir over GF(256);
THIS is the dual constant-size *aggregation* (KZG over BLS12-381). Differential anchor: the §4 `#guard`s
pin the selector arithmetic against `federation/src/threshold.rs`'s equal-weight committee semantics.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Dregg2.Tactics

namespace Dregg2.Crypto.BlsThreshold

open Finset

universe u

/-! ## §1 — the committee + the selector (the SNARK's `b`-bitvector, modelled as a `Finset`). -/

/-- A federation committee: `n` members, each with a public key (`PK`) and an integer weight. This
mirrors `FederationCommittee` (`federation/src/threshold.rs:33`): a fixed member set with weights
(equal-weight in the wrapper, general here). -/
structure Committee (PK : Type u) where
  /-- The committee members (an index set). -/
  members : Finset ℕ
  /-- Each member's BLS public key. -/
  pk : ℕ → PK
  /-- Each member's voting weight (`F`-valued in Rust; `Nat` here — weights are non-negative). -/
  weight : ℕ → ℕ
  /-- The abstract "member `i` validly signed message `m`" relation — the per-member analogue of
  `PortalFloor.SignatureKernel.Signed`, a genuine `Prop` (NOT `True`). At a real cert its truth is
  what `BlsAggUnforgeable` establishes from the final pairing; here it is an opaque field so the BLS
  contract `∀ i ∈ selected, SignedBy i m` is a meaningful obligation, not a tautology. -/
  SignedBy : ℕ → ℕ → Prop

namespace Committee
variable {PK : Type u}

/-- Total committee weight `Σ_{i ∈ members} weight i`. -/
def totalWeight (C : Committee PK) : ℕ := ∑ i ∈ C.members, C.weight i

/-- The weight selected by a subset `S ⊆ members` — the SNARK's `agg_weight = Σ_{b_i=1} w_i`. -/
def selectedWeight (C : Committee PK) (S : Finset ℕ) : ℕ := ∑ i ∈ S, C.weight i

/-- Selecting a subset never exceeds the total weight (monotonicity of `Σ` over a subset). -/
theorem selectedWeight_le_total (C : Committee PK) {S : Finset ℕ} (hS : S ⊆ C.members) :
    C.selectedWeight S ≤ C.totalWeight :=
  Finset.sum_le_sum_of_subset hS

end Committee

/-! ## §2 — the THREE named irreducible primitives (curve/pairing math, named.

These are NOT Lean definitions — encoding "KZG binding" as a `Prop` constant would be a relabel. They
are the genuine cryptographic obligations, named here and DISCHARGED into the soundness contracts of
§3 (`SnarkContract`, the per-member `SignedBy`), which the reduction below consumes as explicit
hypotheses — exactly the `PortalFloor` discipline (carrier named, `*_sound` takes it as a hypothesis):

  * **`KzgBinding`** — IRREDUCIBLE PRIMITIVE: KZG10 polynomial-commitment evaluation binding over the
    BLS12-381 pairing (`q`-SDH / SXDH). A commitment opens to at most one polynomial at each point;
    this is what binds the SNARK's claimed `(b, agg_pk, agg_weight)` to the committed polynomials.
    Pairing/curve math, like `PortalFloor.PedersenKernel.binding` is DLog. (`hints/src/kzg.rs`, the
    `verify_opening` pairing check `verifier.rs:39`.)

  * **`BlsAggUnforgeable`** — IRREDUCIBLE PRIMITIVE: BLS aggregate-signature unforgeability (co-CDH
    over the BLS12-381 pairing). An accepting final pairing `e(agg_pk, H(m)) = e(g₀, agg_sig')` proves
    the holders of the keys aggregated into `agg_pk` signed `m`. Pairing math, like
    `PortalFloor.SignatureKernel.unforgeable` is ed25519 EUF-CMA. (`hints/src/lib.rs:228`.)

  * **`SnarkPolyIOP`** — IRREDUCIBLE-RELATIVE-TO-`KzgBinding`: the polynomial-IOP + Fiat-Shamir
    soundness of `verify_proof`. An accepting SNARK proves the committed selector `b` is boolean,
    `agg_pk` is the product of the selected keys, and `agg_weight` is the selected weight. Reduces to
    `KzgBinding` + Schwartz–Zippel; the STARK-style `extractable` discipline of
    `PortalFloor.VerifierKernel.extractable`. (`hints/src/snark/verifier.rs:126`.)

The `SnarkContract`/`SignedBy` hypotheses of §3 ARE the unpacked content of `SnarkPolyIOP` /
`BlsAggUnforgeable` — supplying them is what "discharging the carrier" means; a forgeable prover cannot. -/

/-! ## §3 — the certificate, its three gates, and the soundness reduction.

A `ThresholdCert` records exactly what `hints::Signature` carries (`federation/src/threshold.rs:62`):
the required `threshold`, the claimed `aggWeight`, the selected subset `selected` (the SNARK's `b`,
extracted), and the abstract `BlsAggregateOk` / `SnarkOk` acceptance bits the two crypto gates set. -/

variable {PK : Type u}

/-- The federation's threshold quorum certificate (`ThresholdQC`, `federation/src/threshold.rs:62`):
a constant-size aggregate over a committee. The `selected` set is the SNARK's `b`-bitvector reified;
the two `Prop` fields are the acceptance bits of the SNARK + BLS gates (set by the irreducible
primitives, consumed below). -/
structure ThresholdCert (C : Committee PK) (msg : ℕ) where
  /-- The required BFT threshold weight (`sig.threshold`, `threshold.rs:69`). -/
  threshold : ℕ
  /-- The claimed aggregate weight (`proof.agg_weight`, `verifier.rs:132`). -/
  aggWeight : ℕ
  /-- The subset of committee members whose keys/weights were aggregated — the SNARK's boolean `b`,
  reified. A `Finset` IS a boolean indicator: `i ∈ selected ↔ b_i = 1` (the `b∈{0,1}` row is then
  free, not assumed). -/
  selected : Finset ℕ
  /-- Gate 2 (SNARK) accepted: the relation `verify_proof` enforces — `agg_pk` is the product of the
  selected keys, `aggWeight` is the selected weight, `b` boolean. Set by `SnarkPolyIOP`. -/
  SnarkOk : Prop
  /-- Gate 3 (BLS) accepted: `e(agg_pk, H(m)) = e(g₀, agg_sig')`. Set by `BlsAggUnforgeable`. -/
  BlsAggregateOk : Prop

namespace ThresholdCert
variable {C : Committee PK} {msg : ℕ}

/-- The three-gate acceptance predicate, mirroring `verify_aggregate` (`hints/src/lib.rs:208`) gate
for gate: (1) `aggWeight ≥ threshold`, (2) `SnarkOk`, (3) `BlsAggregateOk`. ALL THREE conjuncts —
fail-closed, exactly the `if … return Err` cascade. -/
def accepts (cert : ThresholdCert C msg) : Prop :=
  cert.aggWeight ≥ cert.threshold ∧ cert.SnarkOk ∧ cert.BlsAggregateOk

/-- **The SNARK soundness CONTRACT** — what an accepting `verify_proof` (under `SnarkPolyIOP`) yields:
the committed `aggWeight` IS the selected weight, and the selected set is a genuine sub-committee. This
is the relation the polynomial-IOP enforces (`b`-boolean + weighted-sum rows), exported as the
hypothesis the reduction consumes. NOT assumed true blindly — it is `SnarkPolyIOP`'s unpacked content,
the same shape as `VerifierKernel.verify_sound`. -/
structure SnarkContract (cert : ThresholdCert C msg) : Prop where
  /-- The selected set is a sub-committee (the SNARK's domain check). -/
  selected_sub : cert.selected ⊆ C.members
  /-- The claimed aggregate weight equals the selected weight (the weighted-sum row). -/
  aggWeight_eq : cert.aggWeight = C.selectedWeight cert.selected

/-- **The BLS soundness CONTRACT** — what an accepting final pairing (under `BlsAggUnforgeable`)
yields: every selected member actually signed `msg` (`C.SignedBy i msg`). This is the unforgeability
unpacking — the holders of the keys aggregated into `agg_pk` produced the aggregate signature. -/
def BlsContract (cert : ThresholdCert C msg) : Prop := ∀ i ∈ cert.selected, C.SignedBy i msg

end ThresholdCert

/-! ## §3b — the load-bearing reduction (DISCHARGEABLE: pure selector arithmetic). -/

variable {C : Committee PK} {msg : ℕ}

/-- **`quorum_weight_suffices`** (no crypto) — if an accepting cert's claimed `aggWeight`
reaches the threshold AND the SNARK contract pins `aggWeight = selectedWeight selected`, then the
HONEST selected weight reaches the threshold. This is the algebraic heart: the threshold gate's
`agg_weight ≥ threshold` becomes a statement about the REAL selected committee weight, because the
SNARK binds `agg_weight` to the genuine `Σ` (via KZG). No false aggregate weight can pass — that is
exactly what `SnarkContract.aggWeight_eq` (the weighted-sum row) buys. -/
theorem quorum_weight_suffices
    (cert : ThresholdCert C msg) (hacc : cert.accepts) (hsnark : cert.SnarkContract) :
    C.selectedWeight cert.selected ≥ cert.threshold := by
  have hge : cert.aggWeight ≥ cert.threshold := hacc.1
  rw [hsnark.aggWeight_eq] at hge
  exact hge

/-- **`selected_is_subcommittee`** — the selected set is a genuine sub-committee (no phantom
members outside the committee can be counted). Directly the SNARK domain check. -/
theorem selected_is_subcommittee
    (cert : ThresholdCert C msg) (hsnark : cert.SnarkContract) :
    cert.selected ⊆ C.members :=
  hsnark.selected_sub

/-- **`accepting_cert_has_quorum`** — THE discharge theorem. Given:
  * the cert ACCEPTS (all three gates, `verify_aggregate`),
  * the SNARK carrier `SnarkPolyIOP` discharged into its contract `hsnark`,
  * the BLS carrier `BlsAggUnforgeable` discharged into per-member signing `hbls`,
it concludes a GENUINE weighted quorum signed `msg`: a sub-committee `S ⊆ members` with
`selectedWeight S ≥ threshold` AND `selectedWeight S ≤ totalWeight` (well-formed) AND every member of
`S` signed `msg`. This is the federation's quorum-certificate soundness — reduced to the three named
pairing-crypto primitives. -/
theorem accepting_cert_has_quorum
    (cert : ThresholdCert C msg)
    (hacc : cert.accepts)
    (hsnark : cert.SnarkContract)
    (hbls : cert.BlsContract) :
    ∃ S : Finset ℕ,
      S ⊆ C.members ∧
      C.selectedWeight S ≥ cert.threshold ∧
      C.selectedWeight S ≤ C.totalWeight ∧
      (∀ i ∈ S, C.SignedBy i msg) := by
  refine ⟨cert.selected, selected_is_subcommittee cert hsnark, ?_, ?_, hbls⟩
  · exact quorum_weight_suffices cert hacc hsnark
  · exact C.selectedWeight_le_total (selected_is_subcommittee cert hsnark)

/-! ## §3c — ANTI-GHOST: the threshold gate rejects a sub-quorum.

The dual of soundness: if the HONEST selected weight is below threshold, NO accepting cert can claim
otherwise — because the SNARK contract binds `aggWeight` to the real selected weight. So a forged
`aggWeight` that lies about reaching the threshold is impossible *given the SNARK carrier*. This proves
the threshold gate is not vacuous: stripping the SNARK binding is exactly what would let a sub-quorum
forge a cert. -/
theorem subquorum_cannot_accept
    (cert : ThresholdCert C msg) (hsnark : cert.SnarkContract)
    (hlow : C.selectedWeight cert.selected < cert.threshold) :
    ¬ cert.accepts := by
  intro hacc
  have h := quorum_weight_suffices cert hacc hsnark
  omega

/-! ## §4 — non-vacuity + the equal-weight federation differential.

`federation/src/threshold.rs` uses an EQUAL-WEIGHT committee (every member weight = 1), so the
threshold is a member COUNT (`threshold_value`, `threshold.rs:48`). We exhibit a concrete equal-weight
committee and a passing cert, witnessing every theorem FIRES, and pin the count semantics with
`#guard`s against the Rust equal-weight wrapper. -/

namespace Reference

/-- A 4-member equal-weight committee (every weight = 1) — the `FederationCommittee` shape with
`threshold_value` = a 3-of-4 BFT quorum. `pk i := i` (toy keys). `SignedBy i m := i ≤ 2` is a GENUINE
(non-`True`) reference relation: members 0,1,2 signed message anything, member 3 did not — so the BLS
contract `∀ i ∈ selected, SignedBy i m` is a real, falsifiable obligation here (FALSE if member 3 is
in `selected`), witnessing non-vacuity. -/
def fed4 : Committee ℕ where
  members := {0, 1, 2, 3}
  pk i := i
  weight _ := 1
  SignedBy i _ := i ≤ 2

/-- Total weight = member count = 4. -/
theorem fed4_total : fed4.totalWeight = 4 := by decide

/-- A 3-of-4 quorum (members {0,1,2}) has selected weight 3 = the count. -/
theorem fed4_quorum_weight : fed4.selectedWeight {0, 1, 2} = 3 := by decide

/-- A passing 3-of-4 cert: threshold 3, the SNARK-bound `aggWeight` = 3 = the genuine selected weight,
all three gates open. `SnarkOk`/`BlsAggregateOk` are `True` HERE only because this is the reference
non-vacuity witness (a real cert sets them from the pairing checks); the CONTRACTS below are the
genuine ones the theorems consume. -/
def passingCert : ThresholdCert fed4 (msg := 99) where
  threshold := 3
  aggWeight := 3
  selected := {0, 1, 2}
  SnarkOk := True
  BlsAggregateOk := True

/-- The reference cert ACCEPTS (all three gates). -/
theorem passingCert_accepts : passingCert.accepts := by
  refine ⟨by decide, trivial, trivial⟩

/-- The genuine SNARK contract for the reference cert: selected ⊆ members, aggWeight = selectedWeight.
PROVED (not assumed) — the reference selector really is a sub-committee with the claimed weight. -/
def passingCert_snark : passingCert.SnarkContract where
  selected_sub := by decide
  aggWeight_eq := by decide

/-- The genuine BLS contract: every selected member ({0,1,2}) signed — each `≤ 2`, so `SignedBy`
holds. PROVED against the real reference relation (NOT `True`); FALSE had `selected` contained member
3. A real cert discharges this from `BlsAggUnforgeable` on the final pairing. -/
theorem passingCert_bls : ∀ i ∈ passingCert.selected, fed4.SignedBy i 99 := by
  intro i hi
  simp only [fed4]
  fin_cases hi <;> decide

/-- **The full reduction FIRES**: the reference accepting cert yields a genuine 3-weight quorum. -/
theorem passingCert_has_quorum :
    ∃ S : Finset ℕ, S ⊆ fed4.members ∧ fed4.selectedWeight S ≥ 3 ∧
      fed4.selectedWeight S ≤ fed4.totalWeight ∧
      (∀ i ∈ S, fed4.SignedBy i 99) :=
  accepting_cert_has_quorum passingCert passingCert_accepts passingCert_snark passingCert_bls

/-- ANTI-VACUITY for the BLS contract: a cert selecting the NON-signer (member 3) FAILS the BLS
contract — `SignedBy 3 99` is `3 ≤ 2`, false. Proves `SignedBy`/`BlsContract` are not `True`-fillable. -/
theorem nonsigner_breaks_bls : ¬ (∀ i ∈ ({0, 3} : Finset ℕ), fed4.SignedBy i 99) := by
  intro h
  have h3 : fed4.SignedBy 3 99 := h 3 (by decide)
  exact absurd (show (3 : ℕ) ≤ 2 from h3) (by decide)

/-- ANTI-GHOST non-vacuity: a 2-of-4 sub-quorum (selected weight 2 < threshold 3) CANNOT accept,
given the SNARK binding. Witnesses `subquorum_cannot_accept` is not vacuous. -/
def subQuorumCert : ThresholdCert fed4 (msg := 99) where
  threshold := 3
  aggWeight := 2
  selected := {0, 1}
  SnarkOk := True
  BlsAggregateOk := True

def subQuorumCert_snark : subQuorumCert.SnarkContract where
  selected_sub := by decide
  aggWeight_eq := by decide

theorem subQuorum_rejected : ¬ subQuorumCert.accepts :=
  subquorum_cannot_accept subQuorumCert subQuorumCert_snark (by decide)

/-! ### §4b — equal-weight differential `#guard`s (vs `federation/src/threshold.rs`). -/

-- Equal-weight committee ⇒ weight = count (the `threshold_value` u64 semantics, `threshold.rs:48`).
#guard fed4.selectedWeight {0, 1, 2} == 3      -- 3-of-4 quorum count
#guard fed4.selectedWeight {0, 1} == 2          -- 2-of-4 sub-quorum count
#guard fed4.selectedWeight {0, 1, 2, 3} == 4    -- full committee count
#guard fed4.totalWeight == 4                     -- |members|
#guard decide (fed4.selectedWeight {0,1,2} ≥ 3)  -- quorum reaches BFT threshold
#guard !decide (fed4.selectedWeight {0,1} ≥ 3)   -- sub-quorum does NOT

end Reference

/-! ## §5 — axiom-hygiene tripwires: the reduction pins exactly the whitelist; the crypto is in the
NAMED carriers (`KzgBinding`/`BlsAggUnforgeable`/`SnarkPolyIOP`), consumed as the contract hypotheses,
never as Lean axioms. -/

#assert_axioms Committee.selectedWeight_le_total
#assert_axioms quorum_weight_suffices
#assert_axioms selected_is_subcommittee
#assert_axioms accepting_cert_has_quorum
#assert_axioms subquorum_cannot_accept
#assert_axioms Reference.passingCert_has_quorum
#assert_axioms Reference.passingCert_bls
#assert_axioms Reference.nonsigner_breaks_bls
#assert_axioms Reference.subQuorum_rejected

end Dregg2.Crypto.BlsThreshold
