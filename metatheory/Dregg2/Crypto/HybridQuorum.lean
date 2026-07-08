/-
# `Dregg2.Crypto.HybridQuorum` — hybrid (classical + PQ) quorum-certificate unforgeability.

A hybrid quorum certificate carries BOTH a classical signature (FROST/ed25519 — the DL-carrier
half) and a post-quantum one (ML-DSA — the lattice-carrier half). The hybrid VERIFIES iff BOTH
halves verify: `hybridVerify Vc Vp m σc σp := Vc m σc ∧ Vp m σp`.

The security payoff is a DISJUNCTION: the hybrid is unforgeable if EITHER half is. A hybrid
forgery contains, by projection, a verifying classical signature AND a verifying PQ signature on
the same un-signed message — it is simultaneously a forgery of BOTH schemes. So breaking the
hybrid requires breaking BOTH carriers at once. In particular a QUANTUM adversary that breaks the
classical half completely (Shor kills discrete log — every classical "signature" verifies) still
cannot forge the hybrid, because the PQ half holds. That is `hybrid_survives_classical_break`.

## What is PROVEN here (scheme-generic; two opaque verifiers over a message type)

- `hybridVerify` — the AND-composition: both halves must verify.
- `hybrid_forgery_breaks_both` — a hybrid signature verifying on an un-signed message yields a
  forgery of the classical scheme AND a forgery of the PQ scheme (the conjunction projects).
- `hybrid_unforgeable_of_either` — THE headline: `Unforgeable Vc Signed ∨ Unforgeable Vp Signed`
  implies the hybrid is unforgeable. Security of the composite = the OR of the halves' security.
- `hybrid_survives_classical_break` — quantum-safety corollary: with the classical verifier
  TOTALLY broken (`Vc := fun _ _ => True`, accepting everything), the hybrid remains unforgeable
  as long as the PQ half is `Unforgeable`. "ed25519 falls to Shor, the federation still can't be
  forged."

## Non-vacuity (the `Unforgeable` hypothesis is LOAD-BEARING)

`hybrid_survives_classical_break` gets NOTHING from the classical half — with `Vc = fun _ _ => True`
the classical conjunct is trivially satisfied by any bytes, so the rejection of a forgery rests
entirely on the PQ hypothesis. We prove the hypothesis is genuinely needed:
- `both_broken_is_forgeable` — if BOTH halves accept everything (no `Unforgeable` half at all),
  the hybrid IS forgeable: a concrete forgery on a never-signed message verifies. Strip the
  hypothesis and the conclusion is FALSE — no `P → P` laundering.
- A concrete toy instance (§5) where the hybrid, with its classical half broken, still ACCEPTS a
  legitimately signed message and REJECTS a forgery — both polarities fire.

`Unforgeable V Signed := ∀ m σ, V m σ → Signed m` packages EUF-CMA at the same boundary as
`ThresholdReduction.Unforgeable`: the claim that no efficient (or quantum) adversary violates it
for the PQ half is the ML-DSA (MLWE/MSIS) carrier, named at this boundary, not discharged.

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}`; no fresh axiom).
-/
import Dregg2.Tactics

namespace Dregg2.Crypto.HybridQuorum

universe u v w

/-! ## §1 — The abstract unforgeability predicate (mirrors `ThresholdReduction.Unforgeable`).

A verifier `V : M → S → Prop` over messages `M` and signatures `S` is unforgeable w.r.t. a
"legitimately signed" predicate `Signed` when every verifying signature is on a signed message —
no verifying signature on an un-signed message exists. -/

/-- **`Unforgeable V Signed`** — every signature that verifies on `m` had `m` legitimately signed.
This is the EUF-CMA guarantee shape; for the classical half it is what the DL/forking carrier
buys (and what Shor DESTROYS), for the PQ half what the MLWE/MSIS carrier buys. -/
def Unforgeable {M : Type u} {S : Type v} (V : M → S → Prop) (Signed : M → Prop) : Prop :=
  ∀ m σ, V m σ → Signed m

/-! ## §2 — The hybrid verifier: BOTH halves must verify. -/

/-- **`hybridVerify Vc Vp m σc σp`** — the hybrid certificate verifies iff the classical half
verifies AND the PQ half verifies. The AND is the whole design: an attacker must satisfy both. -/
def hybridVerify {M : Type u} {Sc : Type v} {Sp : Type w}
    (Vc : M → Sc → Prop) (Vp : M → Sp → Prop) (m : M) (σc : Sc) (σp : Sp) : Prop :=
  Vc m σc ∧ Vp m σp

/-- Hybrid unforgeability: no hybrid certificate verifies on an un-signed message. This is
`Unforgeable` instantiated at the paired-signature verifier, stated directly over the two halves. -/
def HybridUnforgeable {M : Type u} {Sc : Type v} {Sp : Type w}
    (Vc : M → Sc → Prop) (Vp : M → Sp → Prop) (Signed : M → Prop) : Prop :=
  ∀ m σc σp, hybridVerify Vc Vp m σc σp → Signed m

/-! ## §3 — A hybrid forgery is a forgery of BOTH schemes. -/

/-- **THEOREM — `hybrid_forgery_breaks_both`.** A hybrid certificate that verifies on an UN-signed
message contains a classical forgery AND a PQ forgery: each half verifies on the same un-signed
`m`. So an adversary that forges the hybrid has, in hand, a break of the classical scheme and a
break of the PQ scheme simultaneously — the reduction runs to EITHER carrier. -/
theorem hybrid_forgery_breaks_both {M : Type u} {Sc : Type v} {Sp : Type w}
    {Vc : M → Sc → Prop} {Vp : M → Sp → Prop} {Signed : M → Prop}
    {m : M} {σc : Sc} {σp : Sp}
    (hver : hybridVerify Vc Vp m σc σp) (hforge : ¬ Signed m) :
    (Vc m σc ∧ ¬ Signed m) ∧ (Vp m σp ∧ ¬ Signed m) :=
  ⟨⟨hver.1, hforge⟩, ⟨hver.2, hforge⟩⟩

/-! ## §4 — THE headline: the hybrid is unforgeable if EITHER half is. -/

/-- **THEOREM — `hybrid_unforgeable_of_either`.** If the classical scheme is `Unforgeable` OR the
PQ scheme is `Unforgeable`, the hybrid is unforgeable: a verifying hybrid certificate's message is
always `Signed`. Breaking the hybrid therefore requires breaking BOTH halves — the composite's
security is the disjunction of the halves'. -/
theorem hybrid_unforgeable_of_either {M : Type u} {Sc : Type v} {Sp : Type w}
    {Vc : M → Sc → Prop} {Vp : M → Sp → Prop} {Signed : M → Prop}
    (h : Unforgeable Vc Signed ∨ Unforgeable Vp Signed) :
    HybridUnforgeable Vc Vp Signed := by
  intro m σc σp hver
  cases h with
  | inl hc => exact hc m σc hver.1
  | inr hp => exact hp m σp hver.2

/-- Companion (contrapositive bite): if either half is `Unforgeable`, NO hybrid certificate
verifies on an un-signed message — the forgery is refuted outright, not merely reclassified. -/
theorem hybrid_no_forgery_of_either {M : Type u} {Sc : Type v} {Sp : Type w}
    {Vc : M → Sc → Prop} {Vp : M → Sp → Prop} {Signed : M → Prop}
    (h : Unforgeable Vc Signed ∨ Unforgeable Vp Signed)
    {m : M} (hforge : ¬ Signed m) (σc : Sc) (σp : Sp) :
    ¬ hybridVerify Vc Vp m σc σp :=
  fun hver => hforge (hybrid_unforgeable_of_either h m σc σp hver)

/-! ## §5 — Quantum safety: the classical half TOTALLY broken, the hybrid stands.

`Vc := fun _ _ => True` is the strongest possible classical break — every string of bytes is a
"verifying" classical signature on every message (Shor recovered the secret key; worse, the
verifier is a rubber stamp). The classical conjunct of `hybridVerify` is then satisfied for FREE,
so it contributes NOTHING: the hybrid's rejection of a forgery rests entirely on the PQ
hypothesis. That is exactly what makes the theorem non-vacuous — and §6 proves that stripping the
PQ hypothesis makes the conclusion FALSE. -/

/-- **THEOREM — `hybrid_survives_classical_break`.** Even with the classical verifier replaced by
the always-accepting rubber stamp (`fun _ _ => True` — discrete log fell to Shor, every classical
"signature" verifies), the hybrid remains unforgeable as long as the PQ half is `Unforgeable`.
This is "ed25519 falls to Shor, the federation still can't be forged": the quantum adversary's
total classical break buys it nothing against the AND-composition. -/
theorem hybrid_survives_classical_break {M : Type u} {Sc : Type v} {Sp : Type w}
    {Vp : M → Sp → Prop} {Signed : M → Prop}
    (hpq : Unforgeable Vp Signed) :
    HybridUnforgeable (fun (_ : M) (_ : Sc) => True) Vp Signed :=
  hybrid_unforgeable_of_either (Or.inr hpq)

/-- The forgery-shaped restatement: under a TOTAL classical break, a hybrid certificate on an
un-signed message still fails to verify, provided the PQ half is `Unforgeable`. The candidate
forgery's classical half passes vacuously; its PQ half CANNOT pass on an un-signed message. -/
theorem hybrid_rejects_forgery_after_classical_break {M : Type u} {Sc : Type v} {Sp : Type w}
    {Vp : M → Sp → Prop} {Signed : M → Prop}
    (hpq : Unforgeable Vp Signed) {m : M} (hforge : ¬ Signed m) (σc : Sc) (σp : Sp) :
    ¬ hybridVerify (fun (_ : M) (_ : Sc) => True) Vp m σc σp :=
  hybrid_no_forgery_of_either (Or.inr hpq) hforge σc σp

/-- Symmetric corollary (the disjunction cuts both ways): if instead the PQ half were the broken
one, a still-`Unforgeable` classical half carries the hybrid. Hybrid deployment is safe against
EITHER carrier failing — including a future lattice break. -/
theorem hybrid_survives_pq_break {M : Type u} {Sc : Type v} {Sp : Type w}
    {Vc : M → Sc → Prop} {Signed : M → Prop}
    (hc : Unforgeable Vc Signed) :
    HybridUnforgeable Vc (fun (_ : M) (_ : Sp) => True) Signed :=
  hybrid_unforgeable_of_either (Or.inl hc)

/-! ## §6 — Non-vacuity teeth: the `Unforgeable` hypothesis is LOAD-BEARING.

If BOTH halves accept everything and nothing was ever signed, the hybrid IS forgeable — a
concrete forgery verifies. So `hybrid_survives_classical_break` is not `P → P`: delete its PQ
hypothesis and the conclusion is refutable. -/

/-- **THEOREM — `both_broken_is_forgeable`.** With BOTH verifiers rubber stamps and an empty
`Signed`, hybrid unforgeability FAILS: the certificate `(0, 0)` on the never-signed message `0`
verifies. This is the counterexample that makes the §4/§5 hypotheses load-bearing: the disjunction
`Unforgeable Vc ∨ Unforgeable Vp` cannot be dropped. -/
theorem both_broken_is_forgeable :
    ¬ HybridUnforgeable (fun (_ : Nat) (_ : Nat) => True) (fun (_ : Nat) (_ : Nat) => True)
        (fun _ => False) :=
  fun h => h 0 0 0 ⟨trivial, trivial⟩

/-! Concrete toy instance, BOTH polarities: messages are `Nat`, the even ones were signed, and the
toy PQ verifier verifies exactly the signed messages (so it is `Unforgeable` — legitimately). The
classical half is the BROKEN rubber stamp throughout. -/

/-- Toy signing predicate: the even messages were legitimately signed. -/
def toySigned (m : Nat) : Prop := m % 2 = 0

/-- Toy PQ verifier: accepts exactly (signed message, tag 0) pairs. Sound by construction. -/
def toyVp (m σ : Nat) : Prop := m % 2 = 0 ∧ σ = 0

/-- The toy PQ half is `Unforgeable` — genuinely, by its verification condition. -/
theorem toyVp_unforgeable : Unforgeable toyVp toySigned :=
  fun _ _ hv => hv.1

/-- POSITIVE polarity: the hybrid (classical half broken) still ACCEPTS a legitimate certificate —
message `2` was signed, and `(σc, σp) = (17, 0)` verifies (any classical bytes pass; the PQ tag is
right). The composite is not the empty verifier. -/
theorem toy_hybrid_accepts_legitimate :
    hybridVerify (fun (_ : Nat) (_ : Nat) => True) toyVp 2 17 0 :=
  ⟨trivial, rfl, rfl⟩

/-- NEGATIVE polarity: the hybrid (classical half broken) REJECTS the forgery — message `3` was
never signed, and NO certificate `(σc, σp)` verifies on it, even though every `σc` passes the
broken classical check. Security rests entirely on the PQ half, and it holds. -/
theorem toy_hybrid_rejects_forgery (σc σp : Nat) :
    ¬ hybridVerify (fun (_ : Nat) (_ : Nat) => True) toyVp 3 σc σp :=
  hybrid_rejects_forgery_after_classical_break toyVp_unforgeable
    (by unfold toySigned; decide) σc σp

/-! ## §7 — Axiom-hygiene tripwires. No fresh axiom: the PQ (resp. classical) hardness enters only
as the explicit `Unforgeable` hypothesis at the stated boundary, never discharged here. -/

#assert_all_clean [
  hybrid_forgery_breaks_both,
  hybrid_unforgeable_of_either,
  hybrid_no_forgery_of_either,
  hybrid_survives_classical_break,
  hybrid_rejects_forgery_after_classical_break,
  hybrid_survives_pq_break,
  both_broken_is_forgeable,
  toyVp_unforgeable,
  toy_hybrid_accepts_legitimate,
  toy_hybrid_rejects_forgery
]

end Dregg2.Crypto.HybridQuorum
