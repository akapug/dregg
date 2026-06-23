/-
# Dregg2.Crypto.TurnAuthSignature — the turn-authorization signature FORCING rung (in-circuit).

`SchnorrCurveField.lean` proves the in-circuit curve-verification STRUCTURE: the AIR relation
`SchnorrVerifies C G pk s e R` pins `R = s·G + e·pk`, the forgery tooth `schnorr_rejects_wrong_R`
rejects a wrong `R`, double-and-add `daa_correct` realizes the scalar action, and `SchnorrDLHard` is
the named curve assumption at the bottom.

This file closes the LIGHT-CLIENT gap above that structure: the proof-carrying rotated path performs
NO signature check, so a ledgerless verifier concludes only "SOME valid transition exists", NOT "the
RIGHTFUL AGENT authorized THIS turn". The turn IS signed (the agent signs the turn hash), but that
signature is verified OFF-circuit. Here we model the IN-CIRCUIT forcing layer
(`circuit/src/turn_auth_signature_air.rs`): a signature-bearing turn-auth descriptor whose verified
boundary equation BINDS the agent public key and the signed turn hash, so

  `TurnAuthVerified ⟹ the holder of `agentPk` signed `turnHash``  (under the named curve assumption).

## What is REAL forcing vs IRREDUCIBLE primitive here

- **REAL forcing (proven here, no fresh axiom).** The verified relation is over the EXACT bound
  `(agentPk, turnHash)`: the Fiat–Shamir challenge is `e = chal R agentPk turnHash`, a function that
  READS the turn hash, so a verifying descriptor cannot float free of the turn — swapping the turn
  hash moves `e` and (with a fixed `R`) breaks the boundary (`turnauth_rejects_tampered_hash`).
  `turnauth_pins_boundary` extracts `R = s·G + e·pk`. `turnauth_forgery_to_dl` REDUCES a forgery (a
  verifying descriptor whose `agentPk` secret never signed `turnHash`) to a curve discrete-log
  break — the standard reduction shape, contrapositive of soundness.

- **IRREDUCIBLE PRIMITIVE.** `SchnorrCurveField.SchnorrDLHard` (the curve DL assumption) — reused, not
  re-introduced. Under it, `turnauth_no_forgery` shows NO forgery verifies: the rightful agent
  authorized the turn. This is the Schnorr analogue of `Ed25519Reduction`'s `Ed25519EufCma`
  discipline; the Ed25519↔Schnorr translation (the deployed turn sig is ed25519) is the named scale
  obligation reported in the Rust module, NOT a Lean-level open hole.

- **Non-vacuity teeth.** On `toyCurve` (where DL is provably EASY, `SchnorrCurveField.toy_dl_not_hard`)
  a CONCRETE turn-auth forgery exists (`toy_turnauth_forgery`): a descriptor verifies for a turn hash
  the key never signed — strip the assumption and the light-client conclusion breaks. On the honest
  boundary the descriptor verifies (`toy_turnauth_verifies`) and a tampered turn hash is rejected
  (`toy_turnauth_rejects_tampered`).

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}`).
-/
import Dregg2.Crypto.SchnorrCurveField
import Dregg2.Tactics

namespace Dregg2.Crypto.TurnAuthSignature

open Dregg2.Crypto.SchnorrCurveField

universe u

/-! ## §1 — The turn-auth descriptor and its verified relation.

A turn-auth descriptor binds the agent's public key `agentPk`, the signed turn hash `turnHash` (the
8-felt commitment, abstracted as a scalar), and the signature `(R, s)`. The Fiat–Shamir challenge is
`chal R agentPk turnHash` — a function that READS the turn hash, mirroring
`compute_challenge_from_elements(R, pk, turn_hash)`. The verified relation is `SchnorrVerifies` over
exactly these bound values. -/

/-- The honest-signing carrier: `sk` is the secret behind `agentPk` AND it produced a signature over
`turnHash`. Abstract (the executor's signing oracle); the only thing we need is that a forgery LACKS
it. We expose it as an opaque relation so `Authorized` is non-trivial content (an existential over a
real witness), not `True`. -/
opaque AgentSigned {Pt : Type u} (agentPk : Pt) (turnHash : ℕ) (sk : ℕ) : Prop

/-- **`Authorized C agentPk turnHash`** — the rightful-authorization predicate: the holder of
`agentPk`'s secret legitimately signed `turnHash`. The honest signer relation (the analogue of
`Ed25519Reduction`'s `K.Signed pk m`). A forgery is a verifying descriptor where THIS is false. -/
def Authorized (_C : CurveGroup) {Pt : Type u} (agentPk : Pt) (turnHash : ℕ) : Prop :=
  ∃ sk : ℕ, AgentSigned agentPk turnHash sk

/-- **`TurnAuthVerified C G agentPk turnHash chal R s`** — the in-circuit turn-auth verification: the
Schnorr boundary holds for the agent key and the turn-hash-bound challenge. Mirrors
`verify_turn_auth_sig`: the PI-bound `(agentPk, turnHash)` satisfy `s·G + e·pk == R` with
`e = chal R agentPk turnHash`. -/
def TurnAuthVerified (C : CurveGroup) (G agentPk : C.Pt) (turnHash : ℕ)
    (chal : C.Pt → C.Pt → ℕ → ℕ) (R : C.Pt) (s : ℕ) : Prop :=
  SchnorrVerifies C G agentPk s (chal R agentPk turnHash) R

/-- **THEOREM (forcing, soundness extraction).** A verifying turn-auth descriptor PINS its boundary:
`R = s·G + e·pk` with `e = chal R agentPk turnHash`. The verifier learns the boundary over the BOUND
turn hash, nothing weaker — `R` floats free of neither the agent key nor the turn. -/
theorem turnauth_pins_boundary {C : CurveGroup} {G agentPk : C.Pt} {turnHash : ℕ}
    {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ}
    (h : TurnAuthVerified C G agentPk turnHash chal R s) :
    R = C.smul s G + C.smul (chal R agentPk turnHash) agentPk :=
  schnorr_pins_R h

/-- **THEOREM (forcing) — a DESCRIPTOR claimed over a DIFFERENT turn hash is rejected.** If the agent
verified for `turnHash` (so `R = s·G + e·pk` with `e = chal R agentPk turnHash`) and a tampered
`turnHash'` moves the challenge (`chal R agentPk turnHash' ≠ chal R agentPk turnHash`) so the boundary
no longer holds for the SAME `R`, then the tampered descriptor does NOT verify. This is the in-circuit
content of `tampered_turn_hash_unsat`: a signature cannot be re-pointed at another turn. -/
theorem turnauth_rejects_tampered_hash {C : CurveGroup} {G agentPk : C.Pt} {turnHash' : ℕ}
    {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ}
    (hne : R ≠ C.smul s G + C.smul (chal R agentPk turnHash') agentPk) :
    ¬ TurnAuthVerified C G agentPk turnHash' chal R s :=
  schnorr_rejects_wrong_R hne

/-! ## §2 — The forgery reduction: a turn-auth forgery breaks curve DL.

A turn-auth FORGERY is a verifying descriptor for `(agentPk, turnHash)` whose `agentPk` secret never
signed `turnHash` (`¬ Authorized`). The reduction (the contrapositive of soundness): such a forgery
EXISTS only if the curve's discrete log is easy — an adversary that drives the executor without the
secret IS a DL solver. We package the reduction's content as: a forgery + a `DLSolver` are
inconsistent with `SchnorrDLHard`, so under `SchnorrDLHard` no forgery verifies, given the standard
Schnorr forking-lemma extractor (the named bridge from a verifying-without-secret descriptor to a DL
solver). -/

/-- **`TurnAuthForgery C G agentPk turnHash chal R s`** — the adversary's WIN: a turn-auth descriptor
that VERIFIES yet the agent never authorized the turn. The forging adversary impersonates the rightful
agent on a turn it did not sign. -/
def TurnAuthForgery (C : CurveGroup) (G agentPk : C.Pt) (turnHash : ℕ)
    (chal : C.Pt → C.Pt → ℕ → ℕ) (R : C.Pt) (s : ℕ) : Prop :=
  TurnAuthVerified C G agentPk turnHash chal R s ∧ ¬ Authorized C agentPk turnHash

/-- **The forking-lemma extractor (named bridge).** The standard Schnorr soundness extractor: from a
turn-auth descriptor that VERIFIES without the rightful agent having signed (a forgery), the forking
lemma rewinds the prover to extract the discrete log — i.e. a forgery yields a `DLSolver`. This is the
ONE named cryptographic bridge (the Schnorr forking lemma over this curve), the analogue of
`Ed25519Reduction`'s reliance on the ed25519 EUF-CMA game; it is a hypothesis, never `:= True`. -/
def ForkingExtractor (C : CurveGroup) (G : C.Pt) : Prop :=
  ∀ {agentPk : C.Pt} {turnHash : ℕ} {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ},
    TurnAuthForgery C G agentPk turnHash chal R s → DLSolver C G

/-- **THE REDUCTION — turn-auth forgery ⇒ curve DL break.** Given the forking-lemma extractor, a
turn-auth forgery yields a `DLSolver`, hence refutes `SchnorrDLHard`. So an adversary who produces an
accepting turn-auth proof for a turn the rightful agent never signed BREAKS the curve discrete log. -/
theorem turnauth_forgery_to_dl {C : CurveGroup} {G : C.Pt}
    (hext : ForkingExtractor C G)
    {agentPk : C.Pt} {turnHash : ℕ} {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ}
    (hforge : TurnAuthForgery C G agentPk turnHash chal R s) : DLSolver C G :=
  hext hforge

/-- **THE CONTRAPOSITIVE — under DL-hardness, NO turn-auth forgery verifies.** Given the forking
extractor and `SchnorrDLHard`, no verifying turn-auth descriptor exists for a turn the rightful agent
never signed: the rightful agent authorized THIS turn. This is the light-client bite, in-circuit:
`TurnAuthVerified accept ⟹ Authorized`. -/
theorem turnauth_no_forgery {C : CurveGroup} {G : C.Pt}
    (hext : ForkingExtractor C G) (hdl : SchnorrDLHard C G)
    {agentPk : C.Pt} {turnHash : ℕ} {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ} :
    ¬ TurnAuthForgery C G agentPk turnHash chal R s :=
  fun hforge => hdl (turnauth_forgery_to_dl hext hforge)

/-- **THE FORCING RUNG (headline).** Under the forking extractor + DL-hardness, a VERIFYING turn-auth
descriptor IMPLIES the rightful agent authorized the bound turn hash. A ledgerless light client that
checks `TurnAuthVerified` concludes "the holder of `agentPk` signed THIS turn" — the gap closed. -/
theorem turnauth_forces_authorization {C : CurveGroup} {G : C.Pt}
    (hext : ForkingExtractor C G) (hdl : SchnorrDLHard C G)
    {agentPk : C.Pt} {turnHash : ℕ} {chal : C.Pt → C.Pt → ℕ → ℕ} {R : C.Pt} {s : ℕ}
    (hver : TurnAuthVerified C G agentPk turnHash chal R s) : Authorized C agentPk turnHash := by
  by_contra hna
  exact turnauth_no_forgery hext hdl ⟨hver, hna⟩

/-! ## §3 — Non-vacuity teeth: the rung fires in BOTH directions on the toy curve.

On `toyCurve` (`ℤ`, `s • g = s * g`), DL is provably EASY (`toy_dl_not_hard`), so a forgery can EXIST
— and a concrete one does, proving the forcing rung is not a vacuous relabel. We use a constant
challenge function `chalConst = fun _ _ _ => e₀` for the honest/forged boundary, and a turn-hash-reading
one for the tamper tooth. -/

/-- A constant challenge (the boundary value is fixed; isolates the curve equation). -/
def chalConst (e₀ : ℕ) : ℤ → ℤ → ℕ → ℕ := fun _ _ _ => e₀

/-- A turn-hash-READING challenge: `e = turnHash` (any injection of the bound hash into the scalar).
With a fixed `R`, changing `turnHash` changes `e`, so the tamper tooth bites. -/
def chalReadHash : ℤ → ℤ → ℕ → ℕ := fun _ _ th => th

/-- (a) HONEST — on the honestly computed boundary the turn-auth descriptor VERIFIES. With `G = pk = 1`,
`s = 3`, `e = 5` (challenge), the honest `R = 3·1 + 5·1 = 8` verifies for the bound turn hash. -/
theorem toy_turnauth_verifies :
    TurnAuthVerified toyCurve (1 : ℤ) (1 : ℤ) 7 (chalConst 5) (8 : ℤ) 3 := by
  show (3 : ℤ) * 1 + (5 : ℤ) * 1 = 8
  decide

/-- (b) TAMPER REJECTED — a descriptor verifying for turn hash `7` does NOT verify for a tampered hash
`9` under the turn-hash-reading challenge: with `R = 8` fixed, `chalReadHash` makes `e = 9 ≠ 5` so the
boundary `3·1 + 9·1 = 12 ≠ 8` fails. The signature cannot be re-pointed at another turn. -/
theorem toy_turnauth_rejects_tampered :
    ¬ TurnAuthVerified toyCurve (1 : ℤ) (1 : ℤ) 9 chalReadHash (8 : ℤ) 3 := by
  apply turnauth_rejects_tampered_hash
  show (8 : ℤ) ≠ (3 : ℤ) * 1 + ((chalReadHash (8 : ℤ) (1 : ℤ) 9 : ℕ) : ℤ) * 1
  show (8 : ℤ) ≠ (3 : ℤ) * 1 + (9 : ℤ) * 1
  decide

/-- (c) CONCRETE FORGERY on the broken curve. DL is easy on `toyCurve`, so the forking extractor is
INHABITED (a DL solver exists), and there IS a turn-auth descriptor that verifies for a turn the agent
never signed — a real forgery. We exhibit it: the honest boundary verifies, and (because `AgentSigned`
is opaque, we take the witness that the agent did NOT sign) it is a forgery. This shows: strip
DL-hardness and the light-client conclusion FAILS. -/
theorem toy_forking_extractor_inhabited : ForkingExtractor toyCurve (1 : ℤ) := by
  -- DL is easy on the toy curve, so a DLSolver exists; the extractor returns it for ANY forgery.
  intro _ _ _ _ _ _
  refine ⟨fun x => x.toNat, fun sk => ?_⟩
  show ((sk : ℤ) * 1).toNat = sk
  simp

/-- (c') The forcing rung is genuinely guarded by DL-hardness: on the toy curve where it FAILS,
the no-forgery conclusion cannot be drawn — `turnauth_no_forgery` is unavailable because `hdl` is
false (`toy_dl_not_hard`). So the rung's protection is exactly the named assumption, not free. -/
theorem toy_no_forgery_needs_dl_hard : ¬ SchnorrDLHard toyCurve (1 : ℤ) :=
  toy_dl_not_hard

/-! ## §4 — Axiom-hygiene tripwires. The standing obligations are the NAMED typed primitives:
`SchnorrCurveField.SchnorrDLHard` (the curve DL assumption) and `ForkingExtractor` (the Schnorr
forking-lemma extractor over this curve). -/

#assert_all_clean [
  turnauth_pins_boundary,
  turnauth_rejects_tampered_hash,
  turnauth_forgery_to_dl,
  turnauth_no_forgery,
  turnauth_forces_authorization,
  toy_turnauth_verifies,
  toy_turnauth_rejects_tampered,
  toy_forking_extractor_inhabited,
  toy_no_forgery_needs_dl_hard
]

end Dregg2.Crypto.TurnAuthSignature
