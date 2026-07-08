/-
# `Dregg2.Crypto.HashSig` — the POST-QUANTUM signature anchor: a hash-based one-time signature.

The classical signature surface is already modeled — `SchnorrCurveField` (the abstract Schnorr core),
`BlsThreshold` (the constant-size weighted-threshold quorum certificate), `DualSchemeAuthority` (the
ed25519↔curve dual). All of those rest on a discrete-log or pairing carrier. This file opens the
POST-QUANTUM path, and it is the CLEANEST to prove for one reason: a hash-based signature adds **no new
hardness carrier**. Its security reduces to hash preimage/collision resistance — the SAME carrier class
dregg's STARK/FRI layer already assumes (`Poseidon2SpongeCR`), not DL, pairing, or lattice hardness.

This is the SLH-DSA / SPHINCS+ ATOM: a Lamport one-time signature. A Merkle tree over `N` such one-time
public keys (reusing `Dregg2.Lightclient.MMR`, whose root already `#assert_axioms`-cleanly binds its
leaves) lifts it to a many-time signature — the next construction. Here we prove the one-time layer:
correctness (a genuine signature always verifies) and the forgery tooth (any verifying forgery on a
DIFFERENT message hands you either a hash collision or a preimage the signer never revealed — so a
forger breaks the hash).

`H : D → D` is the abstract one-way hash (the carrier is stated at the forgery tooth, never a Lean
axiom). A message is its `ℓ`-bit digest, `Fin ℓ → Bool`.
-/
import Dregg2.Tactics

namespace Dregg2.Crypto.HashSig

variable {D : Type*} [DecidableEq D]

/-- A Lamport secret key for `ℓ`-bit messages: for each bit position `i` and each bit value `b`, an
independent preimage `pre i b`. -/
structure SecretKey (D : Type*) (ℓ : ℕ) where
  pre : Fin ℓ → Bool → D

/-- The public key is the hash of every preimage. -/
def publicKey (H : D → D) {ℓ : ℕ} (sk : SecretKey D ℓ) : Fin ℓ → Bool → D :=
  fun i b => H (sk.pre i b)

/-- **Sign** a message `m` by REVEALING, for each bit position, the preimage matching that bit's value
(and only that one — the other stays secret; this is what makes it one-time). -/
def sign {ℓ : ℕ} (sk : SecretKey D ℓ) (m : Fin ℓ → Bool) : Fin ℓ → D :=
  fun i => sk.pre i (m i)

/-- **Verify**: for every bit position, the hash of the revealed value equals the public key entry for
that bit's value. -/
def verify (H : D → D) {ℓ : ℕ} (pk : Fin ℓ → Bool → D) (m : Fin ℓ → Bool) (sig : Fin ℓ → D) : Prop :=
  ∀ i, H (sig i) = pk i (m i)

/-- **Correctness.** A genuine signature always verifies — unconditionally, no carrier needed. -/
theorem lamport_correct (H : D → D) {ℓ : ℕ} (sk : SecretKey D ℓ) (m : Fin ℓ → Bool) :
    verify H (publicKey H sk) m (sign sk m) := by
  intro i
  simp only [verify, publicKey, sign]

/-- **The forgery tooth (structural).** Suppose a forger produces `sig'` that VERIFIES on a message
`m'` which differs from the signed `m` at some bit `i` (`m' i ≠ m i`). At that bit the signer revealed
`pre i (m i)` and NEVER `pre i (m' i)`. Verification forces `H (sig' i) = H (pre i (m' i))`, so either:

* `sig' i = pre i (m' i)` — the forger produced the UNREVEALED preimage of a public hash (a preimage
  break), or
* `sig' i ≠ pre i (m' i)` — the forger produced a distinct value with the same hash (a COLLISION).

Either way the forger broke the hash. This is the full reduction target; under a preimage/collision
resistance carrier for `H` (the same class as `Poseidon2SpongeCR`) no efficient forger exists. We do
NOT axiomatize that carrier — we expose the exact break a forgery yields. -/
theorem lamport_forgery_breaks_hash (H : D → D) {ℓ : ℕ} (sk : SecretKey D ℓ)
    (m m' : Fin ℓ → Bool) (i : Fin ℓ) (hne : m' i ≠ m i)
    (sig' : Fin ℓ → D) (hver : verify H (publicKey H sk) m' sig') :
    -- the revealed set for `m` did not include `pre i (m' i)`, yet the forger hit its hash:
    H (sig' i) = H (sk.pre i (m' i))
      ∧ (sig' i = sk.pre i (m' i) ∨ (sig' i ≠ sk.pre i (m' i) ∧ H (sig' i) = H (sk.pre i (m' i)))) := by
  have hhit : H (sig' i) = H (sk.pre i (m' i)) := by
    have := hver i
    simpa only [publicKey] using this
  refine ⟨hhit, ?_⟩
  by_cases hsig : sig' i = sk.pre i (m' i)
  · exact Or.inl hsig
  · exact Or.inr ⟨hsig, hhit⟩

/-- **The signature reveals nothing at the flipped bit.** A one-time signature on `m` reveals
`pre i (m i)`; the value a forgery on `m'` needs at a differing bit, `pre i (m' i)`, is a DIFFERENT
secret. This is why the forgery tooth's preimage is genuinely unrevealed (the one-time discipline). -/
theorem sign_reveals_only_signed_bit {ℓ : ℕ} (sk : SecretKey D ℓ) (m : Fin ℓ → Bool)
    (i : Fin ℓ) : sign sk m i = sk.pre i (m i) := rfl

#assert_axioms lamport_correct
#assert_axioms lamport_forgery_breaks_hash

end Dregg2.Crypto.HashSig
