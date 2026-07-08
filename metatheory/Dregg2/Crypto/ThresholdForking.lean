/-
# `Dregg2.Crypto.ThresholdForking` — the capstone: a forked threshold forger HANDS YOU the group secret.

This composes the two halves the swarm just proved into the complete threshold→DL reduction:
* `Frost.frost_cert_verifies_under_group_key` — a threshold certificate verifies under the group key
  via the single-signer Schnorr verifier;
* `SchnorrExtractor.schnorr_special_soundness_extracts_dl` — two accepting Schnorr transcripts sharing
  the commitment `R` with different challenges yield the discrete-log witness.

A forking-lemma rewind runs the threshold adversary twice on the SAME nonce commitments (so the group
`R = (Σ kᵢ)·g` is identical) but with different Fiat–Shamir challenges `e ≠ e'`. Each run's combined
certificate is a Schnorr signature under the group public key. Feeding the two through the extractor
recovers the GROUP secret `x` (with `pk = x·g`). So a threshold forger, forked, breaks the discrete log
of the federation's group key — i.e. threshold-EUF-CMA reduces to DL, all the way down to the algebraic
extractor, with only the ROM forking PROBABILITY (that the rewind succeeds) left as the named carrier.
-/
import Dregg2.Crypto.Frost
import Dregg2.Crypto.SchnorrExtractor
import Dregg2.Crypto.HermineThreshold
import Dregg2.Crypto.HermineExtractor

namespace Dregg2.Crypto.ThresholdForking

open scoped BigOperators
open Dregg2.Crypto.Frost
open Dregg2.Crypto.Schnorr

variable {S : Type*} [Field S] {G : Type*} [AddCommGroup G] [Module S G]

/-- **A forked threshold forger extracts the group secret.** Run the threshold adversary twice on the
SAME per-signer nonces `k` (so both runs share the group commitment `R = (Σ kᵢ)·g`) with two different
challenges `e ≠ e'`, producing two combined certificates. Each verifies under the group key `x·g`
(`frost_cert_verifies_under_group_key`, with `x = Σ lamᵢ·sharesᵢ`), so the pair are two special-sound
Schnorr transcripts — and the extractor recovers the group secret: `x·g = extractWitness(e,e',z,z')·g`.
The federation's group discrete log falls out of a threshold forgery. -/
theorem forked_threshold_cert_extracts_group_secret {ι : Type*}
    (g : G) (parts : Finset ι) (shares lam k : ι → S) (x e e' : S)
    (hrecon : x = ∑ i ∈ parts, lam i * shares i) (hne : e ≠ e') :
    x • g = extractWitness e e'
        (∑ i ∈ parts, (k i + e * (lam i * shares i)))
        (∑ i ∈ parts, (k i + e' * (lam i * shares i))) • g :=
  schnorr_special_soundness_extracts_dl g (x • g) ((∑ i ∈ parts, k i) • g) e e' _ _ hne
    (frost_cert_verifies_under_group_key g parts shares lam k x e hrecon)
    (frost_cert_verifies_under_group_key g parts shares lam k x e' hrecon)

#assert_axioms forked_threshold_cert_extracts_group_secret

/-- **The post-quantum capstone.** The same result over the lattice: run the Hermine threshold adversary
twice on the SAME masks with different challenges `c ≠ c'`; each combined certificate verifies under the
group key `A·s` (`HermineThreshold.hermine_cert_verifies_under_group_key`), so the pair are two
special-sound Raccoon transcripts, and `Hermine.hermine_special_soundness_extracts_preimage` recovers a
preimage of the group key: `A (extractPreimage …) = A s`. So a forked Hermine threshold forger hands you
a preimage of the federation's group key `t = A·s` — the MSIS/MLWE break (its SHORTNESS the named carrier). -/
theorem forked_hermine_cert_extracts_group_secret {ι : Type*} {K : Type*} [Field K]
    {M P : Type*} [AddCommGroup M] [AddCommGroup P] [Module K M] [Module K P]
    (A : M →ₗ[K] P) (parts : Finset ι) (shares : ι → M) (lam : ι → K) (masks : ι → M)
    (s : M) (c c' : K) (hrecon : s = ∑ i ∈ parts, lam i • shares i) (hne : c ≠ c') :
    A (Dregg2.Crypto.Hermine.extractPreimage c c'
        (∑ i ∈ parts, (masks i + c • (lam i • shares i)))
        (∑ i ∈ parts, (masks i + c' • (lam i • shares i)))) = A s :=
  Dregg2.Crypto.Hermine.hermine_special_soundness_extracts_preimage
    A (A s) (A (∑ i ∈ parts, masks i)) c c' _ _ hne
    (Dregg2.Crypto.HermineThreshold.hermine_cert_verifies_under_group_key A parts shares lam masks s c hrecon)
    (Dregg2.Crypto.HermineThreshold.hermine_cert_verifies_under_group_key A parts shares lam masks s c' hrecon)

#assert_axioms forked_hermine_cert_extracts_group_secret

end Dregg2.Crypto.ThresholdForking
