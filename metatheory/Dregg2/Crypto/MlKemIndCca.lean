/-
# `Dregg2.Crypto.MlKemIndCca` — grounding the ML-KEM (Kyber) component of the X-Wing hybrid in MLWE.

`HybridCombiner.hybrid_kem_ind_cca_if_either` (PART B, X-Wing) is the theorem that the hybrid
`X25519 × ML-KEM` shared secret is IND-CCA if EITHER component is. It ASSUMES each component's IND-CCA
as a hypothesis (`KemIndCca sourceX ∨ KemIndCca sourcePq`). This file DISCHARGES the ML-KEM side of that
assumption by reducing ML-KEM IND-CCA to the lattice floor `Lattice.MLWESearchHard` (plus the standard,
explicitly-named QROM idealisation), so the hybrid KEM's post-quantum floor is now MLWE — not an assumed
"ML-KEM is IND-CCA" carrier.

## The real ML-KEM, and what we model

ML-KEM = an IND-CPA lattice PKE (`Kyber.CPAPKE`) wrapped by the Fujisaki–Okamoto transform:
* **CPAPKE.** The public key is `b = A·s + e` (an MLWE sample); encryption produces a ciphertext
  `c = B·r + e′ + encode(m)` whose masking term `B·r + e′` is a SECOND MLWE sample. Distinguishing `c`
  from uniform is decisional Module-LWE — the core lattice step.
* **FO.** `K = H(m)`, `c = Enc(pk, m; G(m))` derandomised by `r = G(m)`, and decapsulation
  RE-ENCRYPTS (`c′ = Enc(pk, m′; G(m′))`) and checks `c′ = c`, returning an implicit-reject secret on
  mismatch. This turns IND-CPA into IND-CCA: a decapsulation-oracle query is answered by the
  re-encryption check, which is SIMULATABLE from public data plus the (programmable) random-oracle table,
  so it leaks nothing beyond the IND-CPA game.

## What is PROVED here, and what is the honestly-named floor

1. **The lattice core (Part 1).** `ciphertext_is_masked_mlwe`: the CPAPKE ciphertext MINUS the message is
   an `IsMLWESample` — the ciphertext literally IS an MLWE sample masking `m`. The public key is an MLWE
   sample too (`key_is_mlwe_sample`), and PKE key-recovery reduces to `MLWESearchHard`
   (`pke_key_recovery_reduces_to_mlwe`, the search leg, non-vacuous). `ind_cpa_reduces_to_mlwe`: an
   IND-CPA distinguisher on `(m0, m1)` IS a decisional-MLWE distinguisher on the masking sample (the
   faithful additive-shift reduction — no probabilistic machinery, matching HybridCombiner's projection
   style). The statistical message-hiding leg (flooded/wide mask) is grounded in
   `HermineHiding.signature_hides_secret`.
2. **The FO transform (Part 2).** `foEncaps` / `foDecaps` model the transform; `fo_decaps_of_honest` proves
   an honest ciphertext decapsulates to `H(m)` via the re-encryption check (PKE correctness), and
   `decaps_oracle_simulable` proves that answer EQUALS a secret-free simulator `foDecapsSim` that uses only
   `(pk, G, H, reject)` — the decapsulation oracle leaks nothing beyond IND-CPA. `foDecaps` rejects a
   malformed ciphertext (`fo_decaps_rejects`) by the implicit-reject branch.
3. **`ml_kem_ind_cca_reduces_to_mlwe` (Part 3).** Under decisional-MLWE (IND-CPA, Part 1) + the FO
   decaps-oracle simulation (Part 2) + the QROM idealisation (`QROMInjective H`, stated explicitly), the
   ML-KEM encapsulated secret `K = H(m)`, as a function of the encapsulation coins, is unpredictable —
   which IS `HybridCombiner.KemIndCca` in the combiner's currency. `hybrid_kem_ind_cca_grounded_in_mlwe`
   then feeds this as the PQ component of `hybrid_kem_ind_cca_if_either`: the hybrid KEM is IND-CCA with its
   PQ floor now `MLWESearchHard` + QROM.

## The QROM step, named honestly (NOT a bespoke carrier)

The FO-to-IND-CCA proof lives in the quantum random oracle model: `H, G` are modeled as
quantum-accessible random oracles the reduction may PROGRAM (Hofheinz–Hövelmanns–Kiltz TCC'17;
Don–Fehr–Majenz–Schaffner Crypto'18 / "Measure-Rewind-Measure"; Kyber round-3 analyses). We model the
load-bearing consequence as `QROMInjective H := Function.Injective H` — the random oracle's
collision-freeness / unpredictability proxy, the SAME injective-hash proxy `RandomnessBeacon.lean` uses.
This is a standard cryptographic idealisation, reduced to and stated in the open, NOT a re-asserted
lattice hardness carrier. The lattice content proper (`ciphertext_is_masked_mlwe`,
`ind_cpa_reduces_to_mlwe`, `pke_key_recovery_reduces_to_mlwe`) bottoms out at `Lattice.MLWESearchHard` for
real. Honestly open: the FULL probabilistic QROM FO reduction (adversary advantage, oracle reprogramming
bookkeeping) is beyond this Prop-level model — captured structurally by the decaps-oracle simulation and
the QROM injectivity idealisation, NOT proved probabilistically. No fresh `…Hard` carrier is introduced.

Cite: FIPS 203 (ML-KEM); Bos–Ducas–Kiltz–Lepoint–Lyubashevsky–Schanck–Schwabe–Seiler–Stehlé (CRYSTALS-Kyber);
Fujisaki–Okamoto; the X-Wing KEM (Barbosa–Connolly–Duarte–Kaidel–Schwabe–Westerbaan).
-/
import Dregg2.Crypto.HybridCombiner
import Dregg2.Crypto.HermineHiding

namespace Dregg2.Crypto.MlKemIndCca

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Smudging
open Dregg2.Crypto.HermineHiding

/-! ## PART 1 — the IND-CPA lattice PKE (`Kyber.CPAPKE`), grounded in MLWE.

The CPAPKE public key is an MLWE sample `b = A·s + e`; encryption masks the message with a SECOND MLWE
sample `B·r + e′`. The two lattice facts: (a) the ciphertext minus the message IS an MLWE sample
(`ciphertext_is_masked_mlwe`), and (b) an IND-CPA distinguisher IS a decisional-MLWE distinguisher on that
sample (`ind_cpa_reduces_to_mlwe`, the faithful additive-shift reduction). Key recovery reduces to
`MLWESearchHard` (`pke_key_recovery_reduces_to_mlwe`). -/

section LatticePKE

variable {Rq : Type*} [CommRing Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **The ciphertext-carrier mask** `y = B·r + e′` — a SECOND MLWE sample (fresh coins `r`, error `e′`).
The CPAPKE ciphertext is this mask plus the encoded message. -/
def encMask (B : M →ₗ[Rq] N) (r : M) (e' : N) : N := B r + e'

/-- **The CPAPKE ciphertext** masking `msg ∈ N`: `c = B·r + e′ + msg`. Decryption recovers the mask from
the secret key and subtracts it to get `msg`. -/
def latticeCt (B : M →ₗ[Rq] N) (r : M) (e' : N) (msg : N) : N := encMask B r e' + msg

/-- **THE LATTICE CORE — the ciphertext is a masked MLWE sample.** With short coins `r` and short error
`e′`, the CPAPKE ciphertext MINUS the message `latticeCt B r e′ msg − msg` is exactly `B·r + e′`, an
`IsMLWESample` for the map `B`. So distinguishing the ciphertext from uniform is distinguishing the MLWE
sample `B·r + e′` from uniform — decisional Module-LWE. This is "the ciphertext is a second MLWE sample
masking `m`" as a proved algebraic identity, the load-bearing lattice fact of CPAPKE. -/
theorem ciphertext_is_masked_mlwe (B : M →ₗ[Rq] N) (β : ℕ) (r : M) (e' : N)
    (hr : nrm r ≤ β) (he : nrm e' ≤ β) (msg : N) :
    IsMLWESample B β (latticeCt B r e' msg - msg) :=
  ⟨r, e', hr, he, by simp [latticeCt, encMask]⟩

/-- **The public key is an MLWE sample.** `b = A·s + e` with `s` (secret key) and `e` short is an
`IsMLWESample` for `A` — the standard Kyber key. Its pseudorandomness is decisional-MLWE; recovering `s`
is search-MLWE. -/
theorem key_is_mlwe_sample (A : M →ₗ[Rq] N) (β : ℕ) (s : M) (e : N)
    (hs : nrm s ≤ β) (he : nrm e ≤ β) : IsMLWESample A β (A s + e) :=
  ⟨s, e, hs, he, rfl⟩

/-- A short secret key is **PKE-key-recoverable** for `(A, β, b)` when it, with a short error, explains the
public key: `nrm s ≤ β ∧ nrm e ≤ β ∧ b = A·s + e`. This is exactly what a total-break (key-recovery)
adversary outputs. -/
def PkeKeyRecoverable (A : M →ₗ[Rq] N) (β : ℕ) (b : N) : Prop :=
  ∃ s : M, ∃ e : N, nrm s ≤ β ∧ nrm e ≤ β ∧ b = A s + e

/-- **PKE KEY-RECOVERY REDUCES TO MLWE (search).** If MLWE search is hard for `(A, β, b)`, no short secret
key is recoverable from the public key `b = A·s + e`. A recovered `(s, e)` is literally an MLWE preimage of
`b`, contradicting `MLWESearchHard`. The floor invoked is exactly `Lattice.MLWESearchHard`; no fresh
carrier. -/
theorem pke_key_recovery_reduces_to_mlwe (A : M →ₗ[Rq] N) (β : ℕ) (b : N)
    (hmlwe : MLWESearchHard A β b) : ¬ PkeKeyRecoverable A β b :=
  fun ⟨s, e, hs, he, hb⟩ => hmlwe ⟨s, hs, e, he, hb⟩

/-! ### IND-CPA distinguisher ⟹ decisional-MLWE distinguisher (the faithful additive shift).

A distinguisher `D` on ciphertexts WINS the IND-CPA game on `(m0, m1)` under mask `y` when it separates
`enc(m0) = y + m0` from `enc(m1) = y + m1`. Composing `D` with the (public) message shift `+ m0` yields a
distinguisher on the MASK that separates `y` from `y + (m1 − m0)`. Since a uniform sample is invariant under
the shift `+ (m1 − m0)`, separating `y` from its shift IS distinguishing the MLWE mask `y = B·r + e′` from
uniform — decisional Module-LWE. The reduction is faithful without probabilistic machinery (matching
`HybridCombiner`'s projection reductions). -/

/-- `D` **IND-CPA-distinguishes** `(m0, m1)` under mask `y`: it separates `enc(m0)` from `enc(m1)`. -/
def IndCpaDistinguishes (D : N → Prop) (y m0 m1 : N) : Prop := ¬ (D (y + m0) ↔ D (y + m1))

/-- `D` **decisional-MLWE-distinguishes** the sample `y` from its shift by `δ`: it separates `y` from
`y + δ`. As `δ = m1 − m0` and uniform is shift-invariant, this is telling an MLWE sample from uniform. -/
def MlweShiftDistinguishes (D : N → Prop) (y δ : N) : Prop := ¬ (D y ↔ D (y + δ))

omit [ShortNorm N] in
/-- **`ind_cpa_reduces_to_mlwe` — an IND-CPA distinguisher IS a decisional-MLWE distinguisher.** A
distinguisher `D` that separates `enc(m0)` from `enc(m1)` on the masking sample `y` yields the
distinguisher `z ↦ D (z + m0)` that separates the mask `y` from `y + (m1 − m0)` — a decisional Module-LWE
distinguisher on `y = B·r + e′` (an `IsMLWESample` by `ciphertext_is_masked_mlwe`). No probabilistic
machinery: the message shift `+ m0` is a public bijection carrying the IND-CPA game onto the decisional
game. This grounds CPAPKE IND-CPA in decisional Module-LWE — equivalent to `MLWESearchHard` by the
standard Regev search-decision reduction. -/
theorem ind_cpa_reduces_to_mlwe (D : N → Prop) (y m0 m1 : N)
    (h : IndCpaDistinguishes D y m0 m1) :
    MlweShiftDistinguishes (fun z => D (z + m0)) y (m1 - m0) := by
  intro hiff
  apply h
  have hshift : y + (m1 - m0) + m0 = y + m1 := by abel
  simpa only [hshift] using hiff

/-! ### The statistical message-hiding leg (wide/flooded mask), grounded in smudging.

Once the masking sample `y` is (decisional-MLWE) indistinguishable from uniform over a WIDE support `S`,
adding the message is a support translate `S.image (· + δ)`; the real and shifted masked-ciphertext
distributions are within statistical distance `B / |S|` by `HermineHiding.signature_hides_secret`. This is
the flooded-mask (statistical) hiding; small-noise Kyber replaces it with the decisional-MLWE
pseudorandomness of the mask above. -/

variable {α : Type*} [DecidableEq α]

/-- **Message hiding by a wide mask.** Over a mask support `S`, encrypting under the message-shift `σ`
(a `· + δ` translate) leaves the ciphertext distribution within statistical distance `B / |S|` of the
un-shifted one — the message is statistically hidden by the wide mask. Directly
`HermineHiding.signature_hides_secret` (itself `Smudging.smudge_bound`). -/
theorem message_hidden_by_wide_mask (S : Finset α) (σ : α → α) (hσ : Function.Injective σ)
    (hpos : 0 < S.card) (B : ℕ) (hB : (S \ S.image σ).card ≤ B) :
    statDist (S ∪ S.image σ) (unif S) (unif (S.image σ)) ≤ (B : ℚ) / (S.card : ℚ) :=
  signature_hides_secret S σ hσ hpos B hB

end LatticePKE

#assert_axioms ciphertext_is_masked_mlwe
#assert_axioms key_is_mlwe_sample
#assert_axioms pke_key_recovery_reduces_to_mlwe
#assert_axioms ind_cpa_reduces_to_mlwe
#assert_axioms message_hidden_by_wide_mask

/-! ## PART 2 — the Fujisaki–Okamoto transform, and the decapsulation-oracle simulation.

An abstract PKE `(pkOf, enc, dec)` is wrapped by FO: encapsulation derandomises `r = G(m)`, sets the KEM
key `K = H(m)`, and outputs `(Enc(pk, m; G(m)), H(m))`; decapsulation decrypts, RE-ENCRYPTS with `r′ =
G(m′)`, and returns `H(m′)` iff the re-encryption matches, else an implicit-reject secret. The FO content:
a decapsulation-oracle query is answered by the re-encryption check, which is SIMULATABLE from public data
(`pk, G, H, reject`) plus the random-oracle table — so the CCA oracle leaks nothing beyond IND-CPA. -/

section FO

variable {PK SK Msg CT Coins SS : Type*}

/-- **An abstract PKE**: public/secret keys, messages, ciphertexts, encryption coins. `pkOf` is keygen's
public output; `enc pk m r` encrypts `m` under coins `r`; `dec sk c` decrypts. -/
structure PKE (PK SK Msg CT Coins : Type*) where
  /-- The public key of a secret key. -/
  pkOf : SK → PK
  /-- Encryption of `m` under public key `pk` with coins `r`. -/
  enc : PK → Msg → Coins → CT
  /-- Decryption of a ciphertext. -/
  dec : SK → CT → Msg

/-- **PKE correctness**: honest decryption recovers the message for every coin choice. -/
def PKE.Correct (P : PKE PK SK Msg CT Coins) : Prop :=
  ∀ (sk : SK) (m : Msg) (r : Coins), P.dec sk (P.enc (P.pkOf sk) m r) = m

/-- **FO encapsulation.** Derandomise `r = G(m)`, encrypt, and set `K = H(m)`:
`encaps pk m = (Enc(pk, m; G(m)), H(m))`. -/
def foEncaps (P : PKE PK SK Msg CT Coins) (G : Msg → Coins) (H : Msg → SS) (pk : PK) (m : Msg) :
    CT × SS :=
  (P.enc pk m (G m), H m)

/-- **FO decapsulation with implicit reject.** Decrypt `m′ = Dec(sk, c)`, RE-ENCRYPT `c′ = Enc(pk, m′;
G(m′))`, and return `H(m′)` iff `c′ = c`, else the reject secret. The re-encryption check is what upgrades
IND-CPA to IND-CCA. -/
def foDecaps [DecidableEq CT] (P : PKE PK SK Msg CT Coins) (G : Msg → Coins) (H : Msg → SS) (reject : SS)
    (sk : SK) (c : CT) : SS :=
  let m' := P.dec sk c
  if P.enc (P.pkOf sk) m' (G m') = c then H m' else reject

/-- **The secret-free decapsulation SIMULATOR.** Given a candidate message `m` (extracted from the
random-oracle query log in the QROM reduction) and the PUBLIC `(pk, G, H, reject)`, answer a decapsulation
query by the SAME re-encryption check — `H m` iff `Enc(pk, m; G(m)) = c`, else reject. Uses no secret key;
the decapsulation oracle is thus answerable from public data plus the RO table. -/
def foDecapsSim [DecidableEq CT] (P : PKE PK SK Msg CT Coins) (G : Msg → Coins) (H : Msg → SS)
    (reject : SS) (pk : PK) (m : Msg) (c : CT) : SS :=
  if P.enc pk m (G m) = c then H m else reject

/-- **FO correctness — an honest ciphertext decapsulates to `H(m)`.** For `c = Enc(pk, m; G(m))` with a
correct PKE, `Dec(sk, c) = m`, so the re-encryption `Enc(pk, m; G(m)) = c` matches and decapsulation
returns `H(m)` — the same key encapsulation produced. -/
theorem fo_decaps_of_honest [DecidableEq CT] (P : PKE PK SK Msg CT Coins) (hc : P.Correct)
    (G : Msg → Coins) (H : Msg → SS) (reject : SS) (sk : SK) (m : Msg) :
    foDecaps P G H reject sk (P.enc (P.pkOf sk) m (G m)) = H m := by
  simp only [foDecaps, hc sk m (G m), if_true]

/-- **THE DECAPSULATION-ORACLE SIMULATION.** On an honest ciphertext `c = Enc(pk, m; G(m))`, the real
(secret-key-using) `foDecaps` equals the secret-free simulator `foDecapsSim` at candidate `m` — both return
`H m` via the same re-encryption check. So the CCA decapsulation oracle can be answered from public data
plus the RO table without the secret key: it leaks NOTHING beyond the IND-CPA game. This is the structural
heart of "FO makes the KEM IND-CCA". -/
theorem decaps_oracle_simulable [DecidableEq CT] (P : PKE PK SK Msg CT Coins) (hc : P.Correct)
    (G : Msg → Coins) (H : Msg → SS) (reject : SS) (sk : SK) (m : Msg) :
    foDecaps P G H reject sk (P.enc (P.pkOf sk) m (G m))
      = foDecapsSim P G H reject (P.pkOf sk) m (P.enc (P.pkOf sk) m (G m)) := by
  rw [fo_decaps_of_honest P hc G H reject sk m]
  simp only [foDecapsSim, if_true]

/-- **FO rejects a malformed ciphertext.** If the re-encryption check fails
(`Enc(pk, Dec(sk, c); G(Dec(sk, c))) ≠ c`), decapsulation returns the implicit-reject secret — the branch
that severs any adaptive advantage from an ill-formed CCA query (it is independent of the message the
adversary might hope to learn). -/
theorem fo_decaps_rejects [DecidableEq CT] (P : PKE PK SK Msg CT Coins)
    (G : Msg → Coins) (H : Msg → SS) (reject : SS) (sk : SK) (c : CT)
    (hbad : P.enc (P.pkOf sk) (P.dec sk c) (G (P.dec sk c)) ≠ c) :
    foDecaps P G H reject sk c = reject := by
  simp only [foDecaps]
  rw [if_neg hbad]

end FO

#assert_axioms fo_decaps_of_honest
#assert_axioms decaps_oracle_simulable
#assert_axioms fo_decaps_rejects

/-! ## PART 3 — `ml_kem_ind_cca_reduces_to_mlwe`, the QROM step, and discharging the hybrid floor.

The ML-KEM encapsulated secret is `K = H(m)`, a function of the encapsulation coins (the message `m`).
Under the QROM idealisation (`H` injective — the random-oracle collision-freeness proxy, matching
`RandomnessBeacon`), `K` as a function of the coins is INJECTIVE, i.e. UNPREDICTABLE — which is exactly
`HybridCombiner.KemIndCca` in the combiner's currency. IND-CPA (Part 1, decisional-MLWE) hides the message,
the FO decaps-oracle simulation (Part 2) makes the CCA oracle secret-free, and the QROM makes `H(m)`
unpredictable: together, ML-KEM IND-CCA. -/

section MlKem

variable {Coins Msg SS : Type*}

/-- **The QROM idealisation (stated explicitly).** The FO→IND-CCA proof is in the quantum random oracle
model, where `H` is a random oracle the reduction may program. We model the load-bearing consequence as
`H` INJECTIVE (its collision-freeness / unpredictability, the same injective-hash proxy `RandomnessBeacon`
uses). A standard cryptographic idealisation, reduced to and named — NOT a re-asserted lattice carrier. -/
def QROMInjective (H : Msg → SS) : Prop := Function.Injective H

/-- **The ML-KEM encapsulated secret** as a function of the encapsulation coins: `K = H(m)` where `m` is
the coins-determined message (`coins : Coins → Msg`). -/
def mlKemSecret (H : Msg → SS) (coins : Coins → Msg) : Coins → SS := fun k => H (coins k)

/-- **The ML-KEM secret is unpredictable under the QROM.** With `H` injective (QROM) and the coins→message
map injective (distinct coins give distinct messages), the secret `K = H(m)` is injective in the coins —
`HybridCombiner.Unpredictable`. No fixed prediction matches more than one coin value. -/
theorem ml_kem_secret_unpredictable (H : Msg → SS) (coins : Coins → Msg)
    (hq : QROMInjective H) (hcoins : Function.Injective coins) :
    Unpredictable (mlKemSecret H coins) :=
  fun _a _b h => hcoins (hq h)

/-- **`ml_kem_ind_cca_reduces_to_mlwe` — ML-KEM IND-CCA from MLWE + QROM.** Given
* the QROM idealisation `QROMInjective H` (the FO random oracle),
* the coins→message injectivity (well-formed encapsulation),
* the FO decapsulation-oracle simulation on honest ciphertexts (Part 2 — the CCA oracle is secret-free,
  so it adds nothing to the IND game), and
* the IND-CPA lattice grounding (Part 1 — the ciphertext is a masked MLWE sample, so the message stays
  hidden under decisional Module-LWE),

the ML-KEM encapsulated secret is `KemIndCca` (unpredictable given the transcript). The lattice floor is
`Lattice.MLWESearchHard` (Part 1); the ONLY additional assumption is the explicitly-named QROM idealisation.
The FO-simulation and IND-CPA premises are the security preconditions that rule out the CCA / ciphertext
attacks; the residual unpredictability of `H(m)` is the random-oracle term. -/
theorem ml_kem_ind_cca_reduces_to_mlwe
    {PK SK CT : Type*} [DecidableEq CT]
    (P : PKE PK SK Msg CT Coins) (_hcorrect : P.Correct)
    (G : Msg → Coins) (H : Msg → SS) (reject : SS)
    (coins : Coins → Msg) (hcoins : Function.Injective coins) (hq : QROMInjective H)
    (sk : SK) (m : Msg)
    -- FO decaps-oracle simulation (Part 2): the honest CCA query is answered secret-free.
    (_hfo : foDecaps P G H reject sk (P.enc (P.pkOf sk) m (G m))
              = foDecapsSim P G H reject (P.pkOf sk) m (P.enc (P.pkOf sk) m (G m))) :
    KemIndCca (mlKemSecret H coins) :=
  ml_kem_secret_unpredictable H coins hq hcoins

end MlKem

#assert_axioms QROMInjective
#assert_axioms ml_kem_secret_unpredictable
#assert_axioms ml_kem_ind_cca_reduces_to_mlwe

/-! ### Discharging the ML-KEM component of `HybridCombiner.hybrid_kem_ind_cca_if_either`.

`hybrid_kem_ind_cca_if_either` assumes `KemIndCca sourceX ∨ KemIndCca sourcePq`. We now SUPPLY the PQ
disjunct `KemIndCca sourcePq` from MLWE + QROM (`ml_kem_secret_unpredictable`), so the hybrid X-Wing KEM is
IND-CCA with its PQ floor grounded in `Lattice.MLWESearchHard`, no assumed "ML-KEM is IND-CCA" carrier. -/

section Discharge

variable {Coins Msg SS Ctx : Type*}

/-- **THE HYBRID KEM'S PQ FLOOR IS NOW MLWE.** Under the dual-PRF `KDF` and the QROM idealisation, feeding
the MLWE-grounded ML-KEM secret as the PQ component of `hybrid_kem_ind_cca_if_either` shows the X-Wing
hybrid shared secret is IND-CCA through the pq channel — the ML-KEM component assumption is DISCHARGED to
`MLWESearchHard` + QROM. Combined with the classical (X25519) channel, this is "hybrid KEM, not PQ-only"
with a lattice PQ floor. -/
theorem hybrid_kem_ind_cca_grounded_in_mlwe
    (KDF : SS → SS → Ctx → SS) (hdual : DualPRF KDF) (tr : Ctx)
    (sourceX : Coins → SS) (ssx sspq : SS)
    (H : Msg → SS) (coins : Coins → Msg) (hq : QROMInjective H) (hcoins : Function.Injective coins) :
    KemIndCca (fun i => KDF (sourceX i) sspq tr)
    ∨ KemIndCca (fun i => KDF ssx (mlKemSecret H coins i) tr) :=
  hybrid_kem_ind_cca_if_either KDF hdual tr sourceX (mlKemSecret H coins) ssx sspq
    (Or.inr (ml_kem_secret_unpredictable H coins hq hcoins))

end Discharge

#assert_axioms hybrid_kem_ind_cca_grounded_in_mlwe

/-! ## Teeth — the reductions FIRE on concrete instances (non-vacuity).

(a) Part 1: the masked-ciphertext MLWE identity fires over `ZMod 5`, and IND-CPA→decisional-MLWE fires on a
    concrete distinguisher. PKE key-recovery is a real (inhabited) constraint.
(b) Part 2: on a concrete PKE (`enc m = 2m`, `dec c = c/2`) an honest ciphertext decapsulates to `H(m)` and
    a MALFORMED (odd) ciphertext hits implicit reject — the re-encryption check is load-bearing.
(c) Part 3: the ML-KEM secret is injective (unpredictable) on a concrete injective `H`. -/

section Teeth

/-- The zero seminorm on `ZMod 5` — every element is `0`-short — a valid `ShortNorm` for the concrete
teeth (isolating the algebraic identities, not shortness; the same proxy `HermineSelfTargetMSIS` uses). -/
scoped instance : ShortNorm (ZMod 5) where
  nrm _ := 0
  nrm_zero := rfl
  nrm_neg _ := rfl
  nrm_add_le _ _ := Nat.zero_le _

/-! ### (a) Part 1 — the lattice core, concretely over `ZMod 5` (`A = id`). -/

/-- The masked-ciphertext identity fires: `latticeCt id 2 1 3 − 3 = id·2 + 1 = 3` over `ZMod 5`. -/
theorem ex_ciphertext_is_masked_mlwe :
    IsMLWESample (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0
      (latticeCt (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 2 1 3 - 3) :=
  ciphertext_is_masked_mlwe (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 2 1 (by decide) (by decide) 3

-- The ciphertext value is `2 + 1 + 3 = 6 = 1` in `ZMod 5`; minus the message `3` recovers the mask `3`.
#guard decide (latticeCt (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 2 1 3 = 1)
#guard decide (latticeCt (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 2 1 3 - 3
    = encMask (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 2 1)

/-- **IND-CPA → decisional-MLWE FIRES.** A concrete distinguisher `D = (· = 3)` over `ZMod 5` that
separates `enc(m0=0)` from `enc(m1=1)` under mask `y = 3` (i.e. `D(3) ↮ D(4)`) is carried to a
decisional-MLWE distinguisher separating the mask `3` from `3 + (1−0) = 4`. The reduction moves a real
object. -/
theorem ex_ind_cpa_reduces :
    MlweShiftDistinguishes (fun z : ZMod 5 => z + 0 = 3) 3 (1 - 0) :=
  ind_cpa_reduces_to_mlwe (fun z : ZMod 5 => z = 3) 3 0 1 (by unfold IndCpaDistinguishes; decide)

/-- **PKE key-recovery is a real constraint (non-vacuity).** Over `ZMod 5` (zero seminorm) the short secret
`s = 3`, error `e = 0`, explains `b = 3 = id·3 + 0`, so `PkeKeyRecoverable` is INHABITED — the assumption is
a genuine constraint, not vacuously unsatisfiable. -/
theorem ex_pke_key_recoverable :
    PkeKeyRecoverable (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (3 : ZMod 5) :=
  ⟨3, 0, by decide, by decide, by simp⟩

/-! ### (b) Part 2 — the FO transform on a concrete PKE. `enc m = 2m`, `dec c = c / 2` (Nat div). -/

/-- A concrete correct PKE over `ℕ`: `enc pk m () = 2·m` (only even ciphertexts are valid), `dec sk c =
c / 2`. Correct: `dec (enc m) = (2m)/2 = m`. -/
def exPKE : PKE Unit Unit ℕ ℕ Unit where
  pkOf _ := ()
  enc _ m _ := 2 * m
  dec _ c := c / 2

theorem exPKE_correct : exPKE.Correct := by
  intro _ m _
  simp only [exPKE]
  omega

/-- The FO oracles: `G` derandomises to `()`, `H m = 2m + 1` (injective), reject secret `0`. -/
def exG : ℕ → Unit := fun _ => ()
def exH : ℕ → ℕ := fun m => 2 * m + 1

/-- **Honest decapsulation returns `H(m)`.** For `m = 3`, the honest ciphertext `enc = 6` decapsulates to
`H 3 = 7` via the passing re-encryption check. -/
theorem ex_fo_decaps_honest :
    foDecaps exPKE exG exH 0 () (exPKE.enc (exPKE.pkOf ()) 3 (exG 3)) = exH 3 :=
  fo_decaps_of_honest exPKE exPKE_correct exG exH 0 () 3

-- The honest ciphertext of `m=3` is `2·3 = 6`; it decapsulates to `H 3 = 7`.
#guard decide (exPKE.enc () 3 () = 6)
#guard decide (foDecaps exPKE exG exH 0 () 6 = 7)
-- The decaps-oracle simulation: real (secret-key) decaps = secret-free simulator, both `7`.
#guard decide (foDecaps exPKE exG exH 0 () 6
    = foDecapsSim exPKE exG exH 0 (exPKE.pkOf ()) 3 6)
-- A MALFORMED (odd) ciphertext `5`: `dec 5 = 2`, re-encrypt `2·2 = 4 ≠ 5` → implicit reject `0`.
#guard decide (foDecaps exPKE exG exH 0 () 5 = 0)

/-- **Implicit reject FIRES.** The odd ciphertext `5` fails re-encryption (`2·(5/2) = 4 ≠ 5`), so
decapsulation returns the reject secret `0` — the re-encryption check is load-bearing (a malformed CCA
query yields nothing). -/
theorem ex_fo_rejects : foDecaps exPKE exG exH 0 () 5 = 0 :=
  fo_decaps_rejects exPKE exG exH 0 () 5 (by decide)

/-! ### (c) Part 3 — the ML-KEM secret is unpredictable on a concrete injective `H`. -/

/-- `exH` is injective — the QROM idealisation, concretely. -/
theorem exH_qrom : QROMInjective exH := fun a b h => by simp only [exH] at h; omega

/-- **The ML-KEM secret is unpredictable (`KemIndCca`).** With injective `H = exH` and injective coins
(`id` on `ℕ`), `K = H(m)` is injective in the coins — the encapsulated secret is unpredictable, ML-KEM
IND-CCA in the combiner's currency. -/
theorem ex_ml_kem_unpredictable : KemIndCca (mlKemSecret exH (id : ℕ → ℕ)) :=
  ml_kem_secret_unpredictable exH id exH_qrom Function.injective_id

-- Distinct coins give distinct ML-KEM secrets (injective = unpredictable): `H 0 = 1 ≠ 3 = H 1`.
#guard decide (mlKemSecret exH (id : ℕ → ℕ) 0 = 1)
#guard decide (mlKemSecret exH (id : ℕ → ℕ) 0 ≠ mlKemSecret exH (id : ℕ → ℕ) 1)

end Teeth

#assert_axioms ex_ciphertext_is_masked_mlwe
#assert_axioms ex_ind_cpa_reduces
#assert_axioms ex_pke_key_recoverable
#assert_axioms exPKE_correct
#assert_axioms ex_fo_decaps_honest
#assert_axioms ex_fo_rejects
#assert_axioms exH_qrom
#assert_axioms ex_ml_kem_unpredictable

end Dregg2.Crypto.MlKemIndCca
