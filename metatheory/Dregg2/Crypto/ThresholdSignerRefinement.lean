/-
# `Dregg2.Crypto.ThresholdSignerRefinement` — the DEPLOYED Hermine threshold signer refines the TS-UF-0 model.

The DOWN direction for the threshold signer, mirroring `Dregg2.Crypto.DreggPqRefinement` (deployed `dregg-pq`
signer ⟶ abstract `SigScheme`), `Dregg2.Crypto.XmVrfRefinement` (deployed XM-VRF ⟶ abstract `VRF`), and
`Dregg2.Crypto.HashRandRefinement` (deployed beacon ⟶ `RandomnessBeacon`). Here the deployed object is the
**Hermine Raccoon 2-round commit-then-reveal threshold signer** (`crypto-hermine/src/threshold.rs`), whose
observable surface this file connects to the FULL concurrent + adaptive TS-UF-0 model
(`Dregg2.Crypto.HermineTSUF`, `Dregg2.Crypto.AdaptiveTSUF`) — so those theorems' unforgeability applies to the
CODE, not just the model, and bottoms out at the SAME true floor `MSIS ∨ MLWE ∨ HashCR`.

## WHICH signer is DEPLOYED — the explicit determination

Two candidate threshold signers live in the tree:

  1. **crypto-hermine's Raccoon 2-round signer** (`hermine_sign_raccoon` / `RaccoonSignSession` /
     `verify_hermine_raccoon`): a lattice threshold signature. Round 1 broadcasts the hash commitment
     `cm_i = H("dregg-raccoon-commit" ‖ i ‖ w_i)` to each signer's one-time flooded-mask nonce commitment
     `w_i = A·y_i`; Round 2 REVEALS `w_i` (checked against `cm_i`, an equivocation named+aborted), sums
     `w = Σ w_i`, derives the short-ternary challenge `c`, and each signer responds
     `z_i = y_i + c·(λ_i·s_i)`; the certificate `(w, c, z = Σ z_i)` is verified by the group-key relation
     `A·z = w + c·t`. TS-UF-0 IS its security model. The federation EXPOSES it as the compact post-quantum
     quorum half (`QuorumScheme::HermineHybrid` / `HermineHybridQC` in `federation/src/frost.rs`).

  2. **federation/src/frost.rs's quorum signer**: the FROST/Schnorr `frost_sign` rests on the DL carrier and is
     single-ceremony (no RFC 9591 binding factors); the LIVE-wired federation quorum is `QuorumScheme::HybridVotes`
     — a COUNT-based quorum of per-member ed25519 votes + per-member ML-DSA-65 signatures (`MlDsaSigningKey`),
     where threshold is enforced by counting distinct valid signatures, NOT by Shamir/Lagrange reconstruction.

**We refine #1, the Hermine Raccoon signer**, and state the honest deployment status precisely: it is
`QuorumScheme::HermineHybrid`, a STAGED reference (default-off, pre-audit — toy challenge hash, reference
sampling), while the live-wired quorum is the count-based `HybridVotes`. #1 is the correct target because
TS-UF-0 (concurrent, adaptive, loss-free, forking) is *precisely* its security model and its floor is the
post-quantum MSIS/MLWE floor this campaign is about; #2's PQ half (per-member ML-DSA) is already refined
per-signature by `DreggPqRefinement` (EUF-CMA → MSIS), and its classical/count legs rest on the DL floor —
neither is a lattice threshold signature.

## The honest boundary — UNIFORM vs GAUSSIAN flooding (a parameter/statistical-distance matter, not a gap)

The deployed Raccoon ceremony's one-time masks (`RaccoonSigner::round1`) are sampled UNIFORM over the wide
centered range `[−M/2, M/2)` (`sample_wide_mask`, width `MASK_WIDTH_WIDE`). That is EXACTLY the leg the Lean
masking pillar proves: `HermineHintMLWE.HintTranscriptSimulatable` is the uniform+total-variation smudging
bound (`signature_hides_secret`, `TV ≤ ‖c·Δs‖∞ / M` per coefficient), grounded in `MLWESearchHard` by
`hint_mlwe_reduces_to_mlwe`. So the deployed sampler and the modeled masking MATCH — no mismatch to launder.
The code ALSO offers a discrete-Gaussian variant (`hermine_sign_gaussian`) that production Raccoon/Hermine
prefers for its TIGHTER Rényi-divergence parameter accounting (`TV ≲ ‖c·Δs‖∞ / (σ√(2π))` per coefficient). The
cost of the uniform choice the model pins is purely quantitative: to buy the same per-query hiding, uniform
needs a wider `M` than Gaussian needs a `σ` — a PARAMETER-SIZING / statistical-distance engineering matter
(`MASK_WIDTH_WIDE` already carries real headroom, `signature.rs` shortness accounting), NOT an open problem
and NOT a fresh trusted boundary. The short-ternary challenge (`‖c‖∞ ≤ 1`) the smudging shift bound needs is
matched by the model's `nrm c ≤ β`. The reference challenge hash is the SAME trusted-RO/HashCR floor named in
the commit-reveal pillar, not a new carrier.

## What this file CONNECTS

  * `ThresholdSignerApi` — the deployed observable surface as function shapes only (the public matrix `A`, the
    group key `t = A·s`, the threshold, the Round-1 hash commitment `H(i, w_i)`, the fail-closed Bool group-key
    verify `A·z = w + c·t`), matched to the Rust signatures; NO proof fields.
  * `IsHermineVerify` — the observable-behaviour capture: the Bool verify is `true` exactly when the Prop
    relation `HermineThreshold.verify A t w c z` holds (the honest instance proves it by construction).
  * `threshold_signer_refines` — the model faithfully abstracts the contract (keygen/commit-reveal/verify all
    agree). `Refines` has TEETH: a model that drops the commit-then-reveal binding does NOT refine.
  * `deployed_forgery_accepts` — the bridge: the DEPLOYED Bool verify accepting (plus shortness) IS a TS-UF-0
    SelfTargetMSIS accept, so the inheritance is about the actual code's verifier.
  * `threshold_signer_concurrent_ts_uf_0` / `threshold_signer_adaptive_ts_uf_lossfree` — the INHERITANCE: the
    deployed signer inherits concurrent AND adaptive (loss-free, Unmasking-TRaccoon) TS-UF-0, its security
    reducing to `¬ HashCR ∨ (an MSIS solution on [A | t]) ∨ ¬ MLWESearchHard` — the floor.

Reads matched to the actual Rust (`crypto-hermine/src/threshold.rs`): `RaccoonSigner::round1` /
`raccoon_commitment` (the Round-1 hash commitment), `RaccoonSignSession::combine_reveals` (the equivocation
catch = commit-binding), `partial_response` (`z_i = y_i + c·(λ_i·s_i)`), `sign_ceremony`
(`w = A·(Σ y_i)`, `z = Σ z_i`), and `verify_hermine_raccoon` / `crate::verify` (`A·z = w + c·t`). The only
irreducible objects are the standard `MSIS`/`MLWESearchHard`/`HashCR`; everything else is proved glue or an
inherited model game.
-/
import Dregg2.Crypto.AdaptiveTSUF
import Dregg2.Crypto.HermineThreshold

namespace Dregg2.Crypto.ThresholdSignerRefinement

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.HermineHintMLWE
open Dregg2.Crypto.HermineTSUF
open Dregg2.Crypto.AdaptiveTSUF
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble)
open Dregg2.Crypto.ProbCrypto (DecisionMLWEHardQuant)

/-! ## PART 1 — the deployed Hermine threshold-signer API surface, as a Lean contract.

The OBSERVABLE surface (`crypto-hermine/src/threshold.rs`), stated as function shapes only — no proof
obligations baked in, because the primitive's guarantees are the inherited model games, named separately:

  * `A : M →ₗ[Rq] N`   ⇐ the public matrix (the shared CRS the group key `t = A·s` is built over).
  * `groupKey : N`   ⇐ `t = A·s`, the federation's Hermine group public key.
  * `thr : ℕ`   ⇐ the reconstruction threshold (any `thr` signers reconstruct, any `thr−1` learn nothing).
  * `round1Commit : Idx → N → Cm`   ⇐ `raccoon_commitment(i, w_i) = H("…commit" ‖ i ‖ w_i)` — the Round-1
    hash commitment to the nonce commitment `w_i = A·y_i`, the rushing/concurrency defense.
  * `verify : N → Rq → M → Bool`   ⇐ `verify_hermine_raccoon` / `crate::verify` — the fail-closed Bool
    group-key check `A·z = w + c·t`. It returns a `Bool` (never a `Prop`, never a panic): "fail-CLOSED" is
    captured by `verify` being TOTAL and Bool-valued. -/

/-- The observable `crypto-hermine` Raccoon-threshold API surface, matched to the Rust signatures. Carries NO
proof fields — its unforgeability is the inherited TS-UF-0 game, reduced to the floor below. -/
structure ThresholdSignerApi (Rq : Type*) [CommRing Rq] (M N : Type*) [AddCommGroup M] [Module Rq M]
    [AddCommGroup N] [Module Rq N] (Idx Cm : Type*) where
  /-- The public matrix `A : M →ₗ[Rq] N` (the CRS the group key is `A·s`). -/
  A : M →ₗ[Rq] N
  /-- The group public key `t = A·s`. -/
  groupKey : N
  /-- The reconstruction threshold `thr`: any `thr` signers reconstruct, any `thr−1` learn nothing. -/
  thr : ℕ
  /-- `raccoon_commitment(i, w_i) = H("…commit" ‖ i ‖ w_i)` — the Round-1 hash commitment. -/
  round1Commit : Idx → N → Cm
  /-- `verify_hermine_raccoon` — the fail-closed Bool group-key verifier `A·z = w + c·t`. -/
  verify : N → Rq → M → Bool

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Idx Cm : Type*}

/-- The TS-UF-0 game keygen read off the API contract: the public matrix, the group key, the threshold.
Mirror of `dreggPqSigScheme`'s `pkOf`. -/
@[reducible] def ThresholdSignerApi.keygen (api : ThresholdSignerApi Rq M N Idx Cm) : KeyGen Rq M N :=
  ⟨api.A, api.groupKey, api.thr⟩

/-- The Round-1 commit-reveal surface read off the API contract: `H(i, w_i)`, the shared `CommitReveal`
carrier the whole tree's binding/`HashCR` machinery rides. The equivocation catch
(`RaccoonSignSession::combine_reveals`) is exactly `commitment_binding` / `HashCR`. -/
@[reducible] def ThresholdSignerApi.commitReveal (api : ThresholdSignerApi Rq M N Idx Cm) :
    CommitReveal Idx N Cm :=
  ⟨api.round1Commit⟩

/-! ### THE OBSERVABLE-BEHAVIOUR CAPTURE — the Bool verify IS the group-key relation.

`IsHermineVerify` says the API's fail-closed `Bool` verify is `true` exactly when the group-key relation
`A·z = w + c·t` holds — a faithful description of what `verify_hermine_raccoon` DOES, not a trusted floor;
the honest instance proves it by construction (`decide_eq_true_iff`). -/

/-- **The observable-behaviour capture.** The API's Bool `verify w c z` is `true` iff the Prop relation
`HermineThreshold.verify A t w c z` (i.e. `A·z = w + c·t`) holds. This is `IsMerkleVerify`'s / `IsHashRandOpen`'s
analogue for the threshold signer. -/
def IsHermineVerify (api : ThresholdSignerApi Rq M N Idx Cm) : Prop :=
  ∀ w c z, api.verify w c z = true ↔ HermineThreshold.verify api.A api.groupKey w c z

/-! ## PART 2 — honest correctness: an honest `thr`-of-`n` certificate verifies.

The deployed signer's honest ceremony forms `w = A·(Σ yᵢ)` and `z = Σ (yᵢ + c·(λᵢ·sᵢ))` over a signing subset
whose Lagrange coefficients reconstruct the group secret `s = Σ λᵢ·sᵢ`. `HermineThreshold`'s unconditional
module algebra (`hermine_cert_verifies_under_group_key`) says that certificate satisfies `A·z = w + c·t`, so
the deployed Bool verify accepts it — EXACTLY when the shares reconstruct the group secret. -/

omit [ShortNorm Rq] [ShortNorm M] [ShortNorm N] in
/-- **HONEST `thr`-OF-`n` CORRECTNESS.** For any signing subset `parts` whose Lagrange coefficients `lam`
reconstruct the group secret `s = Σ_{i∈parts} lam i • shares i` (with `t = A·s`), the honest certificate
`w = A·(Σ masks)`, `z = Σ (masks i + c·(lam i • shares i))` VERIFIES under the deployed Bool verifier. The
deployed `hermine_sign_raccoon` output is accepted by `verify_hermine_raccoon`, reduced to the module algebra
`hermine_cert_verifies_under_group_key`. -/
theorem honest_cert_verifies (api : ThresholdSignerApi Rq M N Idx Cm) (hv : IsHermineVerify api)
    {ι : Type*} (parts : Finset ι) (shares : ι → M) (lam : ι → Rq) (masks : ι → M) (s : M) (c : Rq)
    (hrecon : s = ∑ i ∈ parts, lam i • shares i) (hkey : api.groupKey = api.A s) :
    api.verify (api.A (∑ i ∈ parts, masks i)) c
      (∑ i ∈ parts, (masks i + c • (lam i • shares i))) = true := by
  rw [hv, hkey]
  exact HermineThreshold.hermine_cert_verifies_under_group_key api.A parts shares lam masks s c hrecon

/-! ## PART 3 — THE REFINEMENT RELATION: the model faithfully abstracts the API contract.

`Refines api S` says the model `S` reads back EXACTLY the API's public behaviour: same keygen data, the same
Round-1 commit-reveal surface, and the model's `Prop`-verify matching the API's `Bool`-verify pointwise.
`threshold_signer_refines` proves the canonical model `api.model` refines by construction. The relation has
TEETH: a model that drops the commit-then-reveal binding (a constant, non-binding commit) fails to refine
(`badModel_not_refines`), so `Refines` genuinely distinguishes a faithful abstraction — it is not vacuous. -/

/-- The modeled threshold signer: the TS-UF-0 keygen, the Round-1 commit-reveal carrier, and the group-key
verify RELATION (a `Prop`). The abstract object the deployed API is connected to. -/
structure ThresholdSignerModel (Rq : Type*) [CommRing Rq] (M N : Type*) [AddCommGroup M] [Module Rq M]
    [AddCommGroup N] [Module Rq N] (Idx Cm : Type*) where
  /-- The TS-UF-0 keygen (public matrix, group key, threshold). -/
  kg : KeyGen Rq M N
  /-- The Round-1 commit-reveal surface (`H(i, w_i)`). -/
  cr : CommitReveal Idx N Cm
  /-- The group-key verify relation `A·z = w + c·t`. -/
  verifyRel : N → Rq → M → Prop

/-- **THE REFINEMENT RELATION.** The model `S` faithfully abstracts the API contract `api`: (1) the keygen
data agrees, (2) the Round-1 commit-reveal agrees, (3) the model's `Prop`-verify holds iff the API's
`Bool`-verify is `true`. A model that mis-reads any clause does NOT refine. -/
def Refines (api : ThresholdSignerApi Rq M N Idx Cm) (S : ThresholdSignerModel Rq M N Idx Cm) : Prop :=
  S.kg.A = api.A ∧ S.kg.t = api.groupKey ∧ S.kg.thr = api.thr ∧
  (∀ i w, S.cr.H i w = api.round1Commit i w) ∧
  (∀ w c z, S.verifyRel w c z ↔ api.verify w c z = true)

/-- The canonical model built from the API contract: keygen/commit-reveal from the contract, and the group-key
verify relation `HermineThreshold.verify A t`. Mirror of `dreggPqSigScheme` / `xmVrfModel`. -/
@[reducible] def ThresholdSignerApi.model (api : ThresholdSignerApi Rq M N Idx Cm) :
    ThresholdSignerModel Rq M N Idx Cm :=
  ⟨api.keygen, api.commitReveal, HermineThreshold.verify api.A api.groupKey⟩

omit [ShortNorm Rq] [ShortNorm M] [ShortNorm N] in
/-- **THE REFINEMENT HOLDS.** `api.model` is a faithful abstraction of its API contract — the keygen and
commit-reveal clauses are definitional (the model is BUILT from the contract), and the verify clause is
exactly the observable capture `IsHermineVerify`. The beachhead: the deployed Raccoon-threshold surface and the
proved TS-UF-0 model are one connected object. Mirror of `dregg_pq_refines_sigscheme`. -/
theorem threshold_signer_refines (api : ThresholdSignerApi Rq M N Idx Cm) (hv : IsHermineVerify api) :
    Refines api api.model :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun w c z => (hv w c z).symm⟩

/-! ## PART 4 — the bridge and the inheritance: the deployed signer inherits concurrent + adaptive TS-UF-0. -/

/-- **THE BRIDGE — the deployed Bool verify accepting IS a TS-UF-0 SelfTargetMSIS accept.** A forger whose
commitment/challenge/response are short and whose output passes the DEPLOYED Bool verifier
(`api.verify … = true`) is an accepting `Accepts` instance for the model game. So the inheritance below is
about the ACTUAL code's verifier, not merely the model relation. -/
theorem deployed_forgery_accepts (api : ThresholdSignerApi Rq M N Idx Cm) (hv : IsHermineVerify api)
    {Msg : Type*} (β : ℕ) (F : Forger Rq M N Msg) (ρ : ℕ → Rq)
    (hz : nrm (F.response ρ) ≤ β) (hc : nrm (ρ F.challengeIdx) ≤ β) (hw : nrm (F.commitment ρ) ≤ β)
    (hver : api.verify (F.commitment ρ) (ρ F.challengeIdx) (F.response ρ) = true) :
    Accepts api.A api.groupKey β F ρ :=
  ⟨hz, hc, hw, (hv (F.commitment ρ) (ρ F.challengeIdx) (F.response ρ)).mp hver⟩

/-- **THE DEPLOYED SIGNER INHERITS CONCURRENT TS-UF-0 → the floor.** Specializes
`HermineTSUF.concurrent_ts_uf_0_reduces` to the deployed API's keygen `(A, t, thr)` and its Round-1
commit-reveal. A concurrent TS-UF-0 forger against the deployed signer — static `≤ thr−1` corruption, a
concurrent signing oracle, and a fresh forgery whose fork succeeds — implies
`¬ HashCR (deployed commit-reveal) ∨ (an MSIS solution on [A | t]) ∨ ¬ MLWESearchHard`. Each attack mode
routes to its break: equivocating a Round-1 commitment → `HashCR` (the rushing defense); recovering the honest
secret from the flooding hints → `MLWESearchHard`; a forked fresh forgery → `MSIS`. All three disjuncts are
load-bearing. -/
theorem threshold_signer_concurrent_ts_uf_0 (api : ThresholdSignerApi Rq M N Idx Cm)
    (β : ℕ) {Msg : Type*} (F : Forger Rq M N Msg)
    (outcome :
      (∃ (cm : Cm) (i : Idx) (w w' : N), w ≠ w' ∧
        api.commitReveal.opens cm i w ∧ api.commitReveal.opens cm i w') ∨
      (HintRecoverable api.A β api.groupKey) ∨
      (∃ (ρ : ℕ → Rq) (c' : Rq), ρ F.challengeIdx ≠ c' ∧
        Accepts api.A api.groupKey β F ρ ∧ Accepts api.A api.groupKey β F (F.rewind ρ c'))) :
    (¬ HashCR api.commitReveal)
    ∨ (∃ v, IsMSISSolution (augmented api.A api.groupKey) ((β + β) + (β + β)) v)
    ∨ (¬ MLWESearchHard api.A β api.groupKey) :=
  concurrent_ts_uf_0_reduces api.keygen β api.commitReveal F outcome

/-- **THE DEPLOYED SIGNER INHERITS ADAPTIVE, LOSS-FREE TS-UF-0 → the floor.** Specializes
`AdaptiveTSUF.adaptive_ts_uf_reduces_lossfree` to the deployed API. An ADAPTIVE TS-UF-0 forger — corrupting
committee members DURING the run, interleaved with concurrent signing queries, transcript-dependently, up to
`thr−1` total — cannot win without breaking the floor, with NO combinatorial guessing loss. The reduction
simulates every member's partial signature from PUBLIC data up front (`simTranscriptCommit`, the
Unmasking-TRaccoon HVZK back-computation) and reveals shares on demand; `adaptive_erasure_from_simulation`
PROVES that simulated transcript is erasure-consistent with the ENTIRE realized corrupt set, so no corrupt set
need be guessed. The output carries the (PROVED) erasure witness alongside
`¬ HashCR ∨ (MSIS on [A | t]) ∨ ¬ MLWESearchHard`. The sole trusted base is the lattice/hash floor;
adaptivity is FREE. -/
theorem threshold_signer_adaptive_ts_uf_lossfree (api : ThresholdSignerApi Rq M N Idx Cm)
    (β : ℕ) {Msg : Type*} (F : Forger Rq M N Msg)
    {Fld : Type*} [DecidableEq Fld] (trace : List (AdaptiveStep Fld Msg))
    (memberKey : Fld → N) (chal : Fld → Rq) (resp : Fld → M)
    (outcome :
      (∃ (cm : Cm) (i : Idx) (w w' : N), w ≠ w' ∧
        api.commitReveal.opens cm i w ∧ api.commitReveal.opens cm i w') ∨
      (HintRecoverable api.A β api.groupKey) ∨
      (∃ (ρ : ℕ → Rq) (c' : Rq), ρ F.challengeIdx ≠ c' ∧
        Accepts api.A api.groupKey β F ρ ∧ Accepts api.A api.groupKey β F (F.rewind ρ c'))) :
    AdaptiveErasure api.A trace memberKey chal resp (simTranscriptCommit api.A memberKey chal resp)
    ∧ ((¬ HashCR api.commitReveal)
       ∨ (∃ v, IsMSISSolution (augmented api.A api.groupKey) ((β + β) + (β + β)) v)
       ∨ (¬ MLWESearchHard api.A β api.groupKey)) :=
  adaptive_ts_uf_reduces_lossfree api.keygen β api.commitReveal F trace memberKey chal resp outcome

/-- **THE DEPLOYED SIGNER INHERITS THE DECISIONAL NON-LEAKING PROPERTY → the proper distinguishing floor.**
Specializes `AdaptiveTSUF.adaptive_transcript_nonleaking_under_decision_floor` to the deployed API's public
matrix `api.A`. The Round-1/Round-2 masking of the deployed Raccoon signer (`sample_wide_mask`, the
uniform-smudging that hides each share on adaptive corruption) is a DECISIONAL guarantee: the sampled masked
transcript is INDISTINGUISHABLE from real. Under the proper decisional floor `DecisionMLWEHardQuant advSim`
(the transcript distinguisher's LWE-vs-uniform advantage ENSEMBLE negligible), the deployed signer's on-demand
share reveal is NON-LEAKING: the simulated transcript `simTranscriptCommit` is (a) algebraically
erasure-consistent with the ENTIRE realized corrupt set — PROVED — AND (b) computationally indistinguishable
from real (`Negl advSim`). This re-grounds the masking leg on the honest distinguishing floor, replacing the
SEARCH-`MLWESearchHard` grounding of `HintTranscriptSimulatable` for the indistinguishability content. The
forgery/secret-recovery leg remains SEARCH (handled by the search-quant threshold migration), not decisional. -/
theorem threshold_signer_transcript_nonleaking (api : ThresholdSignerApi Rq M N Idx Cm)
    {Msg : Type*} {Fld : Type*} [DecidableEq Fld] (trace : List (AdaptiveStep Fld Msg))
    (memberKey : Fld → N) (chal : Fld → Rq) (resp : Fld → M)
    {S : Type*} (advSim : S → Ensemble) (s : S) (hfloor : DecisionMLWEHardQuant advSim) :
    AdaptiveErasure api.A trace memberKey chal resp (simTranscriptCommit api.A memberKey chal resp)
    ∧ Negl (advSim s) :=
  adaptive_transcript_nonleaking_under_decision_floor api.A trace memberKey chal resp advSim s hfloor

omit [ShortNorm Rq] [ShortNorm M] [ShortNorm N] in
/-- **AN EQUIVOCATION BREAKS `HashCR`** — the rushing defense, on the DEPLOYED commit-reveal. Two DISTINCT
Round-2 reveals `w ≠ w'` of one Round-1 commitment `cm` witness a hash collision, so `HashCR` cannot hold —
exactly what `RaccoonSignSession::combine_reveals` catches (`RaccoonError::Equivocation`). The contrapositive
of the commit-binding that pins the two forgery transcripts to a single commitment. -/
theorem deployed_equivocation_breaks_hashcr (api : ThresholdSignerApi Rq M N Idx Cm)
    (cm : Cm) (i : Idx) (w w' : N) (hne : w ≠ w')
    (ho : api.commitReveal.opens cm i w) (ho' : api.commitReveal.opens cm i w') :
    ¬ HashCR api.commitReveal :=
  equivocation_breaks_hashcr api.commitReveal cm i w w' hne ho ho'

/-! ## Teeth — an honest `t`-of-`n` signature (respecting), sub-threshold rejection, and the rushing tooth.

`A = id`, group key `t = 1`, over `ZMod 5` (zero seminorm, isolating the algebraic content). Concretely:

(a) `goodApi` — an honest certificate VERIFIES (`honest_cert_verifies` fires; `#guard` on data), the refinement
    holds, and a forged response is REJECTED (verify is not always true).
(b) `sub_threshold_not_valid` — a sub-threshold set reconstructs a WRONG secret `s' ≠ s`, so its combined
    response solves the verify relation for the WRONG group key `t' = A·s'` and is REJECTED by the true
    group-key verifier — the deployed `sub_threshold_subset_cannot_forge`, as a theorem.
(c) THE RUSHING TOOTH is load-bearing two ways: a model that drops the commit-then-reveal binding does NOT
    refine (`badModel_not_refines`), and a signer with a constant (non-binding) Round-1 commit can EQUIVOCATE
    → `¬ HashCR` (`badBind_equivocation`). The concurrent + adaptive headlines FIRE on the deployed signer. -/

section Teeth

/-! ### (a) The honest, correct, refining instance. -/

/-- The honest deployed Raccoon-threshold API over `ZMod 5`: public matrix `id`, group key `1`, threshold `3`,
Round-1 commit `H(i, w) = (i, w)` (injective per index ⇒ `HashCR`), verify the fail-closed group-key `decide`. -/
def goodApi : ThresholdSignerApi (ZMod 5) (ZMod 5) (ZMod 5) ℕ (ℕ × ZMod 5) where
  A := LinearMap.id
  groupKey := 1
  thr := 3
  round1Commit i w := (i, w)
  verify w c z := decide ((LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) z = w + c • (1 : ZMod 5))

/-- `goodApi.verify` IS the group-key relation — `IsHermineVerify` holds by `decide_eq_true_iff`. -/
theorem goodApi_isHermineVerify : IsHermineVerify goodApi :=
  fun _ _ _ => decide_eq_true_iff

/-- `goodApi` refines its canonical model — the honest instance is one connected object with the TS-UF-0 model. -/
theorem goodApi_refines : Refines goodApi goodApi.model :=
  threshold_signer_refines goodApi goodApi_isHermineVerify

/-- **AN HONEST CERTIFICATE VERIFIES** (through the abstract theorem). A 1-of-1 reconstruction (`shares 1 = 1`,
`lam 1 = 1`, so `Σ lam • shares = 1 = s`, `t = id·1`) with mask `masks 1 = 3` and challenge `2` produces a
certificate the deployed verifier accepts — `honest_cert_verifies`, non-vacuously. -/
example :
    goodApi.verify (goodApi.A (∑ i ∈ ({1} : Finset ℕ), (fun _ => (3 : ZMod 5)) i)) 2
      (∑ i ∈ ({1} : Finset ℕ),
        ((fun _ => (3 : ZMod 5)) i + (2 : ZMod 5) • ((fun _ => (1 : ZMod 5)) i • (fun _ => (1 : ZMod 5)) i)))
      = true :=
  honest_cert_verifies goodApi goodApi_isHermineVerify ({1} : Finset ℕ)
    (fun _ => 1) (fun _ => 1) (fun _ => 3) 1 2 (by simp) (by simp [goodApi])

-- The honest signature VERIFIES (`z = w + c·t`: `2 = 0 + 2·1`, round-trip on concrete data).
#guard goodApi.verify 0 2 2 = true
-- A FORGED response (`3 ≠ 2`) is REJECTED — the verifier is non-vacuous (not always true).
#guard goodApi.verify 0 2 3 = false

/-! ### (b) Sub-threshold rejection — a below-threshold subset cannot produce a valid signature. -/

omit [ShortNorm Rq] [ShortNorm M] [ShortNorm N] in
/-- **SUB-THRESHOLD REJECTION.** If a below-threshold subset's Lagrange reconstruction lands on a WRONG secret
whose image `tSub = A·s'` differs from the true group key (so `w + c·tSub ≠ w + c·t`), then any response `z`
consistent with `tSub` (`A·z = w + c·tSub`) is REJECTED by the true group-key verifier. This is the deployed
`sub_threshold_subset_cannot_forge`: fewer than `thr` shares reconstruct a different degree-`<thr` polynomial's
value at `0`, so the combined response verifies for the wrong key and the group-key check fails. -/
theorem sub_threshold_not_valid (api : ThresholdSignerApi Rq M N Idx Cm) (hv : IsHermineVerify api)
    (w : N) (c : Rq) (z : M) (tSub : N)
    (hsub : HermineThreshold.verify api.A tSub w c z)
    (hne : w + c • tSub ≠ w + c • api.groupKey) :
    api.verify w c z = false := by
  cases hb : api.verify w c z with
  | false => rfl
  | true =>
    exfalso
    have hgood : HermineThreshold.verify api.A api.groupKey w c z := (hv w c z).mp hb
    rw [HermineThreshold.verify] at hsub hgood
    exact hne (hsub.symm.trans hgood)

/-- **SUB-THRESHOLD REJECTION FIRES.** A sub-threshold reconstruction giving `s' = 2` (`tSub = id·2 = 2 ≠ 1`):
the response `z = 4` verifies for the wrong key (`4 = 0 + 2·2`) but is REJECTED under the true group key `1`
(`0 + 2·2 = 4 ≠ 2 = 0 + 2·1`). Non-vacuous. -/
example : goodApi.verify 0 2 4 = false :=
  sub_threshold_not_valid goodApi goodApi_isHermineVerify 0 2 4 2
    (by simp only [HermineThreshold.verify, goodApi, LinearMap.id_coe, id_eq]; decide) (by decide)

-- The sub-threshold certificate (built for the wrong reconstructed key) is REJECTED by the true verifier.
#guard goodApi.verify 0 2 4 = false

/-! ### (c) The rushing tooth — commit-then-reveal binding is load-bearing. -/

/-- An UNFAITHFUL model whose Round-1 commit-reveal is CONSTANT (`H(i, w) = (0, 0)`) — it DROPS the binding, so
it cannot equivocation-catch. It is a `ThresholdSignerModel`, but does NOT abstract `goodApi` (whose commit is
the index-bound `(i, w)`). -/
def badModel : ThresholdSignerModel (ZMod 5) (ZMod 5) (ZMod 5) ℕ (ℕ × ZMod 5) where
  kg := goodApi.keygen
  cr := ⟨fun _ _ => (0, 0)⟩
  verifyRel := HermineThreshold.verify goodApi.A goodApi.groupKey

/-- **REFINEMENT TEETH (the rushing defense is load-bearing).** `badModel` does NOT refine `goodApi`: its
constant, non-binding commit disagrees with the deployed index-bound `round1Commit` at `(1, 5)`
(`(0,0) ≠ (1,5)`). So `Refines` genuinely rejects a signer that drops the commit-then-reveal binding — it is
not vacuously true. -/
theorem badModel_not_refines : ¬ Refines goodApi badModel := by
  rintro ⟨_, _, _, hcr, _⟩
  exact absurd (hcr 1 5) (by decide)

/-- A signer with a CONSTANT (non-binding) Round-1 commit — the limit of dropping the commit-then-reveal
binding (every `w` hashes to `0`). -/
def badBindApi : ThresholdSignerApi (ZMod 5) (ZMod 5) (ZMod 5) ℕ ℕ where
  A := LinearMap.id
  groupKey := 1
  thr := 3
  round1Commit _ _ := 0
  verify w c z := decide ((LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) z = w + c • (1 : ZMod 5))

/-- **THE RUSHING TOOTH.** The constant Round-1 commit lets two DISTINCT nonce commitments `w = 5 ≠ 7 = w'`
(i.e. `0 ≠ 2` in `ZMod 5`) BOTH open the commitment `0` — an equivocation, so `¬ HashCR`. Without
collision-resistant commit-then-reveal binding a rushing adversary equivocates freely; the deployed
`raccoon_commitment` (a real blake3 hash) is exactly what buys the binding. Non-vacuous: the reduction's
`HashCR` floor is load-bearing. -/
theorem badBind_equivocation : ¬ HashCR badBindApi.commitReveal :=
  deployed_equivocation_breaks_hashcr badBindApi (0 : ℕ) 0 5 7 (by decide) rfl rfl

/-! ### (d) The inheritance headlines FIRE on the deployed signer (reusing `HermineTSUF.exForger`). -/

/-- **THE CONCURRENT HEADLINE FIRES on the deployed signer**, via the forgery door: `HermineTSUF.exForger`'s
fresh forgery, forked at `1 ≠ 2`, yields the MSIS floor disjunct for `goodApi` — secret-free, non-vacuously. -/
example :
    (¬ HashCR goodApi.commitReveal)
    ∨ (∃ v, IsMSISSolution (augmented goodApi.A goodApi.groupKey) ((0 + 0) + (0 + 0)) v)
    ∨ (¬ MLWESearchHard goodApi.A 0 goodApi.groupKey) :=
  threshold_signer_concurrent_ts_uf_0 goodApi 0 exForger
    (Or.inr (Or.inr ⟨fun _ => 1, 2, by decide, exForger_accepts _, exForger_accepts _⟩))

/-- **THE ADAPTIVE, LOSS-FREE HEADLINE FIRES on the deployed signer.** With `exForger`'s forked forgery over the
interleaved Shamir-field trace, the adaptive reduction reaches the MSIS floor disjunct WITHOUT the guessing
loss AND without any erasure hypothesis — the erasure witness is the PROVED `simTranscriptCommit` consistency.
Adaptivity is free, on the code. -/
example :
    AdaptiveErasure goodApi.A ([AdaptiveStep.corrupt 1, AdaptiveStep.sign 10] : List (AdaptiveStep ℚ ℕ))
      (fun _ => 3) (fun _ => 2) (fun _ => 4)
      (simTranscriptCommit goodApi.A (fun _ => 3) (fun _ => 2) (fun _ => 4))
    ∧ ((¬ HashCR goodApi.commitReveal)
       ∨ (∃ v, IsMSISSolution (augmented goodApi.A goodApi.groupKey) ((0 + 0) + (0 + 0)) v)
       ∨ (¬ MLWESearchHard goodApi.A 0 goodApi.groupKey)) :=
  threshold_signer_adaptive_ts_uf_lossfree goodApi 0 exForger
    ([AdaptiveStep.corrupt 1, AdaptiveStep.sign 10] : List (AdaptiveStep ℚ ℕ))
    (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (Or.inr (Or.inr ⟨fun _ => 1, 2, by decide, exForger_accepts _, exForger_accepts _⟩))

/-- **THE BRIDGE FIRES** — the deployed Bool verify accepting (plus shortness, trivial over the zero seminorm)
IS a TS-UF-0 accept for `exForger`. So the inheritance is genuinely about the deployed verifier. -/
theorem deployed_bridge_fires (ρ : ℕ → ZMod 5)
    (hver : goodApi.verify (exForger.commitment ρ) (ρ exForger.challengeIdx) (exForger.response ρ) = true) :
    Accepts goodApi.A goodApi.groupKey 0 exForger ρ :=
  deployed_forgery_accepts goodApi goodApi_isHermineVerify 0 exForger ρ
    (Nat.le_zero.mpr rfl) (Nat.le_zero.mpr rfl) (Nat.le_zero.mpr rfl) hver

/-- **THE DEPLOYED-SIGNER DECISIONAL NON-LEAKING FIRES.** On `goodApi`, under the decaying transcript
distinguisher (`ProbCrypto.decayDist.adv = 1/2^l`), the deployed signer's adaptive reveal is non-leaking: the
simulated transcript is erasure-consistent (PROVED) AND its distinguishing advantage is negligible — the
masking guarantee re-grounded on the code, on the honest decisional floor. -/
theorem deployed_transcript_nonleaking_fires :
    AdaptiveErasure goodApi.A ([AdaptiveStep.corrupt 1, AdaptiveStep.sign 10] : List (AdaptiveStep ℚ ℕ))
      (fun _ => 3) (fun _ => 2) (fun _ => 4)
      (simTranscriptCommit goodApi.A (fun _ => 3) (fun _ => 2) (fun _ => 4))
    ∧ Negl ProbCrypto.decayDist.adv :=
  threshold_signer_transcript_nonleaking goodApi
    ([AdaptiveStep.corrupt 1, AdaptiveStep.sign 10] : List (AdaptiveStep ℚ ℕ))
    (fun _ => 3) (fun _ => 2) (fun _ => 4)
    (fun _ : Unit => ProbCrypto.decayDist.adv) () ProbCrypto.decisionMLWEHardQuant_decay_holds

/-- **THE DEPLOYED SIGNER'S DECISIONAL FLOOR IS LOAD-BEARING** — the perfect transcript distinguisher
(advantage `1`) refutes it, so the deployed masking indistinguishability is a genuine decisional hardness
assumption. -/
theorem deployed_decision_floor_load_bearing :
    ¬ DecisionMLWEHardQuant (fun _ : Unit => ProbCrypto.perfectDist.adv) :=
  ProbCrypto.decisionMLWEHardQuant_perfect_refuted

end Teeth

#assert_all_clean [
  honest_cert_verifies,
  threshold_signer_refines,
  deployed_forgery_accepts,
  threshold_signer_concurrent_ts_uf_0,
  threshold_signer_adaptive_ts_uf_lossfree,
  threshold_signer_transcript_nonleaking,
  deployed_transcript_nonleaking_fires,
  deployed_decision_floor_load_bearing,
  deployed_equivocation_breaks_hashcr,
  goodApi_isHermineVerify,
  goodApi_refines,
  sub_threshold_not_valid,
  badModel_not_refines,
  badBind_equivocation,
  deployed_bridge_fires
]

end Dregg2.Crypto.ThresholdSignerRefinement
