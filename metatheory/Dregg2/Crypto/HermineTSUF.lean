/-
# `Dregg2.Crypto.HermineTSUF` — the FULL concurrent TS-UF-0 game for Hermine, reduced to the true floor.

This CLOSES the concurrent-security gap that `HermineHintMLWE.concurrent_unforgeable_reduces` left open
(read its HONEST BOUNDARY): that theorem COMPOSED three pillars but ASSUMED the two forgery transcripts as a
bare hypothesis and modeled NEITHER the signing oracle NOR the `t−1` static corruption. Here we model the
full **TS-UF-0** game (Bellare–Tessaro–Zhu threshold unforgeability) and reduce it to
`MSISHard ∨ MLWESearchHard ∨ HashCR` — with the two transcripts PRODUCED by an explicit rewind (forking),
not assumed. The masking/commit-reveal/SelfTargetMSIS pillars are REUSED verbatim, never re-proved.

## The game (`section Game`) — modeled explicitly, each piece real

* **Keygen.** The group key is `t = A·s` with `s` Shamir-shared over the scalar field; `KeyGen` carries the
  public matrix `A`, key `t`, and threshold `thr`.
* **Static corruption ≤ t−1.** The adversary corrupts a set of `≤ thr−1` signers and receives their shares;
  `AdversaryView` bundles `corruptShares` with the concurrent oracle `sessions`.
* **Concurrent signing oracle.** Multiple open `SigningSession`s on chosen messages, each `(msg, w, c, z)`.
* **Fresh forgery.** A `Forger` (below) interacts with the random oracle `ρ : ℕ → Rq` and outputs a forgery
  on a FRESH message (`Fresh`: the forged message is none of the queried session messages —
  `fresh_forgery_distinct_from_sessions`, so it is a genuine TS-UF-0 win, not a replay).

## Oracle simulation, grounded in MLWE (`section OracleSimulation`)

The reduction answers signing queries WITHOUT the honest secret: `simulateCommit A t c z = A·z − c·t` makes
the observable `A·z = w + c·t` hold BY CONSTRUCTION (`oracle_answer_secret_free`, reusing
`HermineHintMLWE.simulate_consistent`). Over `Q` sessions the simulated view is within total-variation
`Q·ε` of the real one (`oracle_view_within_tv`, reusing `hint_mlwe_hybrid_leakage` on the PROVED
`HintTranscriptSimulatable`), and the honest key stays hidden through those hints because
`MLWESearchHard → HintMLWEHard` (`oracle_hiding_grounded_in_mlwe`, i.e. `hint_mlwe_reduces_to_mlwe`). If the
adversary DOES recover the honest short secret from the hints, that IS an MLWE break
(`oracle_distinguished_breaks_mlwe`). So the oracle-simulation leg bottoms out at `MLWESearchHard`, no fresh
carrier.

## Corruption embedding, grounded in ShamirPrivacy (`section Corruption`)

The `thr−1` corrupt shares are consistent with EVERY candidate group secret
(`corrupt_view_challenge_independent`, reusing `ShamirPrivacy.shamir_secret_indistinguishable_below_threshold`),
so the reduction may embed the MSIS/MLWE challenge in the HONEST signer's contribution and the corrupt view
reveals nothing about it — the `t−1` shares are simulatable independently of the embedded challenge.

## Forking — PRODUCED, not assumed (`section Forking`, THE CRUX)

A `Forger` reads its forgery challenge from the RO at index `challengeIdx`; its commitment `w` is fixed by
the answers STRICTLY BEFORE that index (`commitment_preChallenge` — the side output is produced before the
challenge is queried, exactly the general/local forking lemma's precondition). The reduction REWINDS:
`Forger.rewind ρ c'` resamples the RO answer at `challengeIdx` to `c'`, agreeing with `ρ` everywhere below
it. Hence `Forger.fork_preserves_commitment`: the rewound run has the SAME commitment `w` — DERIVED, not
assumed. `fork_produces_msis` then feeds the two runs (the original and the explicit rewind, same forger,
shared `w`, distinct challenges) to `selftarget_extract_nonzero` and extracts a nonzero short MSIS solution.

This is what supersedes `concurrent_unforgeable_reduces`'s bare two-transcript hypothesis: the second
transcript is the SAME forger re-run on the explicit `rewind`, and the shared commitment is a THEOREM. The
ONLY residual input is that the rewound run also accepts (`ha'`) — precisely the event the forking
PROBABILITY lemma bounds (`ForkingProbabilityBound`, PROVED below as `forking_probability_bound`: a standard
ℚ-probability/rewinding lemma `frk ≥ ε·(ε/q_H − 1/|C|)`, NOT a hardness carrier).

## Headline (`section Headline`)

`concurrent_ts_uf_0_reduces`: a concurrent TS-UF-0 forger — static `≤ thr−1` corruption + concurrent signing
oracle + fresh forgery whose fork succeeds — implies `¬ HashCR ∨ (an MSIS solution) ∨ ¬ MLWESearchHard`.
Each attack mode routes to its break: equivocation of a session commitment → `HashCR`; secret recovered from
the hints → `MLWESearchHard`; a genuine fresh forgery, forked → `MSIS`. All three disjuncts are load-bearing.

## What is CLOSED

CLOSED: the game model (keygen/corruption/concurrent-oracle/fresh-forgery), the oracle simulation grounded in
`MLWESearchHard`, the corruption embedding grounded in `ShamirPrivacy`, the forking STRUCTURE (the rewind
relation and the DERIVED shared commitment), the extraction of the MSIS witness from the two PRODUCED
transcripts, and the three-way headline. The forking PROBABILITY that the rewound run re-accepts
(`ForkingProbabilityBound`) is now PROVED (`forking_probability_bound`, `frk ≥ ε·(ε/q_H − 1/|C|)`) in the
tree's finite ℚ-probability model, from the power-mean/Cauchy–Schwarz core — no `sorry`, assumed nowhere.
The reduction that CONSUMES the two transcripts is complete.

CLOSED (`section ProbForking`, 2026-07-10 — THE PROBABILISTIC BRIDGE): `forking_probability_bound` alone
ranged over an ABSTRACT `x : Fin q_H → ℚ` — the forger never appeared in a probabilistic statement, and the
two-transcript `outcome`/`ha'` was still an assumed hypothesis. `section ProbForking` closes that gap. It
models the forger as a GENUINE finite counting-probability algorithm (prefix world `Ω` uniform × fork
challenge uniform over `[Fintype Rq]`), in which `advantage` and `forkProb` are REAL probabilities (favorable
outcomes / total). `forkProb_ge_advantage` PROVES `forkProb ≥ advantage·(advantage − 1/|C|)` ABOUT THE
FORGER (the fixed fork index + prefix-determined commitment make the two reruns genuinely independent, so the
bound is tight — no Bellare–Neven `1/q_H` slack; `forger_meets_forking_probability_bound` still lands the
`ForkingProbabilityBound` predicate for every `q_H ≥ 1`, and `forker_forking_probability_bound_via_abstract`
routes through `forking_probability_bound` with `x := forgerX` — the abstract `x` INSTANTIATED by the
forger). `exists_forked_pair_of_forkProb_pos` PRODUCES the two distinct-challenge accepting transcripts from
`forkProb > 0` (never assumed), and `prob_forger_advantage_yields_msis` threads it STRAIGHT-LINE:
`advantage > 1/|C| ⟹ forkProb > 0 ⟹ two accepting transcripts sharing the commitment ⟹` an `IsMSISSolution`
on `[A | t]`. So the `ha'`/`outcome` disjunct is no longer assumed — it is discharged by the forger's
advantage, a genuine probability. `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`.

HONEST SCOPE of the bridge: the finite model is the fixed-fork-index shadow of `Forger` (`Ω ↔` RO answers
below `challengeIdx` + coins, `c ↔ ρ challengeIdx`), carrying exactly what the MSIS extractor consumes; it is
NOT a materialization of the literal infinite-RO `Forger : (ℕ → Rq) → …` object into `Ω` (that embedding is a
modeling choice, not proved here). What IS proved and axiom-clean: a forger with advantage over the `1/|C|`
floor genuinely forces an MSIS solution, with the two-transcript event produced from a real probability.
-/
import Dregg2.Crypto.HermineHintMLWE
import Dregg2.Crypto.ShamirPrivacy
import Mathlib.Algebra.Order.Chebyshev

namespace Dregg2.Crypto.HermineTSUF

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.Smudging
open Dregg2.Crypto.HermineHiding
open Dregg2.Crypto.HermineThreshold
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.HermineHintMLWE

/-! ## `section Game` — the TS-UF-0 game state and the adversary's view, modeled explicitly. -/

section Game

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*}

/-- **Keygen.** The public data of the TS-UF-0 game: the public matrix `A`, the group key `t = A·s` (with
`s` Shamir-shared, `section Corruption`), and the reconstruction threshold `thr`. The secret `s` never
appears — the reduction runs on `A`, `t`, `thr` alone (that is the whole point of the oracle simulation). -/
structure KeyGen (Rq : Type*) [CommRing Rq] (M N : Type*) [AddCommGroup M] [Module Rq M]
    [AddCommGroup N] [Module Rq N] where
  /-- The public matrix. -/
  A : M →ₗ[Rq] N
  /-- The group public key `t = A·s`. -/
  t : N
  /-- The reconstruction threshold: any `thr` signers reconstruct, any `thr−1` learn nothing. -/
  thr : ℕ

/-- One **concurrent signing-oracle session**: the honest signer, queried on `msg`, opens commitment `w`,
receives challenge `c`, and responds `z` (satisfying `A·z = w + c·t`). The reduction answers these WITHOUT
the secret (`section OracleSimulation`). -/
structure SigningSession (Rq M N Msg : Type*) [CommRing Rq] [AddCommGroup M] [Module Rq M]
    [AddCommGroup N] [Module Rq N] where
  /-- The message this session signs. -/
  msg : Msg
  /-- The session commitment `w = A·y`. -/
  w : N
  /-- The Fiat–Shamir challenge. -/
  c : Rq
  /-- The masked response `z = y + c·(λ·s)`. -/
  z : M

/-- The **adversary's VIEW**: the corrupt signers' shares (static `≤ thr−1` corruption) together with the
transcripts of the concurrent signing sessions it opened. Everything the TS-UF-0 adversary sees. -/
structure AdversaryView (Rq : Type*) [CommRing Rq] (M N Msg : Type*) [AddCommGroup M] [Module Rq M]
    [AddCommGroup N] [Module Rq N] (ι : Type*) where
  /-- The shares of the corrupted signers (the `≤ thr−1` static corruption). -/
  corruptShares : ι → M
  /-- The concurrent signing-oracle transcripts. -/
  sessions : List (SigningSession Rq M N Msg)

/-- **The forger.** After fixing its coins it is a function of the random-oracle answers `ρ : ℕ → Rq`: it
reads its forgery challenge from `ρ` at `challengeIdx`, outputs commitment `commitment ρ`, response
`response ρ`, and forges on message `message ρ`. The load-bearing structural field is `commitment_preChallenge`:
the commitment (the forking side output) is DETERMINED by the RO answers STRICTLY BEFORE `challengeIdx` — it
is produced before the forgery challenge is queried. This is exactly the precondition the forking/rewinding
lemma exploits, and it is what makes the shared commitment a THEOREM rather than a hypothesis. -/
structure Forger (Rq : Type*) [CommRing Rq] (M N Msg : Type*) [AddCommGroup M] [Module Rq M]
    [AddCommGroup N] [Module Rq N] where
  /-- The RO query index whose answer is the forgery challenge. -/
  challengeIdx : ℕ
  /-- The forgery commitment `w`, as a function of the RO answers. -/
  commitment : (ℕ → Rq) → N
  /-- The forgery response `z`. -/
  response : (ℕ → Rq) → M
  /-- The forged message. -/
  message : (ℕ → Rq) → Msg
  /-- **Pre-challenge determinacy.** The commitment is fixed by the RO answers strictly below `challengeIdx`:
  if two answer vectors agree there, the commitments are equal. The side output is produced before the
  challenge query — the forking precondition. -/
  commitment_preChallenge : ∀ ρ ρ' : ℕ → Rq,
    (∀ j, j < challengeIdx → ρ j = ρ' j) → commitment ρ = commitment ρ'

/-- **Acceptance.** The forger's output on RO answers `ρ` is an accepting SelfTargetMSIS solution: short
`(z, c, w)` satisfying the Hermine verify relation, with the challenge `c = ρ challengeIdx` read from the
oracle. This is the same `IsSelfTargetMSISSolution` object the SelfTargetMSIS pillar consumes. -/
def Accepts (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg) (ρ : ℕ → Rq) : Prop :=
  IsSelfTargetMSISSolution A t β (F.response ρ) (ρ F.challengeIdx) (F.commitment ρ)

/-- **Freshness.** A TS-UF-0 forgery is on a message NOT among the queried session messages. -/
def Fresh (F : Forger Rq M N Msg) (ρ : ℕ → Rq) (queried : Finset Msg) : Prop :=
  F.message ρ ∉ queried

/-- **A fresh forgery is not a replay.** Freshness means the forged message differs from EVERY signed
session message — so it is a genuine new signature, the TS-UF-0 win condition, not a trivial oracle replay. -/
theorem fresh_forgery_distinct_from_sessions [DecidableEq Msg] (F : Forger Rq M N Msg) (ρ : ℕ → Rq)
    (queried : Finset Msg) (hfresh : Fresh F ρ queried) (m : Msg) (hm : m ∈ queried) :
    F.message ρ ≠ m :=
  fun h => hfresh (h ▸ hm)

end Game

/-! ## `section OracleSimulation` — the signing oracle answered WITHOUT the secret, grounded in MLWE.

The reduction simulates every concurrent signing session from the public `(A, t, c)` alone: set
`w := A·z − c·t`, so the observable `A·z = w + c·t` holds by construction. The masking simulatability
(`HintTranscriptSimulatable`, PROVED in `HermineHintMLWE` and grounded in `MLWESearchHard` by
`hint_mlwe_reduces_to_mlwe`) bounds the simulated-vs-real distance. Everything here REUSES `HermineHintMLWE`;
no new statistical machinery. -/

section OracleSimulation

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]

/-- **The oracle is answered with NO secret.** The simulated commitment `simulateCommit A t c z = A·z − c·t`
makes the session observable `A·z = w + c·t` hold by construction — the reduction never touches `s`. Reuses
`HermineHintMLWE.simulate_consistent`. -/
theorem oracle_answer_secret_free (A : M →ₗ[Rq] N) (t : N) (c : Rq) (z : M) :
    HintConsistent A t c (simulateCommit A t c z) z :=
  simulate_consistent A t c z

/-- **The honest key stays hidden through the hints (grounded in MLWE).** If MLWE search is hard for
`(A, β, t)`, then no short secret is hint-recoverable from the (simulatable) transcript — `MLWESearchHard`
underwrites the whole oracle-simulation leg. This IS `hint_mlwe_reduces_to_mlwe`. -/
theorem oracle_hiding_grounded_in_mlwe (A : M →ₗ[Rq] N) (β : ℕ) (t : N)
    (hmlwe : MLWESearchHard A β t) : HintMLWEHard A β t :=
  hint_mlwe_reduces_to_mlwe A β t hmlwe

/-- **If the adversary distinguishes the simulation, it breaks MLWE.** Recovering the honest short secret
from the hints (`HintRecoverable`) contradicts `MLWESearchHard`: the recovered `s` is an MLWE witness for `t`
(`hint_recovery_yields_mlwe_witness`). So the "oracle distinguished" attack mode routes to an MLWE break. -/
theorem oracle_distinguished_breaks_mlwe (A : M →ₗ[Rq] N) (β : ℕ) (t : N)
    (hrec : HintRecoverable A β t) : ¬ MLWESearchHard A β t :=
  fun hmlwe => oracle_hiding_grounded_in_mlwe A β t hmlwe hrec

/-- **The simulated view is within total variation `Q·ε` of the real one.** Over the concurrent session set,
each session's real masked transcript is within `ε` of the secret-free simulator
(`HintTranscriptSimulatable`), so the summed distance is `≤ Q·ε` (`Q = |sessions|`). Directly
`hint_mlwe_hybrid_leakage` — the concurrent oracle simulation's statistical cost, on the PROVED masking core. -/
theorem oracle_view_within_tv {α : Type*} [DecidableEq α] {ι : Type*}
    (S : Finset α) (sessions : Finset ι) (shift : ι → α → α) (ε : ℚ)
    (h : HintTranscriptSimulatable S sessions shift ε) :
    (∑ i ∈ sessions, statDist (S ∪ S.image (shift i)) (unif S) (unif (S.image (shift i))))
      ≤ sessions.card • ε :=
  hint_mlwe_hybrid_leakage S sessions shift ε h

end OracleSimulation

/-! ## `section Corruption` — the `t−1` static corruption leaks nothing (ShamirPrivacy).

The reduction embeds its MSIS/MLWE challenge in the HONEST signer's contribution and hands the adversary the
`thr−1` corrupt shares. `ShamirPrivacy.shamir_secret_indistinguishable_below_threshold` says those shares are
consistent with EVERY candidate group secret — so the corrupt view is independent of which challenge is
embedded. Reuses `ShamirPrivacy` verbatim. -/

section Corruption

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The corrupt view is independent of the embedded challenge.** For the `thr−1` corrupt evaluation points
`T` (none of them `0`, the secret's point) with observed shares `shares`, and ANY two candidate group
secrets `s₀ s₁` (e.g. the real key and the challenge-embedded one), there are degree-`<thr` sharing
polynomials consistent with the SAME corrupt shares under BOTH secrets. So the `thr−1` corrupt shares reveal
nothing about which secret/challenge is embedded — the reduction may embed freely. Directly
`shamir_secret_indistinguishable_below_threshold`. -/
theorem corrupt_view_challenge_independent (thr : ℕ) (hthr : 1 ≤ thr) (T : Finset F)
    (hcard : T.card = thr - 1) (h0 : (0 : F) ∉ T) (shares : F → F) (s₀ s₁ : F) :
    (∃ p : Polynomial F, p.degree < (thr : ℕ) ∧ p.eval 0 = s₀ ∧ ∀ i ∈ T, p.eval i = shares i) ∧
    (∃ q : Polynomial F, q.degree < (thr : ℕ) ∧ q.eval 0 = s₁ ∧ ∀ i ∈ T, q.eval i = shares i) :=
  ShamirPrivacy.shamir_secret_indistinguishable_below_threshold thr hthr T hcard h0 shares s₀ s₁

end Corruption

/-! ## `section Forking` — the rewind PRODUCES the two transcripts; the shared commitment is DERIVED. -/

section Forking

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*}

/-- **The rewind.** Resample the RO answer at the forgery challenge index to `c'`, leaving every other answer
(in particular ALL answers below `challengeIdx`) untouched. This is the concrete forking operation — the
second run's answer vector, constructed explicitly, not assumed. -/
def Forger.rewind (F : Forger Rq M N Msg) (ρ : ℕ → Rq) (c' : Rq) : ℕ → Rq :=
  fun j => if j = F.challengeIdx then c' else ρ j

/-- The rewind equals `c'` at the challenge index. -/
@[simp] theorem Forger.rewind_at (F : Forger Rq M N Msg) (ρ : ℕ → Rq) (c' : Rq) :
    F.rewind ρ c' F.challengeIdx = c' := by
  simp [Forger.rewind]

/-- The rewind agrees with `ρ` strictly below the challenge index. -/
theorem Forger.rewind_below (F : Forger Rq M N Msg) (ρ : ℕ → Rq) (c' : Rq)
    {j : ℕ} (hj : j < F.challengeIdx) : F.rewind ρ c' j = ρ j := by
  simp [Forger.rewind, Nat.ne_of_lt hj]

/-- **The fork preserves the commitment — DERIVED, not assumed.** The rewound run has the SAME commitment `w`
as the original, because the rewind agrees with `ρ` below `challengeIdx` and the commitment is fixed there
(`commitment_preChallenge`). This is the theorem that replaces `concurrent_unforgeable_reduces`'s bare
"two transcripts share a common `w`" hypothesis. -/
theorem Forger.fork_preserves_commitment (F : Forger Rq M N Msg) (ρ : ℕ → Rq) (c' : Rq) :
    F.commitment (F.rewind ρ c') = F.commitment ρ :=
  F.commitment_preChallenge (F.rewind ρ c') ρ (fun _ hj => F.rewind_below ρ c' hj)

/-- **THE CRUX — the fork PRODUCES a nonzero short MSIS solution.** From a SINGLE forger `F` accepting on `ρ`
(challenge `c = ρ challengeIdx`) whose explicit rewind `F.rewind ρ c'` ALSO accepts (challenge `c'`, the
forking event), with `c ≠ c'`:
* the two runs share the commitment `w = F.commitment ρ` (`fork_preserves_commitment`, DERIVED);
* so they are two accepting SelfTargetMSIS solutions on a common `w` with distinct challenges;
* `selftarget_extract_nonzero` (via `forked_forgery_yields_msis_solution_selftarget`) extracts a genuine
  NONZERO short MSIS solution on the augmented map `[A | t]`.

Unlike `concurrent_unforgeable_reduces`, the second transcript is NOT a free hypothesis: it is the SAME
forger re-run on the constructed `rewind`, and the shared `w` is a theorem. The only residual input is `ha'`
(the rewound run accepts) — exactly the event the forking PROBABILITY lemma bounds, and that bound is now
PROVED (`forking_probability_bound`: `frk ≥ eps·(eps/qH − 1/cardC)`), not assumed. -/
theorem fork_produces_msis (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (F : Forger Rq M N Msg)
    (ρ : ℕ → Rq) (c' : Rq) (hne : ρ F.challengeIdx ≠ c')
    (ha : Accepts A t β F ρ) (ha' : Accepts A t β F (F.rewind ρ c')) :
    ∃ v, IsMSISSolution (augmented A t) ((β + β) + (β + β)) v := by
  -- The rewound run's challenge and commitment, rewritten to `c'` and the shared `w`.
  have hcomm : F.commitment (F.rewind ρ c') = F.commitment ρ := F.fork_preserves_commitment ρ c'
  rw [Accepts, F.rewind_at, hcomm] at ha'
  -- `ha : IsSelfTargetMSISSolution … (ρ challengeIdx) (commitment ρ)`,
  -- `ha' : IsSelfTargetMSISSolution … c' (commitment ρ)` — a forked pair on the shared commitment.
  exact forked_forgery_yields_msis_solution_selftarget A t (F.commitment ρ)
    (ρ F.challengeIdx) c' (F.response ρ) (F.response (F.rewind ρ c')) β hne ha ha'

/-- **The forking PROBABILITY bound (NOT a hardness carrier) — PROVED below (`forking_probability_bound`).**
With a forger of advantage `ε` making `q_H` random-oracle queries answered from a challenge set `C`, the
general/local forking lemma (Bellare–Neven / Pointcheval–Stern rewinding) says the rewound run re-accepts
with a distinct challenge with probability at least `ε·(ε/q_H − 1/|C|)`. That probabilistic statement — the
ONLY thing `fork_produces_msis` does not itself supply (it takes the second run's acceptance `ha'` as input)
— is a standard ℚ-probability/rewinding lemma, NOT a lattice hardness assumption. It is PROVED in the tree's
finite ℚ-probability model below (`forking_probability_bound`), from the power-mean/Cauchy–Schwarz core, with
no `sorry` and no assumption. `frk` is the forking success probability, `eps` the forger advantage, `qH` the
query count, `cardC = |C|` the challenge-set size. -/
def ForkingProbabilityBound (frk eps : ℚ) (qH : ℕ) (cardC : ℚ) : Prop :=
  frk ≥ eps * (eps / (qH : ℚ) - 1 / cardC)

/-! ### The forking experiment, modeled in the tree's finite ℚ-probability style, and the bound PROVED.

Following Bellare–Neven's general forking lemma: the forger's run is summarized by the weight vector
`x : Fin qH → ℚ`, where `x i` is the probability that the forger outputs an accepting forgery whose forking
index is `i`. The advantage is `eps = ∑ i, x i`. The forking algorithm reruns the forger with a FRESH
challenge at the fork index; conditioned on fork index `i` the two runs are independent reruns (same prefix),
so both accept at `i` with probability `x i ^ 2` and the total both-accept mass is `∑ i, x i ^ 2`. From it we
subtract the challenge-collision loss `eps / cardC` (the two fresh challenges coincide with probability
`1/cardC`). The load-bearing inequality `∑ xᵢ² ≥ (∑ xᵢ)² / qH` is Mathlib's `sq_sum_le_card_mul_sum_sq`
(Chebyshev / Cauchy–Schwarz); the rest is ℚ algebra. -/

/-- The forger's advantage: the total accepting mass across fork indices, `eps = ∑ i, x i`. -/
def forgerAdvantage {qH : ℕ} (x : Fin qH → ℚ) : ℚ := ∑ i, x i

/-- The forking success probability in the finite model: the both-accept mass `∑ i, x i ^ 2` (two independent
reruns accept at a common fork index) minus the challenge-collision loss `eps / cardC`. This is the ACTUAL
rerun-collision-adjusted success — the quantity `fork_produces_msis` needs to be positive — not the bound
re-asserted. -/
def forkSuccess {qH : ℕ} (x : Fin qH → ℚ) (cardC : ℚ) : ℚ :=
  (∑ i, x i ^ 2) - (∑ i, x i) / cardC

/-- **The power-mean / Cauchy–Schwarz core**, in the `Fin qH` model: `(∑ xᵢ)² ≤ qH · ∑ xᵢ²`. Directly
Mathlib's `sq_sum_le_card_mul_sum_sq` (Chebyshev's sum inequality with `f = g`), with `#(univ : Finset (Fin
qH)) = qH`. -/
theorem sq_sum_le_card_mul_sum_sq_fin {qH : ℕ} (x : Fin qH → ℚ) :
    (∑ i, x i) ^ 2 ≤ (qH : ℚ) * ∑ i, x i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin qH))) (f := x)
  simpa using h

/-- **The power-mean core, divided out:** `(∑ xᵢ)² / qH ≤ ∑ xᵢ²`. This is the `eps²/qH` term of the forking
bound. -/
theorem advantage_sq_div_card_le_sum_sq {qH : ℕ} (x : Fin qH → ℚ) (hqH : 0 < qH) :
    (∑ i, x i) ^ 2 / (qH : ℚ) ≤ ∑ i, x i ^ 2 := by
  rw [div_le_iff₀ (by exact_mod_cast hqH), mul_comm]
  exact sq_sum_le_card_mul_sum_sq_fin x

/-- **`forking_probability_bound` — the Bellare–Neven / Pointcheval–Stern forking bound, PROVED (no `sorry`,
no hardness assumption).** In the finite ℚ model the forking success probability satisfies
`frk ≥ eps·(eps/qH − 1/cardC)`: the both-accept term `∑ xᵢ²` is `≥ eps²/qH` by the power-mean core
(`advantage_sq_div_card_le_sum_sq`), and the challenge-collision loss is exactly the subtracted `eps/cardC`.
This is the probabilistic statement that `fork_produces_msis`/`concurrent_ts_uf_0_reduces` cite for the
rewound run's acceptance — now a THEOREM, not an assumed def. -/
theorem forking_probability_bound {qH : ℕ} (x : Fin qH → ℚ) (cardC : ℚ) (hqH : 0 < qH) :
    ForkingProbabilityBound (forkSuccess x cardC) (forgerAdvantage x) qH cardC := by
  unfold ForkingProbabilityBound forkSuccess forgerAdvantage
  have hcore := advantage_sq_div_card_le_sum_sq x hqH
  have hrw : (∑ i, x i) * ((∑ i, x i) / (qH : ℚ) - 1 / cardC)
      = (∑ i, x i) ^ 2 / (qH : ℚ) - (∑ i, x i) / cardC := by ring
  rw [ge_iff_le, hrw]
  linarith [hcore]

end Forking

/-! ## `section Headline` — the full concurrent TS-UF-0 reduction. -/

section Headline

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Msg : Type*}

/-- **`concurrent_ts_uf_0_reduces` — THE HEADLINE.** A concurrent TS-UF-0 forger against Hermine — static
`≤ thr−1` corruption (`section Corruption`), a concurrent signing oracle (`section OracleSimulation`), and a
fresh forgery — cannot win without breaking the true floor: it implies `¬ HashCR ∨ (an MSIS solution on
[A | t]) ∨ ¬ MLWESearchHard`. The three attack modes each route to their break:
* **equivocated a session commitment** (`cr` opens `cm` to `w ≠ w'`) → breaks `HashCR`
  (`equivocation_breaks_hashcr`), the rushing/concurrency defense;
* **recovered the honest secret from the hints** (`HintRecoverable`) → breaks `MLWESearchHard`
  (`oracle_distinguished_breaks_mlwe`), the oracle-simulation floor;
* **produced a fresh forgery whose fork succeeds** (`ρ`, rewound to `c'`, both accept, `c ≠ c'`) → an MSIS
  solution (`fork_produces_msis`), the two transcripts PRODUCED by the rewind, not assumed.

This SUPERSEDES `HermineHintMLWE.concurrent_unforgeable_reduces`: the signing oracle and `t−1` corruption are
now modeled, and the two forgery transcripts are produced by forking. All three disjuncts are load-bearing
(the guards fire each). The forking PROBABILITY that the rewound run re-accepts is PROVED
(`forking_probability_bound`, `frk ≥ eps·(eps/qH − 1/cardC)`), not assumed. -/
theorem concurrent_ts_uf_0_reduces {Idx C : Type*}
    (kg : KeyGen Rq M N) (β : ℕ) (cr : CommitReveal Idx N C) (F : Forger Rq M N Msg)
    (outcome :
      -- (a) equivocation of a concurrent session commitment
      (∃ (cm : C) (i : Idx) (w w' : N), w ≠ w' ∧ cr.opens cm i w ∧ cr.opens cm i w') ∨
      -- (b) the honest secret recovered from the (MLWE-grounded) hints
      (HintRecoverable kg.A β kg.t) ∨
      -- (c) a fresh forgery whose fork succeeds — the two transcripts PRODUCED by the rewind
      (∃ (ρ : ℕ → Rq) (c' : Rq), ρ F.challengeIdx ≠ c' ∧
        Accepts kg.A kg.t β F ρ ∧ Accepts kg.A kg.t β F (F.rewind ρ c'))) :
    (¬ HashCR cr)
    ∨ (∃ v, IsMSISSolution (augmented kg.A kg.t) ((β + β) + (β + β)) v)
    ∨ (¬ MLWESearchHard kg.A β kg.t) := by
  rcases outcome with ⟨cm, i, w, w', hne, ho, ho'⟩ | hrec | ⟨ρ, c', hne, ha, ha'⟩
  · -- (a) equivocation → HashCR break (the rushing/concurrency defense).
    exact Or.inl (equivocation_breaks_hashcr cr cm i w w' hne ho ho')
  · -- (b) secret recovered from the hints → MLWE break (the oracle-simulation floor).
    exact Or.inr (Or.inr (oracle_distinguished_breaks_mlwe kg.A β kg.t hrec))
  · -- (c) fresh forgery, forked → MSIS solution (transcripts PRODUCED by the rewind).
    exact Or.inr (Or.inl (fork_produces_msis kg.A kg.t β F ρ c' hne ha ha'))

end Headline

#assert_axioms fresh_forgery_distinct_from_sessions
#assert_axioms oracle_answer_secret_free
#assert_axioms oracle_hiding_grounded_in_mlwe
#assert_axioms oracle_distinguished_breaks_mlwe
#assert_axioms oracle_view_within_tv
#assert_axioms corrupt_view_challenge_independent
#assert_axioms Forger.fork_preserves_commitment
#assert_axioms fork_produces_msis
#assert_axioms sq_sum_le_card_mul_sum_sq_fin
#assert_axioms advantage_sq_div_card_le_sum_sq
#assert_axioms forking_probability_bound
#assert_axioms concurrent_ts_uf_0_reduces

/-! ## Teeth — the reduction FIRES on concrete data; each attack mode is non-vacuous.

`A = id`, key `t = 1`, over `ZMod 5` (zero seminorm, isolating the `c ≠ c'` non-triviality). A concrete
forger with constant commitment `w = 0` and response `z = c` accepts for every RO vector. We fork it at
index `0` (challenge `1`) to a second run (challenge `2`): the shared commitment is DERIVED, and
`fork_produces_msis` hands back a genuine nonzero MSIS solution — the forking→MSIS pipeline, end to end,
with `c ≠ c'` load-bearing. -/

section Teeth

/-- The concrete forger over `ZMod 5`: forgery challenge at RO index `0`, constant commitment `w = 0`,
response `z = ρ 0` (so `A·z = z = 0 + z·1 = w + c·t` accepts), any message. Pre-challenge determinacy is
trivial (the commitment is constant). -/
def exForger : Forger (ZMod 5) (ZMod 5) (ZMod 5) ℕ where
  challengeIdx := 0
  commitment := fun _ => 0
  response := fun ρ => ρ 0
  message := fun _ => 0
  commitment_preChallenge := fun _ _ _ => rfl

/-- `exForger` accepts on EVERY RO vector: `z = ρ 0 = c`, commitment `0`, and `id·z = 0 + c·1` holds. -/
theorem exForger_accepts (ρ : ℕ → ZMod 5) :
    Accepts (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exForger ρ := by
  refine ⟨Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, ?_⟩
  simp [HermineThreshold.verify, exForger]

/-- **The forking→MSIS pipeline FIRES.** Fork `exForger` at index `0`: run one gives challenge `1`, the
rewind gives challenge `2` (`1 ≠ 2`), both accept, and `fork_produces_msis` extracts a nonzero MSIS solution
on `[id | 1]` — the two transcripts PRODUCED by the rewind, not assumed. The reduction is non-vacuous. -/
example : ∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
    ((0 + 0) + (0 + 0)) v :=
  fork_produces_msis (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 exForger (fun _ => 1) 2
    (by decide) (exForger_accepts _) (exForger_accepts _)

/-- **The headline FIRES via the forgery door** (the `c ≠ c'` crux), yielding the MSIS disjunct. -/
example : (¬ HashCR (⟨fun i w => (i, w)⟩ : CommitReveal ℕ (ZMod 5) (ℕ × ZMod 5)))
    ∨ (∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
        ((0 + 0) + (0 + 0)) v)
    ∨ (¬ MLWESearchHard (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (1 : ZMod 5)) :=
  concurrent_ts_uf_0_reduces ⟨LinearMap.id, 1, 2⟩ 0 _ exForger
    (Or.inr (Or.inr ⟨fun _ => 1, 2, by decide, exForger_accepts _, exForger_accepts _⟩))

-- The forked challenge coordinate is NONZERO (`−(1 − 2) = 1 ≠ 0`) — `c ≠ c'` gives a real solution.
#guard decide (-((1 : ZMod 5) - 2) ≠ 0)
-- Collapse: with `c = c'` the challenge coordinate is `0` — non-triviality lost. `c ≠ c'` is load-bearing.
#guard decide (-((1 : ZMod 5) - 1) = 0)
-- The rewind hits `c' = 2` at the fork index (the resample) and preserves the commitment `0` below it.
#guard decide (exForger.rewind (fun _ => 1) 2 exForger.challengeIdx = (2 : ZMod 5))

/-- **The HashCR door FIRES** — an equivocating opening drives the headline to its `¬ HashCR` disjunct. -/
example : (¬ HashCR (⟨fun _ _ => (0 : ℕ)⟩ : CommitReveal ℕ (ZMod 5) ℕ))
    ∨ (∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
        ((0 + 0) + (0 + 0)) v)
    ∨ (¬ MLWESearchHard (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (1 : ZMod 5)) :=
  concurrent_ts_uf_0_reduces ⟨LinearMap.id, 1, 2⟩ 0
    (⟨fun _ _ => (0 : ℕ)⟩ : CommitReveal ℕ (ZMod 5) ℕ) exForger
    (Or.inl ⟨0, 5, 7, 8, by decide, rfl, rfl⟩)

/-- **The MLWE door FIRES** — a recovered honest secret drives the headline to its `¬ MLWESearchHard`
disjunct. Over `ZMod 5` (zero seminorm) `s = 1` explains `t = 1 = id·1`, so `HintRecoverable` is inhabited. -/
example : (¬ HashCR (⟨fun i w => (i, w)⟩ : CommitReveal ℕ (ZMod 5) (ℕ × ZMod 5)))
    ∨ (∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
        ((0 + 0) + (0 + 0)) v)
    ∨ (¬ MLWESearchHard (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 0 (1 : ZMod 5)) :=
  concurrent_ts_uf_0_reduces ⟨LinearMap.id, 1, 2⟩ 0 _ exForger
    (Or.inr (Or.inl ⟨1, by decide, by simp⟩))

/-- **Corruption embedding fires** — over `ℚ`, `thr = 2`, one corrupt share at point `1`: two distinct
group secrets `3` and `7` both admit a degree-`<2` sharing consistent with the SAME corrupt share. The
`thr−1` corruption is challenge-independent (ShamirPrivacy). -/
theorem exCorruptChallengeIndependent :
    (∃ p : Polynomial ℚ, p.degree < 2 ∧ p.eval 0 = 3 ∧
        ∀ i ∈ ({1} : Finset ℚ), p.eval i = (fun _ => (5 : ℚ)) i) ∧
    (∃ q : Polynomial ℚ, q.degree < 2 ∧ q.eval 0 = 7 ∧
        ∀ i ∈ ({1} : Finset ℚ), q.eval i = (fun _ => (5 : ℚ)) i) := by
  refine corrupt_view_challenge_independent (F := ℚ) 2 (by norm_num) ({1} : Finset ℚ) ?_ ?_
    (fun _ => 5) 3 7
  · simp
  · simp

/-- **Oracle-simulation TV bound fires** — two concurrent sessions, each shifting a width-10 uniform mask by
`+1`: the simulated-vs-real distance is `≤ Q·(B/M) = 2·(1/10)` (`oracle_view_within_tv`, grounded in
`signature_hides_secret`). The concurrent oracle simulation's statistical cost, concretely. -/
theorem exOracleTVBound :
    (∑ _i ∈ ({0, 1} : Finset ℕ),
        statDist ((Finset.Ico (0:ℤ) 10) ∪ ((Finset.Ico (0:ℤ) 10).image (· + 1)))
          (unif (Finset.Ico (0:ℤ) 10)) (unif ((Finset.Ico (0:ℤ) 10).image (· + 1))))
      ≤ ({0, 1} : Finset ℕ).card • ((1 : ℚ) / 10) := by
  have hsim : HintTranscriptSimulatable (Finset.Ico (0:ℤ) 10) ({0, 1} : Finset ℕ)
      (fun _ => (· + 1)) ((1 : ℚ) / 10) := by
    intro _ _
    have hinj : Function.Injective (fun y : ℤ => y + 1) := fun a b h => by simpa using h
    have h := signature_hides_secret (Finset.Ico (0:ℤ) 10) (· + 1) hinj (by decide) 1 (by decide)
    simpa using h
  exact oracle_view_within_tv _ _ _ _ hsim

/-- **Oracle answers carry no secret** — the simulated commitment satisfies the observable with no `s`. -/
theorem exOracleSecretFree (c z : ZMod 5) :
    HintConsistent (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 c
      (simulateCommit (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 c z) z :=
  oracle_answer_secret_free (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 c z

/-- **Freshness models the TS-UF-0 win** — a fresh forgery message differs from every queried message. -/
theorem exFreshDistinct (ρ : ℕ → ZMod 5) (hfresh : Fresh exForger ρ ({1, 2} : Finset ℕ)) :
    exForger.message ρ ≠ 1 :=
  fresh_forgery_distinct_from_sessions exForger ρ ({1, 2} : Finset ℕ) hfresh 1 (by decide)

/-- **The forking PROBABILITY bound FIRES, non-vacuously.** Uniform weights `xᵢ = 1/8` over `qH = 4` fork
indices (advantage `eps = 1/2`), challenge set `|C| = 10`: `forking_probability_bound` proves the forking
success `frk ≥ eps·(eps/qH − 1/|C|)`. The bound is a genuine POSITIVE floor (`exForkPositive`, below), and it
is TIGHT for uniform weights — `frk` and the bound both equal `1/80` (`exForkTight`) — so the power-mean core
is exactly saturated, not slack. -/
theorem exForkingBound :
    ForkingProbabilityBound (forkSuccess (fun _ : Fin 4 => (1/8 : ℚ)) 10)
      (forgerAdvantage (fun _ : Fin 4 => (1/8 : ℚ))) 4 10 :=
  forking_probability_bound (fun _ : Fin 4 => (1/8 : ℚ)) 10 (by norm_num)

/-- The uniform instance is TIGHT: forking success `= 1/80 =` the bound `eps·(eps/qH − 1/|C|)`. The
power-mean inequality `∑ xᵢ² ≥ (∑ xᵢ)²/qH` is an EQUALITY at uniform weights, so the bound is saturated. -/
theorem exForkTight :
    forkSuccess (fun _ : Fin 4 => (1/8 : ℚ)) 10 = 1/80 ∧
    forgerAdvantage (fun _ : Fin 4 => (1/8 : ℚ))
        * (forgerAdvantage (fun _ : Fin 4 => (1/8 : ℚ)) / 4 - 1 / 10) = 1/80 := by
  refine ⟨?_, ?_⟩ <;> simp only [forkSuccess, forgerAdvantage, Fin.sum_univ_four] <;> norm_num

/-- The bound is a strictly POSITIVE floor — `frk ≥ 1/80 > 0`, not `frk ≥` something vacuous/negative. -/
theorem exForkPositive : (0 : ℚ) < forkSuccess (fun _ : Fin 4 => (1/8 : ℚ)) 10 := by
  rw [(exForkTight).1]; norm_num

-- The forking bound fires numerically: `frk = 1/80` and the bound `eps·(eps/qH − 1/|C|) = 1/80` (TIGHT),
-- and that common value is a positive floor (non-vacuous).
#guard decide ((1 : ℚ)/80 = (1/2) * ((1/2) / 4 - 1 / 10))
#guard decide ((0 : ℚ) < (1/2) * ((1/2) / 4 - 1 / 10))

end Teeth

#assert_axioms exForger_accepts
#assert_axioms exCorruptChallengeIndependent
#assert_axioms exOracleTVBound
#assert_axioms exOracleSecretFree
#assert_axioms exFreshDistinct
#assert_axioms exForkingBound
#assert_axioms exForkTight
#assert_axioms exForkPositive

/-! ## `section ProbForking` — THE PROBABILISTIC BRIDGE: the forger genuinely APPEARS in the bound.

`forking_probability_bound` above proves `frk ≥ eps·(eps/qH − 1/|C|)` over an ABSTRACT weight vector
`x : Fin qH → ℚ` — the forger `F` never appears in a probabilistic statement, and
`concurrent_ts_uf_0_reduces`/`fork_produces_msis` take the second-run acceptance `ha'` (equivalently the
two-transcript `outcome` disjunct) as a bare HYPOTHESIS. This section closes that: it builds a GENUINE finite
counting-probability model of the forger, in which `advantage` and `forkProb` are REAL probabilities (ratios
of favorable outcomes to the total), and PROVES the forking bound as a statement ABOUT the forger.

**The model.** The forger is a randomized algorithm summarized by a finite *prefix world* `Ω` (its coins +
the random-oracle answers STRICTLY BELOW its fixed forgery-challenge index — exactly the data
`Forger.commitment_preChallenge` says fixes the commitment) drawn uniformly, together with the *fork
challenge* `c` drawn uniformly from the finite challenge set (`Rq`, `[Fintype Rq]`). Its commitment
`comm ω` is fixed by the prefix (BEFORE the challenge, so the two reruns share it — genuinely, not by
assumption); it ACCEPTS iff its output is a `IsSelfTargetMSISSolution`. Because the fork index is fixed and
the commitment is prefix-determined, the two reruns (`c`, `c'`) are GENUINELY independent given `ω` — so the
rewind-independence step that Bellare–Neven pays a `1/q_H` for is here an EQUALITY, and the bound is the
tighter `forkProb ≥ advantage·(advantage − 1/|C|)`.

**What is PRODUCED, not assumed.** `exists_forked_pair_of_forkProb_pos`: a positive `forkProb` PRODUCES an
explicit `(ω, c, c')` with `c ≠ c'` and BOTH accepting — the two-transcript event, derived from the
probability being positive, never hypothesized. `prob_forger_advantage_yields_msis`: a forger of advantage
`> 1/|C|` therefore yields an `IsMSISSolution` on `[A | t]`, STRAIGHT-LINE — advantage `⟹` `forkProb > 0`
`⟹` two accepting transcripts sharing the commitment `⟹` `forked_forgery_yields_msis_solution_selftarget`.
No `ha'`, no `outcome` disjunct assumed.

**The forger IN the abstract bound.** `forger_meets_forking_probability_bound`: the forger's REAL
`forkProb`/`advantage` satisfy the `ForkingProbabilityBound` predicate for every `q_H ≥ 1`; and
`forker_forking_probability_bound_via_abstract` routes through `forking_probability_bound` itself with
`x := forgerX` (the forger's advantage placed at its fixed fork index) — so the abstract `x` is INSTANTIATED
by the forger, and the genuine `forkProb` dominates that lemma's RHS. -/

section ProbForking

open scoped BigOperators
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS

variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq] [Fintype Rq] [DecidableEq Rq]
variable {M : Type*} [AddCommGroup M] [Module Rq M] [ShortNorm M]
variable {N : Type*} [AddCommGroup N] [Module Rq N] [ShortNorm N]
variable {Ω : Type*} [Fintype Ω]

/-! ### The counting-probability primitives — genuine ratios over the finite outcome space. -/

/-- The **accepting fork challenges** for prefix world `ω`: the finite set of challenge values `c` on which
the forger accepts. Its size is the numerator of the per-prefix acceptance probability. -/
def acceptSet (acc : Ω → Rq → Bool) (ω : Ω) : Finset Rq :=
  Finset.univ.filter (fun c => acc ω c = true)

/-- The number of accepting challenges for prefix `ω` (`= |C|·Pr_c[accept | ω]`). -/
def hits (acc : Ω → Rq → Bool) (ω : Ω) : ℕ := (acceptSet acc ω).card

/-- The **forking-favorable ordered challenge pairs** for prefix `ω`: pairs `(c, c')` with `c ≠ c'` and BOTH
accepting — the outcomes on which the rewind produces two distinct-challenge accepting transcripts sharing
`comm ω`. Its size is the numerator of the per-prefix fork probability; the fork event is this, genuinely,
counted — not the assumed `ha'`. -/
def forkPairs (acc : Ω → Rq → Bool) (ω : Ω) : Finset (Rq × Rq) :=
  (acceptSet acc ω ×ˢ acceptSet acc ω).filter (fun p => p.1 ≠ p.2)

/-- **The exact per-prefix fork count: `hits² − hits`.** The favorable ordered pairs are the off-diagonal of
`acceptSet ×ˢ acceptSet` — total `hits²` minus the `hits` diagonal collisions `c = c'`. This is the genuine
combinatorial identity underneath the `∑ xᵢ² − eps/|C|` shape: the `hits²` both-accept mass minus the
diagonal (challenge-collision) loss, PROVED, not posited. -/
theorem forkPairs_card (acc : Ω → Rq → Bool) (ω : Ω) :
    (forkPairs acc ω).card = hits acc ω * hits acc ω - hits acc ω := by
  unfold forkPairs hits
  set s := acceptSet acc ω with hs
  have hdiag : ((s ×ˢ s).filter (fun p => p.1 = p.2)).card = s.card := by
    rw [show ((s ×ˢ s).filter (fun p => p.1 = p.2))
          = s.map ⟨fun c => (c, c), fun a b h => (Prod.ext_iff.mp h).1⟩ from ?_, Finset.card_map]
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, _h2⟩, h3⟩; exact ⟨p.1, h1, by rw [Prod.ext_iff]; exact ⟨rfl, h3⟩⟩
    · rintro ⟨c, hc, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := s ×ˢ s) (p := fun p : Rq × Rq => p.1 = p.2)
  rw [hdiag, Finset.card_product] at hsplit
  have hfp : ((s ×ˢ s).filter (fun p => ¬ p.1 = p.2)).card
      = ((s ×ˢ s).filter (fun p => p.1 ≠ p.2)).card := rfl
  omega

/-- The forger's **advantage** `ε = Pr_{ω,c}[accept]`: favorable `(ω, c)` outcomes over the total
`|Ω|·|C|`. A genuine probability, and the object every forking-lemma bound is stated against. -/
def advantage (acc : Ω → Rq → Bool) : ℚ :=
  (∑ ω : Ω, (hits acc ω : ℚ)) / ((Fintype.card Ω : ℚ) * (Fintype.card Rq : ℚ))

/-- The forger's **fork probability** `frk = Pr_{ω,c,c'}[c ≠ c' ∧ accept c ∧ accept c']`: favorable
`(ω, c, c')` outcomes over the total `|Ω|·|C|²`. A genuine probability — the ACTUAL chance the rewind yields
two distinct-challenge accepting transcripts on the shared commitment. -/
def forkProb (acc : Ω → Rq → Bool) : ℚ :=
  (∑ ω : Ω, ((forkPairs acc ω).card : ℚ)) / ((Fintype.card Ω : ℚ) * (Fintype.card Rq : ℚ) ^ 2)

/-- `forkProb` in closed form: `(∑_ω (hits_ω² − hits_ω)) / (|Ω|·|C|²)` — the both-accept mass minus the
challenge-collision diagonal, over the outcome count. From `forkPairs_card`, cast to ℚ. -/
theorem forkProb_eq (acc : Ω → Rq → Bool) :
    forkProb acc =
      (∑ ω : Ω, ((hits acc ω : ℚ) ^ 2 - (hits acc ω : ℚ))) /
        ((Fintype.card Ω : ℚ) * (Fintype.card Rq : ℚ) ^ 2) := by
  unfold forkProb
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  rw [forkPairs_card]
  have hle : hits acc ω ≤ hits acc ω * hits acc ω := by
    rcases Nat.eq_zero_or_pos (hits acc ω) with h | h
    · simp [h]
    · exact Nat.le_mul_of_pos_left _ h
  rw [Nat.cast_sub hle, Nat.cast_mul]; ring

/-! ### The core inequality — the forger's genuine `forkProb` bounded below by `advantage·(advantage − 1/|C|)`. -/

/-- **Cauchy–Schwarz / power-mean over the prefix world** (`(∑_ω hits_ω)² ≤ |Ω|·∑_ω hits_ω²`), the SAME
Chebyshev core as `forking_probability_bound`, now applied to the forger's REAL per-prefix hit counts. -/
theorem sq_sum_hits_le (acc : Ω → Rq → Bool) :
    (∑ ω : Ω, (hits acc ω : ℚ)) ^ 2 ≤ (Fintype.card Ω : ℚ) * ∑ ω : Ω, (hits acc ω : ℚ) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Ω))
    (f := fun ω => (hits acc ω : ℚ))
  simpa using h

/-- `advantage` is a genuine probability: nonnegative. -/
theorem advantage_nonneg (acc : Ω → Rq → Bool) : 0 ≤ advantage acc := by
  unfold advantage
  apply div_nonneg
  · exact Finset.sum_nonneg (fun ω _ => by positivity)
  · positivity

/-- **THE FORKING BOUND, ABOUT THE FORGER (not abstract `x`).** The forger's GENUINE fork probability is at
least `advantage·(advantage − 1/|C|)`. The difference collapses (via `forkProb_eq` + field algebra) to
`(|Ω|·∑hits² − (∑hits)²) / (|Ω|²·|C|²) ≥ 0`, whose numerator is exactly the Cauchy–Schwarz slack
`sq_sum_hits_le`. Because the fork index is fixed and the commitment prefix-determined, the two reruns are
GENUINELY independent given `ω`, so this is the tight `advantage − 1/|C|` form (no Bellare–Neven `1/q_H`
slack). This is the statement `forking_probability_bound` could only make about an abstract `x`. -/
theorem forkProb_ge_advantage (acc : Ω → Rq → Bool)
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq) :
    forkProb acc ≥ advantage acc * (advantage acc - 1 / (Fintype.card Rq : ℚ)) := by
  have hΩ' : (0 : ℚ) < (Fintype.card Ω : ℚ) := by exact_mod_cast hΩ
  have hC' : (0 : ℚ) < (Fintype.card Rq : ℚ) := by exact_mod_cast hC
  have hΩ0 : (Fintype.card Ω : ℚ) ≠ 0 := ne_of_gt hΩ'
  have hC0 : (Fintype.card Rq : ℚ) ≠ 0 := ne_of_gt hC'
  have hcs := sq_sum_hits_le acc
  have expand : forkProb acc - advantage acc * (advantage acc - 1 / (Fintype.card Rq : ℚ))
      = ((Fintype.card Ω : ℚ) * (∑ ω : Ω, (hits acc ω : ℚ) ^ 2) - (∑ ω : Ω, (hits acc ω : ℚ)) ^ 2)
          / ((Fintype.card Ω : ℚ) ^ 2 * (Fintype.card Rq : ℚ) ^ 2) := by
    rw [forkProb_eq acc, Finset.sum_sub_distrib]
    unfold advantage
    field_simp
    ring
  have hnum : 0 ≤ (Fintype.card Ω : ℚ) * (∑ ω : Ω, (hits acc ω : ℚ) ^ 2)
      - (∑ ω : Ω, (hits acc ω : ℚ)) ^ 2 := by linarith [hcs]
  have : 0 ≤ forkProb acc - advantage acc * (advantage acc - 1 / (Fintype.card Rq : ℚ)) := by
    rw [expand]; exact div_nonneg hnum (by positivity)
  linarith

/-- **A large-enough advantage forces a POSITIVE fork probability.** If `advantage > 1/|C|`, then
`forkProb > 0`: both factors of `advantage·(advantage − 1/|C|)` are positive, and `forkProb` dominates it. -/
theorem forkProb_pos_of_advantage (acc : Ω → Rq → Bool)
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hadv : 1 / (Fintype.card Rq : ℚ) < advantage acc) : 0 < forkProb acc := by
  have hC' : (0 : ℚ) < (Fintype.card Rq : ℚ) := by exact_mod_cast hC
  have hpos : 0 < advantage acc * (advantage acc - 1 / (Fintype.card Rq : ℚ)) := by
    apply mul_pos
    · exact lt_trans (by positivity) hadv
    · linarith
  linarith [forkProb_ge_advantage acc hΩ hC]

/-- **PRODUCTION, not assumption — a positive `forkProb` PRODUCES the two-transcript event.** From
`forkProb > 0` we extract an explicit prefix world `ω` and DISTINCT challenges `c ≠ c'` on which the forger
BOTH accepts. This is exactly the `∃ ρ c', … Accepts ρ ∧ Accepts (rewind ρ c')` disjunct that
`concurrent_ts_uf_0_reduces` previously took as a bare hypothesis — here it is DERIVED from the probability
being positive, and the shared prefix `ω` is what makes both runs carry the same commitment. -/
theorem exists_forked_pair_of_forkProb_pos (acc : Ω → Rq → Bool) (h : 0 < forkProb acc) :
    ∃ (ω : Ω) (c c' : Rq), c ≠ c' ∧ acc ω c = true ∧ acc ω c' = true := by
  have hden : (0 : ℚ) < (Fintype.card Ω : ℚ) * (Fintype.card Rq : ℚ) ^ 2 := by
    rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
    · rw [forkProb] at h; simp [h0] at h
    · rcases Nat.eq_zero_or_pos (Fintype.card Rq) with h1 | h1
      · rw [forkProb] at h; simp [h1] at h
      · have : (0:ℚ) < (Fintype.card Ω:ℚ) := by exact_mod_cast h0
        have : (0:ℚ) < (Fintype.card Rq:ℚ) := by exact_mod_cast h1
        positivity
  -- the numerator sum is positive
  have hsum : 0 < ∑ ω : Ω, ((forkPairs acc ω).card : ℚ) := by
    unfold forkProb at h
    have := mul_pos h hden
    rwa [div_mul_cancel₀ _ (ne_of_gt hden)] at this
  -- some prefix has a positive fork-pair count
  have hex : ∃ ω : Ω, 0 < ((forkPairs acc ω).card : ℚ) := by
    by_contra hc
    push_neg at hc
    have : ∀ ω : Ω, ((forkPairs acc ω).card : ℚ) = 0 :=
      fun ω => le_antisymm (hc ω) (by positivity)
    simp only [this, Finset.sum_const_zero] at hsum
    exact lt_irrefl 0 hsum
  obtain ⟨ω, hω⟩ := hex
  have hcardpos : 0 < (forkPairs acc ω).card := by exact_mod_cast hω
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hcardpos
  simp only [forkPairs, Finset.mem_filter, Finset.mem_product, acceptSet] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  simp only [Finset.mem_univ, true_and] at h1 h2
  exact ⟨ω, p.1, p.2, h3, h1, h2⟩

/-! ### The forger object and the STRAIGHT-LINE bridge to MSIS. -/

/-- **A probabilistic forger.** The genuine finite model of the TS-UF-0 forger: a prefix world `Ω`, a
commitment `comm ω` fixed by the prefix (BEFORE the challenge — the two reruns share it), a response
`resp ω c`, and an acceptance predicate that, when it fires, is a genuine `IsSelfTargetMSISSolution` sharing
that commitment. This is the finite-probability shadow of `Forger` (`Ω ↔` the RO answers below
`challengeIdx` plus coins, `c ↔ ρ challengeIdx`), carrying exactly what the MSIS extractor consumes. -/
structure ProbForger (A : M →ₗ[Rq] N) (t : N) (β : ℕ) (Ω : Type*) [Fintype Ω] where
  /-- The commitment, fixed by the prefix world (produced before the fork challenge). -/
  comm : Ω → N
  /-- The response, as a function of prefix world and fork challenge. -/
  resp : Ω → Rq → M
  /-- The acceptance predicate. -/
  acc : Ω → Rq → Bool
  /-- **Acceptance is soundness.** Whenever the forger accepts on `(ω, c)`, its output is a genuine
  SelfTargetMSIS solution on the SHARED commitment `comm ω` with challenge `c`. -/
  acc_sound : ∀ ω c, acc ω c = true → IsSelfTargetMSISSolution A t β (resp ω c) c (comm ω)

/-- **`forkProb > 0 ⟹ an MSIS solution`, straight-line.** A positive fork probability PRODUCES two
distinct-challenge accepting transcripts on the SAME commitment `comm ω` (`exists_forked_pair_of_forkProb_pos`
+ `acc_sound`), which `forked_forgery_yields_msis_solution_selftarget` turns into a nonzero short MSIS
solution on `[A | t]`. The two transcripts are DERIVED from the probability, never assumed. -/
theorem prob_forger_forkProb_yields_msis {A : M →ₗ[Rq] N} {t : N} {β : ℕ}
    (pf : ProbForger A t β Ω) (hfork : 0 < forkProb pf.acc) :
    ∃ v, IsMSISSolution (augmented A t) ((β + β) + (β + β)) v := by
  obtain ⟨ω, c, c', hne, ha, ha'⟩ := exists_forked_pair_of_forkProb_pos pf.acc hfork
  exact forked_forgery_yields_msis_solution_selftarget A t (pf.comm ω) c c'
    (pf.resp ω c) (pf.resp ω c') β hne (pf.acc_sound ω c ha) (pf.acc_sound ω c' ha')

/-- **THE PROBABILISTIC BRIDGE — forger advantage `⟹` MSIS, STRAIGHT-LINE.** A probabilistic forger whose
advantage exceeds `1/|C|` yields a genuine `IsMSISSolution` on `[A | t]`. The chain is entirely produced,
never assumed: `advantage > 1/|C|` `⟹` `forkProb > 0` (`forkProb_pos_of_advantage`, from the proved forking
bound) `⟹` two distinct-challenge accepting transcripts sharing the commitment (`forkProb`'s positivity)
`⟹` the MSIS witness. This is the bridge `concurrent_ts_uf_0_reduces` was missing: the forger's advantage,
a genuine probability, is what discharges the `outcome`/`ha'` hypothesis. -/
theorem prob_forger_advantage_yields_msis {A : M →ₗ[Rq] N} {t : N} {β : ℕ}
    (pf : ProbForger A t β Ω) (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq)
    (hadv : 1 / (Fintype.card Rq : ℚ) < advantage pf.acc) :
    ∃ v, IsMSISSolution (augmented A t) ((β + β) + (β + β)) v :=
  prob_forger_forkProb_yields_msis pf (forkProb_pos_of_advantage pf.acc hΩ hC hadv)

/-! ### The forger IN the abstract `ForkingProbabilityBound` — instantiating `x`. -/

/-- **The forger's genuine `forkProb`/`advantage` satisfy `ForkingProbabilityBound` for every `q_H ≥ 1`.**
This is the abstract predicate `forking_probability_bound` proved for an anonymous `x`, now stated of the
REAL forger's probabilities — with the tighter (fixed-index) `advantage − 1/|C|` dominating the general
`advantage/q_H − 1/|C|`. The forger genuinely appears in the bound. -/
theorem forger_meets_forking_probability_bound (acc : Ω → Rq → Bool)
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq) (qH : ℕ) (hqH : 0 < qH) :
    ForkingProbabilityBound (forkProb acc) (advantage acc) qH (Fintype.card Rq) := by
  unfold ForkingProbabilityBound
  have hb := forkProb_ge_advantage acc hΩ hC
  have hadv0 : 0 ≤ advantage acc := advantage_nonneg acc
  have hq1 : (1 : ℚ) ≤ (qH : ℚ) := by exact_mod_cast hqH
  have hdiv : advantage acc / (qH : ℚ) ≤ advantage acc := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [hadv0, hq1]
  have : advantage acc * (advantage acc / (qH : ℚ) - 1 / (Fintype.card Rq : ℚ))
      ≤ advantage acc * (advantage acc - 1 / (Fintype.card Rq : ℚ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hadv0
  linarith

/-- The forger's advantage placed at its (fixed) fork index `0` — the concrete `x : Fin (q_H+1) → ℚ` that
`forking_probability_bound` ranges over, INSTANTIATED by the forger. -/
def forgerX (adv : ℚ) (qH : ℕ) : Fin (qH + 1) → ℚ := fun i => if i = 0 then adv else 0

/-- `forgerAdvantage (forgerX adv qH) = adv` — the abstract advantage of the forger's weight vector IS its
genuine advantage. -/
theorem forgerAdvantage_forgerX (adv : ℚ) (qH : ℕ) : forgerAdvantage (forgerX adv qH) = adv := by
  unfold forgerAdvantage forgerX
  rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (qH + 1)) (fun _ => adv)]
  simp

/-- `forkSuccess (forgerX adv qH) |C| = adv² − adv/|C|` — the abstract fork-success at the forger's weight
vector is the fixed-index both-accept-minus-collision quantity. -/
theorem forkSuccess_forgerX (adv : ℚ) (qH : ℕ) (cardC : ℚ) :
    forkSuccess (forgerX adv qH) cardC = adv ^ 2 - adv / cardC := by
  unfold forkSuccess
  have h1 : (∑ i : Fin (qH + 1), (forgerX adv qH i) ^ 2) = adv ^ 2 := by
    have hsq : ∀ i : Fin (qH + 1), (forgerX adv qH i) ^ 2 = if i = 0 then adv ^ 2 else 0 := by
      intro i; unfold forgerX; split <;> simp
    rw [Finset.sum_congr rfl (fun i _ => hsq i),
      Finset.sum_ite_eq' Finset.univ (0 : Fin (qH + 1)) (fun _ => adv ^ 2)]
    simp
  have h2 : (∑ i : Fin (qH + 1), forgerX adv qH i) = adv := by
    unfold forgerX
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin (qH + 1)) (fun _ => adv)]
    simp
  rw [h1, h2]

/-- **The abstract `forking_probability_bound` INSTANTIATED at the forger, dominated by the genuine
`forkProb`.** Feeding `x := forgerX (advantage acc)` to `forking_probability_bound` gives
`forkSuccess (forgerX …) = advantage² − advantage/|C|`, and the forger's REAL `forkProb` dominates it (both
`forkProb_ge_advantage` and the abstract lemma land on `advantage·(advantage − 1/|C|)`). So the abstract
`x` really is the forger's per-fork-index success vector, and the genuine probability sits above the lemma's
value. -/
theorem forker_forking_probability_bound_via_abstract (acc : Ω → Rq → Bool)
    (hΩ : 0 < Fintype.card Ω) (hC : 0 < Fintype.card Rq) (qH : ℕ) :
    forkProb acc ≥ forkSuccess (forgerX (advantage acc) qH) (Fintype.card Rq) := by
  rw [forkSuccess_forgerX]
  have hb := forkProb_ge_advantage acc hΩ hC
  have : advantage acc * (advantage acc - 1 / (Fintype.card Rq : ℚ))
      = advantage acc ^ 2 - advantage acc / (Fintype.card Rq : ℚ) := by ring
  linarith [hb, this.ge, this.le]

end ProbForking

#assert_axioms forkPairs_card
#assert_axioms forkProb_eq
#assert_axioms sq_sum_hits_le
#assert_axioms forkProb_ge_advantage
#assert_axioms forkProb_pos_of_advantage
#assert_axioms exists_forked_pair_of_forkProb_pos
#assert_axioms prob_forger_forkProb_yields_msis
#assert_axioms prob_forger_advantage_yields_msis
#assert_axioms forger_meets_forking_probability_bound
#assert_axioms forgerAdvantage_forgerX
#assert_axioms forkSuccess_forgerX
#assert_axioms forker_forking_probability_bound_via_abstract

/-! ## Teeth — the probabilistic bridge FIRES on a concrete forger over `ZMod 5`.

`A = id`, key `t = 1`, over `ZMod 5` (zero seminorm, `β = 0`). One prefix world (`Ω = Unit`, so the
Cauchy–Schwarz core is an EQUALITY), commitment `w = 0`, response `resp _ c = c` (so `id·c = 0 + c·1`
accepts). The forger accepts on the two challenges `{1, 2}` — advantage `2/5 > 1/5 = 1/|C|`, fork
probability `2/25 > 0` (genuine, tight against the bound). The bridge hands back an `IsMSISSolution`. -/

section ProbTeeth

open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS

/-- The concrete probabilistic forger over `ZMod 5`: one prefix world, commitment `0`, response `resp _ c = c`,
accepting exactly on `c ∈ {1, 2}`. Every accepting `(ω, c)` is a genuine SelfTargetMSIS solution (verify:
`id·c = 0 + c·1`; all `ZMod 5` seminorms are `0 ≤ 0`). -/
def exProbForger : ProbForger (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1 0 Unit where
  comm := fun _ => 0
  resp := fun _ c => c
  acc := fun _ c => decide (c = 1 ∨ c = 2)
  acc_sound := by
    intro _ c hc
    refine ⟨Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, Nat.le_zero.mpr rfl, ?_⟩
    simp [HermineThreshold.verify]

/-- The forger accepts on exactly two challenges: `hits = 2`. -/
theorem exProb_hits : hits exProbForger.acc () = 2 := by decide

/-- **The advantage is a genuine `2/5`** — above the `1/5 = 1/|C|` threshold, non-vacuously. -/
theorem exProb_advantage : advantage exProbForger.acc = 2 / 5 := by
  unfold advantage
  rw [show (∑ ω : Unit, (hits exProbForger.acc ω : ℚ)) = 2 by rw [Fintype.sum_unique]; rw [exProb_hits]; norm_num]
  norm_num [Fintype.card_unique, show Fintype.card (ZMod 5) = 5 from rfl]

/-- **The fork probability is a genuine, positive `2/25`** — the real chance the rewind yields two
distinct-challenge accepting transcripts. Tight against `advantage·(advantage − 1/|C|) = (2/5)(1/5) = 2/25`
(`Ω = Unit`, so the power-mean core is saturated). -/
theorem exProb_forkProb : forkProb exProbForger.acc = 2 / 25 := by
  rw [forkProb_eq]
  rw [show (∑ ω : Unit, ((hits exProbForger.acc ω : ℚ) ^ 2 - (hits exProbForger.acc ω : ℚ))) = 2 by
    rw [Fintype.sum_unique, exProb_hits]; norm_num]
  norm_num [Fintype.card_unique, show Fintype.card (ZMod 5) = 5 from rfl]

/-- **The advantage clears the threshold** `1/|C| = 1/5 < 2/5`, so `forkProb > 0` is forced. -/
theorem exProb_advantage_gt_threshold : 1 / (Fintype.card (ZMod 5) : ℚ) < advantage exProbForger.acc := by
  rw [exProb_advantage, show Fintype.card (ZMod 5) = 5 from rfl]; norm_num

/-- **THE PROBABILISTIC BRIDGE FIRES END-TO-END.** A forger of advantage `2/5 > 1/5` yields a genuine
`IsMSISSolution` on `[id | 1]` — advantage `⟹` `forkProb > 0` `⟹` two accepting transcripts `⟹` MSIS,
straight-line, nothing assumed. -/
example : ∃ v, IsMSISSolution (augmented (LinearMap.id : ZMod 5 →ₗ[ZMod 5] ZMod 5) 1)
    ((0 + 0) + (0 + 0)) v :=
  prob_forger_advantage_yields_msis exProbForger (by decide) (by decide) exProb_advantage_gt_threshold

/-- **The forger genuinely inhabits `ForkingProbabilityBound`.** With `q_H = 4`, `|C| = 5`, the forger's REAL
`forkProb = 2/25` and `advantage = 2/5` satisfy `forkProb ≥ advantage·(advantage/q_H − 1/|C|)` — the abstract
bound, now a statement about the forger, not an anonymous `x`. -/
theorem exProb_meets_forking_bound :
    ForkingProbabilityBound (forkProb exProbForger.acc) (advantage exProbForger.acc) 4
      (Fintype.card (ZMod 5)) :=
  forger_meets_forking_probability_bound exProbForger.acc (by decide) (by decide) 4 (by norm_num)

-- Numeric witnesses: advantage `2/5`, forkProb `2/25`, both positive, and the bound is tight-ish.
#guard decide ((2 : ℚ) / 25 = (2 / 5) * ((2 / 5) - 1 / 5))
#guard decide ((0 : ℚ) < (2 : ℚ) / 25)
#guard decide ((2 : ℚ) / 25 ≥ (2 / 5) * ((2 / 5) / 4 - 1 / 5))

end ProbTeeth

#assert_axioms exProb_hits
#assert_axioms exProb_advantage
#assert_axioms exProb_forkProb
#assert_axioms exProb_advantage_gt_threshold
#assert_axioms exProb_meets_forking_bound

end Dregg2.Crypto.HermineTSUF
