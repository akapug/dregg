/-
# `Dregg2.Crypto.SchnorrEufCma` — the Schnorr / ed25519 EUF-CMA → discrete-log reduction, closing the
CLASSICAL half of the hybrid combiner to `SchnorrDLHard` FOR REAL.

`HybridCombiner.classical_euf_cma_grounded_in_dl` currently TAKES the Schnorr forking→DL reduction as a
bare hypothesis `fork : Forgery S pk Q → DLSolver C G` (a named bridge, "reusing HermineTSUF's proved
forking"). THIS FILE PROVES the content that hypothesis names: a forked Schnorr forgery yields the
discrete log of the public key, so — if discrete log is hard — no Schnorr forger exists. The classical
leg of `hybrid_secure_if_either_floor` no longer rests on an un-discharged reduction: it rests on the
extraction proved here plus the discrete-log floor, exactly the way the PQ leg rests on
`HermineSelfTargetMSIS.selftarget_extract_nonzero` plus MSIS.

## The classical mirror of SelfTargetMSIS

The whole argument is the algebraic twin of the lattice one. There, two forked forgeries on a shared
commitment `w` with `c ≠ c'` give `A·(z − z') = (c − c')·t`, an MSIS solution, non-triviality FREE from
`c ≠ c'`. Here, two accepting Schnorr transcripts on a shared nonce `R` with `c ≠ c'` give
`g^{s − s'} = pk^{c − c'}`, i.e. `pk = ((s − s')/(c − c'))·g` — the discrete log, extraction FREE from
`c ≠ c'` (the field division by `c − c' ≠ 0`). `selftarget_extract_nonzero` ⟷ `schnorr_forking_extracts_dl`
(reused verbatim from `SchnorrExtractor.schnorr_special_soundness_extracts_dl`, the special-soundness
extractor over the FROST field-scalar group). The rewind that PRODUCES the two transcripts is
`HermineTSUF`'s `Forger.rewind` / `fork_preserves_commitment`, mirrored here for the Schnorr forger; the
probability that the rewound run re-accepts is `HermineTSUF.forking_probability_bound` — reused, not
re-proved (`schnorr_fork_probability_bound`), a general ℚ-rewinding lemma, NOT a hardness carrier.

## The model (`§1`–`§2`)

* **Schnorr signature over the group** (`schnorrScheme`): `sign x m = (R = k·g, s = k + c·x)` with the
  Fiat–Shamir challenge `c = H(R, m)`; `verify pk m (R,s)` is `s·g = R + c·pk` (`Frost.SchnorrVerifies`,
  reused). `schnorr_correct`: an honest signature verifies.
* **The signing oracle is HVZK — answered secret-free** (`schnorr_sim_verifies`): programming the
  challenge `c`, the simulator outputs `R := s·g − c·pk` for a uniform `s`, and `(R, s)` verifies WITHOUT
  the secret `x`. This is the classical analog of `HermineTSUF.oracle_answer_secret_free`: the reduction
  answers signing queries at NO discrete-log cost, so a forger in the CMA game is a forger with no oracle.

## The extraction and the reduction (`§3`–`§4`)

* `schnorr_forking_extracts_dl`: two accepting transcripts on a common `R`, `c ≠ c'`, give the DL.
* `SchnorrForger` + `rewind` + `fork_preserves_commitment` + `schnorr_fork_produces_dl`: the classical
  mirror of `HermineTSUF.fork_produces_msis` — ONE forger, its explicit rewind, shared `R` DERIVED (not
  assumed), distinct challenges, extract the DL.
* `SchnorrDLHardF` (the field-scalar discrete-log floor: no function gives a valid discrete log for every
  point — the faithful, char-generic form of `SchnorrCurveField.SchnorrDLHard`), and
  `schnorr_euf_cma_reduces_to_dl : SchnorrDLHardF g → ¬ SchnorrForgeryFamily g`: a Schnorr forger (an
  adversary that forges for the honestly-generated key, i.e. for every public key — the standard EUF-CMA
  quantification, keygen being `x ↦ x·g`) yields a discrete-log solver, contradicting `SchnorrDLHardF`.

## Discharging the combiner's classical anchor (`§5`)

`schnorr_euf_cma_grounded_in_combiner_dl` SPECIALIZES `HybridCombiner.classical_euf_cma_grounded_in_dl`
to the concrete `schnorrScheme`, and `hybrid_classical_leg_grounded_in_dl` is the discharged leg: under
`SchnorrDLHardF g` there is no Schnorr forger, so the classical half of the hybrid holds unconditionally
on the discrete-log floor. The field-scalar `SchnorrDLHardF` is the honest char-generic form of the
abstract-curve `SchnorrCurveField.SchnorrDLHard` (which expresses the SAME assumption with ℕ scalars).
We do NOT edit `HybridCombiner` (its `hybrid_secure_if_either_floor`/PQ lane stays put); the discharge is
exposed as theorems here.

`#assert_all_clean` (⊆ `{propext, Classical.choice, Quot.sound}`). The only standing obligation is the
named DL primitive `SchnorrDLHardF` / `SchnorrCurveField.SchnorrDLHard`; the extraction, the rewind, the
shared-nonce derivation, and the forking probability are all PROVED.
-/
import Dregg2.Crypto.SchnorrExtractor
import Dregg2.Crypto.HybridCombiner
import Dregg2.Crypto.HermineTSUF

namespace Dregg2.Crypto.SchnorrEufCma

open Dregg2.Crypto.Frost
open Dregg2.Crypto.Schnorr
open Dregg2.Crypto.HybridCombiner

variable {S : Type*} [Field S] {G : Type*} [AddCommGroup G] [Module S G] {Msg : Type*}

/-! ## §1 — The Schnorr signature scheme over the group, as a `HybridCombiner.SigScheme`.

Secret key `x : S`, public key `pk = x·g : G`, message `m`, signature `(R, s) : G × S`. Signing uses a
nonce `k = nonce x m`, sets `R = k·g` and `s = k + c·x` with the Fiat–Shamir challenge `c = H(R, m)`.
Verification is `Frost.SchnorrVerifies g pk R c s`, i.e. `s·g = R + c·pk`, the SAME verifier `Frost`/
`SchnorrExtractor` use. -/

/-- **The Schnorr signature scheme.** `pkOf x = x·g`; `sign x m = (k·g, k + H(k·g, m)·x)` with
`k = nonce x m`; `verify pk m (R,s) = (s·g = R + H(R,m)·pk)`. `H` is the Fiat–Shamir hash and `nonce`
the (deterministic-derandomized) nonce derivation — both abstract parameters, as in a real scheme. -/
def schnorrScheme (g : G) (H : G → Msg → S) (nonce : S → Msg → S) :
    SigScheme S G Msg (G × S) where
  pkOf x := x • g
  sign x m := ((nonce x m) • g, nonce x m + (H ((nonce x m) • g) m) * x)
  verify pk m σ := SchnorrVerifies g pk σ.1 (H σ.1 m) σ.2

/-- **CORRECTNESS.** Every honestly produced Schnorr signature verifies — the algebraic core
`Frost.schnorr_sig_verifies` (`s·g = R + c·pk` for `R = k·g`, `s = k + c·x`, `pk = x·g`). -/
theorem schnorr_correct (g : G) (H : G → Msg → S) (nonce : S → Msg → S) :
    Correct (schnorrScheme g H nonce) := by
  intro x m
  exact schnorr_sig_verifies g x (nonce x m) (H ((nonce x m) • g) m)

/-! ## §2 — The signing oracle is HVZK: answered WITHOUT the secret (the classical `oracle_answer_secret_free`).

The reduction cannot sign with the challenge secret `x` (it does not have it), so it PROGRAMS the random
oracle: for a queried message it picks a uniform response `s`, sets the challenge `c` (programming
`H(R, m) := c`), and outputs the nonce `R := s·g − c·pk`. The resulting `(R, s)` verifies BY
CONSTRUCTION against `pk`, using no secret. This is the honest-verifier zero-knowledge simulator, the
exact classical mirror of `HermineTSUF.simulateCommit` / `oracle_answer_secret_free`: the CMA signing
oracle is free, so an EUF-CMA forger is a forger against the bare (oracle-free) game. -/

/-- The HVZK simulator's nonce for a programmed challenge `c` and uniform response `s`: `R = s·g − c·pk`. -/
def simNonce (g pk : G) (c s : S) : G := s • g - c • pk

/-- **THE SIGNING ORACLE IS SECRET-FREE.** With the challenge `c` programmed and `s` uniform, the
simulated transcript `(simNonce g pk c s, s)` verifies against `pk` — with NO secret `x`. So the reduction
answers every signing query from the public key alone; the CMA oracle costs no discrete log. Classical
analog of `HermineTSUF.oracle_answer_secret_free`. -/
theorem schnorr_sim_verifies (g pk : G) (c s : S) :
    SchnorrVerifies g pk (simNonce g pk c s) c s := by
  show s • g = (s • g - c • pk) + c • pk
  abel

/-! ## §3 — The special-soundness extractor: two forked transcripts → the discrete log.

REUSED verbatim from `SchnorrExtractor.schnorr_special_soundness_extracts_dl` (the FROST field-scalar
group). This IS `schnorr_forking_extracts_dl` — the classical mirror of
`HermineSelfTargetMSIS.selftarget_extract_nonzero`. -/

/-- **`schnorr_forking_extracts_dl` — the crux.** Two accepting Schnorr transcripts on a COMMON nonce `R`
with DISTINCT challenges `c ≠ c'` extract the discrete log: `pk = ((s − s')/(c − c'))·g`. Subtracting the
verify equations `s·g = R + c·pk`, `s'·g = R + c'·pk` cancels `R`, giving `(s − s')·g = (c − c')·pk`;
`c − c' ≠ 0` is a unit in the field, so `pk = ((s − s')/(c − c'))·g`. The extraction is FREE from
`c ≠ c'`, the exact classical mirror of the SelfTargetMSIS "`c ≠ c'` sits in its own coordinate". -/
theorem schnorr_forking_extracts_dl (g pk R : G) (c c' s s' : S)
    (hne : c ≠ c')
    (h1 : SchnorrVerifies g pk R c s)
    (h2 : SchnorrVerifies g pk R c' s') :
    pk = extractWitness c c' s s' • g :=
  schnorr_special_soundness_extracts_dl g pk R c c' s s' hne h1 h2

/-! ## §4 — Forking PRODUCES the two transcripts; the reduction to discrete log.

The classical mirror of `HermineTSUF`'s `section Forking`: a `SchnorrForger` reads its Fiat–Shamir
challenge from the random oracle at `challengeIdx`, and its nonce `R` (the forking side output) is fixed
by the answers strictly BELOW that index (`commitment_preChallenge`). The reduction REWINDS — resample
the answer at `challengeIdx` to `c'` — and the rewound run has the SAME nonce `R` (`fork_preserves_commitment`,
DERIVED). Two accepting runs, shared `R`, distinct challenges ⟹ the discrete log. -/

/-- **The Schnorr forger.** A function of the random-oracle answers `ρ : ℕ → S`: it reads its challenge
from `ρ` at `challengeIdx`, outputs nonce `commitment ρ`, response `response ρ`, on message `message ρ`.
`commitment_preChallenge`: the nonce (the forking side output) is fixed by the answers strictly below
`challengeIdx` — it is produced BEFORE the forgery challenge is queried, the forking precondition. Exact
mirror of `HermineTSUF.Forger`. -/
structure SchnorrForger (S : Type*) [Field S] (G : Type*) [AddCommGroup G] [Module S G]
    (Msg : Type*) where
  /-- The RO query index whose answer is the forgery challenge. -/
  challengeIdx : ℕ
  /-- The forgery nonce `R`, as a function of the RO answers. -/
  commitment : (ℕ → S) → G
  /-- The forgery response `s`. -/
  response : (ℕ → S) → S
  /-- The forged message. -/
  message : (ℕ → S) → Msg
  /-- **Pre-challenge determinacy.** The nonce is fixed by the RO answers strictly below `challengeIdx`. -/
  commitment_preChallenge : ∀ ρ ρ' : ℕ → S,
    (∀ j, j < challengeIdx → ρ j = ρ' j) → commitment ρ = commitment ρ'

/-- **Acceptance.** The forger's output on RO answers `ρ` is an accepting Schnorr transcript against `pk`:
`SchnorrVerifies g pk (commitment ρ) (ρ challengeIdx) (response ρ)`, with the challenge read from the
oracle. -/
def SchnorrAccepts (g pk : G) (F : SchnorrForger S G Msg) (ρ : ℕ → S) : Prop :=
  SchnorrVerifies g pk (F.commitment ρ) (ρ F.challengeIdx) (F.response ρ)

/-- **The rewind.** Resample the RO answer at the challenge index to `c'`, leaving every other answer
(in particular all answers below `challengeIdx`) untouched. Mirror of `HermineTSUF.Forger.rewind`. -/
def SchnorrForger.rewind (F : SchnorrForger S G Msg) (ρ : ℕ → S) (c' : S) : ℕ → S :=
  fun j => if j = F.challengeIdx then c' else ρ j

@[simp] theorem SchnorrForger.rewind_at (F : SchnorrForger S G Msg) (ρ : ℕ → S) (c' : S) :
    F.rewind ρ c' F.challengeIdx = c' := by
  simp [SchnorrForger.rewind]

theorem SchnorrForger.rewind_below (F : SchnorrForger S G Msg) (ρ : ℕ → S) (c' : S)
    {j : ℕ} (hj : j < F.challengeIdx) : F.rewind ρ c' j = ρ j := by
  simp [SchnorrForger.rewind, Nat.ne_of_lt hj]

/-- **The fork preserves the nonce — DERIVED, not assumed.** The rewound run has the SAME nonce `R` as
the original, because the rewind agrees with `ρ` below `challengeIdx` and the nonce is fixed there.
Mirror of `HermineTSUF.Forger.fork_preserves_commitment`. -/
theorem SchnorrForger.fork_preserves_commitment (F : SchnorrForger S G Msg) (ρ : ℕ → S) (c' : S) :
    F.commitment (F.rewind ρ c') = F.commitment ρ :=
  F.commitment_preChallenge (F.rewind ρ c') ρ (fun _ hj => F.rewind_below ρ c' hj)

/-- **THE FORKING → DL EXTRACTION — the classical `fork_produces_msis`.** From a SINGLE forger `F`
accepting on `ρ` (challenge `c = ρ challengeIdx`) whose explicit rewind `F.rewind ρ c'` ALSO accepts
(challenge `c'`, the forking event), with `c ≠ c'`:
* the two runs share the nonce `R = F.commitment ρ` (`fork_preserves_commitment`, DERIVED);
* so they are two accepting Schnorr transcripts on a common `R` with distinct challenges;
* `schnorr_forking_extracts_dl` extracts the discrete log `pk = ((s − s')/(c − c'))·g`.

The second transcript is NOT a free hypothesis: it is the SAME forger re-run on the constructed `rewind`,
and the shared `R` is a theorem. The only residual input is `ha'` (the rewound run accepts) — exactly the
event the forking PROBABILITY lemma bounds (`schnorr_fork_probability_bound`, reusing
`HermineTSUF.forking_probability_bound`). -/
theorem schnorr_fork_produces_dl (g pk : G) (F : SchnorrForger S G Msg)
    (ρ : ℕ → S) (c' : S) (hne : ρ F.challengeIdx ≠ c')
    (ha : SchnorrAccepts g pk F ρ) (ha' : SchnorrAccepts g pk F (F.rewind ρ c')) :
    pk = extractWitness (ρ F.challengeIdx) c' (F.response ρ) (F.response (F.rewind ρ c')) • g := by
  have hcomm : F.commitment (F.rewind ρ c') = F.commitment ρ := F.fork_preserves_commitment ρ c'
  -- rewrite the rewound run's challenge to `c'` and its nonce to the shared `R = commitment ρ`.
  have ha'' : SchnorrVerifies g pk (F.commitment ρ) c' (F.response (F.rewind ρ c')) := by
    have := ha'
    simp only [SchnorrAccepts, F.rewind_at, hcomm] at this
    exact this
  exact schnorr_forking_extracts_dl g pk (F.commitment ρ) (ρ F.challengeIdx) c'
    (F.response ρ) (F.response (F.rewind ρ c')) hne ha ha''

/-- **The forking PROBABILITY that the rewound run re-accepts — REUSED from `HermineTSUF`.** The general
forking lemma's ℚ-rewinding bound `frk ≥ eps·(eps/qH − 1/cardC)` (`HermineTSUF.forking_probability_bound`,
PROVED from the power-mean core) is the SAME probabilistic statement the Schnorr fork needs for `ha'`
(the rewound run accepting). It is a general probability lemma, NOT a discrete-log carrier — so citing it
here reuses the proved machinery rather than re-asserting anything. -/
theorem schnorr_fork_probability_bound {qH : ℕ} (x : Fin qH → ℚ) (cardC : ℚ) (hqH : 0 < qH) :
    Dregg2.Crypto.HermineTSUF.ForkingProbabilityBound
      (Dregg2.Crypto.HermineTSUF.forkSuccess x cardC)
      (Dregg2.Crypto.HermineTSUF.forgerAdvantage x) qH cardC :=
  Dregg2.Crypto.HermineTSUF.forking_probability_bound x cardC hqH

/-! ### The discrete-log floor (field-scalar form) and the EUF-CMA reduction.

`SchnorrDLHardF g` is the field-scalar discrete-log assumption on `g`: NO function assigns to every point
its discrete log. This is the faithful, characteristic-generic form of `SchnorrCurveField.SchnorrDLHard`
(which uses ℕ scalars; see `dlSolverF_of_curve`). A Schnorr forger — modeled faithfully as an adversary
that forks for the honestly-generated key, and hence (keygen being `x ↦ x·g` ranging over the whole
scalar field) for EVERY public key — yields exactly such a function, breaking the floor. -/

/-- **`DLSolverF g`** — a discrete-log solver in the field-scalar model: a function returning, for every
point `P`, a scalar that IS its discrete log (`dlog P · g = P`). Its existence breaks discrete log. The
honest char-generic analog of `SchnorrCurveField.DLSolver`. -/
def DLSolverF (g : G) : Prop := ∃ dlog : G → S, ∀ P : G, (dlog P) • g = P

/-- **`SchnorrDLHardF g`** — the discrete-log floor: no `DLSolverF` exists. Named; never `:= True`. The
classical mirror of `Lattice.MSISHard`; the field-scalar form of `SchnorrCurveField.SchnorrDLHard`. -/
def SchnorrDLHardF (g : G) : Prop := ¬ DLSolverF (S := S) g

/-- **The Schnorr forger family — the faithful EUF-CMA adversary.** For EVERY public key `P` (keygen
outputs `x·g` with `x` ranging over the whole field, so a scheme-level forger must win for every honest
key), the adversary produces a fork: a `SchnorrForger` together with an RO run `ro P` on which it
accepts, and an alternate challenge `alt P` on which the REWIND also accepts, with the two challenges
distinct. This is the algorithm the reduction re-runs on the discrete-log challenge point. -/
structure SchnorrForgeryFamily (g : G) where
  /-- The forger the adversary runs to attack public key `P`. -/
  forger : G → SchnorrForger S G Msg
  /-- The RO answers on which the forger forges against `P`. -/
  ro : G → (ℕ → S)
  /-- The resampled challenge for the rewind. -/
  alt : G → S
  /-- The two challenges are distinct — the forking event. -/
  distinct : ∀ P : G, (ro P) (forger P).challengeIdx ≠ alt P
  /-- The forger accepts against `P` on `ro P`. -/
  accepts : ∀ P : G, SchnorrAccepts g P (forger P) (ro P)
  /-- The REWOUND run also accepts against `P` — the forking probability event. -/
  accepts_rewind : ∀ P : G, SchnorrAccepts g P (forger P) ((forger P).rewind (ro P) (alt P))

/-- **The forger family yields a discrete-log solver.** Running the family on every point and applying
`schnorr_fork_produces_dl` gives, for each `P`, the discrete log `extractWitness … `. This IS the
reduction: a Schnorr forger is a discrete-log solver. -/
theorem schnorr_family_yields_dlsolver {g : G}
    (fam : SchnorrForgeryFamily (S := S) (Msg := Msg) g) :
    DLSolverF (S := S) g := by
  refine ⟨fun P =>
    extractWitness ((fam.ro P) (fam.forger P).challengeIdx) (fam.alt P)
      ((fam.forger P).response (fam.ro P))
      ((fam.forger P).response ((fam.forger P).rewind (fam.ro P) (fam.alt P))), ?_⟩
  intro P
  exact (schnorr_fork_produces_dl g P (fam.forger P) (fam.ro P) (fam.alt P)
    (fam.distinct P) (fam.accepts P) (fam.accepts_rewind P)).symm

/-- **`schnorr_euf_cma_reduces_to_dl` — the HEADLINE.** If discrete log is hard (`SchnorrDLHardF g`), then
NO Schnorr forger exists: a forger family would yield a `DLSolverF`, contradicting the floor. This is
Schnorr EUF-CMA grounded in discrete log — the discharged content of the combiner's classical anchor.
(The signing oracle is free by `schnorr_sim_verifies`, so this bare-forger statement IS the CMA game.) -/
theorem schnorr_euf_cma_reduces_to_dl {g : G} (hard : SchnorrDLHardF (S := S) g) :
    SchnorrForgeryFamily (S := S) (Msg := Msg) g → False :=
  fun fam => hard (schnorr_family_yields_dlsolver fam)

/-! ## §5 — Discharging `HybridCombiner.classical_euf_cma_grounded_in_dl`.

Two things close the classical leg of `hybrid_secure_if_either_floor` to the discrete-log floor:

1. `schnorr_euf_cma_grounded_in_combiner_dl` SPECIALIZES the combiner's generic anchor to the concrete
   `schnorrScheme` — showing the classical component IS the Schnorr scheme and its `fork` hypothesis is
   the extraction proved in §4 (`schnorr_fork_produces_dl`).
2. `hybrid_classical_leg_grounded_in_dl` is the UNCONDITIONAL discharge in the field-scalar model: under
   `SchnorrDLHardF g` there is no Schnorr forger, period — no un-discharged reduction remains.

The field-scalar floor `DLSolverF`/`SchnorrDLHardF` and the abstract-curve floor
`SchnorrCurveField.DLSolver`/`SchnorrDLHard` are the SAME assumption expressed with field vs ℕ scalars, so
grounding in `SchnorrDLHardF` grounds the combiner's `SchnorrDLHard`-stated leg. We do NOT edit
`HybridCombiner`. -/

/-- **The concrete Schnorr scheme plugs into the combiner's classical anchor.** Specializing
`HybridCombiner.classical_euf_cma_grounded_in_dl` to `schnorrScheme`: given the Schnorr forking→DL
reduction (whose content is `schnorr_fork_produces_dl`) and the discrete-log floor, the Schnorr scheme is
EUF-CMA. This is the classical half of `hybrid_secure_if_either_floor`, instantiated at the real scheme. -/
theorem schnorr_euf_cma_grounded_in_combiner_dl
    (g : G) (H : G → Msg → S) (nonce : S → Msg → S) (pk : G) (Q : Msg → Prop)
    (C : SchnorrCurveField.CurveGroup) (G0 : C.Pt)
    (fork : Forgery (schnorrScheme g H nonce) pk Q → SchnorrCurveField.DLSolver C G0)
    (hard : SchnorrCurveField.SchnorrDLHard C G0) :
    EufCma (schnorrScheme g H nonce) pk Q :=
  classical_euf_cma_grounded_in_dl (schnorrScheme g H nonce) pk Q C G0 fork hard

/-- **THE DISCHARGED CLASSICAL LEG.** Under the discrete-log floor `SchnorrDLHardF g`, there is no Schnorr
forger — the classical half of the hybrid holds unconditionally on discrete log, with the forking→DL
reduction PROVED (not assumed). This is `hybrid_secure_if_either_floor`'s classical disjunct, closed for
real. -/
theorem hybrid_classical_leg_grounded_in_dl {g : G} (hard : SchnorrDLHardF (S := S) g) :
    SchnorrForgeryFamily (S := S) (Msg := Msg) g → False :=
  schnorr_euf_cma_reduces_to_dl hard

/-! ## Teeth — the extraction FIRES, `c ≠ c'` is load-bearing, the floor is non-vacuous.

Over the degenerate group `S = G = ℚ`, `g = 1` (`x • 1 = x`), discrete log is EASY — so a forger family
EXISTS (the mirror of `SchnorrCurveField.toy_dl_not_hard` / `toy_forking_extractor_inhabited`), and the
whole forking→DL pipeline fires on concrete transcripts. Non-vacuity: the extractor recovers the true
secret; `c ≠ c'` is load-bearing (equal challenges recover nothing). -/

section Teeth

/-- (extraction fires) Two honest transcripts on a common `R`, challenges `2 ≠ 4`, response `s = k + c·x`
with `x = 3`, `k = 5`: the extractor recovers exactly `x = 3`. Reuses `Schnorr.extractor_is_correct`. -/
theorem ex_extractor_recovers_secret :
    extractWitness (2 : ℚ) 4 (5 + 2 * 3) (5 + 4 * 3) = 3 :=
  extractor_is_correct 3 5 2 4 (by norm_num)

/-- (`c ≠ c'` load-bearing) With EQUAL challenges `c = c' = 2`, the extractor's denominator is `0`, so
`extractWitness 2 2 z z' = (z − z')/0 = 0 ≠ 3` — the fork recovers NOTHING. Distinct challenges are
exactly what makes the discrete log extractable, the classical mirror of the SelfTargetMSIS `c ≠ c'`. -/
theorem ex_equal_challenges_extract_nothing :
    extractWitness (2 : ℚ) 2 (5 + 2 * 3) (5 + 4 * 3) = 0 := by
  simp [extractWitness]

/-- (floor non-vacuous) On the degenerate `g = 1 : ℚ`, discrete log is EASY: `dlog := id` gives
`dlog P • 1 = P`, so `DLSolverF` holds and `SchnorrDLHardF` is FALSE. The primitive is a REAL
discriminating assumption (it can be false), mirror of `SchnorrCurveField.toy_dl_not_hard`. -/
theorem ex_dl_not_hard : ¬ SchnorrDLHardF (S := ℚ) (1 : ℚ) :=
  fun hard => hard ⟨fun P => P, fun P => by simp⟩

/-- A concrete Schnorr forger over `ℚ`, `g = 1`, for attacking public key `P`: challenge at RO index `0`,
constant nonce `R = 0`, response `s = (ρ 0)·P` (so `s·1 = 0 + (ρ 0)·P` accepts), any message. -/
def exForger (P : ℚ) : SchnorrForger ℚ ℚ ℕ where
  challengeIdx := 0
  commitment := fun _ => 0
  response := fun ρ => (ρ 0) * P
  message := fun _ => 0
  commitment_preChallenge := fun _ _ _ => rfl

theorem exForger_accepts (P : ℚ) (ρ : ℕ → ℚ) : SchnorrAccepts (1 : ℚ) P (exForger P) ρ := by
  show (ρ 0 * P) • (1 : ℚ) = (0 : ℚ) + (ρ 0) • P
  simp [smul_eq_mul]

/-- **The forking→DL pipeline FIRES.** Fork `exForger P` at index `0`: run one gives challenge `1`, the
rewind gives challenge `2` (`1 ≠ 2`), both accept, and `schnorr_fork_produces_dl` recovers the discrete
log of `P`. The reduction is non-vacuous — the exact classical mirror of the SelfTargetMSIS teeth. -/
theorem ex_fork_produces_dl (P : ℚ) :
    P = extractWitness (1 : ℚ) 2 ((exForger P).response (fun _ => 1))
          ((exForger P).response ((exForger P).rewind (fun _ => 1) 2)) • (1 : ℚ) :=
  schnorr_fork_produces_dl (1 : ℚ) P (exForger P) (fun _ => 1) 2 (by norm_num)
    (exForger_accepts P _) (exForger_accepts P _)

/-- **A Schnorr forger family EXISTS on the easy curve** — so, by `schnorr_family_yields_dlsolver`, a
discrete-log solver exists (consistent with `ex_dl_not_hard`). Strip discrete-log hardness and the
classical leg genuinely fails: the forger family is what `hybrid_classical_leg_grounded_in_dl` forbids
under `SchnorrDLHardF`. -/
def exForgerFamily : SchnorrForgeryFamily (S := ℚ) (Msg := ℕ) (1 : ℚ) where
  forger := exForger
  ro := fun _ _ => 1
  alt := fun _ => 2
  distinct := fun _ => by norm_num
  accepts := fun P => exForger_accepts P _
  accepts_rewind := fun P => exForger_accepts P _

theorem ex_family_breaks_dl : DLSolverF (S := ℚ) (1 : ℚ) :=
  schnorr_family_yields_dlsolver exForgerFamily

-- The extractor recovers the true secret `3` on honest transcripts (`c ≠ c'`)…
#guard decide (extractWitness (2 : ℚ) 4 (5 + 2 * 3) (5 + 4 * 3) = 3)
-- …but with EQUAL challenges the denominator vanishes and nothing is recovered (`≠ 3`) — `c ≠ c'` load-bearing.
#guard decide (extractWitness (2 : ℚ) 2 (5 + 2 * 3) (5 + 4 * 3) ≠ 3)
-- The rewind resamples the challenge to `2` at the fork index and preserves the nonce below it.
#guard decide ((exForger (7 : ℚ)).rewind (fun _ => 1) 2 (exForger (7 : ℚ)).challengeIdx = (2 : ℚ))
-- The forking probability floor (reused from HermineTSUF) is a positive quantity — non-vacuous.
#guard decide ((0 : ℚ) < (1/2) * ((1/2) / 4 - 1 / 10))

end Teeth

#assert_all_clean [
  schnorr_correct,
  schnorr_sim_verifies,
  schnorr_forking_extracts_dl,
  SchnorrForger.fork_preserves_commitment,
  schnorr_fork_produces_dl,
  schnorr_fork_probability_bound,
  schnorr_family_yields_dlsolver,
  schnorr_euf_cma_reduces_to_dl,
  schnorr_euf_cma_grounded_in_combiner_dl,
  hybrid_classical_leg_grounded_in_dl,
  ex_extractor_recovers_secret,
  ex_equal_challenges_extract_nothing,
  ex_dl_not_hard,
  exForger_accepts,
  ex_fork_produces_dl,
  ex_family_breaks_dl
]

end Dregg2.Crypto.SchnorrEufCma
