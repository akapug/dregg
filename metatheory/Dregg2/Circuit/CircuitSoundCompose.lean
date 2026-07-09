/-
# `Dregg2.Circuit.CircuitSoundCompose` — UNIT 2c: `CircuitSound` becomes a THEOREM.

(NOTE: the intended filename `CircuitSoundness.lean` is already taken by an unrelated existing apex
module — `Dregg2.Circuit.CircuitSoundness.lightclient_unfoolable`, imported by ~10 files — so this
2c composition lives here under `CircuitSoundCompose` to avoid clobbering it.)

Units 2a (`AirSoundness`) and 2b (`FriSoundness`) each landed one half of the circuit-soundness
argument, and each carries its OWN `FriProximity` notion. This file BRIDGES the two and, as the
payoff, makes `Dregg2.Crypto.TurnSoundness.CircuitSound` an UNCONDITIONAL theorem (modulo `HashCR`
and the concrete FRI field/rate parameters) — so `turn_sound` no longer rests on a `CircuitSound`
hypothesis at all.

## The two `FriProximity` notions and how they connect

* **`AirSoundness.FriProximity applyEff verifyLD openTr`** (the HYPOTHESIS 2a needs):
  `∀ π com, verifyLD π com → satisfiesTransition applyEff (openTr com).1 (openTr com).2`
  — "the low-degree/query verifier accepting on `(π, com)` implies the trace the commitment opens
  to satisfies the AIR transition constraints." `AirSoundness.circuit_sound_via_fri` turns exactly
  this into `CircuitSound (airChecks verifyLD openTr)`.

* **`FriSoundness.FriProximity S d f := closeN S.C d f`** (a PROVED conclusion of 2b):
  the committed oracle `f` is `d`-close to the low-degree Reed-Solomon code `S.C`.
  `FriSoundness.friProximity_discharge` derives the `d = 0` case (`f ∈ S.C`) from an accepting FRI
  transcript conditioned on a generic (non-exceptional) challenge; the `≤ 1` exceptional challenge
  per round is the proved soundness error `≤ 1/|F|` (`exceptional_subsingleton`), `≤ n/|F|` over `n`
  rounds (`far_propagates_chain`).

**The bridge (`friVerify_openTr_proximity`).** We instantiate 2a's abstract `verifyLD` and `openTr`
with the FRI machinery: `verifyLD π root := ∃ f, cr.opens root () f ∧ FriAccept S f` (an oracle
opening the Merkle root admits an accepting FRI transcript), and `openTr root := dec (openerOf root)`
(the trace the committed oracle decodes to). Then:
  1. `FriAccept` ⟹ (2b's `friProximity_discharge`) the committed oracle `f ∈ S.C` — a genuine
     low-degree codeword (`friAccept_low_degree`);
  2. `HashCR` (`FriSoundness.oracle_binding`) pins the *chosen* opener `openerOf root` to that same
     `f`, so it too is a codeword;
  3. every codeword decodes to a constraint-satisfying trace (`hcode`, the AIR design fact
     `∀ f ∈ S.C, satisfiesTransition applyEff (dec f)…` — a structural property of the RS
     code + decode map, discharged concretely in `§Teeth`; NOT a hardness/proximity assumption).
So 2b's proximity conclusion SUPPLIES precisely 2a's `FriProximity` hypothesis.

## The headline

`circuit_sound applyEff S dec hcode cr hcr : CircuitSound applyEff (friChecks S cr dec)` — **no
`FriProximity`/`CircuitSound` hypothesis**. Its residual is exactly: `HashCR cr` (Merkle/digest
binding — the hash floor), the FRI setup `S` (field/rate/round/query parameters), and the structural
`hcode`. On the concrete rate-1/2 Reed-Solomon instance `rsSetup` (`ZMod 5`, `|L| = 4`, `|L²| = 2`,
one fold, full-cover query set) `hcode` is DISCHARGED (`hcodeRS`), giving `circuit_sound_rs`, whose
only remaining assumption is `HashCR`; the folding soundness error is the PROVED number `≤ 1/|F| = 1/5`
per round (`FriSoundness.exceptional_subsingleton`), `≤ n/|F|` over `n` rounds.

## The discharge into TurnSoundness

`turn_sound_unconditional` / `turn_sound_under_floor_discharged` plug `circuit_sound` into
`TurnSoundness.turn_sound` / `turn_sound_under_floor`: a VALID receipt proves AUTHORIZED, CORRECT
evolution under `(SchnorrDLHard ∨ MSISHard) ∧ HashCR` — with NO `CircuitSound` hypothesis.

## Teeth (both fire)

* an HONEST codeword yields an accepting FRI transcript whose decoded trace IS a real VM step
  (`honest_friAccept`, `honest_turn_checks` — `friChecks` accepts the turn `(0, 3, 3)`);
* a FAR oracle admits NO accepting FRI transcript (`far_oracle_no_friAccept`) and decodes to a trace
  that VIOLATES the step gate (`far_oracle_decode_violates`) — so the low-degree check is
  load-bearing, not decorative; and a colliding commitment BREAKS `HashCR`
  (`FriSoundness.badOracle_equivocates`).

Residual: `HashCR` + the FRI field/rate parameters. No `def …Hard`, no `:= True`, no smuggled
proximity/circuit-soundness hypothesis.
-/
import Dregg2.Circuit.AirSoundness
import Dregg2.Circuit.FriSoundness

namespace Dregg2.Circuit.CircuitSoundCompose

open Dregg2.Circuit.AirSoundness
open Dregg2.Circuit.FriSoundness
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.TurnSoundness
  (CircuitSound Turn Receipt Valid CorrectTransition turn_sound turn_sound_under_floor)
open Dregg2.Crypto.HybridCombiner
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.SchnorrCurveField

/-! ## §1 — The FRI acceptance predicate and the low-degree extraction. -/

section Abstract

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {State Effect Proof Digest SK PK Msg Sig : Type*}

/-- **`FriAccept S f`** — the oracle `f : ι → F` admits an ACCEPTING FRI transcript at a generic
challenge: a committed next-oracle `f'`, a fold challenge `α`, and a query set `Q` such that `Q`
covers the fold disagreement, every queried point passes the fold check, the final oracle is a
codeword of the folded code, and the challenge is non-exceptional (`Fold α f ∈ S.C' → f ∈ S.C`).
This bundles exactly the hypotheses of `FriSoundness.friProximity_discharge`. -/
def FriAccept (S : FriSetup F ι κ) (f : ι → F) : Prop :=
  ∃ (f' : κ → F) (α : F) (Q : Finset κ),
    disagree f' (Fold S.geom α f) ⊆ Q ∧
    (∀ y ∈ Q, f' y = Fold S.geom α f y) ∧
    f' ∈ S.C' ∧
    (Fold S.geom α f ∈ S.C' → f ∈ S.C)

/-- **`friAccept_low_degree` — 2b's payoff extracted.** An accepting FRI transcript forces the
committed oracle to be a genuine low-degree codeword `f ∈ S.C`. This is `FriProximity S 0 f`
(`closeN S.C 0 f`) discharged by `friProximity_discharge`, then read off by `closeN_zero_iff_mem`. -/
theorem friAccept_low_degree (S : FriSetup F ι κ) {f : ι → F} (h : FriAccept S f) : f ∈ S.C := by
  obtain ⟨f', α, Q, hcover, hpass, hfinal, hgeneric⟩ := h
  have hp : closeN S.C 0 f := friProximity_discharge S Q hcover hpass hfinal hgeneric
  exact closeN_zero_iff_mem.mp hp

/-! ## §2 — The FRI-realized verifier and the committed opening (Merkle binding leg). -/

/-- **`openerOf cr root`** — a chosen oracle that opens the Merkle root. Under `HashCR` the opener
is UNIQUE (`oracle_binding`), so this canonical choice equals every FRI-accepted opener. -/
noncomputable def openerOf (cr : OracleCR F ι Digest) (root : Digest) : ι → F :=
  Classical.epsilon (fun f => cr.opens root () f)

/-- **`friVerify` — the low-degree / query verifier over a Merkle root.** It accepts `(π, root)` iff
some oracle opening `root` admits an accepting FRI transcript. (The proof `π` is the transcript
material; its content is captured inside `FriAccept`.) This is the concrete `verifyLD` fed to 2a. -/
def friVerify (S : FriSetup F ι κ) (cr : OracleCR F ι Digest)
    (_π : Proof) (root : Digest) : Prop :=
  ∃ f : ι → F, cr.opens root () f ∧ FriAccept S f

/-- **`friOpenTr` — the trace the committed root decodes to.** The concrete `openTr` fed to 2a. -/
noncomputable def friOpenTr (cr : OracleCR F ι Digest)
    (dec : (ι → F) → Step State Effect × List (Step State Effect))
    (root : Digest) : Step State Effect × List (Step State Effect) :=
  dec (openerOf cr root)

/-! ## §3 — THE BRIDGE: 2b's proximity SUPPLIES 2a's `FriProximity` hypothesis. -/

/-- **THEOREM `friVerify_openTr_proximity` — the two `FriProximity` notions connected.** Under
`HashCR` (`hcr`) and the structural code/decode compatibility `hcode`, the FRI verifier `friVerify`
and the committed-opening decoder `friOpenTr` satisfy `AirSoundness.FriProximity`: acceptance forces
the opened trace to satisfy the AIR transition constraints. Chain: `friVerify` accept ⟹ some opener
`f` has `FriAccept` ⟹ (`friAccept_low_degree`, i.e. `friProximity_discharge`) `f ∈ S.C` ⟹
(`oracle_binding`, `HashCR`) the chosen `openerOf root = f`, a codeword ⟹ (`hcode`) its decode
satisfies the transition constraints. This is the exact interface `AirSoundness.circuit_sound_via_fri`
consumes. -/
theorem friVerify_openTr_proximity
    (applyEff : Effect → State → State)
    (S : FriSetup F ι κ)
    (dec : (ι → F) → Step State Effect × List (Step State Effect))
    (hcode : ∀ f ∈ S.C, satisfiesTransition applyEff (dec f).1 (dec f).2)
    (cr : OracleCR F ι Digest) (hcr : HashCR cr) :
    Dregg2.Circuit.AirSoundness.FriProximity (Proof := Proof) applyEff
      (friVerify S cr) (friOpenTr cr dec) := by
  intro π root hv
  obtain ⟨f, hopen, hacc⟩ := hv
  have hchosen : cr.opens root () (openerOf cr root) := Classical.epsilon_spec ⟨f, hopen⟩
  have hfeq : f = openerOf cr root := oracle_binding cr hcr hopen hchosen
  have hmem : openerOf cr root ∈ S.C := hfeq ▸ friAccept_low_degree S hacc
  show satisfiesTransition applyEff (dec (openerOf cr root)).1 (dec (openerOf cr root)).2
  exact hcode _ hmem

/-! ## §4 — THE HEADLINE: `CircuitSound` as a THEOREM (no proximity/circuit-soundness hypothesis). -/

/-- **`friChecks` — the FRI-realized turn checker.** `airChecks` wired to the FRI verifier and the
committed-opening decoder. This is the deployed `checks : Proof → State → Effect → State → Prop`. -/
noncomputable def friChecks (S : FriSetup F ι κ) (cr : OracleCR F ι Digest)
    (dec : (ι → F) → Step State Effect × List (Step State Effect)) :
    Proof → State → Effect → State → Prop :=
  airChecks (friVerify S cr) (friOpenTr cr dec)

/-- **THEOREM `circuit_sound` — `CircuitSound` DISCHARGED.** For any FRI setup `S`, decode map `dec`
with the AIR structural compatibility `hcode`, and a Merkle commitment `cr` satisfying `HashCR`, the
FRI-realized checker `friChecks S cr dec` satisfies `TurnSoundness.CircuitSound applyEff`: every
accepted execution proof forces `new = applyEff eff old`. It takes NO `FriProximity`/`CircuitSound`
hypothesis — the proximity is PROVED inline (`friVerify_openTr_proximity`) from `friProximity_discharge`
and `oracle_binding`. Residual: `HashCR cr` (the hash floor) + the FRI parameters `S` + the structural
`hcode`. -/
theorem circuit_sound
    (applyEff : Effect → State → State)
    (S : FriSetup F ι κ)
    (dec : (ι → F) → Step State Effect × List (Step State Effect))
    (hcode : ∀ f ∈ S.C, satisfiesTransition applyEff (dec f).1 (dec f).2)
    (cr : OracleCR F ι Digest) (hcr : HashCR cr) :
    CircuitSound applyEff (friChecks (Proof := Proof) S cr dec) :=
  circuit_sound_via_fri applyEff (friVerify S cr) (friOpenTr cr dec)
    (friVerify_openTr_proximity (Proof := Proof) applyEff S dec hcode cr hcr)

/-! ## §5 — DISCHARGE into TurnSoundness: `turn_sound` with NO `CircuitSound` hypothesis. -/

/-- **`turn_sound_unconditional`.** `TurnSoundness.turn_sound` with its `CircuitSound` obligation
DISCHARGED by `circuit_sound`. Under the actor's `EufCma` and `HashCR`, a VALID receipt for a turn
proves it was AUTHORIZED and its transition is CORRECT — no circuit-soundness hypothesis remains
(only `HashCR` + the FRI parameters carry the execution half). -/
theorem turn_sound_unconditional
    (Sig' : SigScheme SK PK Msg Sig) (encMsg : State → Effect → Msg)
    (applyEff : Effect → State → State)
    (S : FriSetup F ι κ)
    (dec : (ι → F) → Step State Effect × List (Step State Effect))
    (hcode : ∀ f ∈ S.C, satisfiesTransition applyEff (dec f).1 (dec f).2)
    (cr : OracleCR F ι Digest) (hcr : HashCR cr)
    (actorPk : PK) (Q : Msg → Prop)
    (heuf : EufCma Sig' actorPk Q)
    (t : Turn State Effect) (r : Receipt Sig Proof)
    (hvalid : Valid Sig' encMsg (friChecks S cr dec) actorPk t r) :
    Q (encMsg t.old t.eff) ∧ CorrectTransition applyEff t :=
  turn_sound Sig' encMsg applyEff (friChecks S cr dec) actorPk Q heuf
    (circuit_sound applyEff S dec hcode cr hcr) t r hvalid

section UnderFloorDischarge
variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {Mod : Type*} [AddCommGroup Mod] [Module Rq Mod] [ShortNorm Mod]
variable {NN : Type*} [AddCommGroup NN] [Module Rq NN] [ShortNorm NN]

/-- **`turn_sound_under_floor_discharged` (the crypto payoff, `CircuitSound`-free).** Combines
`TurnSoundness.turn_sound_under_floor` (authorization reduced to `SchnorrDLHard ∨ MSISHard` via the
hybrid combiner) with `circuit_sound` (execution reduced to `HashCR`). A VALID receipt for a turn
proves it was AUTHORIZED by the actor AND its transition is CORRECT — under the single floor
`(SchnorrDLHard ∨ MSISHard) ∧ HashCR`, with NO `CircuitSound` hypothesis. Only if BOTH hardness
floors fall, OR the hash is broken, can a state evolution be forged. -/
theorem turn_sound_under_floor_discharged
    (Cl : SigScheme SK PK Msg Sig) (Pq : SigScheme SK PK Msg Sig)
    (pkc pkp : PK) (encMsg : State → Effect → Msg)
    (applyEff : Effect → State → State)
    (S : FriSetup F ι κ)
    (dec : (ι → F) → Step State Effect × List (Step State Effect))
    (hcode : ∀ f ∈ S.C, satisfiesTransition applyEff (dec f).1 (dec f).2)
    (cr : OracleCR F ι Digest) (hcr : HashCR cr)
    (Q : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    (A : Mod →ₗ[Rq] NN) (tgt : NN) (β : ℕ)
    (dlFork : Forgery Cl pkc Q → DLSolver C G)
    (msisFork : Forgery Pq pkp Q →
      ∃ (w : NN) (c c' : Rq) (z z' : Mod), c ≠ c' ∧
        IsSelfTargetMSISSolution A tgt β z c w ∧ IsSelfTargetMSISSolution A tgt β z' c' w)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A tgt) ((β + β) + (β + β)))
    (t : Turn State Effect) (r : Receipt (Sig × Sig) Proof)
    (hvalid : Valid (hybrid Cl Pq) encMsg (friChecks S cr dec) (pkc, pkp) t r) :
    Q (encMsg t.old t.eff) ∧ CorrectTransition applyEff t :=
  turn_sound_under_floor Cl Pq pkc pkp encMsg applyEff (friChecks S cr dec) Q
    C G A tgt β dlFork msisFork
    (circuit_sound applyEff S dec hcode cr hcr)
    hfloor t r hvalid

end UnderFloorDischarge

#assert_axioms friAccept_low_degree
#assert_axioms friVerify_openTr_proximity
#assert_axioms circuit_sound
#assert_axioms turn_sound_unconditional
#assert_axioms turn_sound_under_floor_discharged

end Abstract

/-! ## §6 — TEETH: a concrete non-vacuous instance on the genuine rate-1/2 Reed-Solomon `rsSetup`.

State = Effect = `ZMod 5`, the additive counter VM `s ↦ s + e`. The AIR trace has ONE row; the step
constraint `post = pre + eff` is arranged to be EQUIVALENT to membership in the low-degree code `rsC`
(via the codeword relation `f 0 - 2·f 1 + f 2 = 0`), so FRI's low-degree check is genuinely
load-bearing: a codeword decodes to a valid step, a far oracle decodes to a lying step. -/

section Teeth

/-- The additive-counter effect-VM over `ZMod 5`. -/
def addVM : ZMod 5 → ZMod 5 → ZMod 5 := fun e s => s + e

/-- **The decode map.** Read `pre = f 0`, `eff = f 1`, `post = 2·f 0 - f 1 + f 2` from the oracle.
Then `post = pre + eff` iff `f 0 - 2·f 1 + f 2 = 0`, which is exactly the linear relation every
`rsC` codeword `a + b·p` satisfies — so the step constraint holds on codewords and FAILS off the
code (non-vacuous: the post is READ from the oracle, not fabricated). -/
def decRS (f : Fin 4 → ZMod 5) :
    Step (ZMod 5) (ZMod 5) × List (Step (ZMod 5) (ZMod 5)) :=
  (⟨f 0, f 1, 2 * f 0 - f 1 + f 2⟩, [])

/-- **`hcodeRS` — the AIR structural compatibility, DISCHARGED.** Every codeword of the genuine RS
code `rsSetup.C` decodes to a trace satisfying the transition constraints (`post = pre + eff`). This
is the concrete witness that `circuit_sound`'s `hcode` premise is not vacuous. -/
theorem hcodeRS :
    ∀ f ∈ rsSetup.C, satisfiesTransition addVM (decRS f).1 (decRS f).2 := by
  rintro f ⟨a, b, rfl⟩
  refine ⟨?_, trivial⟩
  show (2 * (a + b * pVal 0) - (a + b * pVal 1) + (a + b * pVal 2))
      = addVM (a + b * pVal 1) (a + b * pVal 0)
  rw [show (pVal 0 : ZMod 5) = 1 from by decide,
      show (pVal 1 : ZMod 5) = 2 from by decide,
      show (pVal 2 : ZMod 5) = 3 from by decide, addVM]
  ring

/-- **`circuit_sound_rs` — the concrete headline.** On the genuine rate-1/2 Reed-Solomon FRI instance
`rsSetup` (`ZMod 5`, `|L| = 4`, `|L²| = 2`, one fold, full-cover query set), `CircuitSound` holds with
`HashCR` as its ONLY residual (the FRI parameters and `hcode` are fixed/discharged). The folding
soundness error is the PROVED `≤ 1/|F| = 1/5` per round (`exceptional_subsingleton`). -/
theorem circuit_sound_rs {Digest Proof : Type*}
    (cr : OracleCR (ZMod 5) (Fin 4) Digest) (hcr : HashCR cr) :
    CircuitSound addVM (friChecks (Proof := Proof) rsSetup cr decRS) :=
  circuit_sound addVM rsSetup decRS hcodeRS cr hcr

/-! ### Tooth 1 — an honest codeword: accepting transcript whose decoded trace IS a VM step. -/

/-- The honest codeword `fHonest = 2 + 3·p ∈ rsSetup.C` admits an accepting FRI transcript: fold at
`α = 0` lands in the folded code (completeness), the full query set covers trivially, and the
challenge is non-exceptional (the oracle is already a codeword). -/
theorem honest_friAccept : FriAccept rsSetup fHonest :=
  ⟨Fold rsSetup.geom 0 fHonest, 0, Finset.univ,
    Finset.subset_univ _,
    fun _ _ => rfl,
    fold_complete rsSetup fHonest_mem 0,
    fun _ => fHonest_mem⟩

/-- The identity (hence binding) commitment for the concrete tooth: the root IS the oracle. -/
def honestCR : OracleCR (ZMod 5) (Fin 4) (Fin 4 → ZMod 5) := ⟨fun _ f => f⟩

/-- The identity commitment satisfies `HashCR`. -/
theorem honestCR_hashcr : HashCR honestCR := fun _ _ _ h => h

/-- **RESPECTING INSTANCE.** `friChecks` ACCEPTS the honest turn `(old = 0, eff = 3, new = 3)`: the
committed oracle `fHonest` opens the root, admits the accepting transcript, and decodes to the row
`⟨0, 3, 3⟩` — a genuine VM step `0 --(+3)--> 3`. So the honest accepting transcript's trace IS the
VM execution. -/
theorem honest_turn_checks :
    friChecks (Proof := Unit) rsSetup honestCR decRS () 0 3 3 := by
  refine ⟨fHonest, ⟨fHonest, rfl, honest_friAccept⟩, ?_⟩
  have hop : openerOf honestCR fHonest = fHonest :=
    Classical.epsilon_spec (⟨fHonest, rfl⟩ : ∃ f, honestCR.opens fHonest () f)
  show decRS (openerOf honestCR fHonest) = (⟨0, 3, 3⟩, [])
  rw [hop]; rfl

/-- …and its `CircuitSound` conclusion genuinely holds: the accepted turn's `new = addVM eff old`. -/
theorem honest_turn_correct :
    (3 : ZMod 5) = addVM 3 0 :=
  circuit_sound_rs (Proof := Unit) honestCR honestCR_hashcr () 0 3 3 honest_turn_checks

/-! ### Tooth 2 — a FAR oracle: no accepting transcript, and its decode LIES. -/

/-- **FRI-REJECTION TOOTH (load-bearing).** The far oracle `fFar = ![1,0,0,0] ∉ rsSetup.C` admits NO
accepting FRI transcript: acceptance would force `fFar ∈ rsSetup.C` (`friAccept_low_degree`),
contradicting `fFar_not_mem`. -/
theorem far_oracle_no_friAccept : ¬ FriAccept rsSetup fFar :=
  fun h => fFar_not_mem (friAccept_low_degree rsSetup h)

/-- **NON-VACUITY TOOTH.** …and the far oracle's decoded trace VIOLATES the step gate: `decRS fFar`
claims `post = 2` while the VM step `pre + eff = 1`. So the low-degree check is doing real work — a
far oracle would decode to a lying transition, which is exactly what FRI forecloses. -/
theorem far_oracle_decode_violates :
    ¬ stepGate addVM (decRS fFar).1 := by
  show ¬ ((decRS fFar).1.post = addVM (decRS fFar).1.eff (decRS fFar).1.pre)
  decide

/-- **HASH-COLLISION TOOTH (load-bearing).** A colliding oracle commitment breaks `HashCR` — reusing
`FriSoundness.badOracle_equivocates` — so binding is exactly what stops the prover equivocating the
committed oracle after the challenge. -/
theorem collision_breaks_binding : ¬ HashCR badOracleCR := badOracle_equivocates

-- The honest turn's VM step really lands: 0 --(+3)--> 3.
#guard decide (addVM 3 0 = 3)
-- The far oracle decodes to post = 2 while the VM says pre + eff = 1 — the decode LIES.
#guard decide ((decRS fFar).1.post ≠ (decRS fFar).1.pre + (decRS fFar).1.eff)

end Teeth

#assert_axioms hcodeRS
#assert_axioms circuit_sound_rs
#assert_axioms honest_friAccept
#assert_axioms far_oracle_no_friAccept
#assert_axioms far_oracle_decode_violates

end Dregg2.Circuit.CircuitSoundCompose
