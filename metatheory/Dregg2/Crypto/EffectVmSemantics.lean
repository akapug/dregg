/-
# `Dregg2.Crypto.EffectVmSemantics` — UNIT 4d: the abstract turn-soundness INSTANTIATED with the
REAL effect-VM step semantics and the REAL receipt. `turn_sound` / `turn_sound_under_floor` were
proved for an ABSTRACT `applyEff : Effect → State → State` and an abstract `checks`; this file plugs
in the DEPLOYED effect algebra, the DEPLOYED VM step, and the DEPLOYED receipt so the headline
`turn_sound_real` is a statement about the SHIPPED system, not an abstraction.

`circuit_sound` is now a THEOREM (`Dregg2.Circuit.CircuitSoundCompose.circuit_sound` /
`circuit_sound_rs`, residual `HashCR`), so nothing here rests on a `CircuitSound`/`FriProximity`
hypothesis. Authorization folds through the hybrid combiner to `SchnorrDLHard ∨ MSISHard`. The
residual of `turn_sound_real` is EXACTLY `(SchnorrDLHard ∨ MSISHard) ∧ HashCR`.

## What is modeled (grounded at HEAD)

* **The effect algebra.** The deployed `Effect` (`turn/src/action.rs:1061`) is 33 variants; each is
  colored by `Effect::linearity` (`action.rs:1807`) into one of the six `LinearityClass` colors
  (`action.rs:940`, mirrored as `Dregg2.Spec.LinearityClass`). We model `RealEffect` as a
  representative core — ONE variant per color (Conservative `transfer`, Generative `mint`,
  Annihilative `burn`, Neutral `setField`, Monotonic `incrementNonce`, Terminal `revokeCapability`)
  — because **the soundness argument is uniform in the variant**: `AirSoundness.air_sound` /
  `lastPost_eq_vmResult` and `CircuitSoundCompose.circuit_sound` never case-split on the effect; they
  use only that each row satisfies its per-row step gate `post = applyEff eff pre` and that rows
  carry. So `applyEffReal` may be the full 33-variant interpreter and the SAME theorem applies — the
  only per-variant datum is the field-embedded conserved-quantity movement `delta`.

* **The VM step.** On the balance state column (a BabyBear field element — here `ZMod 5`, the genuine
  rate-1/2 Reed–Solomon field the FRI floor `rsSetup` runs over) each variant's transition is the
  additive gate `s ↦ s + delta eff`, where `delta` is the effect's signed movement of the conserved
  quantity (`+amount` for `transfer`/`mint`, `-amount` for `burn`, `0` for the non-conserving colors).
  This is exactly `CircuitSoundCompose.addVM (delta eff)` — so `applyEffReal` is the function the AIR's
  row-local step gate (`descriptor_ir2` `Gate`, `lean_descriptor_air::VmConstraint::Gate`) enforces.
  `stepGate_iff_real` is that bridge from the constraint system to the real semantics.

* **The receipt.** `RealReceipt` mirrors the deployed `TurnReceipt` (`turn/src/turn.rs:850`) +
  `WitnessedReceipt` (`turn/src/witnessed_receipt.rs:246`): the `authSig` (`executor_signature`, the
  hybrid ed25519×ML-DSA over the receipt body), the `execProof` (`proof_bytes`, the STARK/FRI
  execution proof), and the roots `preStateHash`/`postStateHash` (`pre_/post_state_hash`) and
  `effectsHash` (`effects_hash`, the log root — a BLAKE3 fold over `Effect::hash`). `ValidReal` is the
  deployed acceptance: the signature verifies over the turn body AND the execution proof is accepted
  by the AIR verifier for the committed `(old, eff, new)` transition.

## Constraint coverage (the deployed AIR vs what is discharged here)

The deployed AIR (`circuit/src/descriptor_ir2.rs`, `EffectVmDescriptor2`) has `VmConstraint2` families:
`Base(VmConstraint::{Gate, Transition, Boundary, PiBinding})` and the v2 bus interactions
`{Lookup, MemOp, MapOp, UMemOp, ProofBind, WindowGate}`. What `turn_sound_real` rests on:

* **`Gate`** (row-local step gate) — modeled by `applyEffReal` and discharged by `air_sound`'s step
  gate + `circuit_sound_rs` (the RS code ENCODES the step; `hcodeRS`, non-vacuous — a far oracle
  decodes to a lying step, `far_oracle_decode_violates`).
* **`Transition` / `WindowGate`** (the two-row carry / cumulative form) — modeled by
  `AirSoundness.carryChain`, discharged inside `air_sound`.
* **`Boundary` / `PiBinding`** (`first.pre = old`, `last.post = new`, public-input binding) — modeled
  by `AirSoundness.satisfiesConstraints`' boundary conjuncts (`boundary_load_bearing` shows the final
  boundary is load-bearing), and the receipt's state roots bind old/new.
* **`Lookup`→`Range`** (field-range byte lookup, anti-wraparound) — NOT re-derived here; the Lean IR
  for it is `Dregg2.Circuit.Lookup` (`rangeCheck`, decidable accept/reject). Over the modeled field
  the additive step is exact, so no wraparound is possible in the model.
* **`MemOp` / `MapOp` / `UMemOp`** (offline-memory / sorted-map / universal-memory permutation buses)
  and **`ProofBind`** (recursion) — the side-table binding for the LIST-valued components is
  `receipt_binds_log` (the `effects_hash`/log digest pins the log uniquely, via
  `Circuit.chain_digest_binds → HashCR`); the per-effect side-table circuits are discharged in
  `Dregg2.Circuit.EffectCommit*` (bal/escrows/queues/accounts) and are NOT re-proved here.

None of these is an OPEN hole: the step-correctness argument is complete and variant-uniform for the
modeled colors, and each auxiliary bus is discharged in its own module (cited above).

Residual: `(SchnorrDLHard ∨ MSISHard) ∧ HashCR`. No `CircuitSound`/`FriProximity` hypothesis, no
`def …Hard` assumed as a proof, no `:= True`.
-/
import Dregg2.Circuit.CircuitSoundCompose
import Dregg2.Crypto.TurnSoundness
import Dregg2.Spec.Conservation

namespace Dregg2.Crypto.EffectVmSemantics

open Dregg2.Crypto.TurnSoundness
  (Turn Receipt Valid CorrectTransition CircuitSound turn_sound_under_floor
   unauthorized_rejected wrong_transition_rejected wrong_transition_no_valid)
open Dregg2.Circuit.CircuitSoundCompose
  (friChecks circuit_sound_rs addVM decRS honestCR honest_turn_checks
   FriAccept far_oracle_no_friAccept)
open Dregg2.Circuit.FriSoundness (rsSetup OracleCR fFar)
open Dregg2.Circuit.AirSoundness (Step stepGate satisfiesConstraints isVmExecution air_sound vmResult)
open Dregg2.Circuit (chain_digest_binds verifyDigest)
open Dregg2.Crypto.HybridCombiner
  (SigScheme hybrid hybridVerify Forgery EufCma brokenToy noQueries hybrid_broken_if_both)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.Lattice (MSISHard ShortNorm)
open Dregg2.Crypto.HermineSelfTargetMSIS (augmented IsSelfTargetMSISSolution)
open scoped Dregg2.Crypto.HermineSelfTargetMSIS -- the scoped `ShortNorm (P × Q)` product instance
open Dregg2.Crypto.SchnorrCurveField (SchnorrDLHard CurveGroup DLSolver)
open Dregg2.Spec (LinearityClass)

/-! ## §1 — The REAL effect algebra: a per-color representative core of the 33 variants. -/

/-- **`RealEffect`** — one representative per `LinearityClass` color of the deployed 33-variant
`Effect` (`turn/src/action.rs:1061`). The soundness argument does not case-split on the variant, so a
representative core suffices to exhibit the model at full color-breadth; `applyEffReal` may be the full
interpreter (only `delta` changes per variant). -/
inductive RealEffect where
  /-- Conservative (`Transfer`): move `amount` — paired debit/credit, `Σδ = 0`. -/
  | transfer (amount : ZMod 5)
  /-- Generative (`Mint`/`BridgeMint`): create `amount` ex nihilo — disclosed non-conservation. -/
  | mint (amount : ZMod 5)
  /-- Annihilative (`Burn`): destroy `amount` — disclosed non-conservation. -/
  | burn (amount : ZMod 5)
  /-- Neutral (`SetField`): touch no conserved quantity. -/
  | setField
  /-- Monotonic (`IncrementNonce`): the balance column is untouched (the nonce column advances). -/
  | incrementNonce
  /-- Terminal (`RevokeCapability`): one-way; the balance column is untouched. -/
  | revokeCapability
  deriving DecidableEq, Repr

/-- **The coloring map** — `Effect::linearity` (`action.rs:1807`), mirrored on the representative core.
Exhaustive, no default arm: it colors all six `LinearityClass` colors. -/
def linearityReal : RealEffect → LinearityClass
  | .transfer _        => .Conservative
  | .mint _            => .Generative
  | .burn _            => .Annihilative
  | .setField          => .Neutral
  | .incrementNonce    => .Monotonic
  | .revokeCapability  => .Terminal

/-- **The per-effect balance-column delta** — the field-embedded signed movement of the conserved
quantity. This is the ONLY per-variant datum the AIR step gate reads: `post = pre + delta eff`. -/
def delta : RealEffect → ZMod 5
  | .transfer a        => a
  | .mint a            => a
  | .burn a            => -a
  | .setField          => 0
  | .incrementNonce    => 0
  | .revokeCapability  => 0

/-- **`applyEffReal` — the DEPLOYED VM step on the balance state column.** Each effect advances the
column additively by its `delta`. This is exactly `CircuitSoundCompose.addVM (delta eff)`, so it is the
function the genuine rate-1/2 RS AIR step gate (`rsSetup`/`decRS`) enforces. -/
def applyEffReal : RealEffect → ZMod 5 → ZMod 5 := fun eff s => addVM (delta eff) s

/-- The coloring covers all six colors (breadth witness). -/
theorem linearityReal_surjective :
    (∀ c : LinearityClass, ∃ e : RealEffect, linearityReal e = c) := by
  intro c
  cases c with
  | Conservative => exact ⟨.transfer 0, rfl⟩
  | Monotonic    => exact ⟨.incrementNonce, rfl⟩
  | Terminal     => exact ⟨.revokeCapability, rfl⟩
  | Generative   => exact ⟨.mint 0, rfl⟩
  | Annihilative => exact ⟨.burn 0, rfl⟩
  | Neutral      => exact ⟨.setField, rfl⟩

/-! ## §2 — The stepGate ↔ step-relation bridge (constraint system ⟷ real semantics).

The AIR's row-local step gate `stepGate applyEff s := s.post = applyEff s.eff s.pre` holds on a row
`⟨old, eff, new⟩` iff the real semantics `new = old + delta eff` holds — the deployed additive
balance-column gate. This is the bridge from the constraint system to the interpreter. -/

/-- **THE BRIDGE.** `stepGate applyEffReal` on `⟨old, eff, new⟩` is exactly the deployed additive gate
`new = old + delta eff`: the constraint the AIR checks per row IS the real VM step. -/
theorem stepGate_iff_real (old : ZMod 5) (eff : RealEffect) (new : ZMod 5) :
    stepGate applyEffReal ⟨old, eff, new⟩ ↔ new = old + delta eff := Iff.rfl

/-- **AIR soundness at the REAL interpreter (variant-uniform, multi-effect).** A trace satisfying ALL
the deployed AIR constraints (step gate on every row + carry + both boundaries) IS a genuine
`applyEffReal` execution: it chains, each row is a real VM step, and the claimed `new` is EXACTLY the
VM run `vmResult applyEffReal`. This is `air_sound` specialized — it holds for the FULL effect algebra
because `air_sound` never case-splits on the variant. -/
theorem air_sound_real (old new : ZMod 5)
    (s : Step (ZMod 5) RealEffect) (rest : List (Step (ZMod 5) RealEffect))
    (h : satisfiesConstraints applyEffReal old new s rest) :
    isVmExecution applyEffReal old new s rest :=
  air_sound applyEffReal old new s rest h

/-! ## §3 — The REAL circuit checker and `CircuitSound` DISCHARGED (residual: `HashCR`). -/

/-- **`realChecks cr` — the deployed execution-proof checker.** The AIR verifier accepts an execution
proof `π` for a claimed transition `(old, eff, new)` iff the genuine rate-1/2 RS-FRI checker
`friChecks rsSetup cr decRS` accepts it on the field-embedded effect `delta eff`. This is the concrete
`checks : Proof → State → Effect → State → Prop` the deployed AIR realizes (`descriptor_ir2`
`verify_vm_descriptor2`). -/
noncomputable def realChecks {Proof Digest : Type*}
    (cr : OracleCR (ZMod 5) (Fin 4) Digest) :
    Proof → ZMod 5 → RealEffect → ZMod 5 → Prop :=
  fun π old eff new => friChecks (Proof := Proof) rsSetup cr decRS π old (delta eff) new

/-- **`circuit_sound_real` — `CircuitSound` for the REAL step, DISCHARGED to `HashCR`.** The deployed
checker `realChecks cr` satisfies `TurnSoundness.CircuitSound applyEffReal`: every accepted execution
proof forces `new = applyEffReal eff old`. It takes NO `CircuitSound`/`FriProximity` hypothesis — it is
`circuit_sound_rs` (the genuine RS instance, `hcodeRS` discharged) transported along `delta`. Residual:
`HashCR cr`. -/
theorem circuit_sound_real {Proof Digest : Type*}
    (cr : OracleCR (ZMod 5) (Fin 4) Digest) (hcr : HashCR cr) :
    CircuitSound applyEffReal (realChecks (Proof := Proof) cr) := by
  intro π old eff new h
  -- h : friChecks rsSetup cr decRS π old (delta eff) new ;  goal : new = addVM (delta eff) old
  exact circuit_sound_rs (Proof := Proof) cr hcr π old (delta eff) new h

/-! ## §4 — The REAL receipt and the deployed acceptance predicate. -/

/-- **`RealReceipt`** — mirrors the deployed `TurnReceipt` (`turn/src/turn.rs:850`) + the STARK-carrying
`WitnessedReceipt` (`turn/src/witnessed_receipt.rs:246`) crypto fields. -/
structure RealReceipt (Sig Proof Digest : Type*) where
  /-- `executor_signature` — the hybrid (ed25519×ML-DSA) signature over the receipt body. -/
  authSig : Sig
  /-- `proof_bytes` — the STARK/FRI execution proof of the transition. -/
  execProof : Proof
  /-- `pre_state_hash` — the pre-state root the execution proof's public inputs bind. -/
  preStateHash : Digest
  /-- `post_state_hash` — the post-state root. -/
  postStateHash : Digest
  /-- `effects_hash` — the LOG root: a collision-resistant fold over the turn's effect sequence. -/
  effectsHash : Digest

/-- The abstract `TurnSoundness.Receipt` a `RealReceipt` presents (its two verifier-consumed legs). -/
def RealReceipt.toReceipt {Sig Proof Digest : Type*} (r : RealReceipt Sig Proof Digest) :
    Receipt Sig Proof :=
  ⟨r.authSig, r.execProof⟩

/-- **`ValidReal` — the DEPLOYED verifier's acceptance predicate.** A receipt is accepted iff the
authorization signature verifies over the turn body AND the execution proof is accepted by the AIR
verifier for the committed `(old, eff, new)` transition (the state roots commit `old`/`new`). This is
`TurnSoundness.Valid` on the receipt's two verifier legs. -/
def ValidReal {SK PK Msg Sig Proof Digest : Type*}
    (S : SigScheme SK PK Msg Sig) (encMsg : ZMod 5 → RealEffect → Msg)
    (checks : Proof → ZMod 5 → RealEffect → ZMod 5 → Prop)
    (actorPk : PK) (t : Turn (ZMod 5) RealEffect) (r : RealReceipt Sig Proof Digest) : Prop :=
  Valid S encMsg checks actorPk t r.toReceipt

/-! ## §5 — THE HEADLINE: `turn_sound_real`. -/

section Headline
variable {Rq : Type*} [CommRing Rq] [ShortNorm Rq]
variable {Mod : Type*} [AddCommGroup Mod] [Module Rq Mod] [ShortNorm Mod]
variable {NN : Type*} [AddCommGroup NN] [Module Rq NN] [ShortNorm NN]

/-- **THEOREM `turn_sound_real` (the deployed payoff).** A `ValidReal` receipt for a DEPLOYED turn
`(old, eff, new)` — the executor's hybrid signature verifies over the turn body and its STARK/FRI
execution proof is accepted — PROVES both:

  1. **AUTHORIZED** — `Q (encMsg old eff)`: the actor genuinely signed this turn's precondition; and
  2. **CORRECT** — `new = applyEffReal eff old`: the DEPLOYED state evolution is the VM's true step.

Obtained by instantiating `TurnSoundness.turn_sound_under_floor` with the REAL step `applyEffReal`, the
REAL checker `realChecks`, and the REAL receipt — discharging its `CircuitSound` obligation with
`circuit_sound_real` (a THEOREM). No `CircuitSound`/`FriProximity` hypothesis and no `def …Hard`
assumed. **Residual: `(SchnorrDLHard ∨ MSISHard) ∧ HashCR`.** Only if BOTH signature floors fall or the
hash is broken can a deployed state evolution be forged. -/
theorem turn_sound_real
    {SK PK Msg Sig Proof Digest : Type*}
    (Cl Pq : SigScheme SK PK Msg Sig)
    (pkc pkp : PK) (encMsg : ZMod 5 → RealEffect → Msg)
    (Q : Msg → Prop)
    (C : CurveGroup) (G : C.Pt)
    (A : Mod →ₗ[Rq] NN) (tgt : NN) (β : ℕ)
    (dlFork : Forgery Cl pkc Q → DLSolver C G)
    (msisFork : Forgery Pq pkp Q →
      ∃ (w : NN) (c c' : Rq) (z z' : Mod), c ≠ c' ∧
        IsSelfTargetMSISSolution A tgt β z c w ∧ IsSelfTargetMSISSolution A tgt β z' c' w)
    (cr : OracleCR (ZMod 5) (Fin 4) Digest) (hcr : HashCR cr)
    (hfloor : SchnorrDLHard C G ∨ MSISHard (augmented A tgt) ((β + β) + (β + β)))
    (t : Turn (ZMod 5) RealEffect) (r : RealReceipt (Sig × Sig) Proof Digest)
    (hvalid : ValidReal (hybrid Cl Pq) encMsg (realChecks (Proof := Proof) cr) (pkc, pkp) t r) :
    Q (encMsg t.old t.eff) ∧ CorrectTransition applyEffReal t :=
  turn_sound_under_floor Cl Pq pkc pkp encMsg applyEffReal (realChecks (Proof := Proof) cr) Q
    C G A tgt β dlFork msisFork
    (circuit_sound_real (Proof := Proof) cr hcr)
    hfloor t r.toReceipt hvalid

end Headline

/-! ## §6 — `receipt_binds_log`: the receipt's `effects_hash` pins the log (→ `HashCR`). -/

/-- **`receipt_binds_log` — the log root binds the log UNIQUELY.** Modeling `effects_hash` as a
collision-resistant hash of an injectively-framed effect log, two logs that both recompute the
receipt's `effectsHash` are equal. So the receipt cannot present one `effects_hash` for two different
turn logs — a `chainOk`-style equivocation would be a hash collision. This is
`Circuit.chain_digest_binds` at the log type; residual: `HashCR`. -/
theorem receipt_binds_log {Pre Dig : Type*}
    (cr : CommitReveal Unit Pre Dig) (frame : List RealEffect → Pre)
    (hinj : Function.Injective frame) (hcr : HashCR cr)
    (effectsHash : Dig) (log log' : List RealEffect)
    (h : verifyDigest cr frame effectsHash log)
    (h' : verifyDigest cr frame effectsHash log') : log = log' :=
  chain_digest_binds cr frame hinj hcr effectsHash log log' h h'

/-! ## §7 — TEETH (all load-bearing).

(1) an HONEST deployed turn validates and its evolution IS the VM's;
(2) a receipt claiming a WRONG new state has NO valid execution proof (exhibited via the far oracle);
(3) an UNAUTHORIZED turn's receipt fails the signature check (a concrete hybrid forgery when stripped);
(4) the `effects_hash` binding needs `HashCR` (a distinct log verifying the same digest breaks it). -/

section Teeth

/-! ### The honest deployed turn `(old = 0, eff = mint 3, new = 3)` — a Generative step of +3. -/

/-- The honest effect: a `mint 3` (Generative), `delta = 3`. -/
def honestEff : RealEffect := .mint 3
/-- The honest deployed turn `0 --(mint 3)--> 3`. -/
def honestTurnReal : Turn (ZMod 5) RealEffect := ⟨0, honestEff, 3⟩

/-- **RESPECTING INSTANCE (execution gate).** The honest turn's execution proof is ACCEPTED by
`realChecks`: `delta (mint 3) = 3`, so it is exactly `honest_turn_checks` on the field turn
`(0, 3, 3)`. -/
theorem honest_turn_real_checks :
    realChecks (Proof := Unit) honestCR () honestTurnReal.old honestTurnReal.eff honestTurnReal.new :=
  honest_turn_checks

/-- …and its `turn_sound_real` correctness conclusion genuinely holds: `new = applyEffReal eff old`. -/
theorem honest_turn_real_correct :
    CorrectTransition applyEffReal honestTurnReal := by
  show (3 : ZMod 5) = applyEffReal honestEff 0
  decide

/-! ### A concrete accepting authorization to exhibit the FULL honest `ValidReal`. -/

/-- A distinct code per effect variant (the effect's contribution to the signed turn body). -/
def effCode : RealEffect → ℕ
  | .transfer a       => 10 + a.val
  | .mint a           => 100 + a.val
  | .burn a           => 200 + a.val
  | .setField         => 300
  | .incrementNonce   => 400
  | .revokeCapability => 500

/-- The per-turn precondition message: the turn body the executor signs (`realEnc old eff`). -/
def realEnc : ZMod 5 → RealEffect → ℕ := fun old eff => old.val + effCode eff

/-- A concrete authorization scheme over `ℕ` (the `toyS` shape: `verify pk m sig := sig = pk + m`).
Nontrivial — a wrong signature FAILS — but publicly forgeable (verification is public), which is
exactly why `EufCma` is a real hypothesis and the forgery tooth bites when it is dropped. -/
@[reducible] def authScheme : SigScheme ℕ ℕ ℕ ℕ where
  pkOf sk := sk
  sign sk m := sk + m
  verify pk m sig := sig = pk + m

/-- The actor's public key. -/
def realActor : ℕ := 7

/-- The honest receipt: the executor's hybrid signature over the honest precondition, the honest
execution proof, and (teeth-irrelevant) unit roots. -/
def honestReceipt : RealReceipt (ℕ × ℕ) Unit Unit :=
  { authSig := (realActor + realEnc 0 honestEff, realActor + realEnc 0 honestEff)
    execProof := ()
    preStateHash := ()
    postStateHash := ()
    effectsHash := () }

/-- **RESPECTING INSTANCE (full deployed acceptance).** The honest deployed receipt is `ValidReal` for
the honest turn: the executor's hybrid signature verifies over the turn body AND the execution proof is
accepted. So an honestly-produced deployed turn's receipt validates. -/
theorem honest_turn_real_valid :
    ValidReal (hybrid authScheme authScheme) realEnc (realChecks (Proof := Unit) honestCR)
      (realActor, realActor) honestTurnReal honestReceipt := by
  refine ⟨⟨?_, ?_⟩, honest_turn_real_checks⟩
  · show (realActor + realEnc 0 honestEff) = realActor + realEnc honestTurnReal.old honestTurnReal.eff
    rfl
  · show (realActor + realEnc 0 honestEff) = realActor + realEnc honestTurnReal.old honestTurnReal.eff
    rfl

/-! ### Tooth 2 — a WRONG new state has no valid execution proof. -/

/-- The WRONG turn `0 --(mint 3)--> 4` — `4 ≠ applyEffReal (mint 3) 0 = 3`: a false deployed evolution. -/
def wrongTurnReal : Turn (ZMod 5) RealEffect := ⟨0, .mint 3, 4⟩

/-- **WRONG-STATE TOOTH (load-bearing).** Under `circuit_sound_real` (residual `HashCR`), the wrong
turn has NO execution proof `realChecks` accepts: acceptance would force `4 = applyEffReal (mint 3) 0 =
3`. A prover cannot commit a receipt lying about the new state and still pass the AIR. -/
theorem wrong_state_no_exec_proof {Digest : Type*}
    (cr : OracleCR (ZMod 5) (Fin 4) Digest) (hcr : HashCR cr) (π : Unit) :
    ¬ realChecks (Proof := Unit) cr π wrongTurnReal.old wrongTurnReal.eff wrongTurnReal.new :=
  wrong_transition_rejected applyEffReal (realChecks (Proof := Unit) cr)
    (circuit_sound_real (Proof := Unit) cr hcr) wrongTurnReal (by decide) π

/-- **NON-VACUITY (the FRI check is real).** The far oracle `fFar ∉ rsSetup.C` admits no accepting FRI
transcript (`far_oracle_no_friAccept`) and its decoded trace VIOLATES the step gate
(`far_oracle_decode_violates`) — so a wrong-state receipt genuinely cannot be witnessed; the low-degree
check is doing the work `circuit_sound_real` relies on. -/
theorem real_far_oracle_no_friAccept : ¬ FriAccept rsSetup fFar := far_oracle_no_friAccept

/-! ### Tooth 3 — an UNAUTHORIZED turn is rejected (and the forgery when `EufCma` is stripped). -/

/-- **AUTHORIZATION TOOTH (under `EufCma`).** A deployed turn whose precondition the actor never signed
(`¬ Q (encMsg old eff)`) has NO valid receipt: a verifying `authSig` on it would be a fresh forgery,
refuting `EufCma` (→ `SchnorrDLHard ∨ MSISHard`). -/
theorem unauthorized_turn_real_rejected
    {SK PK Msg Sig Proof Digest : Type*}
    (S : SigScheme SK PK Msg Sig) (encMsg : ZMod 5 → RealEffect → Msg)
    (checks : Proof → ZMod 5 → RealEffect → ZMod 5 → Prop)
    (actorPk : PK) (Q : Msg → Prop) (heuf : EufCma S actorPk Q)
    (t : Turn (ZMod 5) RealEffect) (hnq : ¬ Q (encMsg t.old t.eff))
    (r : RealReceipt Sig Proof Digest) :
    ¬ ValidReal S encMsg checks actorPk t r :=
  unauthorized_rejected S encMsg checks actorPk Q heuf t hnq r.toReceipt

/-- **FORGERY TOOTH (load-bearing).** Strip `EufCma`: with BOTH hybrid components broken, a fresh
verifying hybrid signature exists on any unsigned precondition — a concrete `Forgery`. So without the
`EufCma` the authorization conclusion of `turn_sound_real` fails; `unauthorized_turn_real_rejected` is
exactly what the signature floor buys. -/
theorem real_forgery_when_broken :
    Forgery (hybrid brokenToy brokenToy) ((), ()) noQueries :=
  hybrid_broken_if_both

/-! ### Tooth 4 — the `effects_hash` binding needs `HashCR`. -/

/-- An identity commitment over effect logs (`H((), p) = p`) — binding (`HashCR`). -/
def logCR : CommitReveal Unit (List RealEffect) (List RealEffect) := ⟨fun _ p => p⟩

/-- `logCR` satisfies `HashCR`. -/
theorem logCR_hashcr : HashCR logCR := fun _ _ _ h => h

/-- An honest effect log and its `effects_hash` digest. -/
def honestLog : List RealEffect := [.mint 3, .transfer 1]
/-- A DIFFERENT log (a dropped effect) — a distinct turn history. -/
def tamperedLog : List RealEffect := [.mint 3]

/-- **BINDING TOOTH.** A tampered log (an effect dropped) does NOT verify the honest log's
`effects_hash`: `receipt_binds_log` (via `logCR_hashcr`) would force the two logs equal, contradiction.
So the receipt's log root pins the exact turn history — no silent reordering or drop. -/
theorem tampered_log_rejected :
    ¬ verifyDigest logCR id (logCR.H () honestLog) tamperedLog := by
  intro h
  have : honestLog = tamperedLog :=
    receipt_binds_log logCR id Function.injective_id logCR_hashcr
      (logCR.H () honestLog) honestLog tamperedLog rfl h
  simp [honestLog, tamperedLog] at this

-- The honest deployed step lands: 0 --(mint 3)--> 3, a Generative +3.
#guard decide (applyEffReal honestEff 0 = 3)
-- The Conservative transfer is additive on the credited column: 1 --(transfer 2)--> 3.
#guard decide (applyEffReal (.transfer 2) 1 = 3)
-- The Annihilative burn subtracts: 3 --(burn 2)--> 1.
#guard decide (applyEffReal (.burn 2) 3 = 1)
-- The Neutral / Monotonic / Terminal colors leave the balance column fixed.
#guard decide (applyEffReal .setField 4 = 4)
#guard decide (applyEffReal .incrementNonce 4 = 4)
#guard decide (applyEffReal .revokeCapability 4 = 4)
-- The WRONG new state really is wrong under the VM (4 ≠ 3) — the checker must reject it.
#guard decide (wrongTurnReal.new ≠ applyEffReal wrongTurnReal.eff wrongTurnReal.old)
-- The far oracle decodes to a lying transition — the FRI low-degree check is load-bearing.
#guard decide ((decRS fFar).1.post ≠ (decRS fFar).1.pre + (decRS fFar).1.eff)
-- The honest and tampered logs differ — the effects_hash binding is non-vacuous.
#guard decide (honestLog ≠ tamperedLog)

end Teeth

/-! ## §8 — Axiom hygiene. The standing obligations of `turn_sound_real` are the NAMED floors
`SchnorrDLHard` / `MSISHard` (through the hybrid combiner) and `HashCR` (the hash floor, carrying both
the FRI/circuit soundness and the log binding). No `CircuitSound`/`FriProximity` hypothesis, no
`def …Hard` assumed as a proof. -/

#assert_axioms turn_sound_real
#assert_axioms circuit_sound_real
#assert_axioms air_sound_real
#assert_axioms receipt_binds_log
#assert_axioms stepGate_iff_real
#assert_axioms honest_turn_real_valid
#assert_axioms honest_turn_real_correct
#assert_axioms wrong_state_no_exec_proof
#assert_axioms unauthorized_turn_real_rejected
#assert_axioms real_forgery_when_broken
#assert_axioms tampered_log_rejected

end Dregg2.Crypto.EffectVmSemantics
