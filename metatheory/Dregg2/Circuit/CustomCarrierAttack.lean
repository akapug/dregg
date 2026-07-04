/-
# Dregg2.Circuit.CustomCarrierAttack — ADVERSARIAL soundness audit of the two custom-effect carriers.

This module attacks `CustomApex`'s two named carriers (`StarkSoundCustom`, `EngineBinding`) head-on,
IN LEAN, importing everything read-only. It is a refutation file: the load-bearing arms are proved
WITHOUT `sorry`, and the conclusions are stated precisely (an honest "doesn't fully close because X"
is recorded where the opaque-verifier surface blocks a stronger claim).

## The target

`CustomApex.StarkSoundCustom hash E R` asserts a STAGED-AIR extraction:

    verifyBatch (vkOfRegistry R) pi π = accept ⟹
      ∃ … t, Satisfied2Staged hash E (R pi.effect) … t ∧ tracePublishedCommit t = pi.toPublished

`Satisfied2Staged` upgrades the deployed `Satisfied2` on exactly ONE row gate: the `proofBind` op,
whose deployed denotation `DescriptorIR2.VmConstraint2.holdsAt … (.proofBind _) = True` (`:570`,
vacuous) becomes `ProofBind.boundAt E env` (the column commits to a VERIFYING sub-proof). So the
DEPLOYED AIR is STRICTLY WEAKER than the staged AIR.

## What is proved here

§A `deployed_admits_unbacked` — the explicit FORGED TRACE. A concrete custom descriptor (`demoC`)
   and trace whose `custom_proof_commitment` column is `999` (a value NO verifying sub-proof of the
   demo engine exposes), with the Custom selector ON. It SATISFIES the deployed `Satisfied2` (the
   True-gate passes the forged row) yet is REJECTED by `Satisfied2Staged` (`boundAt` is false). The
   deployed AIR admits a trace the staged AIR rejects — the explicit forged custom proof.

§B `starkSoundCustom_unsound_over_deployed` — `StarkSoundCustom`'s staged extraction does NOT follow
   from the deployed `Satisfied2` extraction: there is NO uniform bridge `Satisfied2 ⇒
   Satisfied2Staged` (§A is the counterexample). So consuming `StarkSoundCustom` over the deployed
   True-gate AIR asserts strictly more than the deployed verifier enforces. The precise honest
   statement + its limits are documented at the theorem.

§C `engineBinding_of_floor` — `EngineBinding` is NOT an irreducible axiom: it REDUCES to
   `Poseidon2SpongeCR` (the PI-commitment is a Poseidon2 sponge of the public inputs, the VK among
   them) + the FRI extraction (`verify ⟹ piCommit = sponge of genuine PIs`). Proved as a lemma off
   {Poseidon2-CR, FRI-factoring}, with a vk-headed corollary and a non-vacuous concrete instance.

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound} + the named
floor carrier `Poseidon2SpongeCR` AS A HYPOTHESIS. NO new axiom, NO `sorry`. NEW file; all imports
read-only.
-/
import Dregg2.Circuit.CustomApex

namespace Dregg2.Circuit.CustomCarrierAttack

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.CustomApex
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)
open Dregg2.Exec.CircuitEmit (EmittedExpr)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §A — the forged trace: deployed `Satisfied2` accepts what staged `Satisfied2Staged` rejects.

We reuse the in-tree demo descriptor `DescriptorIR2.demoC` (one `proofBind ⟨.var 2, .var 0, .var 1⟩`:
guard = col 2, `custom_proof_commitment` = col 0, `custom_program_vk_hash` = col 1) and the toy
recursion engine `DescriptorIR2.demoEngine` (the ONLY verifying proof exposes commitment `123` /
vk `45`). The HONEST demo trace (`demoCTrace`, commit = 123) binds; the FORGED trace below sets the
commitment column to `999` while keeping the selector ON. -/

/-- The forged Custom row: `custom_proof_commitment` (col 0) = `999` — a commitment NO verifying
sub-proof of `demoEngine` exposes (the only verifying proof commits to `123`); `custom_program_vk_hash`
(col 1) = `45`; the Custom selector (col 2) = `1` (the binding gate is ACTIVE). -/
def forgedRow : Assignment := fun i => if i = 0 then 999 else if i = 1 then 45 else if i = 2 then 1 else 0

/-- The forged single-row witness: one main row, no auxiliary tables (proof binding rides the engine,
not a committed table) — byte-for-byte the shape of `demoCTrace`, only the commitment column moved. -/
def forgedTrace : VmTrace := { rows := [forgedRow], pub := zeroAsg, tf := fun _ => [] }

/-- **The deployed `proofBind` gate is literally `True` — it enforces NOTHING.** This is the root of
the forgery: the deployed AIR's per-row meaning of a `proofBind` op carries no content, so any column
values pass. (`DescriptorIR2.VmConstraint2.holdsAt … (.proofBind _) = True`, `:570`.) -/
theorem deployed_proofBind_gate_vacuous (hash : List ℤ → ℤ) (tf : TraceFamily) (env : VmRowEnv)
    (isFirst isLast : Bool) (m : ProofBind) :
    VmConstraint2.holdsAt hash tf env isFirst isLast (.proofBind m) := trivial

/-- **The forged trace SATISFIES the deployed `Satisfied2`.** Identical to `demoC_satisfied` minus the
proof-binding leg: the proofBind row passes via the vacuous True-gate, and every memory/hash/range leg
is empty. So the deployed verifier's extraction relation accepts a trace whose Custom row binds to no
verifying sub-proof. -/
theorem forged_satisfied2 :
    Satisfied2 (fun _ => 0) demoC (fun _ => 0) (fun _ => ((0 : ℤ), 0)) [] forgedTrace := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    simp only [demoC, List.mem_cons, List.not_mem_nil, or_false] at hc
    subst hc; trivial
  · intro i hi; trivial
  · intro i hi r hr; simp [demoC] at hr
  · intro op hop; rw [show memLog demoC forgedTrace = [] from rfl] at hop; cases hop
  · rw [show memLog demoC forgedTrace = [] from rfl]; exact by decide
  · rw [show memLog demoC forgedTrace = [] from rfl]; exact memCheck_nil _ _
  · rfl
  · rfl

/-- **The forged trace is REJECTED by the staged `Satisfied2Staged`.** The staged `proofBind` gate is
`ProofBind.boundAt demoEngine env`, which on the active row demands `demoEngine.boundTo 999 45` — a
VERIFYING sub-proof with commitment `999`. The only verifying proof of `demoEngine` commits to `123`,
so no such sub-proof exists: the staged constraint fails. -/
theorem forged_not_staged :
    ¬ Satisfied2Staged (fun _ => 0) demoEngine demoC (fun _ => 0) (fun _ => ((0 : ℤ), 0)) []
        forgedTrace := by
  intro h
  -- the staged proofBind row constraint at row 0:
  have hrow := h.rowConstraints 0 (by decide) (.proofBind ⟨.var 2, .var 0, .var 1⟩) (by simp [demoC])
  -- holdsAtStaged (.proofBind m) ≡ ProofBind.boundAt demoEngine (envAt forgedTrace 0) m
  -- the guard (col 2 = 1) is active, so we obtain demoEngine.boundTo 999 45:
  have hbound := hrow (by decide)
  obtain ⟨p, hp, hpc, hpv⟩ := hbound
  -- demoEngine.piCommit p ≡ 123, the commit column ≡ 999 (defeq); 123 = 999 is false.
  have hcontra : (123 : ℤ) = 999 := hpc
  exact absurd hcontra (by decide)

/-- **§A keystone — `deployed_admits_unbacked`.** ∃ a concrete custom descriptor and trace satisfying
the DEPLOYED `Satisfied2` (True-gate) yet failing the STAGED `Satisfied2Staged` (`boundAt` false): the
deployed AIR admits a Custom trace whose proof-binding commitment is backed by NO verifying sub-proof.
This is the explicit forged custom proof the deployed circuit cannot detect. -/
theorem deployed_admits_unbacked :
    ∃ (E : ProofEngine) (d : EffectVmDescriptor2) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
      (maddrs : List ℤ) (t : VmTrace),
      Satisfied2 (fun _ => 0) d minit mfin maddrs t ∧
      ¬ Satisfied2Staged (fun _ => 0) E d minit mfin maddrs t :=
  ⟨demoEngine, demoC, (fun _ => 0), (fun _ => ((0 : ℤ), 0)), [], forgedTrace,
    forged_satisfied2, forged_not_staged⟩

/-! ## §B — `StarkSoundCustom` is unsound over the deployed True-gate AIR. -/

/-- **§B keystone — `starkSoundCustom_unsound_over_deployed`.** There is NO uniform upgrade
`Satisfied2 ⇒ Satisfied2Staged`. Since `StarkSound`'s extraction payload is `Satisfied2` and
`StarkSoundCustom`'s is `Satisfied2Staged`, the ONLY way to discharge a `StarkSoundCustom` instance
from the deployed verifier (whose AIR-soundness yields the `Satisfied2` of `StarkSound`) is to compose
with such a bridge — which §A proves cannot exist. Hence `StarkSoundCustom` over the deployed registry
asserts strictly MORE than the deployed True-gate AIR enforces (the proof-binding leg), and is NOT a
consequence of the deployed `StarkSound` floor.

PRECISION / limits (honest): this does NOT prove `StarkSoundCustom hash E R → False` as a class —
`verifyBatch` is opaque and `extract` is existential, so if the deployed verifier never accepts (or
always re-extracts a DIFFERENT, backed trace) the class stays vacuously inhabited. What is rigorously
established is the per-witness fact that drives the apex: the deployed extraction's witness type is
STRICTLY WEAKER than the staged one, so the binding `lightclient_unfoolable_custom_binds` claims is
carried ENTIRELY by the `StarkSoundCustom`/`Satisfied2Staged` hypothesis, NOT by the deployed circuit.
Over the deployed True-gate AIR that hypothesis is ungrounded — the theorem is clean-but-vacuous as
deployed. The real binding must come from the SEPARATE staged AIR (the gated VK epoch) or the FOLD
(`AggAirSound`), never from consuming `StarkSoundCustom` against the deployed VK. -/
theorem starkSoundCustom_unsound_over_deployed :
    ¬ ∀ (hash : List ℤ → ℤ) (E : ProofEngine) (d : EffectVmDescriptor2)
        (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace),
        Satisfied2 hash d minit mfin maddrs t →
        Satisfied2Staged hash E d minit mfin maddrs t := by
  intro hbridge
  exact forged_not_staged
    (hbridge (fun _ => 0) demoEngine demoC (fun _ => 0) (fun _ => ((0 : ℤ), 0)) [] forgedTrace
      forged_satisfied2)

/-! ## §C — `EngineBinding` reduces to the floor (it is NOT an irreducible axiom).

`EngineBinding E` says the engine's PI-commitment is collision-free across verifying proofs (two
verifying sub-proofs with the same `piCommit` agree on their program VK). We show this is a THEOREM off
`Poseidon2SpongeCR` (the sponge is injective) once the engine's commitment FACTORS as the Poseidon2
sponge of its public inputs (the FRI extraction obligation) with the program VK among them. -/

/-- **`engineBinding_of_floor` — the reduction (NAMED floor carriers as hypotheses, no new axiom).**
Given an encoding `enc` of a proof's public inputs, IF (FRI extraction) a verifying proof's exposed
`piCommit` is the Poseidon2 sponge of `enc`, and (structural) the program VK is recoverable from `enc`,
THEN `Poseidon2SpongeCR hash` alone yields `EngineBinding E`. The chain: `piCommit p = piCommit q`
⟹ `sponge (enc p) = sponge (enc q)` ⟹ (CR/injective) `enc p = enc q` ⟹ `vkOf p = vkOf q`. -/
theorem engineBinding_of_floor (hash : List ℤ → ℤ) (E : ProofEngine) (enc : E.Proof → List ℤ)
    (hCR : Poseidon2SpongeCR hash)
    -- FRI extraction: a VERIFYING proof's exposed PI-commitment IS the sponge of its genuine PIs.
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (enc p))
    -- structural: the program VK is one of the committed public inputs (recoverable from `enc`).
    (hvk : ∀ p q, E.verify p = true → E.verify q = true → enc p = enc q → E.vkOf p = E.vkOf q) :
    EngineBinding E := by
  refine ⟨fun p q hp hq hpc => ?_⟩
  have hh : hash (enc p) = hash (enc q) := by
    rw [← hfactor p hp, ← hfactor q hq]; exact hpc
  exact hvk p q hp hq (hCR _ _ hh)

/-- **`engineBinding_of_floor_vkHeaded` — the residual is EXACTLY the FRI factoring.** When the PI
encoding is vk-headed (`enc p = vkOf p :: tail p` — the program VK is the leading public input, as the
leaf wrap lays it), the structural `hvk` discharges internally (cons-injectivity). The ONLY remaining
hypothesis beyond `Poseidon2SpongeCR` is `hfactor` = the FRI extraction "`verify ⟹ piCommit = sponge of
the genuine PIs`". So `EngineBinding` rests on {Poseidon2-CR, FRI-extraction} and nothing else. -/
theorem engineBinding_of_floor_vkHeaded (hash : List ℤ → ℤ) (E : ProofEngine)
    (tailEnc : E.Proof → List ℤ)
    (hCR : Poseidon2SpongeCR hash)
    (hfactor : ∀ p, E.verify p = true → E.piCommit p = hash (E.vkOf p :: tailEnc p)) :
    EngineBinding E := by
  refine engineBinding_of_floor hash E (fun p => E.vkOf p :: tailEnc p) hCR hfactor ?_
  intro p q hp hq henc
  injection henc with hvkeq _

/-! ### Non-vacuity: the reduction FIRES, resting on `Poseidon2SpongeCR` ALONE.

`floorEngine hash` is an engine whose proofs are `(vk, statement)` pairs and whose PI-commitment IS the
sponge of `[vk, statement]` — i.e. the FRI factoring holds BY CONSTRUCTION (`rfl`). Its `EngineBinding`
then follows from `Poseidon2SpongeCR hash` with NO `EngineBinding` assumption: a concrete witness that
`EngineBinding` is derivable, not carried. -/
def floorEngine (hash : List ℤ → ℤ) : ProofEngine where
  Proof    := ℤ × ℤ
  verify   := fun _ => true
  piCommit := fun p => hash [p.1, p.2]
  vkOf     := fun p => p.1

/-- The floor engine satisfies `EngineBinding` resting ONLY on `Poseidon2SpongeCR` — the reduction is
non-vacuous and `EngineBinding` is PROVEN (not assumed) here. -/
theorem floorEngine_binding (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    EngineBinding (floorEngine hash) := by
  refine engineBinding_of_floor hash (floorEngine hash) (fun p => [p.1, p.2]) hCR
    (fun p _ => rfl) ?_
  intro p q hp hq henc
  injection henc with h1 _

/-! ## Axiom audit — every load-bearing arm. -/

#assert_axioms deployed_proofBind_gate_vacuous
#assert_axioms forged_satisfied2
#assert_axioms forged_not_staged
#assert_axioms deployed_admits_unbacked
#assert_axioms starkSoundCustom_unsound_over_deployed
#assert_axioms engineBinding_of_floor
#assert_axioms engineBinding_of_floor_vkHeaded
#assert_axioms floorEngine_binding

end Dregg2.Circuit.CustomCarrierAttack
