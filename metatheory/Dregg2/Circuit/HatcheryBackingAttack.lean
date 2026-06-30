/-
# Dregg2.Circuit.HatcheryBackingAttack — ADVERSARIAL soundness audit of the deployed hatchery
  mint's CELL-CONTRACT attestation backing (the analog of `SovereignBackingAttack` /
  `CustomCarrierAttack` / `BridgeBackingAttack` for the hatchery `HpresProof::Attested` crown).

This module attacks the deployed hatchery-mint transition head-on, IN LEAN, importing everything
read-only. It is a refutation file: the load-bearing arms are proved WITHOUT `sorry`, and the
conclusion is stated precisely.

## The target

A hatchery `MintedKind` is born by a deployed `CreateCellFromFactory`-shaped turn: the executor
installs the kind's `state_constraints` (the invariant-as-program) on the child, and re-evaluates
that program on every later turn (`MintedKind::evaluate_transition` → `CellProgram::
evaluate_with_meta`). That cell-BIRTH transition is the deployed effect-vm leg. But the
`HpresProof::Attested { contract_hash }` *forever-crown* — the claim that the kind's invariant is
backed by a machine-checked `Dregg2.Verify.Contract.CellContract` (a real `step_ob` proof term,
holding under EVERY adversarial schedule) — is:

  (a) the CONTRACT BACKING: the published `contract_hash` resolves to a VERIFYING `CellContract`
      proof (a real `step_ob`), and
  (b) the INVARIANT BINDING: that proved contract certifies THIS kind's invariant — not a weaker /
      different one (`Hatchery.lean::forged_attestation_rejected`, the content-hash check).

In `sdk/src/hatchery_mint.rs` the `contract_hash` is only STORED (`attest_hpres`, field
`HpresProof::Attested { contract_hash }`, line 262) — it is read by NO circuit constraint on either
rung, and the Lean `attested_enforces_forever` is an EXECUTOR-image carry, not a deployed-VK one.
So a PURE LIGHT CLIENT (one that only folds the per-turn recursion tree) witnesses neither (a) nor
(b): a mint carrying ANY `contract_hash` produces an `AttestedHistory` identical to one backed by a
real `CellContract` proof. The deployed AIR admits a "forever-crowned" mint whose crown verifies
NOTHING.

This is the SAME vacuity CLASS that `SovereignBackingAttack` proves for the sovereign owner
signature and `BridgeBackingAttack` for the inbound bridge mint: REAL as re-executed (the executor
runs the program gate forever; a properly-built `Attested` carries a real `step_ob`), VACUOUS as
deployed-light-client (the `contract_hash` crown is unwitnessed in the proven kernel transition).

## What is proved here

§A `deployed_admits_unbacked_hatchery` — the explicit FORGED hatchery mint. A contract-attestation
   engine whose only verifying proof attests `contract_hash = 77` certifying invariant-digest `42`,
   and an HONEST-looking hatchery mint leg row that SATISFIES the deployed cell-birth transition
   (the teeth carry the prover's claimed values, the transition holds) while its published
   `contract_hash` is `0` — a hash NO verifying `CellContract` proof attests (a FABRICATED crown).
   The deployed AIR accepts it; the (staged) backing predicate rejects it.

§A′ `deployed_admits_wrong_contract` — the INVARIANT-BINDING forgery (leg (b),
   `forged_attestation_rejected` at the LC level): the leg's `contract_hash` MATCHES a verifying
   proof while that proof certifies a DIFFERENT invariant than the kind's claimed
   `invariant_digest`. The mint waves a real `contract_hash`, but the contract behind it crowns a
   weaker kind — and the light client cannot tell.

§B `deployed_intent_does_not_force_backing` — there is NO uniform "deployed-accepts ⟹ attested":
   §A is the counterexample. So a light client that only checks the deployed hatchery AIR learns
   NOTHING about the `CellContract` backing. The repair (the crown must come from the FOLD over a
   re-proved CONTRACT-ATTESTATION leaf) is named at §C, mirroring `CustomBindingFromFold` /
   `sovereign_leaf_adapter`.

## The repair (named, mirroring the sovereign / custom / bridge fold-wire)

The real forever-crown must come from the per-turn FOLD over a re-proved CONTRACT-ATTESTATION leaf
(`circuit-prove::hatchery_leaf_adapter::prove_hatchery_leaf`) whose in-circuit-bound PIs carry the
attestation tuple `(contract_hash, invariant_digest)`, connected to the deployed hatchery leg's
claimed `contract_hash` teeth via `hatchery_leaf_adapter::prove_hatchery_binding_node_segmented`
(the analog of `prove_sovereign_binding_node_segmented`). The leaf binds the contract-attestation
DIGEST in-circuit; the re-verification that the `contract_hash` resolves to a real verifying
`CellContract` proof term (the full in-AIR `step_ob` recheck) stays off-AIR — the same
digest-of-attestation boundary G8 / membership / the sovereign owner-sig carry (full in-AIR
contract re-proof is the named cost).

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new axiom,
NO `sorry`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.HatcheryBackingAttack

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the contract-attestation engine + the (staged) backing predicate.

A `ContractEngine` abstracts the off-VK `CellContract` attestation the hatchery crown rests on
(`Hatchery.lean::Attested` / `attested_enforces_forever`): `verifyContract` is the bit that a
`contract_hash` resolves to a REAL verifying `CellContract` proof term (a real `step_ob`), and a
VERIFYING proof attests the `contract_hash` (the content hash of the proved artifact) and the
`invariant_digest` it certifies (which kind's invariant the contract crowns). This is the hatchery
analog of `SovereignBackingAttack.SovAuthorityEngine` (`verifySig` + `signedKeyCommit` + …) and
`CustomApex.ProofEngine` (`verify` + `piCommit`). -/

/-- An abstract contract-attestation engine: its accepting bit, and the `(contract_hash,
invariant_digest)` tuple a VERIFYING `CellContract` proof attests. -/
structure ContractEngine where
  /-- The proof type of a `Dregg2.Verify.Contract.CellContract` attestation. -/
  Proof : Type
  /-- The verifier's accepting bit (the `contract_hash` resolves to a real `step_ob` proof term). -/
  verifyContract : Proof → Bool
  /-- The content hash a verifying contract attests (the `HpresProof::Attested { contract_hash }`). -/
  attestedHash : Proof → ℤ
  /-- The invariant digest the proved contract certifies (which kind's invariant it crowns). -/
  certifiedInvariant : Proof → ℤ

/-! ### The hatchery leg's attestation columns.

These are the deployed mint leg's teeth — the `contract_hash` the mint publishes and the kind's
`invariant_digest` (the `kind_id` / child-VK identifying which invariant the crown must certify).
In the deployed AIR they are present (the `contract_hash` is STORED, `hatchery_mint.rs:262`) but
read by NO constraint (dead / ungated) — that is exactly the hole. The birth-transition columns
(`bornCol`/`newCol`) model the cell-birth state step the deployed leg DOES prove. -/

/-- `contract_hash` column (an aux mint tooth, offset 24). -/
def contractHashCol : Nat := 24
/-- The kind's `invariant_digest` column (an aux mint tooth, offset 25). -/
def invariantDigestCol : Nat := 25
/-- The pre/birth state column (offset 0 stands for it here). -/
def bornCol : Nat := 0
/-- The post-state column (offset 8 stands for it here). -/
def newCol : Nat := 8

/-- The `contract_hash` a leg row publishes. -/
def contractHashOf (env : VmRowEnv) : ℤ := env.loc contractHashCol
/-- The kind's `invariant_digest` a leg row publishes. -/
def invariantDigestOf (env : VmRowEnv) : ℤ := env.loc invariantDigestCol
/-- The pre/birth state a leg row publishes. -/
def bornOf (env : VmRowEnv) : ℤ := env.loc bornCol
/-- The post-state a leg row publishes. -/
def newOf (env : VmRowEnv) : ℤ := env.loc newCol

/-- **`Backed E env`** — the STAGED backing predicate the deployed descriptor SHOULD (but does not)
enforce: the leg's published `(contract_hash, invariant_digest)` is attested by SOME verifying
`CellContract` proof that ALSO certifies the kind's invariant. This is the hatchery analog of
`SovereignBackingAttack.Authorized` and `BridgeBackingAttack.BackedAt` — the content the deployed
AIR omits (legs (a) contract-backing + (b) invariant-binding, both OFF-VK in the executor's
attestation check). -/
def Backed (E : ContractEngine) (env : VmRowEnv) : Prop :=
  ∃ p : E.Proof, E.verifyContract p = true
    ∧ E.attestedHash p = contractHashOf env
    ∧ E.certifiedInvariant p = invariantDigestOf env

/-! ### The deployed hatchery leg's row intent.

`DeployedHatchIntent env` is the content the deployed mint leg gates: the cell-birth transition
`new = born + 7` (a concrete stand-in for "the rotated proof proves SOME genuine birth step that
installs the kind's `state_constraints`") together with the teeth carrying the prover's CLAIMED
`contract_hash` / `invariant_digest`. The backing legs (a)/(b) are NOT among the gated content —
that is the point. A forged row satisfies this while no verifying contract proof attests its
crown. -/
def DeployedHatchIntent (env : VmRowEnv) : Prop :=
  newOf env = bornOf env + 7

/-! ## §A — the forged hatchery mint: deployed-accepts what the backing predicate rejects.

A demo contract engine whose ONLY verifying proof attests `(contract_hash, invariant_digest) =
(77, 42)` (the same one-verifying-proof shape `SovereignBackingAttack.demoSov` /
`CustomCarrierAttack.demoEngine` use). The forged leg row carries `contract_hash = 0`,
`invariant_digest = 42`, `born = 0`, `new = 7` — its transition holds (`7 = 0 + 7`) so the deployed
AIR accepts, but its `contract_hash 0` is attested by NO verifying contract (a FABRICATED crown). -/

/-- A demo contract-attestation engine: the only verifying proof (`true`) attests content hash `77`
certifying invariant digest `42`. -/
def demoContract : ContractEngine where
  Proof := Bool
  verifyContract := fun b => b
  attestedHash := fun _ => 77
  certifiedInvariant := fun _ => 42

/-- The forged hatchery leg row: `contract_hash = 0` (col 24), `invariant_digest = 42` (col 25),
`born = 0` (col 0), `new = 7` (col 8). Its transition holds, but `contract_hash 0` is attested by no
verifying proof of `demoContract`. -/
def forgedEnv : VmRowEnv where
  loc := fun i => if i = newCol then 7 else if i = invariantDigestCol then 42 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **The deployed descriptor ACCEPTS the forged row.** Its transition holds: `new (7) = born (0) +
7`. The deployed mint leg gates exactly this; the attestation teeth are stored / ungated. -/
theorem forged_deployed_accepts : DeployedHatchIntent forgedEnv := by
  simp only [DeployedHatchIntent, newOf, bornOf, forgedEnv, newCol, bornCol, invariantDigestCol]
  decide

/-- The forged row's published `contract_hash` is `0` — a hash NO verifying proof of `demoContract`
attests (the only verifying proof attests `77`). -/
theorem contractHash_forgedEnv : contractHashOf forgedEnv = 0 := by
  simp only [contractHashOf, forgedEnv, contractHashCol, newCol, invariantDigestCol]
  decide

/-- **The forged row is REJECTED by the (staged) backing predicate.** Its `contract_hash` is `0`;
the only verifying proof of `demoContract` attests `77`, so no verifying proof attests it — `Backed`
fails. The deployed descriptor cannot detect this: it never reads `contract_hash`. -/
theorem forged_not_backed : ¬ Backed demoContract forgedEnv := by
  rintro ⟨p, _hv, hh, _hinv⟩
  -- demoContract.attestedHash p ≡ 77 (defeq); contractHashOf forgedEnv = 0; 77 = 0 is false.
  rw [contractHash_forgedEnv] at hh
  simp only [demoContract] at hh
  exact absurd hh (by decide)

/-- **§A keystone — `deployed_admits_unbacked_hatchery`.** ∃ a contract-attestation engine and a
hatchery mint leg row that SATISFIES the deployed birth-transition intent yet whose published
`contract_hash` is attested by NO verifying `CellContract` proof: the deployed AIR admits a
"forever-crowned" mint whose crown does NOT verify. This is the explicit fabricated crown the
deployed circuit (and thus a pure light client) cannot detect — the analog of
`SovereignBackingAttack.deployed_admits_unbacked_sovereign` and
`CustomCarrierAttack.deployed_admits_unbacked`. -/
theorem deployed_admits_unbacked_hatchery :
    ∃ (E : ContractEngine) (env : VmRowEnv),
      DeployedHatchIntent env ∧ ¬ Backed E env :=
  ⟨demoContract, forgedEnv, forged_deployed_accepts, forged_not_backed⟩

/-! ## §A′ — the wrong-contract (invariant-binding) forgery.

The same shape, but the leg's `contract_hash` MATCHES a verifying proof while its `invariant_digest`
is a value that proof does NOT certify: a real contract for a DIFFERENT (e.g. weaker) kind, waved
as THIS kind's crown. The LC-level image of `Hatchery.lean::forged_attestation_rejected`: the
deployed transition still proves a genuine birth, but the crown certifies the wrong invariant, and
`execute.rs`'s content-hash check is off-VK. -/

/-- A leg row whose `contract_hash = 77` (a verifying proof attests this) but whose
`invariant_digest = 99` (col 25) — an invariant the only verifying proof of `demoContract` (which
certifies `42`) does NOT crown. `new = 7`, `born = 0` so the transition `7 = 0 + 7` still holds. -/
def wrongContractEnv : VmRowEnv where
  loc := fun i =>
    if i = contractHashCol then 77
    else if i = invariantDigestCol then 99
    else if i = newCol then 7
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The wrong-contract row satisfies the deployed transition intent (`7 = 0 + 7`). -/
theorem wrongContract_deployed_accepts : DeployedHatchIntent wrongContractEnv := by
  simp only [DeployedHatchIntent, newOf, bornOf, wrongContractEnv, newCol, bornCol,
    contractHashCol, invariantDigestCol]
  decide

/-- **`deployed_admits_wrong_contract`.** The wrong-contract row satisfies the deployed transition
intent, but no verifying proof of `demoContract` (which certifies invariant `42`) crowns its
`invariant_digest = 99`, so `Backed` rejects: the deployed AIR does not witness the invariant
binding (leg (b)). -/
theorem deployed_admits_wrong_contract :
    DeployedHatchIntent wrongContractEnv ∧ ¬ Backed demoContract wrongContractEnv := by
  refine ⟨wrongContract_deployed_accepts, ?_⟩
  rintro ⟨p, _hv, _hh, hinv⟩
  -- demoContract.certifiedInvariant p ≡ 42 (defeq); invariantDigestOf wrongContractEnv = 99.
  have hinv99 : invariantDigestOf wrongContractEnv = 99 := by
    simp only [invariantDigestOf, wrongContractEnv, invariantDigestCol, contractHashCol, newCol]
    decide
  rw [hinv99] at hinv
  simp only [demoContract] at hinv
  exact absurd hinv (by decide)

/-! ## §B — the deployed hatchery AIR does not force the backing. -/

/-- **§B keystone — `deployed_intent_does_not_force_backing`.** There is NO uniform implication "the
deployed hatchery leg intent holds ⟹ the forever-crown is backed": §A exhibits a row whose deployed
intent holds while no verifying contract proof attests its `contract_hash`. So consuming an
attestation claim against the deployed hatchery AIR asserts strictly MORE than the verifier
enforces — the deployed descriptor binds only the birth transition, never the `CellContract`
backing / invariant binding. The real crown must come from the per-turn FOLD over the re-proved
contract-attestation leaf (`hatchery_leaf_adapter::prove_hatchery_leaf` connected via
`prove_hatchery_binding_node_segmented` to the published `contract_hash` teeth PIs), exactly as
`CustomBindingFromFold` rebuilds the custom binding from `AggAirSound`. -/
theorem deployed_intent_does_not_force_backing :
    ¬ ∀ (E : ContractEngine) (env : VmRowEnv),
        DeployedHatchIntent env → Backed E env := by
  intro hforce
  exact forged_not_backed (hforce demoContract forgedEnv forged_deployed_accepts)

/-! ## §C — Axiom audit — every load-bearing arm. -/

#assert_axioms forged_deployed_accepts
#assert_axioms contractHash_forgedEnv
#assert_axioms forged_not_backed
#assert_axioms deployed_admits_unbacked_hatchery
#assert_axioms wrongContract_deployed_accepts
#assert_axioms deployed_admits_wrong_contract
#assert_axioms deployed_intent_does_not_force_backing

end Dregg2.Circuit.HatcheryBackingAttack
