/-
# Dregg2.Circuit.FactoryBackingAttack — ADVERSARIAL soundness audit of the deployed factory-born
  cell's creation backing (the analog of `CustomCarrierAttack` / `BridgeBackingAttack` /
  `SovereignBackingAttack` for the `Effect::CreateCellFromFactory` leg).

This module attacks the deployed factory-creation leg head-on, IN LEAN, importing everything
read-only. It is a refutation file: the load-bearing arms are proved WITHOUT `sorry`, and the
conclusion is stated precisely.

## The target

`Effect::CreateCellFromFactory` (`turn/src/action.rs:1218`) installs a child cell's `child_vk`,
capabilities, initial fields, and slot caveats via a GENERIC `EFFECT_CREATE_CELL` selector
(`action.rs:2563`) — there is NO factory AIR and NO STARK that constrains the creation. The off-AIR
validator `dregg_cell::factory::FactoryRegistry::validate_and_record` (`cell/src/factory.rs:917`,
called at `turn/src/executor/apply.rs:2360`) does ALL the work:

  (a) the CHILD-VK DERIVATION: `child_vk` is the descriptor's strategy-derived VK
      (`ChildVkStrategy::validate_child_vk` — `Fixed` exact / `Derived` `Poseidon2(factory_vk ‖
      param_hash)` / `FromSet` membership — `factory.rs:236`);
  (b) the CAPABILITY ENVELOPE: every granted cap is within an `allowed_cap_templates` entry
      (`cap_within_templates`, `factory.rs:481`);
  (c) the FIELD + BUDGET ENVELOPE: initial fields satisfy `field_constraints`, and the per-epoch
      `creation_budget` is not exhausted (`record_creation`, `factory.rs:883`).

The executor then merely INSTALLS the validated `child_vk` / `state_constraints` as IDENTIFIERS on
the new cell (`apply.rs:2416..2443`). A PURE LIGHT CLIENT (one that only folds the per-turn recursion
tree) never witnesses any of (a)/(b)/(c): the deployed `EFFECT_CREATE_CELL` row carries the prover's
CLAIMED `child_vk` / caps / fields with NO constraint linking them to a verifying factory descriptor.
So a forged factory-born cell — an arbitrary `child_vk`, an out-of-template capability, or a creation
past its epoch budget — is admitted with NO witnessed backing.

This is the SAME vacuity CLASS that `CustomCarrierAttack` proves for `Effect::Custom`,
`BridgeBackingAttack` proves for the inbound bridge mint, and `SovereignBackingAttack` proves for the
sovereign-cell leg: REAL as re-executed, VACUOUS as deployed-light-client.

## What is proved here

§A `deployed_admits_forged_child_vk` — the explicit FORGED child VK. A factory engine whose only
   validating creation derives `child_vk = 200` for `factory_vk = 100`, and an HONEST-looking
   creation leg row that SATISFIES the deployed transition intent (a genuine `parent → child`
   commit) while its published `child_vk` is `999` — a VK no validating creation of the factory
   derives (an arbitrary-program forgery). The deployed AIR accepts it; the (staged) backing
   predicate rejects it.

§A′ `deployed_admits_overbudget_factory` — the BUDGET forgery: the same `(factory_vk, child_vk)`
   a validating creation backs, but the factory's per-epoch `creation_budget` is EXHAUSTED. The
   deployed transition still commits a genuine child cell, but `record_creation` (`factory.rs:895`)
   would reject it, and the light client cannot tell — the consume-once budget counter is the
   RE-EXEC tooth, not a light-client one. (The factory analog of the sovereign REPLAY corollary.)

§C `deployed_admits_outside_cap_factory` — the CAPABILITY forgery: a creation whose granted cap is
   NOT within any `allowed_cap_templates` entry. The deployed transition commits the child with the
   over-broad cap installed; `cap_within_templates` (off-AIR) would reject it.

§B `deployed_intent_does_not_force_backing` — there is NO uniform "deployed-accepts ⟹ factory-backed":
   §A is the counterexample. So a light client that only checks the deployed `EFFECT_CREATE_CELL` AIR
   learns NOTHING about the factory descriptor. The repair (the backing must come from the FOLD over
   a re-proved FACTORY leaf) is named at §C, mirroring the sovereign / custom / bridge fold-wire.

Non-vacuity is pinned by `honest_factory_backed`: the backing predicate is SATISFIABLE — an honest
creation whose `child_vk` is the derived VK, whose caps are in-template and whose budget is fresh IS
`Authorized`. (Memory note: a load-bearing predicate must be proved true AND false.)

## The repair (named, mirroring the custom / bridge / sovereign fold-wire)

The real backing must come from the per-turn FOLD over a re-proved FACTORY leaf
(`circuit-prove::factory_leaf_adapter::prove_factory_leaf`) whose in-circuit-bound PIs carry the
factory tuple `(factory_vk, child_vk, derivation_digest)` — the `derivation_digest` a Poseidon2
commitment to the validated `caps ‖ fields ‖ budget ‖ param_hash` — connected to the deployed
`EFFECT_CREATE_CELL` leg's CLAIMED `child_vk` teeth via
`factory_leaf_adapter::prove_factory_binding_node_segmented` (the analog of
`prove_sovereign_binding_node_segmented`). The leaf binds the derivation DIGEST in-circuit; the full
in-AIR re-derivation of `Poseidon2(factory_vk ‖ param_hash)` and the Merkle-membership of
`allowed_cap_templates` stay off-AIR (the same digest-of-attestation boundary the sovereign /
membership carriers ride — full in-AIR derivation is the named cost).

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new axiom,
NO `sorry`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.FactoryBackingAttack

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the factory engine + the (staged) backing predicate.

A `FactoryEngine` abstracts the off-AIR factory validation the executor runs at creation
(`validate_and_record`, `cell/src/factory.rs:917`): a `Creation` is a registered-factory creation
attempt; `validateCreation` is the descriptor-exists + child-VK-derivation + field-constraints
accepting bit; `boundFactoryVk` is the descriptor's `factory_vk`; `derivedChildVk` is the
strategy-derived child VK; `capsWithin` is the `cap_within_templates` bit. This is the factory analog
of `SovereignBackingAttack.SovAuthorityEngine` (`verifySig` + `signedKeyCommit` + …) and
`BridgeBackingAttack.NoteSpendEngine`. -/

/-- An abstract factory engine: its validating bit, the `(factory_vk, child_vk)` a validating
creation binds, and the in-template-capability bit. -/
structure FactoryEngine where
  /-- The creation-attempt type (a registered factory descriptor + claimed creation params). -/
  Creation : Type
  /-- The validator's accepting bit (`validate_and_record` succeeded: descriptor exists, the claimed
  `child_vk` is the strategy-derived VK, the initial fields satisfy `field_constraints`). -/
  validateCreation : Creation → Bool
  /-- The `factory_vk` a validating creation is bound to (the descriptor's `factory_vk`). -/
  boundFactoryVk : Creation → ℤ
  /-- The `child_vk` a validating creation correctly derives (`ChildVkStrategy::validate_child_vk`). -/
  derivedChildVk : Creation → ℤ
  /-- Whether the creation's granted caps are within `allowed_cap_templates` (`cap_within_templates`). -/
  capsWithin : Creation → Bool

/-! ### The factory leg's creation columns.

These are the deployed `EFFECT_CREATE_CELL` aux/PI teeth (the FACTORY_VK / CHILD_VK / cap-status
felts), modeled as the columns the staged backing predicate WOULD read. In the deployed AIR they are
present but read by NO constraint (the claimed values are ungated) — that is exactly the hole. -/

/-- `factory_vk` column (the FACTORY_VK_0 teeth; illustrative aux offset). -/
def factoryVkCol : Nat := 30
/-- `child_vk` column (the CHILD_VK_0 teeth). -/
def childVkCol : Nat := 38
/-- The pre-state parent-commit column (the `EFFECT_CREATE_CELL` rotated `old_commit` felt). -/
def anchorCol : Nat := 0
/-- The post-state child-commit column (the new cell's commitment felt). -/
def newCol : Nat := 8

/-- The `factory_vk` a leg row publishes. -/
def factoryVkOf (env : VmRowEnv) : ℤ := env.loc factoryVkCol
/-- The `child_vk` a leg row publishes. -/
def childVkOf (env : VmRowEnv) : ℤ := env.loc childVkCol
/-- The pre-state parent anchor a leg row publishes. -/
def anchorOf (env : VmRowEnv) : ℤ := env.loc anchorCol
/-- The post-state child commitment a leg row publishes. -/
def newOf (env : VmRowEnv) : ℤ := env.loc newCol

/-- **`Authorized E exhausted env`** — the STAGED backing predicate the deployed descriptor SHOULD
(but does not) enforce: the leg's published `(factory_vk, child_vk)` is backed by SOME validating
creation whose `factory_vk` matches, whose CORRECTLY-DERIVED `child_vk` matches, whose caps are
in-template, and whose factory's epoch budget is NOT exhausted. This is the factory analog of
`SovereignBackingAttack.Authorized` — the content the deployed AIR omits (legs (a) derivation +
(b) caps + (c) field/budget, all OFF-AIR in `validate_and_record`). -/
def Authorized (E : FactoryEngine) (exhausted : ℤ → Prop) (env : VmRowEnv) : Prop :=
  ∃ c : E.Creation, E.validateCreation c = true
    ∧ E.boundFactoryVk c = factoryVkOf env
    ∧ E.derivedChildVk c = childVkOf env
    ∧ E.capsWithin c = true
    ∧ ¬ exhausted (E.boundFactoryVk c)

/-! ### The deployed factory leg's row intent.

`DeployedFactoryIntent env` is the content the deployed `EFFECT_CREATE_CELL` proof gates: the
transition `child_commit = parent_anchor + 7` (a concrete stand-in for "the rotated proof commits
SOME genuine `parent → child` cell"). The backing legs (a)/(b)/(c) are NOT among the gated content —
that is the point. A forged row satisfies this while no validating creation backs its teeth. -/
def DeployedFactoryIntent (env : VmRowEnv) : Prop :=
  newOf env = anchorOf env + 7

/-! ## §0′ — the honest demo factory engine + the non-vacuity witness.

A demo factory whose only validating creation (`true`) binds `factory_vk = 100`, derives
`child_vk = 200`, and grants only in-template caps — the same one-validating-proof shape
`SovereignBackingAttack.demoSov` uses. -/

/-- A demo factory engine: the only validating creation (`true`) binds `factory_vk = 100`, derives
`child_vk = 200`, and is within its cap templates. -/
def demoFactory : FactoryEngine where
  Creation := Bool
  validateCreation := fun b => b
  boundFactoryVk := fun _ => 100
  derivedChildVk := fun _ => 200
  capsWithin := fun _ => true

/-- No factory budget is exhausted (the honest fresh-epoch baseline). -/
def noneExhausted : ℤ → Prop := fun _ => False

/-- The HONEST factory leg row: `factory_vk = 100` (col 30), `child_vk = 200` (col 38),
`anchor = 0` (col 0), `new = 7` (col 8). The validating creation backs exactly these. -/
def honestEnv : VmRowEnv where
  loc := fun i =>
    if i = factoryVkCol then 100
    else if i = childVkCol then 200
    else if i = newCol then 7
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

theorem honestEnv_factoryVk : factoryVkOf honestEnv = 100 := by
  simp only [factoryVkOf, honestEnv, factoryVkCol, childVkCol, newCol]; decide

theorem honestEnv_childVk : childVkOf honestEnv = 200 := by
  simp only [childVkOf, honestEnv, childVkCol, factoryVkCol, newCol]; decide

/-- **NON-VACUITY — `honest_factory_backed`.** The backing predicate is SATISFIABLE: the honest
creation (the validating `true`) backs `honestEnv` — its `factory_vk`/`child_vk` match, its caps are
in-template, and no budget is exhausted. So `Authorized` is not the empty predicate; the forgery
arms below are non-trivial REJECTIONS, not a vacuous "everything fails". -/
theorem honest_factory_backed : Authorized demoFactory noneExhausted honestEnv := by
  refine ⟨true, rfl, ?_, ?_, rfl, ?_⟩
  · show (100 : ℤ) = factoryVkOf honestEnv
    rw [honestEnv_factoryVk]
  · show (200 : ℤ) = childVkOf honestEnv
    rw [honestEnv_childVk]
  · intro h; exact h

/-! ## §A — the forged child VK: deployed-accepts what the backing predicate rejects.

The forged leg row carries `factory_vk = 100` (a legit factory) but `child_vk = 999` — an arbitrary
program VK no validating creation of `demoFactory` derives (it derives `200`). Its transition holds
(`7 = 0 + 7`) so the deployed AIR accepts, but its `child_vk` is backed by NO validating creation
(an arbitrary-program / wrong-VK forgery). -/

/-- The forged child-VK row: `factory_vk = 100`, `child_vk = 999`, `anchor = 0`, `new = 7`. The
transition holds, but `child_vk 999` is derived by no validating creation of `demoFactory`. -/
def forgedChildVkEnv : VmRowEnv where
  loc := fun i =>
    if i = factoryVkCol then 100
    else if i = childVkCol then 999
    else if i = newCol then 7
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **The deployed descriptor ACCEPTS the forged row.** Its transition holds: `new (7) = anchor (0)
+ 7`. The deployed rotated proof gates exactly this; the factory teeth are ungated. -/
theorem forged_deployed_accepts : DeployedFactoryIntent forgedChildVkEnv := by
  simp only [DeployedFactoryIntent, newOf, anchorOf, forgedChildVkEnv, newCol, anchorCol,
    factoryVkCol, childVkCol]
  decide

/-- The forged row's published `child_vk` is `999` — a VK NO validating creation of `demoFactory`
derives (the only validating creation derives `200`). -/
theorem childVk_forgedEnv : childVkOf forgedChildVkEnv = 999 := by
  simp only [childVkOf, forgedChildVkEnv, childVkCol, factoryVkCol, newCol]
  decide

/-- **The forged row is REJECTED by the (staged) backing predicate.** Its `child_vk` is `999`; every
validating creation of `demoFactory` derives `200`, so no validating creation backs it —
`Authorized` fails. The deployed descriptor cannot detect this: it never reads `child_vk`. -/
theorem forged_not_authorized : ¬ Authorized demoFactory noneExhausted forgedChildVkEnv := by
  rintro ⟨c, _hv, _hfvk, hcvk, _hcap, _hfresh⟩
  -- demoFactory.derivedChildVk c ≡ 200 (defeq); childVkOf forgedChildVkEnv = 999; 200 = 999 is false.
  rw [childVk_forgedEnv] at hcvk
  simp only [demoFactory] at hcvk
  exact absurd hcvk (by decide)

/-- **§A keystone — `deployed_admits_forged_child_vk`.** ∃ a factory engine and a creation leg row
that SATISFIES the deployed transition intent yet whose published `child_vk` is derived by NO
validating creation: the deployed AIR admits a factory-born cell whose installed program VK does NOT
match the factory's derivation. This is the explicit forged factory cell the deployed circuit (and
thus a pure light client) cannot detect — the analog of
`SovereignBackingAttack.deployed_admits_unbacked_sovereign`. -/
theorem deployed_admits_forged_child_vk :
    ∃ (E : FactoryEngine) (exhausted : ℤ → Prop) (env : VmRowEnv),
      DeployedFactoryIntent env ∧ ¬ Authorized E exhausted env :=
  ⟨demoFactory, noneExhausted, forgedChildVkEnv, forged_deployed_accepts, forged_not_authorized⟩

/-! ## §A′ — the budget forgery (the factory analog of the sovereign REPLAY corollary).

The same `(factory_vk, child_vk) = (100, 200)` a validating creation backs, but the factory's
per-epoch `creation_budget` is EXHAUSTED. The deployed transition still commits a genuine child cell
(`7 = 0 + 7`), but `record_creation` (`factory.rs:895`, the `*count >= budget` guard) would reject
it — the consume-once budget counter is the RE-EXEC tooth, not a light-client one. -/

/-- The factory `100`'s epoch budget is exhausted. -/
def hundredExhausted : ℤ → Prop := fun x => x = 100

/-- The honest-looking row reuses `honestEnv` (`factory_vk = 100`, `child_vk = 200`): the `(fvk,cvk)`
both bind, but the budget for factory `100` is exhausted. -/
theorem overbudget_deployed_accepts : DeployedFactoryIntent honestEnv := by
  simp only [DeployedFactoryIntent, newOf, anchorOf, honestEnv, newCol, anchorCol, factoryVkCol,
    childVkCol]
  decide

/-- **`deployed_admits_overbudget_factory`.** Take the demo factory and a row whose published
`factory_vk`/`child_vk` BOTH match a validating creation `(100, 200)` (so the derivation binds) — but
the factory's epoch budget is already exhausted. The deployed descriptor still accepts the row's
transition, while `Authorized` (which requires a fresh budget) rejects: the deployed AIR does not
witness the consume-once budget counter (leg (c)). -/
theorem deployed_admits_overbudget_factory :
    DeployedFactoryIntent honestEnv ∧ ¬ Authorized demoFactory hundredExhausted honestEnv := by
  refine ⟨overbudget_deployed_accepts, ?_⟩
  rintro ⟨c, _hv, hfvk, _hcvk, _hcap, hfresh⟩
  -- demoFactory.boundFactoryVk c ≡ 100 (defeq); hundredExhausted 100 ≡ (100 = 100); ¬ that fails.
  exact hfresh rfl

/-! ## §C — the capability forgery: an out-of-template cap.

A creation whose granted capability is NOT within any `allowed_cap_templates` entry
(`cap_within_templates = false`). The deployed transition commits the child with the over-broad cap
installed; the off-AIR `cap_within_templates` check (`factory.rs:481`) would reject it, but the
deployed AIR does not witness the capability envelope (leg (b)). -/

/-- A demo factory IDENTICAL to `demoFactory` except every creation's caps are OUT of template
(`capsWithin = false`) — the over-broad-capability factory attempt. -/
def demoCapOutside : FactoryEngine where
  Creation := Bool
  validateCreation := fun b => b
  boundFactoryVk := fun _ => 100
  derivedChildVk := fun _ => 200
  capsWithin := fun _ => false

/-- **`deployed_admits_outside_cap_factory`.** The honest-looking row (`factory_vk`/`child_vk` both
bind, transition holds) is accepted by the deployed descriptor, but every creation of `demoCapOutside`
grants an out-of-template cap (`capsWithin = false`), so `Authorized` rejects: the deployed AIR does
not witness the capability envelope (leg (b)). -/
theorem deployed_admits_outside_cap_factory :
    DeployedFactoryIntent honestEnv ∧ ¬ Authorized demoCapOutside noneExhausted honestEnv := by
  refine ⟨overbudget_deployed_accepts, ?_⟩
  rintro ⟨c, _hv, _hfvk, _hcvk, hcap, _hfresh⟩
  -- demoCapOutside.capsWithin c ≡ false (defeq); hcap : false = true is absurd.
  simp only [demoCapOutside] at hcap
  exact absurd hcap (by decide)

/-! ## §B — the deployed factory AIR does not force the backing. -/

/-- **§B keystone — `deployed_intent_does_not_force_backing`.** There is NO uniform implication
"the deployed factory leg intent holds ⟹ the factory backing is verified": §A exhibits a row whose
deployed intent holds while no validating creation derives its `child_vk`. So consuming a backing
claim against the deployed `EFFECT_CREATE_CELL` AIR asserts strictly MORE than the verifier enforces —
the deployed descriptor binds only the transition, never the child-VK derivation / caps / budget. The
real backing must come from the per-turn FOLD over the re-proved FACTORY leaf
(`factory_leaf_adapter::prove_factory_leaf` connected via
`prove_factory_binding_node_segmented` to the published `child_vk` teeth PIs), exactly as
`SovereignBackingAttack` rebuilds the sovereign backing from the authority leaf — see the repair. -/
theorem deployed_intent_does_not_force_backing :
    ¬ ∀ (E : FactoryEngine) (exhausted : ℤ → Prop) (env : VmRowEnv),
        DeployedFactoryIntent env → Authorized E exhausted env := by
  intro hforce
  exact forged_not_authorized (hforce demoFactory noneExhausted forgedChildVkEnv forged_deployed_accepts)

/-! ## §D — Axiom audit — every load-bearing arm. -/

#assert_axioms honestEnv_factoryVk
#assert_axioms honestEnv_childVk
#assert_axioms honest_factory_backed
#assert_axioms forged_deployed_accepts
#assert_axioms childVk_forgedEnv
#assert_axioms forged_not_authorized
#assert_axioms deployed_admits_forged_child_vk
#assert_axioms overbudget_deployed_accepts
#assert_axioms deployed_admits_overbudget_factory
#assert_axioms deployed_admits_outside_cap_factory
#assert_axioms deployed_intent_does_not_force_backing

end Dregg2.Circuit.FactoryBackingAttack
