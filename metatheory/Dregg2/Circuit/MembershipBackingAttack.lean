/-
# Dregg2.Circuit.MembershipBackingAttack — ADVERSARIAL soundness audit of the deployed
  `SenderAuthorized { AuthorizedSet::PublicRoot }` turn's set-MEMBERSHIP backing (the analog of
  `CustomCarrierAttack` / `BridgeBackingAttack` / `SovereignBackingAttack` for the membership leg).

This module attacks the deployed `SenderAuthorized` turn head-on, IN LEAN, importing everything
read-only. It is a refutation file: the load-bearing arms are proved WITHOUT `sorry`, and the
conclusion is stated precisely.

## The target

A `StateConstraint::SenderAuthorized { AuthorizedSet::PublicRoot { .. } }` requires the firing
sender's public key to be a LEAF of the Poseidon2 Merkle tree whose root the cell publishes
(`AuthorizedSet::PublicRoot`). That set-membership relation —

  (a) the SENDER LEAF: `compress(sender_pk)` is a leaf of the tree
      (`turn::executor::membership_verifier.rs:143`, `let leaf = compress(&candidate)`);
  (b) the AUTHORIZED ROOT: the leaf's Merkle path reaches the cell's published authorized-set root
      (`membership_verifier.rs:144/158`, `verify_membership_dsl(&proof, leaf, root)`),

— is checked ENTIRELY OFF-AIR, by a re-executing validator running the `MerkleMembershipStarkVerifier`
(a STANDALONE `dregg_circuit::dsl::membership` STARK whose `[leaf, root]` public inputs the executor
pins). A PURE LIGHT CLIENT (one that only folds the per-turn recursion tree) never witnesses (a)/(b):

In the deployed effect-vm AIR there is NO set-membership leg. The column the effect-vm calls
"membership" is the UNRELATED `cap_root` (the capability-set commitment, `circuit/src/cap_root.rs`),
NOT this `SenderAuthorized` set. No effect-vm row publishes `(sender_leaf, authorized_root)` as PIs,
and no constraint links any column to a verifying Merkle path against the cell's authorized-set root.
So for a pure light client a `SenderAuthorized`-gated turn is admitted with NO witnessed membership:
its `AttestedHistory` is BYTE-IDENTICAL to the one a fail-closed-default validator (which never even
ran the off-AIR verifier) would produce. The membership is RE-EXEC-ONLY.

This is the SAME vacuity CLASS that `CustomCarrierAttack` proves for `Effect::Custom`,
`BridgeBackingAttack` for the inbound bridge mint, and `SovereignBackingAttack` for the sovereign
leg: REAL as re-executed, VACUOUS as deployed-light-client.

## What is proved here

§A `deployed_admits_unbacked_membership` — the explicit FORGED `SenderAuthorized` turn. A
   membership-relation engine whose only verifying Merkle path proves leaf `123` under root `5`, and
   an HONEST-looking leg row that SATISFIES the deployed transition intent (the teeth carry the
   prover's claimed values, the transition holds) while its published `sender_leaf` is `0` — a leaf
   NO verifying path proves under the authorized root (a sender NOT in the authorized set). The
   deployed AIR accepts it; the (staged) membership predicate rejects it.

§A′ `deployed_admits_injected_root` — the WRONG-SET forgery: the same shape, but the leg's
   `sender_leaf` matches a verifying path while its `authorized_root` is a value that path does NOT
   reach — the sender is a genuine leaf of a DIFFERENT (attacker) tree, presented against the
   authorized root. The deployed transition still holds; the light client cannot tell the sender's
   tree from the authorized one.

§B `deployed_intent_does_not_force_membership` — there is NO uniform "deployed-accepts ⟹ authorized
   member": §A is the counterexample. So a light client that only checks the deployed AIR learns
   NOTHING about set-membership. The repair (membership must come from the FOLD over a re-proved
   membership leaf) is named at §C, mirroring `CustomBindingFromFold` / `sovereign_leaf_adapter`.

## The repair (named, mirroring the custom / bridge / sovereign fold-wire)

Membership must come from the per-turn FOLD over a re-proved MEMBERSHIP leaf
(`circuit-prove::membership_leaf_adapter::prove_membership_leaf`) whose in-circuit-bound PIs carry the
membership tuple `(sender_leaf, authorized_root)`, connected to the deployed leg's teeth via
`circuit-prove::membership_leaf_adapter::prove_membership_binding_node_segmented` (the analog of
`prove_sovereign_binding_node_segmented`). The leaf binds the tuple in-circuit; the in-AIR Poseidon2
Merkle-path verification (that the path actually hashes `sender_leaf` → `authorized_root`) is the
named big-bang piece — the SAME `MerkleHash` chip-table (TID_P2) lookup the custom adapter names and
the cap-membership crown's `Hash3Cap` would need (the digest-of-attestation boundary every gadget
carrier rides; see `membership_leaf_adapter` module docs).

## Axiom hygiene
`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}. NO new axiom,
NO `sorry`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit

namespace Dregg2.Circuit.MembershipBackingAttack

open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — the set-membership engine + the (staged) membership predicate.

A `MembershipEngine` abstracts the off-AIR Poseidon2 Merkle-membership STARK the executor runs at
authorization (`membership_verifier.rs:158`, `verify_membership_dsl(&proof, leaf, root)`):
`verifyPath` is the membership STARK's accepting bit, and a VERIFYING path attests the `sender_leaf`
it proves (`compress(sender_pk)`) and the `authorized_root` it reaches. This is the membership analog
of `SovereignBackingAttack.SovAuthorityEngine` (`verifySig` + `signedKeyCommit`) and
`BridgeBackingAttack.NoteSpendEngine` (`verify` + `spendDigest`). -/

/-- An abstract set-membership engine: its accepting bit, and the `(sender_leaf, authorized_root)`
tuple a VERIFYING Merkle path attests. -/
structure MembershipEngine where
  /-- The proof type of the Poseidon2 Merkle-membership STARK. -/
  Witness : Type
  /-- The verifier's accepting bit (`verify_membership_dsl(...).is_ok()`). -/
  verifyPath : Witness → Bool
  /-- The sender leaf a verifying path proves (`compress(sender_pk)`, the membership STARK `pi[0]`). -/
  provenLeaf : Witness → ℤ
  /-- The authorized-set root a verifying path reaches (the membership STARK `pi[1]`). -/
  provenRoot : Witness → ℤ

/-! ### The membership leg's teeth columns.

These are the columns the staged membership predicate WOULD read: a published sender leaf and a
published authorized-set root. In the deployed AIR there is NO such leg — the effect-vm "membership"
column is the unrelated `cap_root` — so these are modeled as teeth that exist but are read by NO
constraint (dead / ungated). That is exactly the hole. The `anchor`/`new` columns stand for the
rotated transition the deployed proof DOES gate. -/

/-- The published `sender_leaf` column (an aux teeth slot; stands for `compress(sender_pk)`). -/
def senderLeafCol : Nat := 23
/-- The published `authorized_root` column (an aux teeth slot; stands for the cell's PublicRoot). -/
def authRootCol : Nat := 27
/-- The pre-state `anchor` column (the rotated `old_commit` felt; offset 0 stands for it here). -/
def anchorCol : Nat := 0
/-- The post-state `new_commit` column (offset 8 stands for it here). -/
def newCol : Nat := 8

/-- The sender leaf a leg row publishes. -/
def senderLeafOf (env : VmRowEnv) : ℤ := env.loc senderLeafCol
/-- The authorized root a leg row publishes. -/
def authRootOf (env : VmRowEnv) : ℤ := env.loc authRootCol
/-- The pre-state anchor a leg row publishes. -/
def anchorOf (env : VmRowEnv) : ℤ := env.loc anchorCol
/-- The post-state commitment a leg row publishes. -/
def newOf (env : VmRowEnv) : ℤ := env.loc newCol

/-- **`Authorized E env`** — the STAGED membership predicate the deployed descriptor SHOULD (but does
not) enforce: the leg's published `(sender_leaf, authorized_root)` is attested by SOME verifying
Merkle path. This is the membership analog of `SovereignBackingAttack.Authorized` and
`BridgeBackingAttack.BackedAt` — the content the deployed AIR omits (legs (a) sender-leaf + (b)
authorized-root, both OFF-AIR in `membership_verifier.rs`). -/
def Authorized (E : MembershipEngine) (env : VmRowEnv) : Prop :=
  ∃ w : E.Witness, E.verifyPath w = true
    ∧ E.provenLeaf w = senderLeafOf env
    ∧ E.provenRoot w = authRootOf env

/-! ### The deployed leg's row intent.

`DeployedMembershipIntent env` is the content the deployed ROTATED effect-vm proof gates: the
transition `new_commit = anchor + 7` (a concrete stand-in for "the rotated proof proves SOME genuine
`old→new` through the effects") together with the teeth carrying the prover's CLAIMED values. The
membership legs (a)/(b) are NOT among the gated content — that is the point. A forged row satisfies
this while no verifying path attests its teeth. -/
def DeployedMembershipIntent (env : VmRowEnv) : Prop :=
  newOf env = anchorOf env + 7

/-! ## §A — the forged `SenderAuthorized` turn: deployed-accepts what membership rejects.

A demo membership engine whose ONLY verifying path proves `(sender_leaf, authorized_root) = (123, 5)`
(the same one-verifying-proof shape `SovereignBackingAttack.demoSov` uses). The forged leg row carries
`sender_leaf = 0`, `authorized_root = 5`, `anchor = 0`, `new = 7` — its transition holds (`7 = 0 + 7`)
so the deployed AIR accepts, but its `sender_leaf 0` is proved by NO verifying path (a NOT-IN-THE-SET
forgery). -/

/-- A demo membership engine: the only verifying path (`true`) proves sender leaf `123` under
authorized root `5`. -/
def demoMembership : MembershipEngine where
  Witness := Bool
  verifyPath := fun b => b
  provenLeaf := fun _ => 123
  provenRoot := fun _ => 5

/-- The forged leg row: `sender_leaf = 0` (col 23), `authorized_root = 5` (col 27), `anchor = 0`
(col 0), `new = 7` (col 8). Its transition holds, but `sender_leaf 0` is proved by no verifying path
of `demoMembership`. -/
def forgedEnv : VmRowEnv where
  loc := fun i => if i = newCol then 7 else if i = authRootCol then 5 else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- **The deployed descriptor ACCEPTS the forged row.** Its transition holds: `new (7) = anchor (0)
+ 7`. The deployed rotated proof gates exactly this; the membership teeth are dead / ungated. -/
theorem forged_deployed_accepts : DeployedMembershipIntent forgedEnv := by
  simp only [DeployedMembershipIntent, newOf, anchorOf, forgedEnv, newCol, anchorCol, authRootCol]
  decide

/-- The forged row's published `sender_leaf` is `0` — a leaf NO verifying path of `demoMembership`
proves (the only verifying path proves `123`). -/
theorem senderLeaf_forgedEnv : senderLeafOf forgedEnv = 0 := by
  simp only [senderLeafOf, forgedEnv, senderLeafCol, newCol, authRootCol]
  decide

/-- **The forged row is REJECTED by the (staged) membership predicate.** Its `sender_leaf` is `0`;
the only verifying path of `demoMembership` proves `123`, so no verifying path attests it —
`Authorized` fails. The deployed descriptor cannot detect this: it never reads `sender_leaf`. -/
theorem forged_not_authorized : ¬ Authorized demoMembership forgedEnv := by
  rintro ⟨w, _hv, hleaf, _hroot⟩
  -- demoMembership.provenLeaf w ≡ 123 (defeq); senderLeafOf forgedEnv = 0; 123 = 0 is false.
  rw [senderLeaf_forgedEnv] at hleaf
  simp only [demoMembership] at hleaf
  exact absurd hleaf (by decide)

/-- **§A keystone — `deployed_admits_unbacked_membership`.** ∃ a membership engine and a leg row that
SATISFIES the deployed transition intent yet whose published `sender_leaf` is proved by NO verifying
Merkle path: the deployed AIR admits a `SenderAuthorized` turn whose sender is NOT a member of the
authorized set. This is the explicit forged turn the deployed circuit (and thus a pure light client)
cannot detect — the analog of `SovereignBackingAttack.deployed_admits_unbacked_sovereign` and
`BridgeBackingAttack.deployed_admits_unbacked_bridge`. -/
theorem deployed_admits_unbacked_membership :
    ∃ (E : MembershipEngine) (env : VmRowEnv),
      DeployedMembershipIntent env ∧ ¬ Authorized E env :=
  ⟨demoMembership, forgedEnv, forged_deployed_accepts, forged_not_authorized⟩

/-! ## §A′ — the wrong-set / injected-root forgery.

The same shape, but the leg's `sender_leaf` MATCHES a verifying path while its `authorized_root` is a
value that path does NOT reach: an INJECTED set. The sender is a genuine leaf of a DIFFERENT tree
(`provenRoot = 5`), but the leg publishes authorized root `9` — `membership_verifier.rs:144`'s root
binding is off-AIR, so the light client cannot tell the attacker's tree from the authorized one. -/

/-- A leg row whose `sender_leaf = 123` (a verifying path proves this leaf) but whose
`authorized_root = 9` (col 27) — a root the only verifying path of `demoMembership` (root `5`) does
NOT reach. `new = 7` so the transition `7 = 0 + 7` still holds. -/
def injectedRootEnv : VmRowEnv where
  loc := fun i =>
    if i = senderLeafCol then 123
    else if i = authRootCol then 9
    else if i = newCol then 7
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

/-- The injected-root row satisfies the deployed transition intent (`7 = 0 + 7`). -/
theorem injectedRoot_deployed_accepts : DeployedMembershipIntent injectedRootEnv := by
  simp only [DeployedMembershipIntent, newOf, anchorOf, injectedRootEnv, newCol, anchorCol,
    senderLeafCol, authRootCol]
  decide

/-- **`deployed_admits_injected_root`.** The injected-root row satisfies the deployed transition
intent, but no verifying path of `demoMembership` (which reaches root `5`) reaches its
`authorized_root = 9`, so `Authorized` rejects: the deployed AIR does not witness the authorized-root
binding (leg (b)). -/
theorem deployed_admits_injected_root :
    DeployedMembershipIntent injectedRootEnv ∧ ¬ Authorized demoMembership injectedRootEnv := by
  refine ⟨injectedRoot_deployed_accepts, ?_⟩
  rintro ⟨w, _hv, _hleaf, hroot⟩
  -- demoMembership.provenRoot w ≡ 5 (defeq); authRootOf injectedRootEnv = 9; 5 = 9 is false.
  have hroot9 : authRootOf injectedRootEnv = 9 := by
    simp only [authRootOf, injectedRootEnv, authRootCol, senderLeafCol, newCol]; decide
  rw [hroot9] at hroot
  simp only [demoMembership] at hroot
  exact absurd hroot (by decide)

/-! ## §B — the deployed AIR does not force set-membership. -/

/-- **§B keystone — `deployed_intent_does_not_force_membership`.** There is NO uniform implication
"the deployed leg intent holds ⟹ the sender is an authorized member": §A exhibits a row whose deployed
intent holds while no verifying path attests its `sender_leaf`. So consuming a membership claim against
the deployed AIR asserts strictly MORE than the verifier enforces — the deployed descriptor binds only
the transition, never the sender leaf / authorized root. The real membership must come from the
per-turn FOLD over the re-proved membership leaf
(`membership_leaf_adapter::prove_membership_leaf` connected via
`prove_membership_binding_node_segmented` to the published teeth PIs), exactly as
`CustomBindingFromFold` rebuilds the custom binding from `AggAirSound` — see §C. -/
theorem deployed_intent_does_not_force_membership :
    ¬ ∀ (E : MembershipEngine) (env : VmRowEnv),
        DeployedMembershipIntent env → Authorized E env := by
  intro hforce
  exact forged_not_authorized (hforce demoMembership forgedEnv forged_deployed_accepts)

/-! ## §C — the repair pointer.

The deployed descriptor witnesses NEITHER the sender leaf (§A) NOR the authorized root (§A′). The real
membership must come from the per-turn FOLD over a re-proved MEMBERSHIP leaf
(`circuit-prove::membership_leaf_adapter::prove_membership_leaf`, whose in-circuit-bound PIs carry the
tuple `(sender_leaf, authorized_root)`) connected to the deployed leg's published teeth via
`prove_membership_binding_node_segmented` (the analog of `prove_sovereign_binding_node_segmented`). The
leaf binds the tuple in-circuit; the in-AIR Poseidon2 Merkle-path verification (the `MerkleHash`
relation `circuit/src/dsl/membership.rs:C2` arithmetizes) that the path actually hashes `sender_leaf`
→ `authorized_root` stays the named big-bang piece — the same chip-table (TID_P2) lookup the custom
adapter names and the cap-membership crown's `Hash3Cap` would need (the digest-of-attestation
boundary). -/

/-! ## §D — Axiom audit — every load-bearing arm. -/

#assert_axioms forged_deployed_accepts
#assert_axioms senderLeaf_forgedEnv
#assert_axioms forged_not_authorized
#assert_axioms deployed_admits_unbacked_membership
#assert_axioms injectedRoot_deployed_accepts
#assert_axioms deployed_admits_injected_root
#assert_axioms deployed_intent_does_not_force_membership

end Dregg2.Circuit.MembershipBackingAttack
