/-
# Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten — the ATTENUATED-DELEGATE effect `delegateAttenA`,
  CONNECTED to the runnable EffectVM `cap_root` column descriptor + the validated universe-A
  `delegateAttenA_full_sound`.

## ONE circuit — `delegateAttenA` is a `cap_root` COLUMN MOVE (the same runnable row as `attenuateA`)

`delegateAttenA` (`Inst/delegateAttenA.lean`) is a `caps`-touching v2 instance: it touches the `caps`
table as a WHOLE-FUNCTION injective digest, predicted post value
`grant caps recv (attenuate keep (heldCapTo caps del t))` (the recipient's slot GAINS an ATTENUATED copy
of the delegator's held `t`-conferring cap), freezes the other 16 kernel fields, GATED by
`DelegateAttenGuard`. Its validation `delegateAttenA_full_sound ⇒ DelegateAttenSpec` is DONE.

On the running EffectVM row layout it is EXACTLY the cap-graph row `attenuateA` emits — a `cap_root`
COLUMN MOVE to the post cap-table digest, every other state column frozen, the moved post-state bound
into `state_commit` under Poseidon2 CR. This module REUSES the validated `EffectVmEmitAttenuateA`
cap-root-move descriptor (ONE circuit) and adds the `delegateAttenA` CONNECTOR.

## The CONNECTOR — `capRootProj` to `delegateAttenA_full_sound`

`unify_delegateAtten`: when `DelegateAttenSpec` holds (so `k'.caps = grant caps recv (attenuate keep
(heldCapTo caps del t))`), the projected post-`cap_root` `D k'.caps` is EXACTLY `D` of that attenuated
grant — the column move the descriptor pins. So the runnable `cap_root` transition IS universe-A's
validated `caps`-digest transition; not a fourth spec.

## BOUNDARY (precise)

  * **cap-root recompute + non-amp: CLOSED (§G, §G.4), inherited.** `delegateAttenVmDescriptorGenuine`
    (§G) RECOMPUTES `cap_root = hash[edge_leaf, old_root]` in-row (edge op `capOp.DELEGATE_ATTEN`), so the
    post root is FORCED by the bound attenuated-delegate edge. `delegateAttenVmDescriptorGenuineNonAmp`
    (§G.4) ADDS the in-circuit `granted ⊑ held` submask over the SAME `rights` felt — and since
    `delegateAtten` is the ATTENUATE-then-delegate effect, non-amplification is its DEFINING property,
    now enforced in-circuit (`delegateAttenNonAmp_in_circuit`/`delegateAttenNonAmp_rejects_amplify`). The
    cap-table-as-FUNCTION digest `D` is retained ONLY for the v1 connector `capRootProj` to
    `delegateAttenA_full_sound`; the residual seam is Phase E (sorted-tree update vs digest advance).

  * **The attenuation premise (`DelegateAttenGuard`) is NOT a `cap_root` ROW gate.** It is enforced by
    `delegateAttenA_full_sound`'s `propBit (DelegateAttenGuard)` column, NOT by the cap-root-move row
    gates this module reuses. `unify_delegateAtten_via_full_sound` carries it through the hypothesis;
    the runnable row pins only the MOVE. Flagged, not papered.

  * **ATTENUATION (narrower-or-equal rights) is INSIDE the `caps` value, not a separate row gate.** The
    runnable `cap_root` move pins `post.caps = D⁻¹(cap_root)`; that the granted cap is the ATTENUATED
    `attenuate keep …` (rights ⊆ the held cap) is a property of universe-A's predicted `caps` VALUE
    (`grant … (attenuate keep …)`), enforced by `Function.Injective D` + `delegateAttenA_full_sound`,
    NOT by an in-circuit subset gate. So the runnable row binds the WHOLE post cap-table digest; the
    attenuation semantics ride the validated universe-A value, reported here, not re-proved in-row.

  * PER-CELL / PER-ROW; `state.RESERVED` not commitment-bound (inherited findings).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR`;
cap-table digest ONLY as `Function.Injective D`.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Inst.delegateAttenA

namespace Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptor gCapMove AttenRowIntent CapCellSpec capRootProj
   attenuateVm_faithful attenuateVm_rejects_wrong_capRoot attenuateDescriptor_full_sound
   CapRowEncodes)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap Auth Label)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.DelegateAttenA (DelegateAttenArgs delegateAttenE delegateAttenA_full_sound)
open Dregg2.Circuit.Spec.AuthorityAttenuation (DelegateAttenSpec)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The runnable descriptor IS the reused cap-root-move circuit. -/

/-- **`delegateAttenVmDescriptor`** — the runnable `delegateAttenA` circuit: definitionally the validated
cap-root-move descriptor. The effect-specific content is the post `cap_root` digest VALUE (§3). -/
def delegateAttenVmDescriptor : EffectVmDescriptor := attenuateVmDescriptor

/-- The runnable `delegateAttenA` row pins EXACTLY the cap-graph intent — the validated faithfulness. -/
theorem delegateAttenVm_faithful (env : VmRowEnv) :
    (∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates, c.holdsVm env false false)
      ↔ AttenRowIntent env :=
  attenuateVm_faithful env

/-- **Anti-ghost.** A `delegateAttenA` row whose post-`cap_root` ≠ the supplied digest (both cells
canonical, i.e. in `[0, p)` for the BabyBear prime `p = 2013265921`) fails the MOVE gate (UNSAT mod
`p`). -/
theorem delegateAttenVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hcanonNew : 0 ≤ env.loc (saCol state.CAP_ROOT)
      ∧ env.loc (saCol state.CAP_ROOT) < 2013265921)
    (hcanonDig : 0 ≤ env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW)
      ∧ env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW) < 2013265921)
    (hwrong : env.loc (saCol state.CAP_ROOT)
      ≠ env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false :=
  attenuateVm_rejects_wrong_capRoot env hcanonNew hcanonDig hwrong

/-! ## §2 — The structured per-cell soundness (reused). -/

/-- **`delegateAttenDescriptor_full_sound`** — satisfying the runnable row's gates under the cap-row
decoding forces the structured per-cell `CapCellSpec` — the validated `attenuateDescriptor_full_sound`. -/
theorem delegateAttenDescriptor_full_sound (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates,
        c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  attenuateDescriptor_full_sound env pre post capDigestNew henc hgates

/-! ## §3 — THE CONNECTOR — `capRootProj` to universe-A's `delegateAttenA_full_sound`. -/

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries for `delegateAttenA`:
`D` of the ATTENUATED grant `grant caps recv (attenuate keep (heldCapTo caps del t))`. -/
def delegateAttenCapDigestNew (D : Caps → ℤ) (s : RecChainedState) (args : DelegateAttenArgs) : ℤ :=
  D (grant s.kernel.caps args.recv (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t)))

/-- **`unify_delegateAtten` — THE CONNECTOR.** When `DelegateAttenSpec` holds, the projected post-`cap_root`
is EXACTLY the attenuated-grant cap-digest `delegateAttenCapDigestNew D s args` — the column move the
runnable descriptor pins. -/
theorem unify_delegateAtten (D : Caps → ℤ) (s : RecChainedState) (args : DelegateAttenArgs)
    (s' : RecChainedState)
    (hspec : DelegateAttenSpec s args.del args.recv args.t args.keep s') :
    capRootProj D s'.kernel = delegateAttenCapDigestNew D s args := by
  -- DelegateAttenSpec's `caps` clause: `s'.kernel.caps = grant caps recv (attenuate keep (heldCapTo …))`.
  obtain ⟨_hguard, hcaps, _⟩ := hspec
  show D s'.kernel.caps
      = D (grant s.kernel.caps args.recv (attenuate args.keep (heldCapTo s.kernel.caps args.del args.t)))
  rw [hcaps]

/-- **`unify_delegateAtten_via_full_sound` — inherits the VALIDATED guarantee.** Chaining
`delegateAttenA_full_sound` (the attenuation GUARD enforced by `propBit (DelegateAttenGuard)`, ⟹
`DelegateAttenSpec`) with `unify_delegateAtten`: a satisfying universe-A witness forces the projected
post-`cap_root` to the attenuated-grant cap-digest — the EXACT column the descriptor pins. -/
theorem unify_delegateAtten_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.DelegateAttenA.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : DelegateAttenArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (delegateAttenE D hD) (encodeE2 S (delegateAttenE D hD) s args s')) :
    capRootProj D s'.kernel = delegateAttenCapDigestNew D s args :=
  unify_delegateAtten D s args s' (delegateAttenA_full_sound S D hD hRest hLog s args s' h)

/-! ## §4 — NON-VACUITY (the reused row's witnesses fire). -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (capGoodRow capBadRow capGoodRow_realizes_intent capBadRow_rejected)

/-- **NON-VACUITY (witness TRUE).** The good cap-root row realizes the intent — the runnable
`delegateAttenA` descriptor's intent side is inhabited. -/
theorem delegateAttenGoodRow_realizes_intent : AttenRowIntent capGoodRow := capGoodRow_realizes_intent

/-- **NON-VACUITY (witness FALSE / anti-ghost).** The forged cap-root row is REJECTED — a concrete UNSAT. -/
theorem delegateAttenBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm capBadRow false false :=
  capBadRow_rejected


/-! ## §G — THE GENUINE CLASS-A `delegateAtten` — `cap_root` RECOMPUTED in-row (inherits the shared primitive).

`delegateAtten` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the GENUINE class-A descriptor
`attenuateVmDescriptorGenuine` (the opaque `param.CAP_DIGEST_NEW` move REPLACED by the FORCED in-row
recompute `new_cap_root = hash[edge_leaf, old_cap_root]`, `edge_leaf = hash[holder,target,rights,op]`). The
`delegateAtten`-specific content is the OP tag `capOp.DELEGATE_ATTEN` carried in the edge leaf (the attenuating Granovetter grant), plus the existing
connector to universe-A. We re-export the genuine soundness + edge-binding anti-ghost for `delegateAtten`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuine attenuateGenuineRowGates CapCellSpecGenuine attenuateHashSites
   attenuateGenuine_sound attenuateGenuine_binds_edge CapRowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitCapRoot (capRootHolds)

/-- **`delegateAttenVmDescriptorGenuine`** — the GENUINE `delegateAtten` circuit: definitionally the shared genuine
cap-root-recompute descriptor (the opaque digest param is GONE; `cap_root` is FORCED in-row). -/
def delegateAttenVmDescriptorGenuine : EffectVmDescriptor := attenuateVmDescriptorGenuine

/-- **`delegateAttenGenuine_sound` — THE CLASS-A THEOREM for `delegateAtten`.** Satisfying the genuine descriptor's
frame-freeze gates AND the in-row cap-root recompute forces the GENUINE full per-cell post-state:
`post.capRoot` is the FORCED advance `hash[edge_leaf, pre.capRoot]` (NOT an opaque parameter), every other
field frozen. Inherited from the shared `attenuateGenuine_sound`. -/
theorem delegateAttenGenuine_sound (hash : List ℤ → ℤ) (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (pre post : Dregg2.Circuit.Emit.EffectVmEmitTransferSound.CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ attenuateGenuineRowGates, c.holdsVm env false false)
    (hrec : capRootHolds hash env) :
    CapCellSpecGenuine hash env pre post :=
  attenuateGenuine_sound hash env pre post capDigestNew henc hgates hrec

/-- **`delegateAttenGenuine_binds_edge` — the genuine class-A anti-ghost for `delegateAtten`.** Two genuine `delegateAtten` rows
with EQUAL published `state_commit` share the old `cap_root` AND every bound edge field
(holder/target/rights/op) — so tampering the cap-edge mutation moves `cap_root`, moves `state_commit` ⇒
UNSAT. Inherited from the shared `attenuateGenuine_binds_edge`. -/
theorem delegateAttenGenuine_binds_edge (hash : List ℤ → ℤ)
    (hCR : Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR hash)
    (e₁ e₂ : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hsCommit₁ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₁ attenuateHashSites)
    (hsCommit₂ : Dregg2.Circuit.Emit.EffectVmEmit.siteHoldsAll hash e₂ attenuateHashSites)
    (hrec₁ : capRootHolds hash e₁) (hrec₂ : capRootHolds hash e₂)
    (hcommit : e₁.loc (saCol state.STATE_COMMIT) = e₂.loc (saCol state.STATE_COMMIT)) :
    e₁.loc (sbCol state.CAP_ROOT) = e₂.loc (sbCol state.CAP_ROOT)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.HOLDER)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.TARGET)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.RIGHTS)
    ∧ e₁.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP)
        = e₂.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitCapRoot.cp.OP) :=
  attenuateGenuine_binds_edge hash hCR e₁ e₂ hsCommit₁ hsCommit₂ hrec₁ hrec₂ hcommit

#assert_axioms delegateAttenGenuine_sound
#assert_axioms delegateAttenGenuine_binds_edge

/-! ### §G.4 — `delegateAtten` carries IN-CIRCUIT NON-AMPLIFICATION (`granted ⊑ held`, the ARGUS linchpin).

`delegateAtten` is the cap-graph effect that ATTENUATES-then-delegates, so non-amplification is its
defining property: the granted edge confers a SUBSET of the delegator's held cap. It inherits the shared
GENUINE-NON-AMP descriptor `attenuateVmDescriptorGenuineNonAmp` — the cap-root recompute binds the
granted `rights` into `cap_root`, and the per-bit submask gate forces `granted ⊑ held` on that same felt.
A `delegateAtten` proof now genuinely means the attenuated grant did NOT amplify — in-circuit. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorGenuineNonAmp attenuateGenuineNonAmp_in_circuit
   attenuateGenuineNonAmp_rejects_amplify)

/-- **`delegateAttenVmDescriptorGenuineNonAmp`** — the GENUINE `delegateAtten` circuit WITH in-circuit
non-amp: definitionally the shared genuine-non-amp descriptor (recompute + `granted ⊑ held`). -/
def delegateAttenVmDescriptorGenuineNonAmp : EffectVmDescriptor := attenuateVmDescriptorGenuineNonAmp

/-- **`delegateAttenNonAmp_in_circuit`** — a satisfying `delegateAtten` witness FORCES `granted ⊑ held`
per bit (both bit cells canonical, i.e. in `[0, p)` for the BabyBear prime `p = 2013265921`). Inherited
from the shared in-circuit non-amp tooth. -/
theorem delegateAttenNonAmp_in_circuit (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (hcon : ∀ c ∈ delegateAttenVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hgc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) < 2013265921)
    (hhc : 0 ≤ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i)
      ∧ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) < 2013265921) :
    env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 0
    ∨ env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 1 :=
  attenuateGenuineNonAmp_in_circuit env hcon i hi hgc hhc

/-- **`delegateAttenNonAmp_rejects_amplify`** — an amplifying `delegateAtten` (granted bit set, held bit
clear) does NOT satisfy the descriptor. Inherited from the shared rejection. -/
theorem delegateAttenNonAmp_rejects_amplify (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv)
    (i : Nat) (hi : i < Dregg2.Circuit.Emit.EffectVmEmitCapReshape.MASK_BITS)
    (hg : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.grantedBit i) = 1)
    (hh : env.loc (Dregg2.Circuit.Emit.EffectVmEmitCapReshape.dcol.heldBit i) = 0) :
    ¬ (∀ c ∈ delegateAttenVmDescriptorGenuineNonAmp.constraints, c.holdsVm env false false) :=
  attenuateGenuineNonAmp_rejects_amplify env i hi hg hh

#assert_axioms delegateAttenNonAmp_in_circuit
#assert_axioms delegateAttenNonAmp_rejects_amplify

/-! ## §W — THE MAGNESIUM LIFT: `delegateAtten`'s RUNNABLE descriptor binds the FULL 17-field post-state.

`delegateAtten` is the SAME runnable cap-graph row as `attenuateA`, so it inherits the SHARED cap-graph
WIDE descriptor `attenuateVmDescriptorWide` (`EffectVmEmitAttenuateA §W`): widened to
`EFFECT_VM_WIDTH_SYSROOTS` with `wideHashSites` so the published `state_commit` absorbs the `system_roots`
digest. `delegateAtten`'s kernel step (`recKDelegateAtten`) edits ONLY `caps`; the 8 side-table roots are
FROZEN, so the full clause is the per-cell `CapCellSpec` (cap_root = `delegateAttenCapDigestNew`) AND
`postRoots = preRoots`. -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptorWide CapFullClause cap_runnable_full_sound
   cap_runnable_binds_full_state_or_collides IsAttenRow CapRowEncodes)

/-- **`delegateAttenVmDescriptorWide`** — the runnable `delegateAtten` FULL-state circuit: definitionally
the shared cap-graph WIDE descriptor (`attenuateVmDescriptorWide`), 188-wide with `wideHashSites`. The
`delegateAtten`-specific content is the post `cap_root` digest `delegateAttenCapDigestNew D s args` (the
attenuated-grant digest), connected via `unify_delegateAtten`. -/
def delegateAttenVmDescriptorWide : EffectVmDescriptor := attenuateVmDescriptorWide

/-- **`delegateAtten_runnable_full_sound` — THE MAGNESIUM CROWN for `delegateAtten`.** A row satisfying the
runnable `delegateAtten` WIDE descriptor pins the FULL 17-field cap-graph post-state: the per-cell
`cap_root` MOVE to the attenuated-grant digest + frame freeze (binding `cell`/`caps`/`bal`-here + frame)
AND the frozen `system_roots` sub-block (binding the 8 side-table roots). The `cap_root` value is
universe-A's validated attenuated-grant digest via `unify_delegateAtten` (cited). -/
theorem delegateAtten_runnable_full_sound (D : Caps → ℤ) (s : RecChainedState)
    (args : DelegateAttenArgs) (preRoots : Dregg2.Exec.SystemRoots.SysRoots)
    (hash : List ℤ → ℤ) (env : VmRowEnv) (pre post : CellState)
    (postRoots : Dregg2.Exec.SystemRoots.SysRoots)
    (hrow : IsAttenRow env)
    (henc : CapRowEncodes env pre post (delegateAttenCapDigestNew D s args))
    (hroots : postRoots = preRoots)
    (hgatesat : satisfiedVm hash delegateAttenVmDescriptorWide env true false) :
    CapFullClause (delegateAttenCapDigestNew D s args) preRoots pre post postRoots :=
  cap_runnable_full_sound (delegateAttenCapDigestNew D s args) preRoots hash env pre post postRoots
    hrow henc hroots hgatesat

/-- **`delegateAtten_runnable_binds_full_state_or_collides` — the whole-17-field anti-ghost for
`delegateAtten`, UNCONDITIONALLY.** Two wide `delegateAtten` rows publishing the same `NEW_COMMIT` EITHER
agree on EVERY absorbed state-block column (the moved `cap_root` included) AND every side-table root, OR
exhibit a genuine collision of the deployed sponge — on the state block (`WideColl`) or on the ordered
root list (`RootsColl`). Inherited from `cap_runnable_binds_full_state_or_collides`.

The old form concluded the bare conjunction from `Poseidon2SpongeCR hash`, which the deployed BabyBear
sponge REFUTES, so at deployed parameters it was vacuous. This disjunction is formally weaker and holds
of the deployed sponge. -/
theorem delegateAtten_runnable_binds_full_state_or_collides (capDigestNew : ℤ)
    (preRoots : Dregg2.Exec.SystemRoots.SysRoots)
    (hash : List ℤ → ℤ)
    (e₁ e₂ : VmRowEnv) (sr₁ sr₂ : Dregg2.Exec.SystemRoots.SysRoots)
    (hsat₁ : satisfiedVm hash delegateAttenVmDescriptorWide e₁ true true)
    (hsat₂ : satisfiedVm hash delegateAttenVmDescriptorWide e₂ true true)
    (hpin₁ : e₁.loc (saCol state.STATE_COMMIT) = e₁.pub pi.NEW_COMMIT)
    (hpin₂ : e₂.loc (saCol state.STATE_COMMIT) = e₂.pub pi.NEW_COMMIT)
    (hpub : e₁.pub pi.NEW_COMMIT = e₂.pub pi.NEW_COMMIT)
    (hd₁ : e₁.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₁)
    (hd₂ : e₂.loc sysRootsDigestCol = Dregg2.Exec.SystemRoots.systemRootsDigest hash sr₂) :
    (Dregg2.Circuit.Emit.EffectVmFullStateRunnable.baseAbsorbedCols e₁
        = Dregg2.Circuit.Emit.EffectVmFullStateRunnable.baseAbsorbedCols e₂
      ∧ (∀ i : Fin Dregg2.Exec.SystemRoots.N_SYSTEM_ROOTS, sr₁ i = sr₂ i))
    ∨ Dregg2.Circuit.Emit.EffectVmFullStateRunnable.WideColl hash e₁ e₂
    ∨ Dregg2.Circuit.Emit.EffectVmFullStateRunnable.RootsColl hash sr₁ sr₂ :=
  cap_runnable_binds_full_state_or_collides capDigestNew preRoots hash
    e₁ e₂ sr₁ sr₂ hsat₁ hsat₂ hpin₁ hpin₂ hpub hd₁ hd₂

#assert_axioms delegateAtten_runnable_full_sound
#assert_axioms delegateAtten_runnable_binds_full_state_or_collides

/-! ## §5 — Axiom-hygiene tripwires. -/

#assert_axioms delegateAttenVm_faithful
#assert_axioms delegateAttenVm_rejects_wrong_capRoot
#assert_axioms delegateAttenDescriptor_full_sound
#assert_axioms unify_delegateAtten
#assert_axioms unify_delegateAtten_via_full_sound
#assert_axioms delegateAttenGoodRow_realizes_intent
#assert_axioms delegateAttenBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitDelegateAtten
