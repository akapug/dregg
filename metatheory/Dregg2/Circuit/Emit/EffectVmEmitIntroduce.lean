/-
# Dregg2.Circuit.Emit.EffectVmEmitIntroduce — the AUTHORITY-INTRODUCE effect `introduceA`,
  CONNECTED to the runnable EffectVM `cap_root` column descriptor + the validated universe-A
  `introduceA_full_sound`.

## ONE circuit — `introduceA` is a `cap_root` COLUMN MOVE (the same runnable row as `attenuateA`)

`introduceA` (`Inst/introduceA.lean`) is a `caps`-touching v2 instance: it touches the `caps` table as a
WHOLE-FUNCTION injective digest, predicted post value `recDelegateCaps caps intro recip t` (the
introducer GRANTS its held `t`-conferring cap to the recipient — definitionally the `delegate` grant;
`introduceA` is the introduce-arm of the same authority-unattenuated family, `execFullA_introduceA_eq`),
freezes the other 16 kernel fields, GATED by `delegateGuard` (the introducer holds a `t`-conferring cap).
Its validation `introduceA_full_sound ⇒ DelegateSpec s intro recip t s'` is DONE.

On the running EffectVM row layout it is EXACTLY the cap-graph row `attenuateA` emits — a `cap_root`
COLUMN MOVE to the post cap-table digest, every other state column frozen, the moved post-state bound
into `state_commit` under Poseidon2 CR. This module REUSES the validated `EffectVmEmitAttenuateA`
cap-root-move descriptor (ONE circuit) and adds the `introduceA` CONNECTOR.

## The CONNECTOR — `capRootProj` to `introduceA_full_sound`

`unify_introduce`: when `DelegateSpec` holds for the introduce args (so
`k'.caps = recDelegateCaps k.caps intro recip t`), the projected post-`cap_root` `D k'.caps` is EXACTLY
`D (recDelegateCaps k.caps intro recip t)` — the column move the descriptor pins. So the runnable
`cap_root` transition IS universe-A's validated `caps`-digest transition; not a fourth spec.

## HONEST BOUNDARY (precise)

  * **IR GAP — needs IR extension: cap-root hash-site** (inherited). The `cap_root` column is the SCALAR
    digest of the cap-table FUNCTION; the IR cannot re-derive it IN-circuit from the cap-table rows. The
    cap-table-is-genuinely-Merkled binding lives in `Function.Injective D` (carried, realizable), the
    SAME bar `introduceA_full_sound` uses. We connect through `capRootProj`.

  * **The Granovetter GUARD (`delegateGuard`) is NOT a `cap_root` ROW gate.** It is enforced by
    `introduceA_full_sound`'s `propBit (delegateGuard)` column, NOT by the cap-root-move row gates this
    module reuses. `unify_introduce_via_full_sound` carries it through the hypothesis; the runnable row
    pins only the MOVE. Flagged, not papered.

  * PER-CELL / PER-ROW; `state.RESERVED` not commitment-bound (inherited findings).

## Honesty

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Poseidon2 CR ONLY as `Poseidon2SpongeCR`;
cap-table digest ONLY as `Function.Injective D`. No `sorry`/`:= True`/`native_decide`/rfl-bridge.
Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
import Dregg2.Circuit.Inst.introduceA

namespace Dregg2.Circuit.Emit.EffectVmEmitIntroduce

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState)
open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA
  (attenuateVmDescriptor gCapMove AttenRowIntent CapCellSpec capRootProj
   attenuateVm_faithful attenuateVm_rejects_wrong_capRoot attenuateDescriptor_full_sound
   CapRowEncodes)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Caps Cap)
open Dregg2.Circuit.EffectCommit2 (Surface2 satisfiedE2 encodeE2)
open Dregg2.Circuit.StateCommit (logHashInjective)
open Dregg2.Circuit.Inst.IntroduceA (IntroduceArgs introduceE introduceA_full_sound)
open Dregg2.Circuit.Spec.AuthorityUnattenuated (DelegateSpec recDelegateCaps)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §1 — The runnable descriptor IS the reused cap-root-move circuit. -/

/-- **`introduceVmDescriptor`** — the runnable `introduceA` circuit: definitionally the validated
cap-root-move descriptor. The effect-specific content is the post `cap_root` digest VALUE (§3). -/
def introduceVmDescriptor : EffectVmDescriptor := attenuateVmDescriptor

/-- The runnable `introduceA` row pins EXACTLY the cap-graph intent — the validated faithfulness. -/
theorem introduceVm_faithful (env : VmRowEnv) :
    (∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates, c.holdsVm env false false)
      ↔ AttenRowIntent env :=
  attenuateVm_faithful env

/-- **Anti-ghost.** An `introduceA` row whose post-`cap_root` ≠ the supplied digest fails the MOVE gate
(UNSAT). -/
theorem introduceVm_rejects_wrong_capRoot (env : VmRowEnv)
    (hwrong : env.loc (saCol state.CAP_ROOT)
      ≠ env.loc (prmCol Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.paramA.CAP_DIGEST_NEW)) :
    ¬ (VmConstraint.gate gCapMove).holdsVm env false false :=
  attenuateVm_rejects_wrong_capRoot env hwrong

/-! ## §2 — The structured per-cell soundness (reused). -/

/-- **`introduceDescriptor_full_sound`** — satisfying the runnable row's gates under the cap-row decoding
forces the structured per-cell `CapCellSpec` — the validated `attenuateDescriptor_full_sound`. -/
theorem introduceDescriptor_full_sound (env : VmRowEnv) (pre post : CellState) (capDigestNew : ℤ)
    (henc : CapRowEncodes env pre post capDigestNew)
    (hgates : ∀ c ∈ Dregg2.Circuit.Emit.EffectVmEmitAttenuateA.attenuateRowGates,
        c.holdsVm env false false) :
    CapCellSpec pre post capDigestNew :=
  attenuateDescriptor_full_sound env pre post capDigestNew henc hgates

/-! ## §3 — THE CONNECTOR — `capRootProj` to universe-A's `introduceA_full_sound`. -/

/-- The predicted post cap-digest the descriptor's `param.CAP_DIGEST_NEW` carries for `introduceA`: `D`
of the post cap-table `recDelegateCaps caps intro recip t` (the introducer's grant of its held cap). -/
def introduceCapDigestNew (D : Caps → ℤ) (s : RecChainedState) (args : IntroduceArgs) : ℤ :=
  D (recDelegateCaps s.kernel.caps args.intro args.recip args.t)

/-- **`unify_introduce` — THE CONNECTOR.** When `DelegateSpec` holds for the introduce args, the projected
post-`cap_root` is EXACTLY the introduce cap-digest `introduceCapDigestNew D s args` — the column move the
runnable descriptor pins. -/
theorem unify_introduce (D : Caps → ℤ) (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (hspec : DelegateSpec s args.intro args.recip args.t s') :
    capRootProj D s'.kernel = introduceCapDigestNew D s args := by
  -- DelegateSpec's `caps` clause: `s'.kernel.caps = recDelegateCaps s.kernel.caps intro recip t`.
  obtain ⟨_hguard, hcaps, _⟩ := hspec
  show D s'.kernel.caps = D (recDelegateCaps s.kernel.caps args.intro args.recip args.t)
  rw [hcaps]

/-- **`unify_introduce_via_full_sound` — inherits the VALIDATED guarantee.** Chaining
`introduceA_full_sound` (the Granovetter GUARD enforced by `propBit (delegateGuard)`, ⟹ `DelegateSpec`)
with `unify_introduce`: a satisfying universe-A witness forces the projected post-`cap_root` to the
introduce cap-digest — the EXACT column the runnable descriptor's `param.CAP_DIGEST_NEW` carries. -/
theorem unify_introduce_via_full_sound
    (S : Surface2) (D : Caps → ℤ) (hD : Function.Injective D)
    (hRest : Dregg2.Circuit.Inst.IntroduceA.RestIffNoCaps S.RH)
    (hLog : logHashInjective S.LH)
    (s : RecChainedState) (args : IntroduceArgs) (s' : RecChainedState)
    (h : satisfiedE2 S (introduceE D hD) (encodeE2 S (introduceE D hD) s args s')) :
    capRootProj D s'.kernel = introduceCapDigestNew D s args :=
  unify_introduce D s args s' (introduceA_full_sound S D hD hRest hLog s args s' h)

/-! ## §4 — NON-VACUITY (the reused row's witnesses fire). -/

open Dregg2.Circuit.Emit.EffectVmEmitAttenuateA (capGoodRow capBadRow capGoodRow_realizes_intent capBadRow_rejected)

/-- **NON-VACUITY (witness TRUE).** The good cap-root row realizes the intent — the runnable `introduceA`
descriptor's intent side is inhabited. -/
theorem introduceGoodRow_realizes_intent : AttenRowIntent capGoodRow := capGoodRow_realizes_intent

/-- **NON-VACUITY (witness FALSE / anti-ghost).** The forged cap-root row is REJECTED — a concrete UNSAT. -/
theorem introduceBadRow_rejected : ¬ (VmConstraint.gate gCapMove).holdsVm capBadRow false false :=
  capBadRow_rejected

/-! ## §5 — Axiom-hygiene tripwires. -/

#assert_axioms introduceVm_faithful
#assert_axioms introduceVm_rejects_wrong_capRoot
#assert_axioms introduceDescriptor_full_sound
#assert_axioms unify_introduce
#assert_axioms unify_introduce_via_full_sound
#assert_axioms introduceGoodRow_realizes_intent
#assert_axioms introduceBadRow_rejected

end Dregg2.Circuit.Emit.EffectVmEmitIntroduce
