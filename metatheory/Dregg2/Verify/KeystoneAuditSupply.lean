/-
# Dregg2.Verify.KeystoneAuditSupply — the SUPPLY (mint/burn issuer-move) family keystone-audit.

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the 5
supply-creation keystones pinned in `AssuranceCase` (Wave 1 of `docs/KEYSTONE-LEDGER.md`):

  • `Circuit.Spec.SupplyCreation.mintA_authorized` — a committed mint witnesses the ISSUER cap (E2);
  • `Circuit.Spec.SupplyCreation.execMintA_iff_spec` — executor ⟺ the INDEPENDENT `MintASpec`;
  • `Exec.TurnExecutorFull.recKMintAsset_delta` / `recKBurnAsset_delta` — the issuer-move CONSERVES
    every asset's supply (issuer-debit and recipient-credit cancel in the sum);
  • `Exec.TurnExecutorFull.recKMintAsset_requires_live_issuer` — genesis-order fail-closed gate.

Each is a THEOREM, so the keystone-audit's two checks bite:

  [1] NON-VACUITY — each carries a `*_satisfiable` companion firing its conclusion on the concrete
      genesis fixture `kS0` (cells {0,1} live, actor 9 holds `node 0`, a privileged mint of 50 of
      asset 0 COMMITS): the gate fires (`mintAuthorizedB ... = true`), the executor⟺spec yields a real
      `MintASpec`, the per-asset delta computes `recTotalAsset k' b = recTotalAsset k b` on the committed
      post-state, and the dead-issuer mint refuses.
  [2] TEETH — each carries a `*_teeth` companion REFUTING the dual: an UNPRIVILEGED mint is rejected
      (`mintA_rejects_unauthorized`), and the LEGACY supply-increment / -decrement mint provably BREAKS
      exact conservation (`recKMintAsset_breaks_exact` / `recKBurnAsset_breaks_exact`) — the issuer-move
      reshape is a repair, not a relabeling, so the conservation keystones are not `:= True`.

`#keystone_audit` THROWS on any FAIL, so this module is a CI gate over the supply family.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Circuit.Spec.supplycreation
import Dregg2.Exec.IssuerMove

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditSupply

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Authority (Cap)

/-! ## §1 — the concrete genesis fixture + the committed mint/burn.

`kS0`: cells {0, 1} live, an empty ledger (genesis), actor 9 holds the `node 0` ISSUER cap over
asset 0 (cell 0 IS the issuer of asset 0). Lifecycle defaults Live (= 0). A privileged mint of 50 of
asset 0 INTO cell 1 commits — the issuer well goes negative-capable, the recipient credits, `Σ` = 0. -/

def kS0 : RecordKernelState :=
  { accounts := {0, 1}
    cell := fun _ => .record [("balance", .int 0)]
    caps := fun a => if a = 9 then [Cap.node 0] else [] }

/-- The committed mint post-kernel (a privileged mint of 50 of asset 0 into cell 1). -/
def kS1 : RecordKernelState := { kS0 with bal := recTransferBal kS0.bal 0 1 0 50 }

theorem recKMintAsset_kS0_commits : recKMintAsset kS0 9 1 0 50 = some kS1 := by
  unfold recKMintAsset kS1
  rw [if_pos]
  exact ⟨by decide, by decide, by simp [kS0], by simp [kS0], by decide,
    by simp [kS0, cellLifecycleLive]⟩

/-- A burn that commits: holder cell 1 self-redeems 0 of asset 0 back to the issuer well (cell 0).
`amt = 0` keeps `amt ≤ bal cell a` true on the empty ledger; the conclusion is the supply delta. -/
def kB1 : RecordKernelState := { kS0 with bal := recTransferBal kS0.bal 1 0 0 0 }

theorem recKBurnAsset_kS0_commits : recKBurnAsset kS0 1 1 0 0 = some kB1 := by
  unfold recKBurnAsset kB1
  rw [if_pos]
  exact ⟨Or.inl rfl, by decide, by simp [kS0], by simp [kS0], by simp [kS0], by decide,
    by simp [kS0, cellLifecycleLive]⟩

/-! ## §2 — the satisfiability witnesses (the conclusion EXERCISED on `kS0`). -/

/-- **`mintA_authorized_satisfiable`.** The privileged mint of 50 of asset 0 commits from `stM0`, and
the keystone yields `mintAuthorizedB stM0.kernel.caps 9 0 = true` — the issuer cap E2 binding fires. -/
theorem mintA_authorized_satisfiable
    (st' : RecChainedState)
    (h : execFullA Dregg2.Circuit.Spec.SupplyCreation.stM0 (.mintA 9 1 0 50) = some st') :
    mintAuthorizedB Dregg2.Circuit.Spec.SupplyCreation.stM0.kernel.caps 9 0 = true :=
  Dregg2.Circuit.Spec.SupplyCreation.mintA_authorized
    Dregg2.Circuit.Spec.SupplyCreation.stM0 9 1 0 50 st' h

/-- **`execMintA_iff_spec_satisfiable`.** The executor⟺spec biconditional FIRES forward on the
concrete committed mint: from `execFullA stM0 (.mintA 9 1 0 50) = some st'` it yields a genuine
`MintASpec` (a real post-state, frame and all) — not a vacuous iff. -/
theorem execMintA_iff_spec_satisfiable
    (st' : RecChainedState)
    (h : execFullA Dregg2.Circuit.Spec.SupplyCreation.stM0 (.mintA 9 1 0 50) = some st') :
    Dregg2.Circuit.Spec.SupplyCreation.MintASpec Dregg2.Circuit.Spec.SupplyCreation.stM0 9 1 0 50 st' :=
  (Dregg2.Circuit.Spec.SupplyCreation.execMintA_iff_spec
    Dregg2.Circuit.Spec.SupplyCreation.stM0 9 1 0 50 st').mp h

/-- **`recKMintAsset_delta_satisfiable`.** The committed mint `recKMintAsset kS0 9 1 0 50 = some kS1`
exists, and the keystone fires there: `recTotalAsset kS1 0 = recTotalAsset kS0 0` — the issuer-move
conserves asset 0's supply on a REAL committed mint. -/
theorem recKMintAsset_delta_satisfiable :
    recTotalAsset kS1 0 = recTotalAsset kS0 0 :=
  recKMintAsset_delta kS0 kS1 9 1 0 50 recKMintAsset_kS0_commits 0

/-- **`recKBurnAsset_delta_satisfiable`.** Symmetric: a committed self-redeem burn conserves. -/
theorem recKBurnAsset_delta_satisfiable :
    recTotalAsset kB1 0 = recTotalAsset kS0 0 :=
  recKBurnAsset_delta kS0 kB1 1 1 0 0 recKBurnAsset_kS0_commits 0

/-- **`recKMintAsset_requires_live_issuer_satisfiable`.** Asset 7's issuer cell (7) is NOT in
`kS0.accounts`, so the genesis-order gate fires: the mint of asset 7 REFUSES (`= none`). The hypothesis
`7 ∉ accounts` is satisfiable (it decidably holds) and the conclusion is exercised. -/
theorem recKMintAsset_requires_live_issuer_satisfiable :
    recKMintAsset kS0 9 1 7 50 = none :=
  recKMintAsset_requires_live_issuer kS0 9 1 7 50 (by simp [kS0])

/-! ## §3 — TAG the 5 supply keystones with their companions (re-pinning aliases, type inferred).

The TEETH are the EXISTING refutations the ledger names:
  • `mintA_rejects_unauthorized` — an UNPRIVILEGED mint is rejected (the gate keystones discriminate);
  • `recKMintAsset_breaks_exact` / `recKBurnAsset_breaks_exact` — the LEGACY supply increment (and the
    decrement) operation provably BREAKS `ExactConservation` (the conservation keystones are not `True`). -/

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditSupply.mintA_authorized_satisfiable
    teeth := Dregg2.Circuit.Spec.SupplyCreation.mintA_rejects_unauthorized]
def mintA_authorized_KS := @Dregg2.Circuit.Spec.SupplyCreation.mintA_authorized

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditSupply.execMintA_iff_spec_satisfiable
    teeth := Dregg2.Circuit.Spec.SupplyCreation.mintA_rejects_unauthorized]
def execMintA_iff_spec_KS := @Dregg2.Circuit.Spec.SupplyCreation.execMintA_iff_spec

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditSupply.recKMintAsset_delta_satisfiable
    teeth := Dregg2.Exec.IssuerMove.recKMintAsset_breaks_exact]
def recKMintAsset_delta_KS := @Dregg2.Exec.TurnExecutorFull.recKMintAsset_delta

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditSupply.recKBurnAsset_delta_satisfiable
    teeth := Dregg2.Exec.IssuerMove.recKBurnAsset_breaks_exact]
def recKBurnAsset_delta_KS := @Dregg2.Exec.TurnExecutorFull.recKBurnAsset_delta

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditSupply.recKMintAsset_requires_live_issuer_satisfiable
    teeth := Dregg2.Circuit.Spec.SupplyCreation.mintA_rejects_unauthorized]
def recKMintAsset_requires_live_issuer_KS :=
  @Dregg2.Exec.TurnExecutorFull.recKMintAsset_requires_live_issuer

/-! ## §4 — RUN the audit (the CI gate over the supply family). -/

#keystone_audit Dregg2.Verify.KeystoneAuditSupply.mintA_authorized_KS
#keystone_audit Dregg2.Verify.KeystoneAuditSupply.execMintA_iff_spec_KS
#keystone_audit Dregg2.Verify.KeystoneAuditSupply.recKMintAsset_delta_KS
#keystone_audit Dregg2.Verify.KeystoneAuditSupply.recKBurnAsset_delta_KS
#keystone_audit Dregg2.Verify.KeystoneAuditSupply.recKMintAsset_requires_live_issuer_KS

#keystone_audit_tagged

/-! ## §5 — axiom-hygiene over the witnesses + re-pinned aliases (kernel-triple clean). -/

#assert_axioms recKMintAsset_kS0_commits
#assert_axioms recKBurnAsset_kS0_commits
#assert_axioms mintA_authorized_satisfiable
#assert_axioms execMintA_iff_spec_satisfiable
#assert_axioms recKMintAsset_delta_satisfiable
#assert_axioms recKBurnAsset_delta_satisfiable
#assert_axioms recKMintAsset_requires_live_issuer_satisfiable
#assert_axioms mintA_authorized_KS
#assert_axioms execMintA_iff_spec_KS
#assert_axioms recKMintAsset_delta_KS
#assert_axioms recKBurnAsset_delta_KS
#assert_axioms recKMintAsset_requires_live_issuer_KS

end Dregg2.Verify.KeystoneAuditSupply
