/-
# Dregg2.Verify.KeystoneAuditIntegrity — the INTEGRITY family keystone-audit (guarantee C).

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the integrity /
commitment-binding keystones pinned in `AssuranceCase`'s integrity guarantee:

  • the Argus RECEIPT weld (`Circuit.Argus.Receipt.{transfer_commits_to_one_receipt,
    argus_commits_to_one_receipt, transfer_receipt_is_executor_receipt}`) — the published receipt is the
    canonical commitment of the verified-executor-produced cell;
  • the COMMITMENT CROSS-BIND crown (`Circuit.CommitmentCrossBind.{stateCommit_binds_cellCommit,
    setFieldCommit_binds_cellCommit}`) — equal published roots force equal `cellCommit` on every live cell;
  • the UNIVERSAL BRIDGE verbs (`Exec.UniversalBridge.{gwrite,move,create}_is_memory_program`) — a
    committed verb IS exactly its emitted memory program.

Each is a THEOREM, so the keystone-audit's two checks bite:

  [1] NON-VACUITY — each carries a `*_satisfiable` companion exercising its conclusion on a concrete
      instance: the receipt of `writeCell0 v` IS the `cellCommit` of `v` (`writeCell0_receipt_eq`, pure
      `rfl`); the canonical leaf `chC` SATISFIES the crown portal (`chC_is_cellCommit`, `rfl`); each verb
      FIRES on its concrete committed run (`*_is_memory_program_satisfiable`, the full `uproj` fold
      equality on `s1`/`s2`/`s3`).
  [2] TEETH — each carries a `*_teeth` companion refuting the predicate on a hostile instance: the
      receipt is NON-CONSTANT on distinct-tail outputs (`writeCell0_receipt_observable`); a value-DROPPING
      leaf REFUTES the crown portal (`chC_bad_not_bridge` — not `:= True`); the emitted program really
      MOVES state (`bridge_program_teeth`, `none → some 7`).

`#keystone_audit` THROWS on any FAIL, so this module is a CI gate over the integrity family. The `_KS`
re-pinning aliases are `:= <the keystone>` (type inferred, home modules untouched).

NOT covered here (STOP-REPORT — satisfiable not cheaply witnessed):
  • `Circuit.CommitmentCrossBind.runnable_binds_same_system_roots` — its satisfiable needs a concrete
    `VmRowEnv` pair with matching `STATE_COMMIT` AND each side's `systemRootsDigest` equal to a distinct
    `SysRoots`, exhibited at the side-table-row level; that is a runnable-circuit witness, not a cheap
    `def`+`decide`. Deferred.
  • `Exec.UniversalBridge.{cap_leaf_value_codec, index_boundary_mroot_derived,
    index_boundary_mroot_from_memcheck}` — CR-floor / MMR-canonicity adapters with no existing concrete
    instance; a witness is plausibly cheap but not yet built. Deferred.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Circuit.Argus.Receipt
import Dregg2.Circuit.CommitmentCrossBind
import Dregg2.Exec.UniversalBridge

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditIntegrity

/-! ## §1 — TAG the integrity keystones with their companions (re-pinning aliases, type inferred). -/

/-! ### the Argus receipt weld. -/

-- (1) ARGUS-COMMITS-TO-ONE-RECEIPT (the connection keystone).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_eq
    teeth := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_observable]
def argus_commits_to_one_receipt_KS :=
  @Dregg2.Circuit.Argus.Receipt.argus_commits_to_one_receipt

-- (2) TRANSFER-COMMITS-TO-ONE-RECEIPT (the transfer weld).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_eq
    teeth := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_observable]
def transfer_commits_to_one_receipt_KS :=
  @Dregg2.Circuit.Argus.Receipt.transfer_commits_to_one_receipt

-- (3) TRANSFER-RECEIPT-IS-EXECUTOR-RECEIPT.
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_eq
    teeth := Dregg2.Circuit.Argus.Receipt.writeCell0_receipt_observable]
def transfer_receipt_is_executor_receipt_KS :=
  @Dregg2.Circuit.Argus.Receipt.transfer_receipt_is_executor_receipt

/-! ### the commitment cross-bind crown. -/

-- (4) STATE-COMMIT BINDS CELL-COMMIT (the crown).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.CommitmentCrossBind.chC_is_cellCommit
    teeth := Dregg2.Circuit.CommitmentCrossBind.chC_bad_not_bridge]
def stateCommit_binds_cellCommit_KS :=
  @Dregg2.Circuit.CommitmentCrossBind.stateCommit_binds_cellCommit

-- (5) SET-FIELD-COMMIT BINDS CELL-COMMIT (the executor-side crown).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.CommitmentCrossBind.chC_is_cellCommit
    teeth := Dregg2.Circuit.CommitmentCrossBind.chC_bad_not_bridge]
def setFieldCommit_binds_cellCommit_KS :=
  @Dregg2.Circuit.CommitmentCrossBind.setFieldCommit_binds_cellCommit

/-! ### the universal-bridge verbs. -/

-- (6) GWRITE-IS-MEMORY-PROGRAM.
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.UniversalBridge.gwrite_is_memory_program_satisfiable
    teeth := Dregg2.Exec.UniversalBridge.bridge_program_teeth]
def gwrite_is_memory_program_KS :=
  @Dregg2.Exec.UniversalBridge.gwrite_is_memory_program

-- (7) MOVE-IS-MEMORY-PROGRAM.
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.UniversalBridge.move_is_memory_program_satisfiable
    teeth := Dregg2.Exec.UniversalBridge.bridge_program_teeth]
def move_is_memory_program_KS :=
  @Dregg2.Exec.UniversalBridge.move_is_memory_program

-- (8) CREATE-IS-MEMORY-PROGRAM.
@[load_bearing_keystone
    satisfiable := Dregg2.Exec.UniversalBridge.create_is_memory_program_satisfiable
    teeth := Dregg2.Exec.UniversalBridge.bridge_program_teeth]
def create_is_memory_program_KS :=
  @Dregg2.Exec.UniversalBridge.create_is_memory_program

/-! ## §2 — RUN the audit (the CI gate over the integrity family). -/

#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.argus_commits_to_one_receipt_KS
#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.transfer_commits_to_one_receipt_KS
#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.transfer_receipt_is_executor_receipt_KS
#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.stateCommit_binds_cellCommit_KS
#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.setFieldCommit_binds_cellCommit_KS
#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.gwrite_is_memory_program_KS
#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.move_is_memory_program_KS
#keystone_audit Dregg2.Verify.KeystoneAuditIntegrity.create_is_memory_program_KS

/-! ## §3 — axiom-hygiene over the re-pinned aliases (kernel-triple clean). -/

#assert_axioms argus_commits_to_one_receipt_KS
#assert_axioms transfer_commits_to_one_receipt_KS
#assert_axioms transfer_receipt_is_executor_receipt_KS
#assert_axioms stateCommit_binds_cellCommit_KS
#assert_axioms setFieldCommit_binds_cellCommit_KS
#assert_axioms gwrite_is_memory_program_KS
#assert_axioms move_is_memory_program_KS
#assert_axioms create_is_memory_program_KS

end Dregg2.Verify.KeystoneAuditIntegrity
