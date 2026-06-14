/-
# Dregg2.Authority.ImportBinding — the FIRST-CLASS provenanced import binding (apps gap 2).

A governed cell that wants *"this field IS this provenanced import"* today hand-threads TWO obligations
(see `Apps/GovernedParameters.lean`): `importValid` (the **provenance** — the value really is what a
cited source receipt committed) and a `RecordProgram` `affineEq` constraint (the **enforcement** — the
local post-state field equals that value). The app carried them as a pair and re-derived their
composition inline (`param_binding_matches_constitution`). Both apps lanes hit this seam: the import and
its enforcement are ONE intent, split across two surfaces.

This module fuses them into ONE construct. `ImportedEq` carries the `Import` (so the provenance
obligation `importValid` is RIGHT THERE on the same object) and projects the cell-program constraint
that enforces it (`toConstraint` = the `Program`-layer `affineEq [(1, localField)] value`). `admits`
checks the local field equals the import value (the same proved closure algebra as every other guard);
the soundness keystone `importedEq_binds_provenanced_value` surfaces the `importValid` provenance — an
admitted binding under a valid import means the local field holds EXACTLY the source's committed truth,
recomputable by a verifier, datable by tooling. The two obligations travel together; the app states ONE
clause, not two.

## Why a NEW module (not a `StateConstraint` constructor)

`Exec.Program`'s `StateConstraint` does not (and should not) know about `Exec.Receipt`/`CrossCellImport`
— `Program.lean` is the light, foundational record-grammar layer (it deliberately avoids the heavy
`EffectsState`→`Receipt` chain). Adding an `importedEq` *constructor* to the 73-theorem `StateConstraint`
inductive would force `Program.lean` to import `CrossCellImport` (pulling that chain in) and ripple a new
arm through every `evalConstraint`/`evalConstraintCtx` matcher. Instead this module sits ABOVE both,
importing `Exec.Program` (for the constraint + its `affineEq` admit-char) and `Authority.CrossCellImport`
(for `Import`/`importValid`/`readAt`), and the fused construct's `toConstraint` lands in the EXISTING
`affineEq` atom — no new matcher case, no inductive churn, no import cycle (`CrossCellImport` does not
import `Program`, and neither imports this module).

## What is proven (the fusion, with teeth)

  * **`ImportedEq.admits_iff`** — the binding admits IFF the post-state carries the import value at the
    local field (delegates to `evalConstraint_affineEq_iff`, via the single-term affine atom).
  * **`importedEq_binds_provenanced_value` (THE KEYSTONE)** — provenance + enforcement, fused: when the
    import is VALID (`importValid`: the cited source receipt is in the source's well-linked chain AND the
    source field held `imp.value` there) AND the cell admits the binding, the local field equals the
    value the SOURCE COMMITTED at the cited receipt (`readAt source provenance sourceField`). ONE
    construct discharges the whole cross-cell contract `GovernedParameters` re-derived by hand.
  * **`importedEq_lying_import_rejected`** — the provenance tooth: a LYING import (claiming a value the
    source never committed) is NOT `importValid`, so it cannot even be cited to build a binding whose
    keystone fires; and a truthful import IS valid. The fused construct inherits the anti-lie directly.
  * **`ImportedEq.admits_rejects_off_value`** — the enforcement tooth: a post-state whose local field
    does NOT equal the (provenanced) import value is REJECTED by `admits` — a quiet override is
    impossible.
  * **`importedEq_stable_under_source_advance`** — the I-CONFLUENCE inheritance: a valid binding's
    provenance stays valid as the source cell advances (it cites an immutable past receipt), lifted
    verbatim from `CrossCellImport.importValid_stable_under_source_advance`. So the binding is
    coordination-free where a live cross-cell read is not.
  * **§NON-VACUITY** — a concrete source history + binding: the truthful binding ADMITS and its keystone
    yields the source's committed value; the off-value post-state and the lying import both REJECT.

NEW file only. Touches neither `Program` nor `CrossCellImport`. Every keystone `#assert_axioms`-pinned
to `{propext, Classical.choice, Quot.sound}` — no sorry, no `:= True`. The §8 seam (the source chain's
receipt-digest collision-resistance) is the `HInj`/`HFresh` hypotheses threaded through
`CrossCellImport.chain_tamper_evident`, never a Lean axiom.
-/
import Dregg2.Exec.Program
import Dregg2.Authority.CrossCellImport

namespace Dregg2.Authority.ImportBinding

open Dregg2.Exec (Value FieldName)
open Dregg2.Exec.Receipts (Receipt)
open Dregg2.Authority.CrossCellImport (Import SourceHistory importValid readAt)

/-! ## §1 — `ImportedEq`: the fused provenanced binding (the import + the field it binds, as ONE).

`ImportedEq` is a cited `Import` plus the LOCAL field it binds. The `Import` already carries `localField`
(the local field), `sourceField`, `value`, and `provenance` (the cited source receipt) — so a single
`ImportedEq` is exactly *"local field `localField` IS the value the source committed at `provenance`"*,
the whole cross-cell intent in one object. The provenance obligation is `importValid H source imp`
(checked against the source's history); the enforcement obligation is the projected cell-program
constraint `toConstraint` (an EXISTING `affineEq` atom). -/

/-- **`ImportedEq`** — a first-class provenanced field binding: the cited cross-cell `Import` whose
`localField` the cell program enforces to equal the provenanced `value`. ONE object carrying BOTH the
provenance citation (`imp.provenance`, validated by `importValid`) and the enforcement target
(`imp.localField`). -/
structure ImportedEq where
  /-- The cited cross-cell import (source receipt + the value its field held there). -/
  imp : Import
  deriving Repr

namespace ImportedEq

/-- **`toConstraint`** — the cell-program constraint that ENFORCES the binding: `affineEq [(1,
localField)] value`, the EXISTING single-term affine atom of `Exec.Program`. The local field must equal
the provenanced import value. No new constructor — the enforcement lands in the proved closure algebra. -/
def toConstraint (b : ImportedEq) : Dregg2.Exec.StateConstraint :=
  .affineEq [(1, b.imp.localField)] b.imp.value

/-- **`admits b o n`** — does the binding admit the transition `(o, n)`? Iff the post-state `n` carries
the import value at the local field (the enforcement leg). Decidable, computable, fail-closed (an absent
local field rejects). The provenance leg is `importValid` (§2) — `admits` is the ENFORCEMENT the cell
program runs; the keystone fuses them. -/
def admits (b : ImportedEq) (o n : Value) : Bool :=
  Dregg2.Exec.evalConstraint b.toConstraint o n

/-- `affineSum [(1, f)]` reads exactly the field `f` (the single-term affine atom). -/
private theorem affineSum_single (f : FieldName) (rec : Value) :
    Dregg2.Exec.affineSum rec [(1, f)] = rec.scalar f := by
  simp only [Dregg2.Exec.affineSum, List.foldr]
  cases rec.scalar f <;> simp

/-- **`admits_iff`.** The binding admits IFF the post-state carries the import value at the local field.
Delegates to the program's `affineEq` admit-char through the single-term affine reader. So the
enforcement leg is exactly the proved closure algebra — no new machinery. -/
theorem admits_iff (b : ImportedEq) (o n : Value) :
    b.admits o n = true ↔ n.scalar b.imp.localField = some b.imp.value := by
  unfold admits toConstraint
  rw [Dregg2.Exec.evalConstraint_affineEq_iff]
  constructor
  · rintro ⟨s, hs, rfl⟩
    rw [affineSum_single] at hs; exact hs
  · intro hn
    exact ⟨b.imp.value, by rw [affineSum_single, hn], rfl⟩

/-- **`admits_rejects_off_value` (the ENFORCEMENT tooth).** A post-state whose local field does NOT
equal the provenanced import value is REJECTED. A governed cell cannot carry an off-import parameter —
the binding is enforced by the cell program, so a quiet override is impossible. -/
theorem admits_rejects_off_value (b : ImportedEq) (o n : Value) (localVal : Int)
    (hlocal : n.scalar b.imp.localField = some localVal) (hoff : localVal ≠ b.imp.value) :
    b.admits o n = false := by
  by_contra hc
  -- `admits` is a Bool; ¬(… = false) ⇒ … = true.
  have htrue : b.admits o n = true := by
    cases h : b.admits o n with
    | true => rfl
    | false => exact absurd h hc
  have := (admits_iff b o n).mp htrue
  rw [hlocal] at this; injection this with this; exact hoff this

end ImportedEq

/-! ## §2 — THE FUSION KEYSTONE: provenance (`importValid`) + enforcement (`admits`) discharge together.

This is the contract `Apps/GovernedParameters.param_binding_matches_constitution` re-derived inline — now
a ONE-CONSTRUCT theorem any governed cell reuses. When the import is VALID and the cell admits the
binding, the local field holds EXACTLY the value the source committed at the cited receipt: provenance
(the value is the source's truth, non-forgeable by inheritance from the chain's tamper-evidence) +
enforcement (the cell holds precisely that value), fused. -/

/-- **`importedEq_binds_provenanced_value` (THE KEYSTONE — provenance ∧ enforcement, fused).** When the
binding's import is VALID against the source history (`importValid H source b.imp`: the cited receipt is
in the source's well-linked chain AND the source field held `b.imp.value` there) AND the cell admits the
binding (`b.admits o n`), the post-state's local field equals the value the SOURCE COMMITTED at the
cited receipt — `readAt source b.imp.provenance b.imp.sourceField`. A verifier can recompute it; tooling
can date it. ONE construct surfaces both legs. -/
theorem importedEq_binds_provenanced_value
    {H : Receipt → Nat} {source : SourceHistory} {b : ImportedEq} {o n : Value}
    (hvalid : importValid H source b.imp)
    (hadmit : b.admits o n = true) :
    n.scalar b.imp.localField = some (readAt source b.imp.provenance b.imp.sourceField) := by
  -- enforcement: the local field equals the import value.
  rw [(ImportedEq.admits_iff b o n).mp hadmit]
  -- provenance: importValid's third conjunct says the import value IS the committed readout.
  rw [hvalid.2.2]

/-- **`importedEq_admits_under_valid_import` (the positive composition).** Conversely, if the local
field already holds the value the source committed at the cited receipt AND the import is valid, the
binding admits — the honest provenanced state is accepted. So a faithful cross-cell binding is
constructible, not just refutable. -/
theorem importedEq_admits_under_valid_import
    {H : Receipt → Nat} {source : SourceHistory} {b : ImportedEq} {o n : Value}
    (hvalid : importValid H source b.imp)
    (hheld : n.scalar b.imp.localField = some (readAt source b.imp.provenance b.imp.sourceField)) :
    b.admits o n = true := by
  rw [ImportedEq.admits_iff]
  -- readAt … = b.imp.value (importValid's third conjunct), so the held value IS the import value.
  rw [hheld, hvalid.2.2]

/-! ## §3 — THE PROVENANCE TOOTH (the lie cannot be cited) + I-CONFLUENCE inheritance. -/

/-- **`importedEq_lying_import_rejected` (the PROVENANCE tooth).** A LYING import — one whose `value`
differs from what the source committed at the cited receipt — is NOT `importValid`, so it cannot be used
to build a binding whose keystone fires; a TRUTHFUL import (citing the committed value) IS valid. The
fused construct inherits `CrossCellImport`'s anti-lie directly: an adversary cannot present a false
provenanced value to bind a field to. (Stated over two imports agreeing on the citation but differing on
the claimed value: at most one is valid.) -/
theorem importedEq_lying_import_rejected
    {H : Receipt → Nat} {source : SourceHistory} {truthful lying : ImportedEq}
    (hcite : truthful.imp.provenance = lying.imp.provenance
              ∧ truthful.imp.sourceField = lying.imp.sourceField)
    (hvalues_differ : truthful.imp.value ≠ lying.imp.value)
    (htruthful : importValid H source truthful.imp) :
    ¬ importValid H source lying.imp := by
  intro hlying
  -- importValid is a function of (provenance, sourceField) ⇒ unique value; differing values ⇒ a lie.
  have := Dregg2.Authority.CrossCellImport.importValid_value_unique htruthful hlying hcite
  exact hvalues_differ this

/-- **`importedEq_stable_under_source_advance` (I-CONFLUENCE inheritance).** A valid binding's
provenance stays valid after the source cell takes a further turn (a fresh head receipt): the binding
cites an IMMUTABLE PAST receipt, so the read never changes as the source advances. Lifted verbatim from
`CrossCellImport.importValid_stable_under_source_advance` — the binding is coordination-free where a live
cross-cell read is not. -/
theorem importedEq_stable_under_source_advance
    {H : Receipt → Nat} {source : SourceHistory} {b : ImportedEq} {r : Receipt} {v : Value}
    (hfresh : r ∉ source.chain)
    (hlink : ∀ hd, source.chain.head? = some hd → r.prevHash = H hd)
    (hvalid : importValid H source b.imp) :
    importValid H (Dregg2.Authority.CrossCellImport.advance source r v) b.imp :=
  Dregg2.Authority.CrossCellImport.importValid_stable_under_source_advance hfresh hlink hvalid

/-! ## §4 — §NON-VACUITY: a concrete source + binding, both legs BITE (`#guard` + theorem). -/

section Witnesses

open Dregg2.Exec.Receipts (mkReceipt genesisSentinel demoHash)

/-- A source (constitution) cell: an older receipt committed `fee = 30`. -/
def srcOld : Receipt := mkReceipt genesisSentinel 30 30 0
def srcNew : Receipt := mkReceipt (demoHash srcOld) 30 30 1
def srcState : Receipt → Value := fun r =>
  if r = srcNew then .record [("fee", .int 30)] else .record [("fee", .int 30)]
def srcHist : SourceHistory := ⟨[srcNew, srcOld], srcState⟩

/-- The TRUTHFUL binding: local field `local_fee` IS the source's `fee = 30` at `srcOld`. -/
def truthful : ImportedEq := ⟨⟨"local_fee", "fee", 30, srcOld⟩⟩
/-- The LYING binding: claims the source's fee was 99 (it was 30) at the same receipt. -/
def lying : ImportedEq := ⟨⟨"local_fee", "fee", 99, srcOld⟩⟩

-- The truthful binding ADMITS a post-state carrying 30 at the local field; REJECTS one carrying 31.
#guard truthful.admits (.record []) (.record [("local_fee", .int 30)])
#guard truthful.admits (.record []) (.record [("local_fee", .int 31)]) == false
-- ...and REJECTS an absent local field (fail-closed enforcement).
#guard truthful.admits (.record []) (.record []) == false

-- The truthful import IS importValid on the source; the lying one is NOT (the readout check fails).
#guard decide (readAt srcHist truthful.imp.provenance truthful.imp.sourceField = truthful.imp.value)
#guard decide (readAt srcHist lying.imp.provenance lying.imp.sourceField = lying.imp.value) == false

/-- **`fusion_binds_committed_value` (non-vacuity of the keystone).** The truthful binding is valid AND
admits a state carrying 30, and the keystone yields the source's committed value (30) at the local
field — the fused construct is inhabited, both legs firing. -/
theorem fusion_binds_committed_value :
    truthful.admits (.record []) (.record [("local_fee", .int 30)]) = true ∧
      (.record [("local_fee", .int 30)] : Value).scalar truthful.imp.localField
        = some (readAt srcHist truthful.imp.provenance truthful.imp.sourceField) := by
  have hvalid : importValid demoHash srcHist truthful.imp := by
    refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · decide
  have hadmit : truthful.admits (.record []) (.record [("local_fee", .int 30)]) = true := by decide
  exact ⟨hadmit, importedEq_binds_provenanced_value hvalid hadmit⟩

/-- **`fusion_lying_rejected` (non-vacuity of the provenance tooth).** The truthful binding is valid and
the lying one is not — the lie cannot be cited. -/
theorem fusion_lying_rejected :
    importValid demoHash srcHist truthful.imp ∧ ¬ importValid demoHash srcHist lying.imp := by
  have hvalid : importValid demoHash srcHist truthful.imp := by
    refine ⟨⟨rfl, rfl⟩, ?_, ?_⟩
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · decide
  refine ⟨hvalid, ?_⟩
  exact importedEq_lying_import_rejected (truthful := truthful) (lying := lying)
    ⟨rfl, rfl⟩ (by decide) hvalid

end Witnesses

/-! ## §5 — Axiom hygiene. Every load-bearing fusion theorem checked kernel-clean. -/

#assert_all_clean [
  ImportedEq.admits_iff,
  ImportedEq.admits_rejects_off_value,
  importedEq_binds_provenanced_value,
  importedEq_admits_under_valid_import,
  importedEq_lying_import_rejected,
  importedEq_stable_under_source_advance,
  fusion_binds_committed_value,
  fusion_lying_rejected
]

end Dregg2.Authority.ImportBinding
