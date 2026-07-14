import Dregg2.Circuit.DescriptorIR2

/-
# NarrowChip — the single-output (18-wide) chip lookup for the tuple-narrowing optimizer pass

THE OPTIMIZER'S FIRST PASS (validated by 3 planner-architects, 2026-07-13). The deployed
`chipLookupTuple` is 25-wide: `arity + CHIP_RATE(16) inputs + out0 + 7 lanes`. For SINGLE-OUTPUT sites
(the 133-site 1-felt Merkle–Damgård chain in the wide rotated descriptor), those 7 lane columns are
witnessed only to match the wide chip row and are — in the deployed Lean's own words
(`DescriptorIR2.lean:1144`) — "NOT constrained by the single-output site denotation". They are read by
NOTHING: `chip_lookup_sound` proves `a digestCol = hash inputs` with the lanes riding purely
EXISTENTIALLY, never entering the conclusion.

This file defines the NARROW variant (18-wide: `arity + CHIP_RATE inputs + out0`, no lanes) on a second
chip table, and proves it enforces the IDENTICAL out0 = hash equation. Routing the 134 single-output
sites to a narrow bus therefore drops 7 committed columns/site (~938 on the wide rotated descriptor,
2607→~1669 main) at ZERO soundness cost — a mechanical translation-validation refinement, no new crypto.
`chip_lookup_sound_narrow` is that refinement's soundness core; it is a strict simplification of
`chip_lookup_sound` (the existential lanes are gone).
-/

namespace Dregg2.Circuit.DescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit

/-- The NARROW chip ROW (18-wide): `arity :: padded inputs ++ [hash inputs]` — ONLY out0, no lanes. -/
def chipRowNarrow (hash : List ℤ → ℤ) (ins : List ℤ) : List ℤ :=
  (ins.length : ℤ) :: padTo CHIP_RATE ins ++ [hash ins]

/-- The NARROW chip LOOKUP tuple (18-wide): `arity :: padded input exprs ++ [out0 column]`. -/
def chipLookupTupleNarrow (ins : List EmittedExpr) (digestCol : Nat) : List EmittedExpr :=
  (.const (ins.length : ℤ)) :: padToE CHIP_RATE ins ++ [.var digestCol]

/-- A narrow chip table is SOUND when every row is a genuine `(arity, padded inputs, hash inputs)`
    tuple of the permutation — with NO existential lanes (the simplification over `ChipTableSound`). -/
def ChipTableSoundNarrow (hash : List ℤ → ℤ) (tbl : Table) : Prop :=
  ∀ r ∈ tbl, ∃ ins : List ℤ, ins.length ≤ CHIP_RATE ∧ r = chipRowNarrow hash ins

/-- **THE NARROW LEVER.** Against a sound narrow chip table, a narrow lookup ENFORCES the SAME hash
    equation `a digestCol = hash inputs` that the 25-wide `chip_lookup_sound` does — carrying NO lane
    columns. This is why the 7 lanes/site are droppable for single-output sites at zero soundness cost. -/
theorem chip_lookup_sound_narrow (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSoundNarrow hash tbl) (a : Assignment)
    (ins : List EmittedExpr) (digestCol : Nat) (hlen : ins.length ≤ CHIP_RATE)
    (hmem : (chipLookupTupleNarrow ins digestCol).map (·.eval a) ∈ tbl) :
    a digestCol = hash (ins.map (·.eval a)) := by
  obtain ⟨ws, hwlen, hrow⟩ := hSound _ hmem
  have hev : (chipLookupTupleNarrow ins digestCol).map (·.eval a)
      = (ins.length : ℤ) :: padTo CHIP_RATE (ins.map (·.eval a)) ++ [a digestCol] := by
    simp [chipLookupTupleNarrow, List.map_cons, List.map_append, map_eval_padToE, EmittedExpr.eval,
      List.map_map, Function.comp_def]
  rw [hev] at hrow
  unfold chipRowNarrow at hrow
  injection hrow with hl htail
  have hlens : (ins.map (·.eval a)).length = ws.length := by
    have hcast : (ins.length : ℤ) = (ws.length : ℤ) := hl
    have := Int.natCast_inj.mp hcast
    simpa [List.length_map] using this
  have hlenm : (ins.map (·.eval a)).length ≤ CHIP_RATE := by
    simpa [List.length_map] using hlen
  have hpads := List.append_inj htail (by rw [padTo_length hlenm, padTo_length hwlen])
  have hins : ins.map (·.eval a) = ws := padTo_inj hlens hpads.1
  have hd : a digestCol = hash ws := by
    have hblock : [a digestCol] = [hash ws] := hpads.2
    simpa using hblock
  rw [hins]; exact hd

/-- **The SITE-level narrow refinement** (mirrors `siteLookup_replaces_site`, lanes dropped). Against a
    sound narrow chip table, the narrow lookup of a site `s` enforces EXACTLY the site equation
    `loc digestCol = hash (resolved inputs)` — the v1 in-row Poseidon2 constraint — carrying no lanes.
    This is the unit the tuple-narrowing emit routing replaces per single-output site. -/
theorem siteLookupNarrow_replaces_site (hash : List ℤ → ℤ) (tbl : Table)
    (hSound : ChipTableSoundNarrow hash tbl) (env : VmRowEnv)
    (sites : List VmHashSite) (s : VmHashSite) (digs : List ℤ)
    (hdig : ∀ k, env.loc ((sites.getD k default).digestCol) = digs.getD k 0)
    (hlen : s.inputs.length ≤ CHIP_RATE)
    (hmem : (chipLookupTupleNarrow (s.inputs.map (HashInput.toExpr sites)) s.digestCol).map
              (·.eval env.loc) ∈ tbl) :
    env.loc s.digestCol = hash (s.resolvedInputs env digs) := by
  have h := chip_lookup_sound_narrow hash tbl hSound env.loc
    (s.inputs.map (HashInput.toExpr sites)) s.digestCol
    (by simpa [List.length_map] using hlen) hmem
  rw [h]
  congr 1
  rw [List.map_map]
  unfold VmHashSite.resolvedInputs
  apply List.map_congr_left
  intro i _
  cases i with
  | col c    => rfl
  | digest k =>
    have hk := hdig k
    simp only [List.getD_eq_getElem?_getD] at hk
    simp [HashInput.toExpr, HashInput.resolve, EmittedExpr.eval, hk]
  | zero     => rfl

-- Soundness core + site refinement: axiom-clean (only the standard trio — no sorry, no assumed carrier).
#assert_axioms chip_lookup_sound_narrow
#assert_axioms siteLookupNarrow_replaces_site

end Dregg2.Circuit.DescriptorIR2
