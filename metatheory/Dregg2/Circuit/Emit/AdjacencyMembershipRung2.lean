/-
# Dregg2.Circuit.Emit.AdjacencyMembershipRung2 — the RUNG-2 discharge of the last-row ordering
residual for the emitted neighbor-adjacency (sorted-set non-membership) descriptor
(`adjacencyDesc`), and the PRECISE naming of the emit-fix that closes genuine no-forgery.

## What Rung 1 gave us and what the residual IS (read the ground truth first)

`AdjacencyMembershipRefine.lean` (RUNG 1) proves the whole-descriptor bridge in two pieces:
  * `adjacency_sat_refines` : `Satisfied2 adjacencyDesc` + the NAMED Poseidon2 chip carrier
    (`ChipTableSound`) FORCE an `AdjacencyAuthFragment` — both leaves fold AUTHENTICALLY (dir-ordered
    Poseidon2 combine per active level) up to their top spine node `*_CUR[last]`, both top parents
    `*_PAR[last]` are pinned to the SAME public `root`, `root` is a genuine `hash` of the last-row
    `(left,right)` pair, and the published indices are consecutive.
  * `adjacency_full_bridge` : the fragment PLUS `TopLevelOrdered` (the ONE un-forced fact) yields the
    full functional spec `AdjacentLeavesUnderRoot` — both leaves are the leaves of full authentic
    Poseidon2-Merkle paths reaching the same committed root at consecutive indices.

`TopLevelOrdered` is the residual: on the LAST trace row, each path's `par` is the authentic
dir-ordered combine of its `(cur, sib)`. Rung 1 names WHY it is un-forced: the deployed DSL lowers
the `Binary`/`Polynomial` child-ordering gates as `is_transition = false` (they fire on EVERY row,
`dsl_plonky3.rs:225/240`), but `AdjacencyMembershipEmit` maps them to IR-v2 `.base (.gate …)`, whose
`VmConstraint.holdsVm` makes a `.gate` VACUOUS on the last row. So the top-level ordering
`L_LEFT[last] = dir-order-left(L_CUR[last], L_SIB[last])` (etc.) is DROPPED, breaking exactly ONE edge
of the authentication chain:

    leaf →(fold, ENFORCED)→ L_CUR[last] →(ordering gate, DROPPED)→ {L_LEFT,L_RIGHT}[last]
                                                                  →(chip lookup, ENFORCED)→ root

## The classification (RUNG2_PARTIAL) — and why the residual is NOT crypto-dischargeable

The disclosed commitment is the SHALLOW Merkle `root = hash [L_LEFT[last], L_RIGHT[last]]` — it binds
only the top hash's TWO children. Unlike the DFA route-commitment (a DEEP fold binding every row, which
`fold_inj`/CR pins whole), the CR carrier here can bind the disclosed pair `(L_LEFT, L_RIGHT)[last]` to
the genuine one (`topPair_no_forgery`, §5, consuming `CollisionFree`), but it CANNOT bind the SPINE
CONNECTION `L_CUR[last] ∈ dir-order⁻¹(L_LEFT, L_RIGHT)[last]`: nothing commits `L_CUR[last]` at the top,
and the broken edge is an ARITHMETIC ordering gate, not a hash-preimage relation. So the residual is a
genuine EMIT/lowering-fidelity gap, and the fix is an emit change — not a new crypto carrier.

This file DISCHARGES WHAT CAN BE DISCHARGED and NAMES the emit-fix precisely:
  * §2  `adjacency_rung2_closes` — the closure: `Satisfied2 adjacencyDesc` + `ChipTableSound` +
        `LastRowOrdered` ⟹ the genuine no-forgery spec `AdjacentLeavesUnderRoot`. Consumes the NAMED
        carrier `ChipTableSound` (the last-row `root = hash[left,right]` binding). This is the discharge.
  * §3  `adjLastOrderFix` — the exact 6 constraints the emit must add (`.base (.boundary VmRow.last …)`
        of the dir-binary / left-order / right-order bodies, per path), and `lastRowOrdered_of_fix`
        proving those constraints ENFORCE `LastRowOrdered`. This names the emit-fix constructively.
  * §4  `adjacencyDescFixed` + `adjacency_rung2_fixed_closes` — the CROWN: a `Satisfied2` of the FIXED
        descriptor (the current constraints ++ the fix) forces `AdjacentLeavesUnderRoot` unconditionally
        on any residual. The fix is proven SUFFICIENT.
  * §5  `topPair_no_forgery` — the partial no-forgery the CR carrier DOES buy (the top pair is bound to
        the genuine children), honestly delimited: it does NOT close the spine connection.
  * §6  the TRUE half — a genuine trace whose closure FIRES to `AdjacentLeavesUnderRoot`.
  * §7  the LOAD-BEARING cheat — a concrete trace that `Satisfied2`s the CURRENT `adjacencyDesc` yet
        VIOLATES `TopLevelOrdered`/`LastRowOrdered` (a genuine top-level forgery). Proves the residual is
        REAL: `Satisfied2` + `ChipTableSound` alone do NOT force no-forgery — the anchor/fix is
        load-bearing, not decorative. (This same trace FAILS the fixed descriptor's added gates.)

## The precise emit-fix (the remaining gap, named)

`membership_adjacency_air.rs` / the IR-v2 emit must ensure the three child-ordering gates fire on the
LAST row too. The additive Lean statement is `adjLastOrderFix` (§3): add, per path,
  `.base (.boundary VmRow.last (dirBinaryBody dir))`,
  `.base (.boundary VmRow.last (leftOrderBody cur sib dir left))`,
  `.base (.boundary VmRow.last (rightOrderBody cur sib dir right))`.
Equivalently: lower the ordering `Binary`/`Polynomial` gates as NON-`when_transition` constraints so
`holdsVm` fires them on the last row (the deployed DSL's actual `is_transition = false` semantics).

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The Poseidon2 chip carrier enters ONLY as
the NAMED hypothesis `ChipTableSound hash (t.tf .poseidon2)`; the Poseidon2 CR carrier enters ONLY as
`CollisionFree (dfaPrims hash)`. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.AdjacencyMembershipRefine
import Dregg2.Circuit.Emit.DfaRoutingRung2

namespace Dregg2.Circuit.Emit.AdjacencyMembershipRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   WindowConstraint WindowExpr ChipTableSound chip_lookup_sound chipLookupTuple CHIP_RATE
   chipRow memLog mapLog memCheck_nil)
open Dregg2.Circuit.Emit.AdjacencyMembershipEmit
open Dregg2.Circuit.Emit.AdjacencyMembershipRefine
open Dregg2.Crypto (CryptoPrimitives)
open Dregg2.Crypto.DfaAcceptanceAir (CollisionFree)
open Dregg2.Circuit.Emit.DfaRoutingRung2 (dfaPrims collisionFree_of_injective)

set_option autoImplicit false

/-- The membership tactic (local copy — the Rung-1 macro is file-local): every constraint we name is
literally in `adjacencyDesc.constraints` (= `adjacencyConstraints`). -/
local macro "adj_mem" : tactic =>
  `(tactic| (show _ ∈ adjacencyConstraints; simp [adjacencyConstraints, pathBlock]))

/-! ## §1 — `LastRowOrdered`: the emit-fix's semantic content (the residual, phrased as a hypothesis
the fixed emit supplies). Exactly the three child-ordering bodies of each path, forced to vanish on the
LAST trace row — what the deployed DSL's every-row `Binary`/`Polynomial` gates enforce and the IR-v2
`.gate` mapping drops. -/

/-- The six ordering-gate bodies of both paths, vanishing on the last trace row. -/
def LastRowOrdered (t : VmTrace) : Prop :=
  (dirBinaryBody L_DIR).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (leftOrderBody L_CUR L_SIB L_DIR L_LEFT).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (rightOrderBody L_CUR L_SIB L_DIR L_RIGHT).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (dirBinaryBody U_DIR).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (leftOrderBody U_CUR U_SIB U_DIR U_LEFT).eval (envAt t (t.rows.length - 1)).loc = 0 ∧
  (rightOrderBody U_CUR U_SIB U_DIR U_RIGHT).eval (envAt t (t.rows.length - 1)).loc = 0

/-! ## §2 — THE DISCHARGE: `LastRowOrdered` + the chip carrier close `TopLevelOrdered`, hence the full
functional no-forgery spec via the Rung-1 bridge. -/

/-- **`LastRowOrdered` closes the residual `TopLevelOrdered`.** On the last row, the three ordering
bodies (from `LastRowOrdered`) plus the last-row chip lookup `par = hash[left,right]` (from the NAMED
`ChipTableSound` carrier, escaping the transition zerofier) collapse to the authentic dir-ordered
combine — exactly `combine_of_gates` at the top level, for both paths. -/
theorem topLevelOrdered_of_lastRowOrdered {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlen : 0 < t.rows.length)
    (hlro : LastRowOrdered t) :
    TopLevelOrdered hash t := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  obtain ⟨hdL, hlL, hrL, hdU, hlU, hrU⟩ := hlro
  refine ⟨?_, ?_⟩
  · exact combine_of_gates hash (envAt t (t.rows.length - 1)).loc
      L_CUR L_SIB L_DIR L_LEFT L_RIGHT L_PAR hdL hlL hrL
      (lookupChip hsat hChip _ hLlt L_LEFT L_RIGHT L_PAR L_PAR_LANES (by adj_mem))
  · exact combine_of_gates hash (envAt t (t.rows.length - 1)).loc
      U_CUR U_SIB U_DIR U_LEFT U_RIGHT U_PAR hdU hlU hrU
      (lookupChip hsat hChip _ hLlt U_LEFT U_RIGHT U_PAR U_PAR_LANES (by adj_mem))

/-- **`adjacency_rung2_closes` — THE RUNG-2 DISCHARGE (semantic form).** A trace that `Satisfied2`s the
emitted `adjacencyDesc`, rides the NAMED Poseidon2 chip carrier, and additionally has the last-row
ordering forced (`LastRowOrdered` — exactly what the emit-fix supplies) is a genuine two-path
binary-Merkle authentication transcript of two consecutive-index leaves under one shared committed
root: `AdjacentLeavesUnderRoot`. The named carrier discharged is `ChipTableSound`; the residual removed
is the emit's dropped last-row ordering. -/
theorem adjacency_rung2_closes {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hlro : LastRowOrdered t) :
    AdjacentLeavesUnderRoot hash (t.pub PI_LEAF_LOWER) (t.pub PI_LEAF_UPPER)
      (t.pub PI_ROOT) (t.pub PI_IDX_LOWER) (t.pub PI_IDX_UPPER) :=
  adjacency_full_bridge hlen hsat hChip
    (topLevelOrdered_of_lastRowOrdered hsat hChip hlen hlro)

/-! ## §3 — THE EMIT-FIX, NAMED AS DATA, and proven to ENFORCE `LastRowOrdered`. -/

/-- **The precise emit-fix**: the six last-row ordering boundary constraints the emit must add (three
per path). Each is the exact child-ordering body the DSL's every-row `Binary`/`Polynomial` gate carries,
re-lowered as a `.base (.boundary VmRow.last …)` so it fires on the last row (where the IR-v2 `.gate`
mapping makes it vacuous). -/
def adjLastOrderFix : List VmConstraint2 :=
  [ .base (.boundary VmRow.last (dirBinaryBody L_DIR))
  , .base (.boundary VmRow.last (leftOrderBody L_CUR L_SIB L_DIR L_LEFT))
  , .base (.boundary VmRow.last (rightOrderBody L_CUR L_SIB L_DIR L_RIGHT))
  , .base (.boundary VmRow.last (dirBinaryBody U_DIR))
  , .base (.boundary VmRow.last (leftOrderBody U_CUR U_SIB U_DIR U_LEFT))
  , .base (.boundary VmRow.last (rightOrderBody U_CUR U_SIB U_DIR U_RIGHT)) ]

/-- A declared last-row boundary body vanishes on the last row — the generic form of the Rung-1
`lastBoundaryZero`, over ANY descriptor `d` carrying the constraint. -/
theorem genLastBoundaryZero {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (body : EmittedExpr)
    (hmem : VmConstraint2.base (.boundary VmRow.last body) ∈ d.constraints) :
    body.eval (envAt t (t.rows.length - 1)).loc = 0 := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    simp [this]
  have h := hsat.rowConstraints _ hLlt _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h (by decide)

/-- **`lastRowOrdered_of_fix` — the emit-fix ENFORCES `LastRowOrdered`.** For any descriptor `d` whose
constraints CONTAIN `adjLastOrderFix`, a `Satisfied2` of `d` forces `LastRowOrdered` (each fix
constraint is a last-row boundary read). This is the constructive content of "add these six and the
residual is enforced". -/
theorem lastRowOrdered_of_fix {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hsat : Satisfied2 hash d minit mfin maddrs t) (hlen : 0 < t.rows.length)
    (hmem : ∀ c ∈ adjLastOrderFix, c ∈ d.constraints) :
    LastRowOrdered t := by
  have g : ∀ b : EmittedExpr, VmConstraint2.base (.boundary VmRow.last b) ∈ adjLastOrderFix →
      b.eval (envAt t (t.rows.length - 1)).loc = 0 :=
    fun b hb => genLastBoundaryZero hsat hlen b (hmem _ hb)
  refine ⟨g _ ?_, g _ ?_, g _ ?_, g _ ?_, g _ ?_, g _ ?_⟩ <;>
    (show _ ∈ adjLastOrderFix) <;>
    repeat' first | exact List.Mem.head _ | apply List.Mem.tail

/-! ## §4 — THE CROWN: the FIXED descriptor forces the full no-forgery spec (the fix is SUFFICIENT). -/

/-- **`adjacencyDescFixed`** — the emitted descriptor WITH the emit-fix applied: the current 26
constraints plus the six last-row ordering boundary constraints. This is the descriptor the fixed emit
would produce. -/
def adjacencyDescFixed : EffectVmDescriptor2 :=
  { adjacencyDesc with constraints := adjacencyDesc.constraints ++ adjLastOrderFix }

/-- A `Satisfied2` of the fixed descriptor is a `Satisfied2` of the current one (its constraints are a
prefix; the memory/table/range legs are unchanged). -/
theorem sat_of_fixed {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    {t : VmTrace} (h : Satisfied2 hash adjacencyDescFixed minit mfin maddrs t) :
    Satisfied2 hash adjacencyDesc minit mfin maddrs t where
  rowConstraints i hi c hc :=
    h.rowConstraints i hi c
      (show c ∈ adjacencyDescFixed.constraints from List.mem_append_left adjLastOrderFix hc)
  rowHashes := h.rowHashes
  rowRanges := h.rowRanges
  memAddrsNodup := h.memAddrsNodup
  memClosed := h.memClosed
  memDisciplined := h.memDisciplined
  memBalanced := h.memBalanced
  memTableFaithful := h.memTableFaithful
  mapTableFaithful := h.mapTableFaithful

/-- **`adjacency_rung2_fixed_closes` — the fix is SUFFICIENT.** A `Satisfied2` of the FIXED descriptor,
against the NAMED Poseidon2 chip carrier, forces the genuine functional no-forgery spec
`AdjacentLeavesUnderRoot` — UNCONDITIONALLY on any residual. The emit-fix (`adjLastOrderFix`) closes the
Rung-1 `TopLevelOrdered` gap; nothing else is missing. -/
theorem adjacency_rung2_fixed_closes {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDescFixed minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2)) :
    AdjacentLeavesUnderRoot hash (t.pub PI_LEAF_LOWER) (t.pub PI_LEAF_UPPER)
      (t.pub PI_ROOT) (t.pub PI_IDX_LOWER) (t.pub PI_IDX_UPPER) := by
  have hsatOrig := sat_of_fixed hsat
  have hlro : LastRowOrdered t :=
    lastRowOrdered_of_fix hsat hlen (fun c hc =>
      show c ∈ adjacencyDescFixed.constraints from List.mem_append_right adjacencyDesc.constraints hc)
  exact adjacency_rung2_closes hlen hsatOrig hChip hlro

/-! ## §5 — What the CR carrier DOES buy (and honestly, what it does NOT). -/

/-- **`topPair_no_forgery` — the partial no-forgery the Poseidon2 CR carrier discharges.** Against the
NAMED CR carrier `CollisionFree (dfaPrims hash)` and the honest anchor `root = hash[gL, gR]` (the
disclosed root's genuine children, from a real reference tree), the last-row disclosed child columns
`(L_LEFT, L_RIGHT)[last]` are FORCED to the genuine pair `(gL, gR)`: the prover cannot forge the top
`(left,right)` away from the honest ones. This consumes `compress_pair_inj` non-vacuously.

**What CR does NOT give (the emit gap):** it does NOT force `(gL, gR) = dir-order(L_CUR[last],
L_SIB[last])` — i.e. that the trace's authentic top spine node `L_CUR[last]` is genuinely a child of the
root. That connection is the ARITHMETIC ordering gate the emit drops (§7 exhibits a `Satisfied2` trace
where it fails), and no CR carrier can close it — the Merkle root is a SHALLOW commitment (only the top
hash's two children), so `L_CUR[last]` is uncommitted at the top. Hence the emit-fix (§3/§4), not a
crypto carrier, is the closure. -/
theorem topPair_no_forgery {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} {t : VmTrace}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (cf : @CollisionFree ℤ _ (dfaPrims hash))
    (gL gR : ℤ)
    (hanchor : t.pub PI_ROOT = hash [gL, gR]) :
    (envAt t (t.rows.length - 1)).loc L_LEFT = gL
    ∧ (envAt t (t.rows.length - 1)).loc L_RIGHT = gR := by
  letI := dfaPrims hash
  have frag := adjacency_sat_refines hlen hsat hChip
  have heq : CryptoPrimitives.compress ((envAt t (t.rows.length - 1)).loc L_LEFT)
                ((envAt t (t.rows.length - 1)).loc L_RIGHT)
           = CryptoPrimitives.compress gL gR := by
    show hash [(envAt t (t.rows.length - 1)).loc L_LEFT, (envAt t (t.rows.length - 1)).loc L_RIGHT]
       = hash [gL, gR]
    rw [← frag.rootHashedLower]; exact hanchor
  exact cf.compress_pair_inj _ _ _ _ heq

/-- The CR carrier is realizable (NOT vacuously assumed): `CollisionFree (dfaPrims hash)` is inhabited
from `Function.Injective hash` (`collisionFree_of_injective`, the reference realization). A genuine
Poseidon2 `hash` supplies CR; injectivity is the reference stand-in that makes the hypothesis set of
`topPair_no_forgery` non-empty. -/
theorem cr_carrier_realizable {hash : List ℤ → ℤ} (hinj : Function.Injective hash) :
    @CollisionFree ℤ _ (dfaPrims hash) :=
  collisionFree_of_injective hinj

/-! ## §6 — Non-vacuity, TRUE half: a GENUINE trace whose closure FIRES.

A depth-1 adjacency: the two SIBLING leaves `10` (index 0, LEFT child) and `20` (index 1, RIGHT child)
under the shared parent `root = mHash [10,20] = 1020`. The lower path folds `10` with sibling `20`,
`dir=0`; the upper path folds `20` with sibling `10`, `dir=1` — both reach `1020`. The child-ordering
holds (`L_LEFT=L_CUR=10`, `L_RIGHT=L_SIB=20`; `U_LEFT=10=U_SIB`, `U_RIGHT=20=U_CUR`), so `LastRowOrdered`
holds and the RUNG-2 closure FIRES to the genuine `AdjacentLeavesUnderRoot`. -/

/-- A concrete little-endian digit hash — distinguishes child order (`[a,b] ↦ 100a+b`). -/
private def mHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- The genuine depth-1 row: leaves `10`/`20` as SIBLINGS, ordered children `(10,20)`, both parents =
root `1020`, indices `0`/`1`, `pow=1`. `L_DIR=0` (lower is left), `U_DIR=1` (upper is right). -/
private def wRow : Assignment := fun c =>
  if c = L_CUR then 10 else if c = L_SIB then 20 else if c = L_LEFT then 10
  else if c = L_RIGHT then 20 else if c = L_PAR then 1020
  else if c = U_CUR then 20 else if c = U_SIB then 10 else if c = U_DIR then 1
  else if c = U_LEFT then 10 else if c = U_RIGHT then 20 else if c = U_PAR then 1020
  else if c = U_IDX_OUT then 1 else if c = POW then 1 else 0

private def wPub : Assignment := fun k =>
  if k = PI_ROOT then 1020 else if k = PI_LEAF_LOWER then 10
  else if k = PI_LEAF_UPPER then 20 else if k = PI_IDX_UPPER then 1 else 0

private def wTbl : List (List ℤ) :=
  [chipRow mHash [10, 20] (List.replicate 7 0)]

private def wTrace : VmTrace :=
  { rows := [wRow], pub := wPub
    tf := fun tid => match tid with | .poseidon2 => wTbl | _ => [] }

/-- The concrete chip table is genuinely SOUND (every row is a real `chipRow` of `mHash`). -/
theorem wtChipSound : ChipTableSound mHash (wTrace.tf .poseidon2) := by
  intro r hr
  simp only [wTrace, wTbl, List.mem_singleton] at hr
  exact ⟨[10, 20], List.replicate 7 0, by decide, by decide, hr⟩

/-- **The genuine trace `Satisfied2`s the deployed descriptor** — the two lookups by membership, the
per-row gates vacuous on the single (= last) row, and the boundary/PI pins met. -/
theorem wtSat :
    Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] wTrace := by
  have hmemlog : memLog adjacencyDesc wTrace = [] := rfl
  have hmaplog : mapLog adjacencyDesc wTrace = [] := rfl
  have hF : (0 == 0) = true := rfl
  have hL : (0 + 1 == wTrace.rows.length) = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show wTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show adjacencyDesc.constraints = adjacencyConstraints from rfl] at hc
    simp only [adjacencyConstraints, pathBlock, List.cons_append, List.nil_append] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        copyWindow, Lookup.holdsAt, hF, hL] <;>
      decide
  · intro i _; trivial
  · intro i _ r hr; simp [adjacencyDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- The genuine trace's last-row ordering holds (`decide` over the concrete row) — so `LastRowOrdered`
is jointly satisfiable with `Satisfied2`, not an empty antecedent. -/
theorem wtLastRowOrdered : LastRowOrdered wTrace := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE RUNG-2 CLOSURE FIRES on the genuine witness (TRUE half).** Feeding the concrete satisfying
trace, its sound chip table, and its (achievable) `LastRowOrdered` to `adjacency_rung2_closes` recovers
the genuine `AdjacentLeavesUnderRoot` — two authentic Merkle paths for the sibling leaves `10, 20`
reaching the shared root `1020` at consecutive indices `0, 1`. -/
theorem wtTrace_rung2_fires :
    AdjacentLeavesUnderRoot mHash (wTrace.pub PI_LEAF_LOWER) (wTrace.pub PI_LEAF_UPPER)
      (wTrace.pub PI_ROOT) (wTrace.pub PI_IDX_LOWER) (wTrace.pub PI_IDX_UPPER) :=
  adjacency_rung2_closes (by decide) wtSat wtChipSound wtLastRowOrdered

/-- The recovered spec is over the genuine public values (leaves `10,20`; root `1020`; indices `0,1`) —
a real adjacency, not a constant. -/
theorem wtTrace_value :
    wTrace.pub PI_LEAF_LOWER = 10 ∧ wTrace.pub PI_LEAF_UPPER = 20
    ∧ wTrace.pub PI_ROOT = 1020 ∧ wTrace.pub PI_IDX_UPPER = wTrace.pub PI_IDX_LOWER + 1 := by
  refine ⟨rfl, rfl, rfl, ?_⟩; decide

/-! ## §7 — THE LOAD-BEARING cheat: the residual gap is REAL under the CURRENT emit.

The same depth-1 shape, but the top children are FORGED: `L_LEFT=3, L_RIGHT=4`, `root = mHash[3,4] =
304`, while the leaf is `L_CUR=10` with `L_SIB=0, L_DIR=0`. The child-ordering gate that would force
`L_LEFT = L_CUR = 10` is VACUOUS on the last row (the emit gap), so the trace `Satisfied2`s the CURRENT
`adjacencyDesc` — yet the leaf `10` is NOT a child of the committed root `304` (its authentic top spine
folds to `combine mHash 0 10 0 = 1000 ≠ 304`). `Satisfied2` + `ChipTableSound` therefore do NOT force
`TopLevelOrdered`/`LastRowOrdered`: the anchor/fix is LOAD-BEARING. (This trace FAILS `adjacencyDescFixed`
— the added last-row `leftOrderBody` boundary body is `3 - 10 = -7 ≠ 0`.) -/

/-- The forged row: leaf `10` (lower) / `20` (upper), but top children `(3,4)` unrelated to the leaves,
parents = the forged root `304 = mHash[3,4]`, indices `0`/`1`. Ordering NOT enforced on the last row. -/
private def fRow : Assignment := fun c =>
  if c = L_CUR then 10 else if c = U_CUR then 20
  else if c = L_LEFT then 3 else if c = L_RIGHT then 4 else if c = L_PAR then 304
  else if c = U_LEFT then 3 else if c = U_RIGHT then 4 else if c = U_PAR then 304
  else if c = POW then 1 else if c = U_IDX_OUT then 1 else 0

private def fPub : Assignment := fun k =>
  if k = PI_ROOT then 304 else if k = PI_LEAF_LOWER then 10
  else if k = PI_LEAF_UPPER then 20 else if k = PI_IDX_UPPER then 1 else 0

private def fTbl : List (List ℤ) :=
  [chipRow mHash [3, 4] (List.replicate 7 0)]

private def fTrace : VmTrace :=
  { rows := [fRow], pub := fPub
    tf := fun tid => match tid with | .poseidon2 => fTbl | _ => [] }

theorem fChipSound : ChipTableSound mHash (fTrace.tf .poseidon2) := by
  intro r hr
  simp only [fTrace, fTbl, List.mem_singleton] at hr
  exact ⟨[3, 4], List.replicate 7 0, by decide, by decide, hr⟩

/-- **The forged trace PROVABLY `Satisfied2`s the CURRENT `adjacencyDesc`** — the dropped last-row
ordering gates let the top children lie while every other constraint holds. -/
theorem fSat :
    Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace := by
  have hmemlog : memLog adjacencyDesc fTrace = [] := rfl
  have hmaplog : mapLog adjacencyDesc fTrace = [] := rfl
  have hF : (0 == 0) = true := rfl
  have hL : (0 + 1 == fTrace.rows.length) = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show fTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show adjacencyDesc.constraints = adjacencyConstraints from rfl] at hc
    simp only [adjacencyConstraints, pathBlock, List.cons_append, List.nil_append] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        copyWindow, Lookup.holdsAt, hF, hL] <;>
      decide
  · intro i _; trivial
  · intro i _ r hr; simp [adjacencyDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The residual `TopLevelOrdered` genuinely FAILS on the forged trace.** The lower top parent `304`
is not the authentic combine `combine mHash 0 10 0 = 1000` — so `Satisfied2` + `ChipTableSound` do NOT
force `TopLevelOrdered`. The Rung-1 residual is a REAL gap, not a proof artifact. -/
theorem cheat_not_topLevelOrdered : ¬ TopLevelOrdered mHash fTrace := by
  intro h; exact absurd h.1 (by decide)

/-- **The emit-fix hypothesis `LastRowOrdered` genuinely FAILS on the forged trace** — the lower
`leftOrderBody` is `3 - 10 = -7 ≠ 0`. So `LastRowOrdered` is NOT derivable from `Satisfied2`: it is
load-bearing, and the same fact makes the forged trace FAIL `adjacencyDescFixed`. -/
theorem cheat_not_lastRowOrdered : ¬ LastRowOrdered fTrace := by
  intro h; exact absurd h.2.1 (by decide)

/-- The forged trace jointly witnesses the load-bearing anchor: it `Satisfied2`s the CURRENT descriptor
(with a sound chip table) yet BREAKS the no-forgery residual. No `Satisfied2`+`ChipTableSound`-only
theorem could conclude `AdjacentLeavesUnderRoot` for the current emit. -/
theorem cheat_load_bearing :
    Satisfied2 mHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] fTrace
    ∧ ChipTableSound mHash (fTrace.tf .poseidon2)
    ∧ ¬ TopLevelOrdered mHash fTrace
    ∧ ¬ LastRowOrdered fTrace :=
  ⟨fSat, fChipSound, cheat_not_topLevelOrdered, cheat_not_lastRowOrdered⟩

/-! ## §8 — Axiom tripwires. -/

#assert_axioms topLevelOrdered_of_lastRowOrdered
#assert_axioms adjacency_rung2_closes
#assert_axioms lastRowOrdered_of_fix
#assert_axioms sat_of_fixed
#assert_axioms adjacency_rung2_fixed_closes
#assert_axioms topPair_no_forgery
#assert_axioms cr_carrier_realizable
#assert_axioms wtSat
#assert_axioms wtTrace_rung2_fires
#assert_axioms fSat
#assert_axioms cheat_not_topLevelOrdered
#assert_axioms cheat_not_lastRowOrdered
#assert_axioms cheat_load_bearing

end Dregg2.Circuit.Emit.AdjacencyMembershipRung2
