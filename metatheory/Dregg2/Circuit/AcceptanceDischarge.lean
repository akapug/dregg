/-
# `Dregg2.Circuit.AcceptanceDischarge` — DISCHARGING `kernelConfigSound`'s carried STARK-side facts.

`KernelConfigSoundness.kernelConfigSound` carries `BusModelFamily`, `MapTableAssembly` and the
`ClosureReadouts`/`WitnessDecodes` per-effect readouts as NAMED hypotheses. The scope doc
(`docs/reference/CONFIG-EVOLUTION-SOUNDNESS-SCOPE.md` §Layer-1) classifies these as
"NEEDS-A-LEMMA / NEAR-FLOOR" — provable debt that should reduce into `{Poseidon2SpongeCR, FRI-LDT}`.
This module supplies the discharge lemmas that were NAMED but never present in the tree, and — for
the ones that genuinely CANNOT be discharged from acceptance — states precisely why, and which floor
they reduce to. Nothing here re-assumes the fact it discharges: every `balanced`/`mapTableFaithful`
conjunct is EXTRACTED (from the AIR gates / the `Satisfied2` witness), the FS/SZ side conditions are
the ALLOWED floor, and the genuine residuals are named, not laundered.

## What is proved (real extraction, sorry-free)

  * **`MapTableAssembly` — FULL DISCHARGE** (`mapTableAssembly_conj_of_satisfied2`,
    `mapTableAssembly_of_satisfied2Family`). `MapTableAssembly`'s conjunction
    `t.tf .memory = [] ∧ t.tf .mapOps = mapLog d t` is LITERALLY the `Satisfied2.memTableFaithful` /
    `Satisfied2.mapTableFaithful` fields (the map half is `rfl`-equal to the field; the mem half is the
    field composed with the descriptor-shape fact `memLog d t = []`). So `MapTableAssembly` carries NO
    content beyond `Satisfied2`'s own faithfulness fields + the (rfl-per-effect) shape: it is a
    PROJECTION of the acceptance witness, hence reduces into the FRI extraction that produces the
    committed trace. It is NOT a genuine assumption beyond `{FRI-LDT}`.

  * **`BusModelFamily` — FULL DISCHARGE from `Satisfied2` + a 3-conjunct FS/SZ floor** (§3b:
    `busModelOk_of_satisfied2_and_floor` / `busModelFamily_of_satisfied2_and_floor`; §2's
    gate-shaped per-run form `busModelOk_of_gates_and_floor` is retained). `BusModelOk` is
    EXISTENTIAL in the multiplicity column, and `Satisfied2` forces every looked-up tuple INTO the
    committed table — so over the HONEST multiplicities (`honestMult`) the expanded table side is a
    PERMUTATION of the extracted lookup side, `balanced` is LogUp COMPLETENESS (`logup_complete`),
    transported to the deployed cumsum equal-close boundary by the ∀-d column-layout LAW
    (`satisfied2_forces_cumsum_close`, via `logupColumnLayout_law`) and re-extracted through the
    gate triple (`busGates_force_balance`); `polesB`/`nonexceptional` come FREE on the honest bus
    (`busNum_self` — the exceptional set is EMPTY). The residual floor is EXACTLY
    {`polesA`, `nodupA`, `fpFaithful`} — named FS/SZ ε events, nothing else re-assumed.

  * **the `WitnessDecodes` readout — the MEMBERSHIP half is a genuine consequence, the readout is
    BLOCKED at the chip-table floor** (`satisfied2_forces_declared_lookup_holds`). `Satisfied2` DOES
    force every declared `.lookup`'s membership (`Lookup.holdsAt`, a projection of `rowConstraints`).
    But the per-effect `<e>TraceReadout` additionally produces a `RotTableSide`, whose
    `chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)` conjunct — "every committed chip row
    IS a genuine permutation tuple" — is NOT forced by row-local constraint satisfaction; it is the
    table-faithfulness half of `Satisfied2Faithful`, a knowledge-extraction fact of the same class as
    `FriLdtExtract`. So the readout reduces into the chip-table-soundness (Poseidon2/FRI-extraction)
    floor, not into acceptance's row satisfaction.

## Discipline
Sorry-free; no `decide`/`Fintype` over field-sized objects (BabyBear is noncomputable — no field
`decide`); NEW file; imports read-only; builds targeted
(`lake build Dregg2.Circuit.AcceptanceDischarge`). `#assert_axioms` ⊆ Lean's own.
-/
import Dregg2.Circuit.AlgoStarkSoundFanoutMemory

namespace Dregg2.Circuit.AcceptanceDischarge

open Dregg2.Circuit.DescriptorIR2
  (VmTrace EffectVmDescriptor2 envAt VmConstraint2 Lookup MapOp Satisfied2
   memLog mapLog memOpsOf mapOpsOf opRow)
open Dregg2.Circuit.AirChecksSatisfied (isArith)
open Dregg2.Circuit.FriVerifier (FriParams RecursionVk FriCore FieldArith)
open Dregg2.Circuit.FriVerifierBridge (ProofView)
open Dregg2.Circuit.CircuitSoundness (BatchPublicInputs BatchProof)
open Dregg2.Circuit.AlgoStarkSoundGeneral
  (AcceptsFull BusModelFamily memLog_eq_nil_of_lookupShape mapLog_eq_nil_of_lookupShape)
open Dregg2.Circuit.AlgoStarkSoundFanoutMemory (MapTableAssembly memOpsOf_eq_nil_of_mapShape)
open Dregg2.Circuit.LogUpColumnLayout
  (BusModelOk busGates_force_balance busModel_forces_lookup_holds busColA busColB
   logupA logupBM logupB logupChallenge lookedTuples rowTuples mem_lookupsInto
   runCol runCol_zero runCol_succ logupColumnLayout_law busBalance)
open Dregg2.Circuit.LogUpSoundness
  (exceptionalSet expand logup_complete exceptionalSet_perm_left busNum_self)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — `MapTableAssembly` : FULL DISCHARGE from the `Satisfied2` faithfulness fields.

`MapTableAssembly d` = "per accepting batch, `t.tf .memory = [] ∧ t.tf .mapOps = mapLog d t`".
The map conjunct is `Satisfied2.mapTableFaithful` verbatim; the mem conjunct is
`Satisfied2.memTableFaithful` (`t.tf .memory = (memLog d t).map opRow`) collapsed by the descriptor
shape (`memOpsOf d = []` ⟹ `memLog d t = []`). No table-assembly premise beyond `Satisfied2`. -/

/-- Under the lookup-or-mapOp shape (rfl per mapOp effect), the gathered memory log is empty on every
trace — a projection of the descriptor's declared constraints (`memOpsOf d = []`). -/
theorem memLog_eq_nil_of_mapShape (d : EffectVmDescriptor2) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m)) :
    memLog d t = [] := by
  unfold memLog
  rw [memOpsOf_eq_nil_of_mapShape d hshape]
  simp

/-- **THE DISCHARGE (per accepting run).** From a single `Satisfied2` witness for a lookup-or-mapOp
shaped descriptor, `MapTableAssembly`'s conjunction falls out with NO further premise: the map half is
the `mapTableFaithful` field, the mem half is the `memTableFaithful` field collapsed by the shape. The
`Satisfied2` witness is EXACTLY what the STARK extraction (`StarkSound`/`AlgoStarkSound`) produces from
acceptance — so this shows `MapTableAssembly` is not content beyond that extraction. -/
theorem mapTableAssembly_conj_of_satisfied2
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m))
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    t.tf .memory = [] ∧ t.tf .mapOps = mapLog d t := by
  refine ⟨?_, hsat.mapTableFaithful⟩
  rw [hsat.memTableFaithful, memLog_eq_nil_of_mapShape d t hshape]
  rfl

/-- **THE DISCHARGE (family form).** Given the `Satisfied2` extraction that acceptance ALREADY
delivers (the `StarkSound`/`AlgoStarkSound` deliverable: per accepting batch, some memory boundary and
a `Satisfied2` witness for the SAME extracted trace), the named premise `MapTableAssembly` is FREE.
This is the honest reduction the scope doc §Layer-1.4 predicts — `MapTableAssembly` bundles into the
FRI extraction; it is never an independent assumption. -/
theorem mapTableAssembly_of_satisfied2Family
    (hash : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c →
      (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m))
    (hSat : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
      ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
        Satisfied2 hash d minit mfin maddrs (tr pi π)) :
    MapTableAssembly perm RATE toNat params vk core A initState logN view tr d := by
  intro pi π hacc
  obtain ⟨minit, mfin, maddrs, hsat⟩ := hSat pi π hacc
  exact mapTableAssembly_conj_of_satisfied2 hash d minit mfin maddrs (tr pi π) hshape hsat

/-! ## §2 — `BusModelFamily` : the `balanced` conjunct EXTRACTED from the cumsum gates; residual named.

`BusModelOk` has SIX conjuncts. Exactly ONE — `balanced` — is an AIR-forced fact: it is the deployed
cumsum column's equal-close boundary, which the proven `busGates_force_balance` turns into the bus
balance (gates in, `busBalance` out — NOT re-assumed). The other five are the FS/SZ ε side conditions
(pole-freeness, challenge non-exceptionality, distinct support, β-RLC fingerprint faithfulness) — the
ALLOWED floor, the SAME epistemic class as `FriLdtExtract`'s own FS non-exceptionality. (§3b sharpens
this further FROM `Satisfied2`: there `balanced`, `polesB` AND `nonexceptional` are all DERIVED over
the honest multiplicity column, shrinking the floor to {`polesA`, `nodupA`, `fpFaithful`}.) -/

/-- **`busModelOk_of_gates_and_floor` — `BusModelOk` from {cumsum AIR gates} + {FS/SZ ε floor}.** The
`balanced` conjunct is DERIVED by `busGates_force_balance` from the deployed cumsum column gates
(first-row-zero + running-add over the extracted A/B contributions, closing equal) — the arithmetic AIR
constraints acceptance forces. The remaining conjuncts are the named FS/SZ floor. No conjunct is
re-assumed: `balanced` is EXTRACTED. This is the honest reduction of `BusModelFamily` into
`{cumsum-gate-forced balance (acceptance), Schwartz–Zippel/Poseidon2 fingerprint floor}`. -/
theorem busModelOk_of_gates_and_floor {F : Type*} [Field F] [DecidableEq F]
    (fp : List ℤ → F) (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId) (mult : List ℕ)
    (colA colB : Nat → F)
    -- the deployed cumsum AIR gates (the arithmetic constraints `Satisfied2.rowConstraints` forces):
    (h0A : colA 0 = 0)
    (hstepA : ∀ j, (h : j < (busColA fp (logupChallenge embed d t) d t tid).length) →
        colA (j + 1) = colA j + (busColA fp (logupChallenge embed d t) d t tid)[j])
    (h0B : colB 0 = 0)
    (hstepB : ∀ j, (h : j < (busColB fp (logupChallenge embed d t) t tid mult).length) →
        colB (j + 1) = colB j + (busColB fp (logupChallenge embed d t) t tid mult)[j])
    (hclose : colA (busColA fp (logupChallenge embed d t) d t tid).length
        = colB (busColB fp (logupChallenge embed d t) t tid mult).length)
    -- the ALLOWED FS/SZ ε floor (NOT `balanced` — that is extracted below):
    (hpolesA : ∀ a ∈ logupA fp d t tid, logupChallenge embed d t + a ≠ 0)
    (hpolesB : ∀ b ∈ logupB fp t tid mult, logupChallenge embed d t + b ≠ 0)
    (hnonexc : logupChallenge embed d t
        ∉ exceptionalSet (logupA fp d t tid) (logupB fp t tid mult))
    (hnodupA : (logupA fp d t tid).Nodup)
    (hfpFaithful : ∀ x ∈ lookedTuples d t tid, ∀ y ∈ t.tf tid, fp x = fp y → x = y) :
    BusModelOk fp embed d t tid mult where
  polesA := hpolesA
  polesB := hpolesB
  balanced :=
    busGates_force_balance fp (logupChallenge embed d t) d t tid mult colA colB
      h0A hstepA h0B hstepB hclose
  nonexceptional := hnonexc
  nodupA := hnodupA
  fpFaithful := hfpFaithful

/-! ### Why BARE `Satisfied2 ⟹ BusModelOk` (no floor) is NOT a theorem — and what IS (§3b).

`Satisfied2.rowConstraints` at a `.lookup l` yields ONLY the membership `Lookup.holdsAt`. Three of
`BusModelOk`'s conjuncts are NOT consequences of membership — `polesA`/`nodupA`/`fpFaithful` are
genuine FS/SZ ε events about the challenge and the β-RLC fingerprint — so `Satisfied2` ALONE cannot
produce `BusModelOk`. But the other three ARE recoverable, because `BusModelOk`'s multiplicity
column is EXISTENTIAL: over the HONEST multiplicities the expanded table side is a PERMUTATION of
the looked-up side, so `balanced` is LogUp completeness and `polesB`/`nonexceptional` ride the
permutation (`busNum_self` — the honest bus's exceptional set is EMPTY). §3b proves exactly that
(`busModelOk_of_satisfied2_and_floor`), reducing `BusModelFamily` into {the `Satisfied2` extraction}
+ {`polesA`, `nodupA`, `fpFaithful`}. The proven modeler arrow `BusModelOk ⟹ Lookup.holdsAt`
(`busModel_forces_lookup_holds`, re-exported below) is the SOUNDNESS direction the general assembler
consumes; in THAT position (the bus FORCING the lookup arm of `Satisfied2`) the balance is
acceptance-side content of the deployed p3 bus columns — assembly AUX columns, NOT `VmConstraint2`s
of any descriptor — and §3b's completeness-side discharge does not (and must not) substitute for
it. -/
theorem busModelOk_forces_membership {F : Type*} [Field F] [DecidableEq F]
    (fp : List ℤ → F) (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId) (mult : List ℕ)
    (hok : BusModelOk fp embed d t tid mult) :
    ∀ i < t.rows.length, ∀ l ∈ Dregg2.Circuit.LogUpColumnLayout.lookupsInto d tid,
      Lookup.holdsAt t.tf (envAt t i) l :=
  busModel_forces_lookup_holds fp embed d t tid mult hok

/-! ## §3 — the `WitnessDecodes`/`<e>TraceReadout` readout: MEMBERSHIP half genuine, readout BLOCKED.

The per-effect readout `<e>TraceReadout : Satisfied2 (Rfix e) ⟹ <e>Encodes` produces a `RotTableSide`
(carrying `chipTableFaithful : ChipTableSoundN permOut (t.tf .poseidon2)` — every committed chip row IS
a genuine permutation tuple). `Satisfied2` forces lookup MEMBERSHIP but NOT that table faithfulness, so
the readout is not a consequence of acceptance's row satisfaction; it reduces to the chip-table
(Poseidon2/FRI-extraction) floor. What IS a genuine consequence — the membership half — is proved
here. -/

/-- **`Satisfied2` forces every declared lookup's membership.** A pure projection of
`Satisfied2.rowConstraints` at the `.lookup` arm (`VmConstraint2.holdsAt … (.lookup l) = l.holdsAt`).
This is the extent to which the readout IS a consequence of acceptance; the readout's residual
`RotTableSide.chipTableFaithful` (`ChipTableSoundN`) lies BEYOND this — the table-faithfulness half of
`Satisfied2Faithful`, a knowledge-extraction floor, not derivable from `Satisfied2`. -/
theorem satisfied2_forces_declared_lookup_holds
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    ∀ i < t.rows.length, ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
      Lookup.holdsAt t.tf (envAt t i) l := by
  intro i hi l hl
  have h := hsat.rowConstraints i hi (VmConstraint2.lookup l) hl
  simpa [VmConstraint2.holdsAt] using h

/-! ## §3b — THE SHARPER BUS DISCHARGE: `Satisfied2 + {polesA, nodupA, fpFaithful} ⟹ BusModelOk`,
through the HONEST MULTIPLICITY COLUMN + the CUMSUM COLUMN-LAYOUT LAW.

`BusModelFamily` asks only `∃ mult, BusModelOk … mult` — the multiplicity column is the prover's
witness, not an input. For the EXTRACTED accepting trace, `Satisfied2` forces every looked-up tuple
INTO the committed table (§3's `satisfied2_forces_declared_lookup_holds`), so the HONEST
multiplicity column — the FIRST occurrence of each table fingerprint carries its full looked-up
count (`honestMult`) — makes the expanded B side a PERMUTATION of the extracted A side
(`perm_expand_honestMult`, for ANY descriptor: no per-descriptor shape fact of any kind). Then:

  * `balanced` is LogUp COMPLETENESS (`LogUpSoundness.logup_complete`) — derived, not assumed;
  * via `logupColumnLayout_law` (mpr), that balance IS the modeled cumsum columns' equal-close
    boundary — `satisfied2_forces_cumsum_close`, the CUMSUM COLUMN-LAYOUT BINDING as a ∀-d THEOREM
    (the binding needs NO floor at all: completeness has no side conditions);
  * `busGates_force_balance` re-extracts `balanced` from the gate triple + that close, so the
    discharge runs THROUGH the deployed cumsum gate shape (first-row-zero / running-add /
    equal-close), the same wire §2 extracts from;
  * `polesB` and `nonexceptional` come FREE on the honest bus: every B-side fingerprint is an
    A-side member (the permutation), and the honest bus's `busNum` SELF-CANCELS (`busNum_self`), so
    its exceptional set is EMPTY.

The residual floor is EXACTLY {`polesA`, `nodupA`, `fpFaithful`} — the named FS/SZ ε events
(challenge off the looked-up poles, distinct looked-up support, β-RLC fingerprint faithfulness on
the supports). NOTHING else: no `BusModelFamily` re-assumption, no balance assumption, no cumsum
gate assumption.

WHERE THE CUMSUM GATES ACTUALLY LIVE (the precise finding): the deployed LogUp bus's cumsum
columns are p3-ASSEMBLY aux columns — they are NOT `VmConstraint2`s in any deployed descriptor
(`d.constraints` declares the `.lookup`s; the Rust assembly builds the bus around them, the pinned
Lean-model↔Rust correspondence `LogUpColumnLayout` names in its header). So there is NO
per-descriptor rfl "cumsum shape" fact to consume and none is needed: the column-layout binding is
the ∀-d `logupColumnLayout_law`, and the close is DERIVED here from `Satisfied2` via completeness.
In the ASSEMBLER position (`algoStarkSound_of_memoryLegs`, where `BusModelOk` FORCES the lookup arm
rather than being recovered from it), the balance remains acceptance-side content of the deployed
bus argument — that direction is `busModel_forces_lookup_holds` and is untouched here. -/

section HonestBus

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The honest multiplicity column** over the table-fingerprint column `L` for the looked-up
multiset `A`: the FIRST occurrence of each table value carries its full looked-up count; later
duplicate rows carry `0`. This is the witness the existential multiplicity slot of `BusModelOk` is
FOR — the column an honest prover commits. -/
def honestMult : List F → List F → List ℕ
  | _, [] => []
  | A, v :: rest => A.count v :: honestMult (A.filter (· ≠ v)) rest

omit [Field F] [DecidableEq F] in
/-- `expand` peels one multiplicity pair into its replicate block. -/
theorem expand_cons (v : F) (m : ℕ) (B : List (F × ℕ)) :
    expand ((v, m) :: B) = List.replicate m v ++ expand B := by
  simp [expand]

omit [Field F] in
/-- The multiplicity-expansion of the honest column has EXACTLY the looked-up counts: for any
support-contained `A` (every looked-up fingerprint IS a table fingerprint — what `Satisfied2`'s
memberships deliver), the expansion of `L.zip (honestMult A L)` counts every value as `A` does. -/
theorem count_expand_honestMult (x : F) (L : List F) :
    ∀ A : List F, (∀ a ∈ A, a ∈ L) →
      (expand (L.zip (honestMult A L))).count x = A.count x := by
  induction L with
  | nil =>
      intro A h
      have hA : A = [] :=
        List.eq_nil_iff_forall_not_mem.mpr fun a ha => by simpa using h a ha
      subst hA; rfl
  | cons v rest ih =>
      intro A h
      have hsub : ∀ a ∈ A.filter (· ≠ v), a ∈ rest := by
        intro a ha
        obtain ⟨haA, hav⟩ := List.mem_filter.mp ha
        have hav' : a ≠ v := by simpa using hav
        rcases List.mem_cons.mp (h a haA) with rfl | hm
        · exact absurd rfl hav'
        · exact hm
      simp only [honestMult, List.zip_cons_cons]
      rw [expand_cons, List.count_append, ih (A.filter (· ≠ v)) hsub]
      by_cases hxv : x = v
      · subst hxv
        have h0 : (A.filter (· ≠ x)).count x = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          have := (List.mem_filter.mp hmem).2
          simp at this
        rw [List.count_replicate_self, h0, Nat.add_zero]
      · have h0 : (List.replicate (A.count v) v).count x = 0 := by
          rw [List.count_eq_zero]
          intro hmem
          exact hxv (List.eq_of_mem_replicate hmem)
        rw [h0, Nat.zero_add, List.count_filter (by simpa using hxv)]

omit [Field F] in
/-- **The honest bus is a PERMUTATION of the lookups**: whenever every looked-up fingerprint is a
table fingerprint, the honest multiplicity column's expansion is `A` up to reordering — the exact
premise of `logup_complete`. -/
theorem perm_expand_honestMult (L A : List F) (h : ∀ a ∈ A, a ∈ L) :
    A.Perm (expand (L.zip (honestMult A L))) := by
  rw [List.perm_iff_count]
  intro x
  exact (count_expand_honestMult x L A h).symm

/-- **`Satisfied2` puts every looked-up tuple IN the committed table** (∀ d, ∀ tid): the
`lookedTuples` multiset — the bus's A side before fingerprinting — is support-contained in
`t.tf tid`. A pure projection of §3's forced memberships through the extraction. -/
theorem satisfied2_lookedTuples_mem
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    ∀ x ∈ lookedTuples d t tid, x ∈ t.tf tid := by
  intro x hx
  unfold lookedTuples at hx
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
  rw [List.mem_range] at hi
  unfold rowTuples at hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
  obtain ⟨hcon, htid⟩ := mem_lookupsInto.mp hl
  have h := satisfied2_forces_declared_lookup_holds hash d minit mfin maddrs t hsat i hi l hcon
  unfold Lookup.holdsAt at h
  rwa [htid] at h

omit [Field F] in
/-- The extracted A side rides the honest multiplicity column as a genuine LogUp permutation:
`logupA` is a permutation of the expanded `logupBM` at `honestMult`. The single bridge between
`Satisfied2`'s memberships and the bus algebra. -/
theorem satisfied2_honest_bus_perm
    (fp : List ℤ → F) (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    (logupA fp d t tid).Perm
      (expand (logupBM fp t tid (honestMult (logupA fp d t tid) ((t.tf tid).map fp)))) := by
  have hmemL : ∀ a ∈ logupA fp d t tid, a ∈ (t.tf tid).map fp := by
    intro a ha
    unfold logupA at ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact List.mem_map.mpr
      ⟨x, satisfied2_lookedTuples_mem hash d minit mfin maddrs t tid hsat x hx, rfl⟩
  show (logupA fp d t tid).Perm
    (expand (((t.tf tid).map fp).zip (honestMult (logupA fp d t tid) ((t.tf tid).map fp))))
  exact perm_expand_honestMult _ _ hmemL

/-- **THE CUMSUM COLUMN-LAYOUT BINDING, DERIVED (∀ d, NO floor).** For the extracted accepting
trace of ANY descriptor, the modeled cumsum/bus columns over the extracted A/B/α CLOSE EQUAL at
the honest multiplicity column — the deployed equal-close boundary gate, produced from
`Satisfied2` alone through `logup_complete` + `logupColumnLayout_law` (completeness needs no side
conditions). This is the binding §2 named as the residual "which columns carry the running-add":
it is a THEOREM for every `d`, not a per-descriptor shape fact. -/
theorem satisfied2_forces_cumsum_close
    (fp : List ℤ → F) (embed : ℤ → F)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId)
    (hsat : Satisfied2 hash d minit mfin maddrs t) :
    ∃ mult : List ℕ,
      runCol (busColA fp (logupChallenge embed d t) d t tid)
          (busColA fp (logupChallenge embed d t) d t tid).length
        = runCol (busColB fp (logupChallenge embed d t) t tid mult)
            (busColB fp (logupChallenge embed d t) t tid mult).length := by
  refine ⟨honestMult (logupA fp d t tid) ((t.tf tid).map fp), ?_⟩
  exact (logupColumnLayout_law fp (logupChallenge embed d t) d t tid _).mpr
    (logup_complete _ (satisfied2_honest_bus_perm fp hash d minit mfin maddrs t tid hsat))

/-- **THE SHARPER DISCHARGE (per accepting run): `Satisfied2` + the 3-conjunct FS/SZ floor ⟹
`BusModelOk`.** The multiplicity witness is `honestMult`; `balanced` is routed THROUGH the deployed
cumsum gate shape (`busGates_force_balance` on the `runCol` columns, whose equal-close is the
derived binding above); `polesB` and `nonexceptional` are derived from the permutation
(`busNum_self`: the honest bus's exceptional set is EMPTY). Only `polesA`/`nodupA`/`fpFaithful` —
the named FS/SZ ε floor — remain as hypotheses. Nothing is re-assumed. -/
theorem busModelOk_of_satisfied2_and_floor
    (fp : List ℤ → F) (embed : ℤ → F)
    (hash : List ℤ → ℤ) (d : EffectVmDescriptor2)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (tid : Dregg2.Circuit.DescriptorIR2.TableId)
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    -- the ALLOWED FS/SZ ε floor — everything else is DERIVED:
    (hpolesA : ∀ a ∈ logupA fp d t tid, logupChallenge embed d t + a ≠ 0)
    (hnodupA : (logupA fp d t tid).Nodup)
    (hfpFaithful : ∀ x ∈ lookedTuples d t tid, ∀ y ∈ t.tf tid, fp x = fp y → x = y) :
    ∃ mult : List ℕ, BusModelOk fp embed d t tid mult := by
  refine ⟨honestMult (logupA fp d t tid) ((t.tf tid).map fp), ?_⟩
  have hperm := satisfied2_honest_bus_perm fp hash d minit mfin maddrs t tid hsat
  -- the balance = completeness over the honest multiplicities …
  have hbal := logup_complete (logupChallenge embed d t) hperm
  -- … equivalently (the column-layout LAW, mpr): the modeled cumsum columns close equal —
  have hclose := (logupColumnLayout_law fp (logupChallenge embed d t) d t tid
    (honestMult (logupA fp d t tid) ((t.tf tid).map fp))).mpr hbal
  exact
    { polesA := hpolesA
      -- every B-side fingerprint is an A-side member (the permutation) — polesA covers it:
      polesB := fun b hb => hpolesA b (hperm.mem_iff.mpr hb)
      -- … and the gate triple re-extracts the balance from that close (`§2`'s wire, satisfied):
      balanced := busGates_force_balance fp (logupChallenge embed d t) d t tid
        (honestMult (logupA fp d t tid) ((t.tf tid).map fp))
        (runCol (busColA fp (logupChallenge embed d t) d t tid))
        (runCol (busColB fp (logupChallenge embed d t) t tid
          (honestMult (logupA fp d t tid) ((t.tf tid).map fp))))
        (runCol_zero _) (fun j h => runCol_succ _ j h)
        (runCol_zero _) (fun j h => runCol_succ _ j h) hclose
      nonexceptional := by
        show logupChallenge embed d t
          ∉ exceptionalSet (logupA fp d t tid)
              (expand (logupBM fp t tid (honestMult (logupA fp d t tid) ((t.tf tid).map fp))))
        rw [exceptionalSet_perm_left hperm, exceptionalSet, busNum_self,
          Polynomial.roots_zero, Multiset.toFinset_zero]
        exact Finset.notMem_empty _
      nodupA := hnodupA
      fpFaithful := hfpFaithful }

/-- **THE DISCHARGE (family form): `BusModelFamily` from the `Satisfied2` extraction + the
3-conjunct FS/SZ floor.** Given the extraction acceptance ALREADY delivers (per accepting batch, a
`Satisfied2` witness for the extracted trace — the same deliverable
`mapTableAssembly_of_satisfied2Family` consumes) plus the named per-lookup FS/SZ ε floor, the named
premise `BusModelFamily` is DERIVED: no free-standing bus-family assumption remains. This is the
honest reduction of `BusModelFamily` into {the FRI extraction, `polesA`/`nodupA`/`fpFaithful`}. -/
theorem busModelFamily_of_satisfied2_and_floor
    (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat) (view : ProofView)
    (tr : BatchPublicInputs → BatchProof → VmTrace) (d : EffectVmDescriptor2)
    (hSat : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
      ∃ (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ),
        Satisfied2 hash d minit mfin maddrs (tr pi π))
    (hfloor : ∀ (pi : BatchPublicInputs) (π : BatchProof),
      AcceptsFull perm RATE toNat params vk core A initState logN view pi π →
      ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
        (∀ a ∈ logupA fp d (tr pi π) l.table,
            logupChallenge embed d (tr pi π) + a ≠ 0) ∧
        (logupA fp d (tr pi π) l.table).Nodup ∧
        (∀ x ∈ lookedTuples d (tr pi π) l.table, ∀ y ∈ (tr pi π).tf l.table,
            fp x = fp y → x = y)) :
    BusModelFamily fp embed perm RATE toNat params vk core A initState logN view tr d := by
  intro pi π hacc l hl
  obtain ⟨minit, mfin, maddrs, hsat⟩ := hSat pi π hacc
  obtain ⟨hpA, hnd, hfp⟩ := hfloor pi π hacc l hl
  exact busModelOk_of_satisfied2_and_floor fp embed hash d minit mfin maddrs (tr pi π) l.table
    hsat hpA hnd hfp

end HonestBus

/-! ## §4 — NON-VACUITY: the discharges FIRE on concrete descriptors (extraction, not assumption). -/

section NonVacuity

/-- A concrete mapOp-declaring descriptor (guard column 1, root/key/value/newRoot on cols 2/3/4/2):
`mapOpsOf` is NON-empty, so the lookup-or-mapOp shape is genuine (not the trivial all-empty case). -/
def dMapNV : EffectVmDescriptor2 :=
  { name := "acceptance-discharge-mapnv", traceWidth := 5, piCount := 0
  , tables := []
  , constraints := [VmConstraint2.mapOp
      { guard := EmittedExpr.var 1, root := fun _ => EmittedExpr.var 2, key := EmittedExpr.var 3
      , value := EmittedExpr.var 4, newRoot := fun _ => EmittedExpr.var 2
      , op := Dregg2.Circuit.DescriptorIR2.MapOpKind.read }]
  , hashSites := [], ranges := [] }

/-- The descriptor genuinely declares a map op (the shape is not vacuously all-lookup). -/
theorem dMapNV_has_mapOp : mapOpsOf dMapNV ≠ [] := by
  simp [mapOpsOf, dMapNV]

/-- The lookup-or-mapOp shape holds for `dMapNV` (the single non-arith constraint is the `.mapOp`). -/
theorem dMapNV_shape : ∀ c ∈ dMapNV.constraints, ¬ isArith c →
    (∃ l : Lookup, c = VmConstraint2.lookup l) ∨ (∃ m : MapOp, c = VmConstraint2.mapOp m) := by
  intro c hc _
  simp only [dMapNV, List.mem_singleton] at hc
  exact Or.inr ⟨_, hc⟩

/-- **The map-table discharge FIRES on a concrete mapOp descriptor.** From ANY `Satisfied2` witness at
`dMapNV`, the `MapTableAssembly` conjunction is produced — the extraction runs on a genuine map-shaped
descriptor, and the map conjunct is definitionally the witness's own `mapTableFaithful` field. -/
theorem mapTableAssembly_fires
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash dMapNV minit mfin maddrs t) :
    t.tf .memory = [] ∧ t.tf .mapOps = mapLog dMapNV t :=
  mapTableAssembly_conj_of_satisfied2 hash dMapNV minit mfin maddrs t dMapNV_shape hsat

/-- **The extraction is the identity on the faithfulness field** (extraction, not fabrication): the map
conjunct the discharge returns is LITERALLY the `Satisfied2.mapTableFaithful` field. -/
theorem mapTableAssembly_extracts_the_field
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash dMapNV minit mfin maddrs t) :
    (mapTableAssembly_fires hash minit mfin maddrs t hsat).2 = hsat.mapTableFaithful :=
  rfl

/-- **The bus discharge FIRES on the deployed LogUp toy** (`LogUpColumnLayout` §5, a REAL range
lookup at BabyBear): `busModelOk_of_gates_and_floor` rebuilds `BusModelOk` on the toy bus, with
`balanced` routed THROUGH `busGates_force_balance` from the honest cumsum (`runCol`) columns — the
close is the toy's proven balance via `logupColumnLayout_law`, the four ε conjuncts are the toy's own
FS/SZ side conditions. The `balanced` conjunct is genuinely gate-extracted, not assumed. -/
theorem busModelOk_fires :
    BusModelOk Dregg2.Circuit.LogUpColumnLayout.fp0 Dregg2.Circuit.LogUpColumnLayout.embed0
      Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range
      Dregg2.Circuit.LogUpColumnLayout.toyMult := by
  have htoy := Dregg2.Circuit.LogUpColumnLayout.toy_busModelOk
  refine busModelOk_of_gates_and_floor
    Dregg2.Circuit.LogUpColumnLayout.fp0 Dregg2.Circuit.LogUpColumnLayout.embed0
    Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range
    Dregg2.Circuit.LogUpColumnLayout.toyMult
    (runCol (busColA Dregg2.Circuit.LogUpColumnLayout.fp0
      (logupChallenge Dregg2.Circuit.LogUpColumnLayout.embed0
        Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT)
      Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range))
    (runCol (busColB Dregg2.Circuit.LogUpColumnLayout.fp0
      (logupChallenge Dregg2.Circuit.LogUpColumnLayout.embed0
        Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT)
      Dregg2.Circuit.LogUpColumnLayout.toyT .range Dregg2.Circuit.LogUpColumnLayout.toyMult))
    (runCol_zero _) (fun j h => runCol_succ _ j h)
    (runCol_zero _) (fun j h => runCol_succ _ j h)
    ?_ htoy.polesA htoy.polesB htoy.nonexceptional htoy.nodupA htoy.fpFaithful
  -- the close = the toy's proven balance, through the column-layout law (gates ↔ balance)
  exact (logupColumnLayout_law Dregg2.Circuit.LogUpColumnLayout.fp0
    (logupChallenge Dregg2.Circuit.LogUpColumnLayout.embed0
      Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT)
    Dregg2.Circuit.LogUpColumnLayout.toyD Dregg2.Circuit.LogUpColumnLayout.toyT .range
    Dregg2.Circuit.LogUpColumnLayout.toyMult).mpr htoy.balanced

/-! ### §4b — the SHARPER discharge fires END-TO-END FROM `Satisfied2` (the §3b teeth). A genuine
`Satisfied2` witness is built for the deployed LogUp toy (`LogUpColumnLayout` §5 — a REAL range
lookup at BabyBear), and `busModelOk_of_satisfied2_and_floor` runs on it: the honest-multiplicity
bus is PRODUCED (balance through the cumsum gate triple), the derived cumsum close is PRODUCED, and
the produced bus feeds the ∀-d soundness discharge back to the real membership. The floor conjuncts
consumed are the toy's own PROVEN concrete facts (`toy_busModelOk`'s fields) — the whole chain is
assumption-free. -/

open Dregg2.Circuit.LogUpColumnLayout (toyD toyT toyTf toyLookup fp0 embed0 toy_busModelOk)

/-- The toy's non-arith constraints are all lookups (its single constraint IS the range lookup). -/
theorem toyD_shape : ∀ c ∈ toyD.constraints, ¬ isArith c →
    ∃ l : Lookup, c = VmConstraint2.lookup l := by
  intro c hc _
  exact ⟨toyLookup, by simpa [toyD] using hc⟩

/-- The toy's gathered memory log is empty (no memOps declared). -/
theorem toy_memLog : memLog toyD toyT = [] :=
  memLog_eq_nil_of_lookupShape toyD toyT toyD_shape

/-- The toy's gathered map-ops log is empty (no mapOps declared). -/
theorem toy_mapLog : mapLog toyD toyT = [] :=
  mapLog_eq_nil_of_lookupShape toyD toyT toyD_shape

set_option maxRecDepth 8000 in
/-- **A GENUINE `Satisfied2` witness for the LogUp toy** (any `hash` — the toy declares no hash
sites): the single range lookup HOLDS on the single row (`[3] ∈ rangeRows 2`, a concrete
membership over ℤ), and all memory legs are the empty-log structurals. -/
theorem toy_satisfied2 (hash : List ℤ → ℤ) :
    Satisfied2 hash toyD (fun _ => 0) (fun _ => (0, 0)) [] toyT where
  rowConstraints := by
    intro i hi c hc
    rw [show toyT.rows.length = 1 from rfl] at hi
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain rfl : c = VmConstraint2.lookup toyLookup := by simpa [toyD] using hc
    simp only [VmConstraint2.holdsAt]
    unfold Lookup.holdsAt
    decide
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp [toyD] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by intro op hop; rw [toy_memLog] at hop; simp at hop
  memDisciplined := by rw [toy_memLog]; trivial
  memBalanced := by
    rw [toy_memLog]
    simp [MemoryChecking.MemCheck, MemoryChecking.initSet, MemoryChecking.finalSet,
      MemoryChecking.readSet, MemoryChecking.writeSetFrom, MemoryChecking.boundarySet]
  memTableFaithful := by rw [toy_memLog]; rfl
  mapTableFaithful := by rw [toy_mapLog]; rfl

/-- **THE SHARPER DISCHARGE FIRES**: from the genuine `Satisfied2` witness + the toy's own proven
FS/SZ floor facts, `busModelOk_of_satisfied2_and_floor` PRODUCES a sound bus model — `balanced`
gate-extracted through the derived cumsum close, `polesB`/`nonexceptional` derived from the honest
permutation. End-to-end from `Satisfied2`; nothing assumed. -/
theorem busModelOk_fires_from_satisfied2 (hash : List ℤ → ℤ) :
    ∃ mult : List ℕ, BusModelOk fp0 embed0 toyD toyT .range mult :=
  busModelOk_of_satisfied2_and_floor fp0 embed0 hash toyD (fun _ => 0) (fun _ => (0, 0)) []
    toyT .range (toy_satisfied2 hash)
    toy_busModelOk.polesA toy_busModelOk.nodupA toy_busModelOk.fpFaithful

/-- **The derived cumsum column-layout binding FIRES** (no floor at all): the toy's modeled
cumsum/bus columns close equal, straight from `Satisfied2` through the law. -/
theorem toy_cumsum_close_fires (hash : List ℤ → ℤ) :
    ∃ mult : List ℕ,
      runCol (busColA fp0 (logupChallenge embed0 toyD toyT) toyD toyT .range)
          (busColA fp0 (logupChallenge embed0 toyD toyT) toyD toyT .range).length
        = runCol (busColB fp0 (logupChallenge embed0 toyD toyT) toyT .range mult)
            (busColB fp0 (logupChallenge embed0 toyD toyT) toyT .range mult).length :=
  satisfied2_forces_cumsum_close fp0 embed0 hash toyD (fun _ => 0) (fun _ => (0, 0)) []
    toyT .range (toy_satisfied2 hash)

/-- …and the PRODUCED bus feeds the ∀-d soundness discharge back to the REAL membership: the
whole loop `Satisfied2 ⟹ bus ⟹ Lookup.holdsAt` runs on the concrete toy. -/
theorem toy_bus_discharge_end_to_end (hash : List ℤ → ℤ) :
    Lookup.holdsAt toyT.tf (envAt toyT 0) toyLookup := by
  obtain ⟨mult, hok⟩ := busModelOk_fires_from_satisfied2 hash
  exact busModel_forces_lookup_holds fp0 embed0 toyD toyT .range mult hok 0 (by decide)
    toyLookup (mem_lookupsInto.mpr ⟨List.mem_cons_self .., rfl⟩)

end NonVacuity

/-! ## Kernel-clean (0 sorries; axiom floor is Lean's own). -/

#assert_axioms mapTableAssembly_conj_of_satisfied2
#assert_axioms mapTableAssembly_of_satisfied2Family
#assert_axioms busModelOk_of_gates_and_floor
#assert_axioms busModelOk_forces_membership
#assert_axioms satisfied2_forces_declared_lookup_holds
#assert_axioms perm_expand_honestMult
#assert_axioms satisfied2_lookedTuples_mem
#assert_axioms satisfied2_honest_bus_perm
#assert_axioms satisfied2_forces_cumsum_close
#assert_axioms busModelOk_of_satisfied2_and_floor
#assert_axioms busModelFamily_of_satisfied2_and_floor
#assert_axioms mapTableAssembly_fires
#assert_axioms busModelOk_fires
#assert_axioms toy_satisfied2
#assert_axioms busModelOk_fires_from_satisfied2
#assert_axioms toy_cumsum_close_fires
#assert_axioms toy_bus_discharge_end_to_end

end Dregg2.Circuit.AcceptanceDischarge
