/-
# `Dregg2.Circuit.LogUpColumnLayout` — the COLUMN-LAYOUT MODELER: from ANY descriptor's lookup/aux
columns onto the LogUp bus arguments (A, B, α, cumsum), ∀ `d : EffectVmDescriptor2`.

## HONEST SCOPE (first sentence)

This file MODELS, for an ARBITRARY v2 descriptor, the wire `LogUpSoundness` §8 named as the
"column-layout plumbing" residual — (i) the looked-up list `A` extracted from the descriptor's
actual `.lookup` constraints evaluated on the trace (`logupA`), (ii) the table side `B` with its
multiplicity column (`logupBM`/`logupB`), (iii) the challenge `α` read from the designated
public-column slot (`logupChallenge`), and (iv) the running cumulative-sum column whose
first-row-zero / running-add / equal-close gates ARE the LogUp bus balance
(`runCol`, `logupColumnLayout_law`, `busGates_force_balance`) — and then APPLIES
`LogUpSoundness.busBalance_forces_membership` through that extraction: a balancing,
non-exceptional, pole-free extracted bus FORCES every `.lookup` constraint's `Lookup.holdsAt`
membership, for ANY `d` (`busModel_forces_lookup_holds`), assembling the whole `hbus` arm for any
graduated-shape descriptor (`hbus_of_busModels`) and in particular for the DEPLOYED `transferV3`
(`airAccept_forces_satisfied2_transferV3_busModeled` — `hbus` is no longer a bare premise there;
it is DERIVED from the extracted bus's balance + the named FS side conditions).

## What is GENERAL (∀ d) vs what stays PER-DESCRIPTOR / per-deployment

GENERAL, proved here for every descriptor:
  * the A/B/α extraction (`logupA`/`logupBM`/`logupB`/`logupChallenge`) — reads any `d`'s
    `.lookup` constraints and any trace's committed tables;
  * the CUMSUM-COLUMN LAW: the accumulator column pinned by the deployed gate shape
    (first row `0`, transition `next = local + contribution`) telescopes to the bus side, so the
    equal-close boundary IS `busBalance α (logupA …) (logupBM …)` (`logupColumnLayout_law`,
    `busGates_force_balance`);
  * the balance ⟹ membership ⟹ `Lookup.holdsAt` arrow (`busModel_forces_lookup_holds`),
    riding `busBalance_forces_membership` — the `hmem : tuple ∈ tbl` that
    `DescriptorIR2.chip_lookup_sound_N` and the range lever consume, now produced by the bus for
    any `d` (`busModel_feeds_chip_leverN`, `busModel_feeds_range_lever`).

PER-DESCRIPTOR / per-deployment (each NAMED, none silently assumed):
  * WHICH table each lookup targets and that table's FAITHFULNESS — range is STRUCTURAL
    (`t.tf .range = rangeRows bits`, argued symbolically, NEVER enumerated); the chip table is the
    Poseidon2 floor (`ChipTableSoundN permOutDeployed`) — same split `LogUpSoundness` §8 records;
  * the FS events, ε-bounded as in `LogUpSoundness` §4: `α` non-exceptional
    (`BusModelOk.nonexceptional`) and the tuple fingerprint `fp` collision-free ON THE RELEVANT
    SUPPORTS (`BusModelOk.fpFaithful` — the β-RLC fingerprint's own Schwartz–Zippel event; a
    GLOBAL injective `List ℤ → F` cannot exist into a finite field, so support-restricted is the
    honest form);
  * `Nodup` of the looked-up support (`BusModelOk.nodupA`) — repeated looked-up values are the
    higher-order-pole extension `LogUpSoundness` §8 names as provable-but-open; this file
    inherits, does not launder, that residual;
  * the Rust-assembly correspondence: that the deployed p3 bus columns are laid out as modeled
    here (challenge at the designated public slot `challengeCol d`, cumsum gates as `runCol`'s
    gate triple). This is the SAME Lean-model-to-Rust faithfulness boundary every `DescriptorIR2`
    denotation sits on — now a PINNED, checkable correspondence instead of an unmodeled wire.

## Heap safety

Everything is symbolic (`List.range`, membership by bound arithmetic). The non-vacuity teeth run
at `bits = 2` (a 4-row table); NOTHING evaluates `rangeTable 30`/`rangeRows 30`.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; sorry-free. NEW file; imports
read-only (`LogUpSoundness` untouched, per the lane charter).
-/
import Dregg2.Circuit.LogUpSoundness
import Dregg2.Circuit.AirLegsDischarged

namespace Dregg2.Circuit.LogUpColumnLayout

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmRange)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.LogUpSoundness
open Dregg2.Circuit.AirChecksSatisfied (isArith MainAirAcceptF)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.BabyBearFriField (BabyBear)

set_option autoImplicit false

variable {F : Type*} [Field F]

/-! ## §1 — THE EXTRACTION (∀ d): A, B (with multiplicity), α from a descriptor's actual columns.

`fp : List ℤ → F` is the bus's TUPLE FINGERPRINT — how one looked-up tuple rides the bus as a
single field element (the deployed p3 bus uses the β-RLC `Σ βⁱ·tupleᵢ`; the extraction is generic
in it). `embed : ℤ → F` is the scalar embedding for the challenge column (ℤ → BabyBear at the
deployment). -/

/-- The lookup payload of a v2 constraint INTO the table `tid`, if any. -/
def lookupInto? (tid : TableId) : VmConstraint2 → Option Lookup
  | .lookup l => if l.table = tid then some l else none
  | _ => none

/-- **The lookups a descriptor declares into `tid`** — read off ANY descriptor's constraint list. -/
def lookupsInto (d : EffectVmDescriptor2) (tid : TableId) : List Lookup :=
  d.constraints.filterMap (lookupInto? tid)

theorem lookupInto?_eq_some {tid : TableId} {c : VmConstraint2} {l : Lookup} :
    lookupInto? tid c = some l ↔ c = .lookup l ∧ l.table = tid := by
  cases c with
  | lookup l' =>
      simp only [lookupInto?, VmConstraint2.lookup.injEq]
      by_cases htid : l'.table = tid
      · simp only [htid, if_true, Option.some.injEq]
        constructor
        · rintro rfl; exact ⟨rfl, htid⟩
        · rintro ⟨rfl, _⟩; rfl
      · simp only [htid, if_false]
        constructor
        · intro h; exact absurd h (by simp)
        · rintro ⟨rfl, hl⟩; exact absurd hl htid
  | base c₀ => simp [lookupInto?]
  | memOp m => simp [lookupInto?]
  | mapOp m => simp [lookupInto?]
  | umemOp m => simp [lookupInto?]
  | proofBind m => simp [lookupInto?]
  | windowGate w => simp [lookupInto?]

/-- Membership in the extracted lookup family: exactly the declared `.lookup`s into `tid`. -/
theorem mem_lookupsInto {d : EffectVmDescriptor2} {tid : TableId} {l : Lookup} :
    l ∈ lookupsInto d tid ↔ VmConstraint2.lookup l ∈ d.constraints ∧ l.table = tid := by
  constructor
  · intro h
    obtain ⟨c, hc, hf⟩ := List.mem_filterMap.mp h
    obtain ⟨rfl, htid⟩ := lookupInto?_eq_some.mp hf
    exact ⟨hc, htid⟩
  · rintro ⟨hc, htid⟩
    exact List.mem_filterMap.mpr ⟨.lookup l, hc, lookupInto?_eq_some.mpr ⟨rfl, htid⟩⟩

/-- Row `i`'s looked-up tuples into `tid`: each declared lookup's column tuple, EVALUATED on the
row (the per-row face of the bus's A side). -/
def rowTuples (d : EffectVmDescriptor2) (t : VmTrace) (tid : TableId) (i : Nat) :
    List (List ℤ) :=
  (lookupsInto d tid).map (fun l => l.tuple.map (·.eval (envAt t i).loc))

/-- **All looked-up tuples** of the trace into `tid`, in row order — the multiset the bus's A side
carries. -/
def lookedTuples (d : EffectVmDescriptor2) (t : VmTrace) (tid : TableId) : List (List ℤ) :=
  (List.range t.rows.length).flatMap (rowTuples d t tid)

/-- A looked-up tuple of any row/lookup IS in the extracted A-side multiset. -/
theorem mem_lookedTuples {d : EffectVmDescriptor2} {t : VmTrace} {tid : TableId} {l : Lookup}
    (hl : l ∈ lookupsInto d tid) {i : Nat} (hi : i < t.rows.length) :
    l.tuple.map (·.eval (envAt t i).loc) ∈ lookedTuples d t tid := by
  unfold lookedTuples
  exact List.mem_flatMap.mpr
    ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨l, hl, rfl⟩⟩

/-- **`logupA d t tid`** — the bus's A side: every looked-up tuple, fingerprinted onto the bus. -/
def logupA (fp : List ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace) (tid : TableId) : List F :=
  (lookedTuples d t tid).map fp

/-- **`logupBM t tid mult`** — the bus's B side IN MULTIPLICITY FORM: the committed table's rows,
fingerprinted, zipped with the multiplicity column `mult` (the aux column the deployed LogUp table
trace carries: how often each row is looked up). -/
def logupBM (fp : List ℤ → F) (t : VmTrace) (tid : TableId) (mult : List ℕ) : List (F × ℕ) :=
  ((t.tf tid).map fp).zip mult

/-- **`logupB`** — the B side as the plain multiset (`expand` of the multiplicity form): the list
`busBalance_forces_membership` consumes. -/
def logupB (fp : List ℤ → F) (t : VmTrace) (tid : TableId) (mult : List ℕ) : List F :=
  expand (logupBM fp t tid mult)

/-- The designated challenge slot: the FS challenge is surfaced in the public column block right
past the descriptor's declared PIs. Reads ANY descriptor's own `piCount`. -/
def challengeCol (d : EffectVmDescriptor2) : Nat := d.piCount

/-- **`logupChallenge d t`** — the α: the bus challenge READ FROM the trace's designated public
slot (the column-layout binding of the FS challenge; sampled post-commit by the verifier, exposed
to the AIR here). -/
def logupChallenge (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace) : F :=
  embed (t.pub (challengeCol d))

/-- Decoding B-side membership: a fingerprint on the expanded bus B side comes from a genuine
committed-table row with a nonzero multiplicity. -/
theorem mem_logupB {fp : List ℤ → F} {t : VmTrace} {tid : TableId} {mult : List ℕ} {c : F}
    (h : c ∈ logupB fp t tid mult) : ∃ y ∈ t.tf tid, fp y = c := by
  unfold logupB expand at h
  obtain ⟨p, hp, hrep⟩ := List.mem_flatMap.mp h
  obtain ⟨-, rfl⟩ := List.mem_replicate.mp hrep
  obtain ⟨y, hy, hfy⟩ := List.mem_map.mp (List.of_mem_zip hp).1
  exact ⟨y, hy, hfy⟩

/-! ## §2 — THE CUMSUM COLUMN: the running accumulator whose gate triple IS the bus.

The deployed bus rides an auxiliary CUMULATIVE-SUM column: first row `0`, transition
`next[cum] = local[cum] + contribution`, and the boundary that the two sides' accumulators close
EQUAL. `runCol` is that column's Lean model; `runCol_zero`/`runCol_succ`/`runCol_full` are the
three gates; the telescoping laws say its close IS the bus side. -/

/-- The running (cumulative-sum) column over a contribution list: entry `j` is the sum of the
first `j` contributions — the Lean model of the deployed `cumulative_sum` aux column. -/
def runCol (c : List F) (j : Nat) : F := (c.take j).sum

/-- FIRST-ROW BOUNDARY GATE: the accumulator starts at `0`. -/
@[simp] theorem runCol_zero (c : List F) : runCol c 0 = 0 := rfl

/-- TRANSITION GATE: `next[cum] = local[cum] + contribution` — the deployed `when_transition()`
running-add. -/
theorem runCol_succ (c : List F) (j : Nat) (h : j < c.length) :
    runCol c (j + 1) = runCol c j + c[j] :=
  List.sum_take_succ c j h

/-- CLOSE: the accumulator's last entry is the whole contribution sum (telescoping). -/
theorem runCol_full (c : List F) : runCol c c.length = c.sum := by
  rw [runCol, List.take_length]

/-- **The gate triple PINS the column**: ANY column satisfying the first-row-zero and running-add
gates closes at the contribution sum — the deployed AIR's cumsum gates admit exactly `runCol`. -/
theorem gates_force_close (c : List F) (col : Nat → F)
    (h0 : col 0 = 0) (hstep : ∀ j, (h : j < c.length) → col (j + 1) = col j + c[j]) :
    col c.length = c.sum := by
  have key : ∀ j, j ≤ c.length → col j = runCol c j := by
    intro j
    induction j with
    | zero => intro _; simpa using h0
    | succ k ih =>
        intro hj
        have hk : k < c.length := Nat.lt_of_succ_le hj
        rw [hstep k hk, ih (Nat.le_of_lt hk), runCol_succ c k hk]
  rw [key c.length le_rfl, runCol_full]

/-- Row `i`'s A-side bus contribution: `Σ` over the row's lookups of `1/(α + fp tuple)` — one
accumulator step per main row. -/
def rowContribA (fp : List ℤ → F) (α : F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : TableId) (i : Nat) : F :=
  logupSum α ((rowTuples d t tid i).map fp)

/-- The A-side contribution COLUMN: one entry per main row. -/
def busColA (fp : List ℤ → F) (α : F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : TableId) : List F :=
  (List.range t.rows.length).map (rowContribA fp α d t tid)

/-- The B-side contribution COLUMN: one entry per committed table row, `m/(α + fp row)` with `m`
the row's multiplicity-column value. -/
def busColB (fp : List ℤ → F) (α : F) (t : VmTrace) (tid : TableId) (mult : List ℕ) : List F :=
  (logupBM fp t tid mult).map (fun p => p.2 • (α + p.1)⁻¹)

/-- `logupSum` distributes over a flatMap the way the per-row accumulator reads it. -/
theorem logupSum_map_flatMap {β : Type*} (α : F) (fp : List ℤ → F) (L : List β)
    (g : β → List (List ℤ)) :
    logupSum α ((L.flatMap g).map fp) = (L.map (fun x => logupSum α ((g x).map fp))).sum := by
  induction L with
  | nil => simp [logupSum]
  | cons x L ih =>
      rw [List.flatMap_cons, List.map_append, logupSum_append, List.map_cons, List.sum_cons, ih]

/-- **A-side telescoping**: the main-trace accumulator column sums to the bus's A side —
`logupSum α (logupA …)`. -/
theorem busColA_sum (fp : List ℤ → F) (α : F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : TableId) :
    (busColA fp α d t tid).sum = logupSum α (logupA fp d t tid) := by
  show (List.map (rowContribA fp α d t tid) (List.range t.rows.length)).sum
      = logupSum α (((List.range t.rows.length).flatMap (rowTuples d t tid)).map fp)
  rw [logupSum_map_flatMap]
  apply congrArg
  apply List.map_congr_left
  intro i _
  rfl

/-- **B-side telescoping**: the table-trace accumulator column sums to the bus's B side —
`logupSumM α (logupBM …)` (definitional: the column IS the multiplicity-form summand list). -/
theorem busColB_sum (fp : List ℤ → F) (α : F) (t : VmTrace) (tid : TableId) (mult : List ℕ) :
    (busColB fp α t tid mult).sum = logupSumM α (logupBM fp t tid mult) := rfl

/-- **The bus balance** over extracted arguments: lookup side = table side (multiplicity form). -/
def busBalance (α : F) (A : List F) (BM : List (F × ℕ)) : Prop :=
  logupSum α A = logupSumM α BM

/-- **THE COLUMN-LAYOUT LAW (∀ d).** For ANY descriptor `d`, ANY trace, ANY table and multiplicity
column: the two accumulator columns' equal-close boundary — the descriptor's actual bus gate —
IS the LogUp bus balance over the extracted A/B/α. The wire `LogUpSoundness` §8 called "the
running cumulative-sum column whose boundary-zero IS `logupSum α A = logupSumM α B`", now a
theorem for every `d`. -/
theorem logupColumnLayout_law (fp : List ℤ → F) (α : F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : TableId) (mult : List ℕ) :
    runCol (busColA fp α d t tid) (busColA fp α d t tid).length =
        runCol (busColB fp α t tid mult) (busColB fp α t tid mult).length ↔
      busBalance α (logupA fp d t tid) (logupBM fp t tid mult) := by
  unfold busBalance
  rw [runCol_full, runCol_full, busColA_sum, busColB_sum]

/-- **The bus GATES force the balance (∀ d).** Any pair of columns satisfying the deployed cumsum
gate shape (first-row zero + running-add over the extracted contributions) that close EQUAL yield
the LogUp bus balance over the extracted A/B/α — gates in, `busBalance` out, for any descriptor. -/
theorem busGates_force_balance (fp : List ℤ → F) (α : F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : TableId) (mult : List ℕ) (colA colB : Nat → F)
    (h0A : colA 0 = 0)
    (hstepA : ∀ j, (h : j < (busColA fp α d t tid).length) →
        colA (j + 1) = colA j + (busColA fp α d t tid)[j])
    (h0B : colB 0 = 0)
    (hstepB : ∀ j, (h : j < (busColB fp α t tid mult).length) →
        colB (j + 1) = colB j + (busColB fp α t tid mult)[j])
    (hclose : colA (busColA fp α d t tid).length = colB (busColB fp α t tid mult).length) :
    busBalance α (logupA fp d t tid) (logupBM fp t tid mult) := by
  unfold busBalance
  rw [← busColA_sum fp α d t tid, ← busColB_sum fp α t tid mult,
      ← gates_force_close _ colA h0A hstepA, ← gates_force_close _ colB h0B hstepB]
  exact hclose

/-! ## §3 — THE DISCHARGE: `busBalance_forces_membership` applied THROUGH the extraction, ∀ d. -/

variable [DecidableEq F]

/-- **The per-table bus model** — the named FS/side conditions under which the extracted bus is
sound (each the exact analog of a `LogUpSoundness` §8 floor item, none new):
pole-freeness (A and B sides), the balance itself (what the gates force —
`busGates_force_balance`), challenge non-exceptionality (the SZ ε-event), distinct looked-up
support (`Nodup` — the named multiplicity residual), and fingerprint faithfulness ON THE SUPPORTS
(the β-RLC collision ε-event). -/
structure BusModelOk (fp : List ℤ → F) (embed : ℤ → F) (d : EffectVmDescriptor2) (t : VmTrace)
    (tid : TableId) (mult : List ℕ) : Prop where
  polesA : ∀ a ∈ logupA fp d t tid, logupChallenge embed d t + a ≠ 0
  polesB : ∀ b ∈ logupB fp t tid mult, logupChallenge embed d t + b ≠ 0
  balanced : busBalance (logupChallenge embed d t) (logupA fp d t tid) (logupBM fp t tid mult)
  nonexceptional :
    logupChallenge embed d t ∉ exceptionalSet (logupA fp d t tid) (logupB fp t tid mult)
  nodupA : (logupA fp d t tid).Nodup
  fpFaithful : ∀ x ∈ lookedTuples d t tid, ∀ y ∈ t.tf tid, fp x = fp y → x = y

/-- **THE DISCHARGE (∀ d): a sound extracted bus forces every lookup's membership.** For ANY
descriptor `d`, a balancing extracted bus at the extracted non-exceptional challenge forces EVERY
declared `.lookup` into `tid` to HOLD on every row — `Lookup.holdsAt`, the exact `hbus` lookup
arm. This is `busBalance_forces_membership` applied to a real descriptor's bus via the modeler:
the tuple's fingerprint lands in `logupA` (extraction), the SZ bridge lands it in `logupB`
(membership), and fingerprint faithfulness decodes it back to a genuine committed-table row. -/
theorem busModel_forces_lookup_holds (fp : List ℤ → F) (embed : ℤ → F)
    (d : EffectVmDescriptor2) (t : VmTrace) (tid : TableId) (mult : List ℕ)
    (hok : BusModelOk fp embed d t tid mult) :
    ∀ i < t.rows.length, ∀ l ∈ lookupsInto d tid, Lookup.holdsAt t.tf (envAt t i) l := by
  intro i hi l hl
  -- the balance, in the plain-list (expanded-multiset) form the SZ bridge consumes
  have hbal' : logupSum (logupChallenge embed d t) (logupA fp d t tid)
      = logupSum (logupChallenge embed d t) (logupB fp t tid mult) := by
    have h := hok.balanced
    unfold busBalance at h
    rw [h]
    exact logupSumM_eq_expand _ _
  -- Schwartz–Zippel support containment: every A-side fingerprint is a B-side member
  have hmemF := busBalance_forces_membership hok.polesA hok.polesB hbal'
    hok.nonexceptional hok.nodupA
  -- the row's evaluated tuple is on the A side
  have htup : l.tuple.map (·.eval (envAt t i).loc) ∈ lookedTuples d t tid :=
    mem_lookedTuples hl hi
  have hfpA : fp (l.tuple.map (·.eval (envAt t i).loc)) ∈ logupA fp d t tid :=
    List.mem_map.mpr ⟨_, htup, rfl⟩
  -- …so its fingerprint is on the B side, and decodes to a genuine table row
  obtain ⟨y, hy, hfy⟩ := mem_logupB (hmemF _ hfpA)
  have heq : l.tuple.map (·.eval (envAt t i).loc) = y :=
    hok.fpFaithful _ htup y hy hfy.symm
  have htid : l.table = tid := (mem_lookupsInto.mp hl).2
  unfold Lookup.holdsAt
  rw [htid, heq]
  exact hy

/-- **The whole `hbus` arm, assembled (∀ graduated-shape d).** For any descriptor whose
non-arithmetic constraints are all `.lookup`s (the graduated shape — `transferV3` proves it via
`AirLegsDischarged.hbus_is_lookup`), per-used-table bus models discharge the FULL `hbus` premise
of `airAccept_forces_satisfied2`. -/
theorem hbus_of_busModels (hash : List ℤ → ℤ) (fp : List ℤ → F) (embed : ℤ → F)
    (d : EffectVmDescriptor2) (t : VmTrace)
    (hshape : ∀ c ∈ d.constraints, ¬ isArith c → ∃ l : Lookup, c = .lookup l)
    (hok : ∀ l : Lookup, VmConstraint2.lookup l ∈ d.constraints →
        ∃ mult : List ℕ, BusModelOk fp embed d t l.table mult) :
    ∀ i < t.rows.length, ∀ c ∈ d.constraints, ¬ isArith c →
      c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length) := by
  intro i hi c hc hA
  obtain ⟨l, rfl⟩ := hshape c hc hA
  obtain ⟨mult, hm⟩ := hok l hc
  exact busModel_forces_lookup_holds fp embed d t l.table mult hm i hi l
    (mem_lookupsInto.mpr ⟨hc, rfl⟩)

/-! ### The extracted membership feeds the EXACT consumers. -/

/-- **The bus feeds the WIDE CHIP LEVER.** For any descriptor with a wide chip lookup, the sound
extracted bus produces exactly the `hmem` premise of `chip_lookup_sound_N`, so the digest columns
carry the genuine permutation output — the hash equation, forced by the bus. -/
theorem busModel_feeds_chip_leverN (fp : List ℤ → F) (embed : ℤ → F)
    (d : EffectVmDescriptor2) (t : VmTrace) (mult : List ℕ)
    (permOut : List ℤ → List ℤ) (hSound : ChipTableSoundN permOut (t.tf .poseidon2))
    (hok : BusModelOk fp embed d t .poseidon2 mult)
    (ins : List EmittedExpr) (digestCols : List Nat) (hlen : ins.length ≤ CHIP_RATE)
    (hl : (⟨.poseidon2, chipLookupTupleN ins digestCols⟩ : Lookup) ∈ lookupsInto d .poseidon2)
    (i : Nat) (hi : i < t.rows.length) :
    digestCols.map (envAt t i).loc = permOut (ins.map (·.eval (envAt t i).loc)) := by
  have h := busModel_forces_lookup_holds fp embed d t .poseidon2 mult hok i hi _ hl
  unfold Lookup.holdsAt at h
  exact chip_lookup_sound_N permOut _ hSound (envAt t i).loc ins digestCols hlen h

/-- **The bus feeds the RANGE LEVER.** For any descriptor with a range lookup against the
STRUCTURAL range table (`rangeRows bits` — symbolic, never enumerated), the sound extracted bus
forces the `VmRange` denotation: the wire lies in `[0, 2^bits)`. -/
theorem busModel_feeds_range_lever (fp : List ℤ → F) (embed : ℤ → F)
    (d : EffectVmDescriptor2) (t : VmTrace) (mult : List ℕ)
    (bits : Nat) (hr : t.tf .range = rangeRows bits)
    (hok : BusModelOk fp embed d t .range mult)
    (w : Nat) (hl : (⟨.range, [.var w]⟩ : Lookup) ∈ lookupsInto d .range)
    (i : Nat) (hi : i < t.rows.length) :
    VmRange.holds (envAt t i) ⟨w, bits⟩ :=
  lookup_replaces_range bits t.tf hr (envAt t i) w
    (busModel_forces_lookup_holds fp embed d t .range mult hok i hi _ hl)

/-! ## §4 — THE DEPLOYED PAYOFF: `transferV3`'s `hbus` DERIVED from the modeled bus. -/

/-- **`airAccept ⟹ Satisfied2` for the DEPLOYED `transferV3`, with `hbus` MODELED.** The bare
`hbus` premise of `AirLegsDischarged.airAccept_forces_satisfied2_transferV3` is REPLACED by the
extracted per-table bus models: AIR acceptance + a sound extracted LogUp bus per used table
(+ the two aux-emptiness assembly facts) give the full `Satisfied2`. The column-layout residual of
`LogUpSoundness` §8 is DISCHARGED into the named `BusModelOk` FS conditions — no unmodeled wire
between the bus and the membership remains in Lean. -/
theorem airAccept_forces_satisfied2_transferV3_busModeled
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (t : VmTrace)
    (fp : List ℤ → F) (embed : ℤ → F)
    (hAir : MainAirAcceptF transferV3 t)
    (hok : ∀ l : Lookup, VmConstraint2.lookup l ∈ transferV3.constraints →
        ∃ mult : List ℕ, BusModelOk fp embed transferV3 t l.table mult)
    (hMemEmpty : t.tf .memory = []) (hMapEmpty : t.tf .mapOps = []) :
    Satisfied2 hash transferV3 minit mfin [] t :=
  Dregg2.Circuit.AirLegsDischarged.airAccept_forces_satisfied2_transferV3
    hash minit mfin t hAir
    (hbus_of_busModels hash fp embed transferV3 t
      (fun c hc hA => Dregg2.Circuit.AirLegsDischarged.hbus_is_lookup c hc hA) hok)
    hMemEmpty hMapEmpty

#assert_axioms mem_lookupsInto
#assert_axioms mem_lookedTuples
#assert_axioms mem_logupB
#assert_axioms runCol_succ
#assert_axioms gates_force_close
#assert_axioms busColA_sum
#assert_axioms busColB_sum
#assert_axioms logupColumnLayout_law
#assert_axioms busGates_force_balance
#assert_axioms busModel_forces_lookup_holds
#assert_axioms hbus_of_busModels
#assert_axioms busModel_feeds_chip_leverN
#assert_axioms busModel_feeds_range_lever
#assert_axioms airAccept_forces_satisfied2_transferV3_busModeled

/-! ## §5 — NON-VACUITY TEETH (both polarities), at BabyBear, on a REAL range lookup.

A tiny descriptor with ONE range lookup at `bits = 2` (a 4-row table — heap-safe; the deployed
`bits = 30` case is the SAME theorems applied symbolically). RESPECTING tooth: a genuinely
balancing bus (the value `3`, in range) satisfies `BusModelOk` and the general discharge FORCES
the real membership `[3] ∈ rangeRows 2` — a real balancing bus forcing a real membership through
the whole extraction. FORGED tooth: for an out-of-range trace (value `5`), NO multiplicity column
gives a sound bus — `BusModelOk` is UNSATISFIABLE, because the discharge would force the false
membership `[5] ∈ rangeRows 2`. -/

section Teeth

set_option maxRecDepth 8000

/-- The toy range lookup: wire 0 into the range table. -/
def toyLookup : Lookup := ⟨.range, [.var 0]⟩

/-- The toy descriptor: one main column, one range lookup — the minimal REAL lookup shape. -/
def toyD : EffectVmDescriptor2 :=
  { name := "logup_layout_toy", traceWidth := 1, piCount := 0
  , tables := [rangeTableDef 2], constraints := [.lookup toyLookup]
  , hashSites := [], ranges := [] }

/-- The toy trace family: the STRUCTURAL range table at `bits = 2`, all else empty. -/
def toyTf : TraceFamily := fun tid => if tid = .range then rangeRows 2 else []

/-- The honest trace: one row with wire 0 = `3` (in range); challenge slot carries `5`. -/
def toyT : VmTrace := { rows := [fun _ => 3], pub := fun _ => 5, tf := toyTf }

/-- The forged trace: wire 0 = `5` — OUT of `[0, 2^2)`. -/
def toyTforged : VmTrace := { rows := [fun _ => 5], pub := fun _ => 5, tf := toyTf }

/-- The toy fingerprint: a singleton tuple rides as its (embedded) value. -/
def fp0 : List ℤ → BabyBear := fun tup => ((tup.headD 0 : ℤ) : BabyBear)

/-- The scalar embedding for the challenge column. -/
def embed0 : ℤ → BabyBear := fun z => (z : BabyBear)

/-- The multiplicity column: row `[3]` looked up once, the rest zero. -/
def toyMult : List ℕ := [0, 0, 0, 1]

/-- `fp0` on a singleton IS the value's field embedding (`headD` of a singleton). -/
theorem fp0_singleton (z : ℤ) : fp0 [z] = (z : BabyBear) := rfl

/-- The extracted challenge computes to `5` (the designated public slot). -/
theorem toy_challenge : logupChallenge embed0 toyD toyT = (5 : BabyBear) := by
  show ((5 : ℤ) : BabyBear) = (5 : BabyBear); norm_num

/-- The extracted A side computes to the genuine looked-up fingerprint. -/
theorem toy_logupA : logupA fp0 toyD toyT .range = [(3 : BabyBear)] := by
  show [((3 : ℤ) : BabyBear)] = [(3 : BabyBear)]; norm_num

/-- The extracted (expanded) B side computes to the multiplicity-weighted table support. -/
theorem toy_logupB : logupB fp0 toyT .range toyMult = [(3 : BabyBear)] := by
  show [((3 : ℤ) : BabyBear)] = [(3 : BabyBear)]; norm_num

/-- The looked-up tuple multiset computes to the single honest tuple `[3]` (over ℤ — no field). -/
theorem toy_lookedTuples : lookedTuples toyD toyT .range = [[(3 : ℤ)]] := rfl

/-- The committed range table is the structural `rangeRows 2` (4 rows — heap-safe). -/
theorem toy_tf_range : toyT.tf .range = rangeRows 2 := rfl

/-- `rangeRows 2` as the explicit 4-row literal (heap-safe; NEVER done at `bits = 30`). -/
theorem toy_rangeRows2 : rangeRows 2 = [[(0 : ℤ)], [1], [2], [3]] := rfl

/-- **RESPECTING TOOTH, part 1: the honest toy bus IS a sound bus model.** Balance is
`logup_complete` (the lookups are exactly the multiplicity-expanded table); non-exceptionality is
`busNum_self` (the honest bus's exceptional set is EMPTY); poles/nodup/fingerprint-faithfulness
are concrete finite checks. -/
theorem toy_busModelOk : BusModelOk fp0 embed0 toyD toyT .range toyMult where
  polesA := by
    rw [toy_logupA]; intro a ha
    rw [List.mem_singleton] at ha; subst ha; rw [toy_challenge]; decide
  polesB := by
    rw [toy_logupB]; intro b hb
    rw [List.mem_singleton] at hb; subst hb; rw [toy_challenge]; decide
  balanced := by
    unfold busBalance
    refine logup_complete _ ?_
    rw [toy_logupA, show expand (logupBM fp0 toyT .range toyMult)
      = [(3 : BabyBear)] from toy_logupB]
  nonexceptional := by
    rw [toy_logupA, toy_logupB, exceptionalSet, busNum_self, Polynomial.roots_zero,
      Multiset.toFinset_zero]
    exact Finset.notMem_empty _
  nodupA := by rw [toy_logupA]; exact List.nodup_singleton _
  fpFaithful := by
    rw [toy_lookedTuples, toy_tf_range, toy_rangeRows2]
    intro x hx y hy hfp
    rw [List.mem_singleton] at hx; subst hx
    -- y ranges over the 4-row structural table; fp0 [3] = fp0 y forces y = [3]
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    all_goals first
      | rfl
      | (exfalso
         rw [fp0_singleton, fp0_singleton, ZMod.intCast_eq_intCast_iff'] at hfp
         revert hfp; decide)

/-- **RESPECTING TOOTH, part 2: the law FIRES.** The general discharge, at the toy bus model,
FORCES the real lookup to hold — `[3] ∈ rangeRows 2`, a genuine membership produced by a genuine
balancing bus through the full extraction. Nothing assumed. -/
theorem toy_law_fires : Lookup.holdsAt toyT.tf (envAt toyT 0) toyLookup :=
  busModel_forces_lookup_holds fp0 embed0 toyD toyT .range toyMult toy_busModelOk
    0 (by decide) toyLookup (mem_lookupsInto.mpr ⟨List.mem_cons_self .., rfl⟩)

/-- …and the forced membership IS the range meaning: wire 0 lies in `[0, 2^2)` — the `VmRange`
denotation, via the range lever the membership feeds. -/
theorem toy_range_denotation : VmRange.holds (envAt toyT 0) ⟨0, 2⟩ :=
  lookup_replaces_range 2 toyT.tf rfl (envAt toyT 0) 0 toy_law_fires

/-- **FORGED TOOTH (bites): an out-of-range trace admits NO sound bus model** — for EVERY
multiplicity column. Were one to exist, the general discharge would force `[5] ∈ rangeRows 2`,
which is false. The modeler cannot be satisfied into accepting a forged lookup. -/
theorem toy_forged_bites (mult : List ℕ) :
    ¬ BusModelOk fp0 embed0 toyD toyTforged .range mult := by
  intro h
  have hmem := busModel_forces_lookup_holds fp0 embed0 toyD toyTforged .range mult h
    0 (by decide) toyLookup (mem_lookupsInto.mpr ⟨List.mem_cons_self .., rfl⟩)
  have : ¬ Lookup.holdsAt toyTforged.tf (envAt toyTforged 0) toyLookup := by
    unfold Lookup.holdsAt
    decide
  exact this hmem

#assert_axioms toy_busModelOk
#assert_axioms toy_law_fires
#assert_axioms toy_range_denotation
#assert_axioms toy_forged_bites

end Teeth

#check @logupColumnLayout_law
#check @busGates_force_balance
#check @busModel_forces_lookup_holds
#check @airAccept_forces_satisfied2_transferV3_busModeled

end Dregg2.Circuit.LogUpColumnLayout
