/-
# Dregg2.Circuit.Emit.PredicatesLtEmit — the emitted `LessThan(value, threshold)`
arithmetic-predicate descriptor (`dregg-predicate-arith-lt::threshold-v1`).

The strict `<` sibling. `value < threshold ↔ threshold − value − 1 ≥ 0`:

  * `≤`:  `DIFF = threshold − value ∈ [0, 2^29)`;
  * `<`:  `DIFF = threshold − value − 1 ∈ [0, 2^29)`.

The C6 range lookup is the load-bearing tooth (a `value ≥ threshold` wraps
`DIFF = threshold − value − 1` below zero — UNSAT).

**THE VALUE↔FACT WELD (M14).** Two Poseidon2 chip lookups force `FACT_COMMITMENT =
hash_2_to_1(hash_fact(pred, [INPUT, t1, t2]), STATE_ROOT)` over the SAME `INPUT` the comparison
bounds — col 4 and col 0 are no longer in DISJOINT constraint sets. Without it a prover proves
`value < threshold` on a value of its choosing against an unrelated honest commitment. Geometry
identical to `≥`.

`#assert_axioms` ⊆ {} on the gate lemmas. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2

namespace Dregg2.Circuit.Emit.PredicatesLtEmit

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff chipLookupTuple CHIP_RATE CHIP_OUT_LANES)

set_option autoImplicit false

def INPUT : Nat := 0
def SLOT_A : Nat := 1
def THRESHOLD : Nat := 2
def DIFF : Nat := 3
def FACT_COMMITMENT : Nat := 4
/-! The value↔fact WELD columns (identical geometry to `≥`): tie `INPUT` to the committed fact. -/
def PREDICATE_SYM : Nat := 5
def TERM1 : Nat := 6
def TERM2 : Nat := 7
def STATE_ROOT : Nat := 8
def FACT_HASH : Nat := 9
def FACT_MARK : Int := 64207
def FACTHASH_LANES : List Nat := [10, 11, 12, 13, 14, 15, 16]
def FACTCOMMIT_LANES : List Nat := [17, 18, 19, 20, 21, 22, 23]
def PRED_WIDTH : Nat := 24
def PI_THRESHOLD : Nat := 0
def PI_FACT_COMMITMENT : Nat := 1
def DIFF_BITS : Nat := 29

def c1ThresholdPin : VmConstraint2 := .base (.piBinding VmRow.first THRESHOLD PI_THRESHOLD)
def c2FactPin : VmConstraint2 := .base (.piBinding VmRow.first FACT_COMMITMENT PI_FACT_COMMITMENT)

def c3Body : EmittedExpr := .add (.var SLOT_A) (.mul (.const (-1)) (.var INPUT))
def c3SlotGate : VmConstraint2 := .base (.gate c3Body)

/-- The C5 diff-computation body `DIFF − THRESHOLD + SLOT_A + 1` (`DIFF = THRESHOLD − SLOT_A − 1`,
i.e. `DIFF = threshold − value − 1` — the strict `<` shift). -/
def c5Body : EmittedExpr :=
  .add (.add (.add (.var DIFF) (.mul (.const (-1)) (.var THRESHOLD))) (.var SLOT_A)) (.const 1)
def c5DiffGate : VmConstraint2 := .base (.gate c5Body)

def c6RangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var DIFF]⟩

/-- **THE VALUE↔FACT WELD, leg 1** — `FACT_HASH = hash_fact(pred, [INPUT, term1, term2])`. -/
def factHashLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
                     .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES⟩

/-- **THE VALUE↔FACT WELD, leg 2** — `FACT_COMMITMENT = Poseidon2(fact_hash, state_root)`. -/
def factCommitLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTuple [.var FACT_HASH, .var STATE_ROOT] FACT_COMMITMENT FACTCOMMIT_LANES⟩

/-- **`predicateLtDesc`** — the arithmetic `LessThan(value, threshold)` descriptor, welded. -/
def predicateLtDesc : EffectVmDescriptor2 :=
  { name        := "dregg-predicate-arith-lt::threshold-v1"
  , traceWidth  := PRED_WIDTH
  , piCount     := 2
  , tables      := [rangeTableDef DIFF_BITS]
  , constraints := [c1ThresholdPin, c2FactPin, c3SlotGate, c5DiffGate, c6RangeLookup,
                    factHashLookup, factCommitLookup]
  , hashSites   := []
  , ranges      := [] }

#guard emitVmJson2 predicateLtDesc ==
  "{\"name\":\"dregg-predicate-arith-lt::threshold-v1\",\"ir\":2,\"trace_width\":24,\"public_input_count\":2,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":29}],\"constraints\":[{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":2,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":4,\"pi_index\":1},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":0}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"var\",\"v\":1}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":7},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":64207},{\"t\":\"const\",\"v\":1},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":10},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":2},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":8},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23}]}],\"hash_sites\":[],\"ranges\":[]}"

theorem c3_body_zero_iff (a : Assignment) :
    c3Body.eval a = 0 ↔ a SLOT_A = a INPUT := by
  simp only [c3Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

/-- The C5 gate body is zero iff `DIFF = THRESHOLD − SLOT_A − 1` (the strict `<` diff identity). -/
theorem c5_body_zero_iff (a : Assignment) :
    c5Body.eval a = 0 ↔ a DIFF = a THRESHOLD - a SLOT_A - 1 := by
  simp only [c5Body, EmittedExpr.eval]
  constructor <;> intro h <;> omega

#guard decide (c3Body.eval (fun i => if i = SLOT_A ∨ i = INPUT then 7 else 0) = 0)
#guard decide (¬ (c3Body.eval (fun i => if i = SLOT_A then 7 else 0) = 0))
#guard decide (c5Body.eval (fun i => if i = DIFF then 59 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0)
#guard decide (¬ (c5Body.eval (fun i => if i = DIFF then 60 else if i = THRESHOLD then 100 else if i = SLOT_A then 40 else 0) = 0))

example : ([59] : List ℤ) ∈ rangeRows DIFF_BITS := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]
example : ¬ (([2 ^ 29] : List ℤ) ∈ rangeRows DIFF_BITS) := by
  rw [range_row_mem_iff]; norm_num [DIFF_BITS]

#guard predicateLtDesc.traceWidth == PRED_WIDTH
#guard predicateLtDesc.piCount == 2
#guard predicateLtDesc.constraints.length == 7
#guard predicateLtDesc.tables.length == 1
#guard (chipLookupTuple [.var PREDICATE_SYM, .var INPUT, .var TERM1, .var TERM2,
                         .const 0, .const FACT_MARK, .const 1] FACT_HASH FACTHASH_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT] FACT_COMMITMENT FACTCOMMIT_LANES).length
         == CHIP_RATE + 1 + CHIP_OUT_LANES

#assert_axioms c3_body_zero_iff
#assert_axioms c5_body_zero_iff

end Dregg2.Circuit.Emit.PredicatesLtEmit
