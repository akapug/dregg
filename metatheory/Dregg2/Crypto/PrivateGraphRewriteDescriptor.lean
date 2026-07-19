/-
# Dregg2.Crypto.PrivateGraphRewriteDescriptor

Lean-authored IR2 for one bounded private graph-rewrite step.  Rust is only a
witness filler for this object.  The public ABI is

  [domain, session, version, shape,
   ruleset_root8, old_graph_root8, new_graph_root8].

The old/new root octets are adjacent history endpoints.  The hidden relation
carries an arbitrary bounded rule (two LHS + two RHS slots), four-variable
injective substitution, two preserved context slots, and independent six-step
controlled-swap networks for the old and new graph orders.  The fixed adjacent
swap schedule `[01,12,23,01,12,01]` realizes every permutation of four slots;
the AIR proves each swap/copy, rather than trusting a host permutation.
-/
import Dregg2.Crypto.PrivateGraphRewrite
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer
import Dregg2.Exec.CircuitEmit

namespace Dregg2.Crypto.PrivateGraphRewriteDescriptor

open Dregg2.Crypto.PrivateGraphRewrite
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
   ChipTableSoundN chipLookupTupleN chip_lookup_sound_N emitVmJson2
   rangeTableDef)

set_option autoImplicit false
set_option maxRecDepth 10000

def v (col : Nat) : EmittedExpr := .var col
def c (z : Int) : EmittedExpr := .const z
def add (x y : EmittedExpr) : EmittedExpr := .add x y
def mul (x y : EmittedExpr) : EmittedExpr := .mul x y
def neg (x : EmittedExpr) : EmittedExpr := mul (c (-1)) x
def sub (x y : EmittedExpr) : EmittedExpr := add x (neg y)
def sumE (xs : List EmittedExpr) : EmittedExpr := xs.foldr add (c 0)
def binaryBody (col : Nat) : EmittedExpr := mul (v col) (sub (v col) (c 1))
def eqBody (left right : EmittedExpr) : EmittedExpr := sub left right

def DOMAIN : Nat := 0
def SESSION : Nat := 1
def VERSION : Nat := 2
def SHAPE : Nat := 3
def RULE_SLOT : Nat := 4
def OLD_BLIND_BASE : Nat := 5
def NEW_BLIND_BASE : Nat := 9
def RULE_BLIND_BASE : Nat := 13
def SIBLING_BASE : Nat := 17
def SIGMA_BASE : Nat := 25
def SIGMA_INV_BASE : Nat := 29
def RULE_BASE : Nat := 35
def CONTEXT_BASE : Nat := 67
def OLD_STAGE_BASE : Nat := 75
def NEW_STAGE_BASE : Nat := 187
def OLD_SWAP_BASE : Nat := 299
def NEW_SWAP_BASE : Nat := 305
def OLD_CORE_BASE : Nat := 311
def OLD_ROOT_BASE : Nat := 319
def NEW_CORE_BASE : Nat := 327
def NEW_ROOT_BASE : Nat := 335
def RULE_CORE_BASE : Nat := 343
def RULE_LEAF_BASE : Nat := 351
def RULESET_ROOT_BASE : Nat := 359
def TRACE_WIDTH : Nat := 367
def PI_COUNT : Nat := 28

def blindCol (base lane : Nat) : Nat := base + lane
def sigmaCol (i : Nat) : Nat := SIGMA_BASE + i
def sigmaInvCol (pair : Nat) : Nat := SIGMA_INV_BASE + pair

def ruleCol (slot field : Nat) : Nat := RULE_BASE + 8 * slot + field
def R_ACTIVE : Nat := 0
def R_LABEL : Nat := 1
def R_SRC : Nat := 2
def R_DST : Nat := 3
def R_SRC_B0 : Nat := 4
def R_SRC_B1 : Nat := 5
def R_DST_B0 : Nat := 6
def R_DST_B1 : Nat := 7

def contextCol (slot field : Nat) : Nat := CONTEXT_BASE + 4 * slot + field
def E_ACTIVE : Nat := 0
def E_LABEL : Nat := 1
def E_SRC : Nat := 2
def E_DST : Nat := 3

def stageCol (base stage slot field : Nat) : Nat :=
  base + 16 * stage + 4 * slot + field

def oldStage := stageCol OLD_STAGE_BASE
def newStage := stageCol NEW_STAGE_BASE

def swapPair : Fin 6 → Fin 4 × Fin 4
  | 0 => (0, 1)
  | 1 => (1, 2)
  | 2 => (2, 3)
  | 3 => (0, 1)
  | 4 => (1, 2)
  | 5 => (0, 1)

def ruleFieldExprs : List EmittedExpr :=
  (List.range 4).flatMap fun slot =>
    (List.range 4).map fun field => v (ruleCol slot field)

def stageFieldExprs (base : Nat) (stage : Nat) : List EmittedExpr :=
  (List.range 4).flatMap fun slot =>
    (List.range 4).map fun field => v (stageCol base stage slot field)

def digestExprs (base : Nat) : List EmittedExpr :=
  (List.range 8).map fun lane => v (base + lane)

def blindExprs (base : Nat) : List EmittedExpr :=
  (List.range 4).map fun lane => v (base + lane)

def graphRootInputExprs (coreBase blindBase : Nat) (sideTag : Int) : List EmittedExpr :=
  digestExprs coreBase ++ blindExprs blindBase ++
    [v DOMAIN, v SESSION, v VERSION, c sideTag]

def ruleLeafInputExprs : List EmittedExpr :=
  digestExprs RULE_CORE_BASE ++ blindExprs RULE_BLIND_BASE ++
    [v DOMAIN, v VERSION, v SHAPE, v RULE_SLOT]

def choose (bit zero one : EmittedExpr) : EmittedExpr :=
  add zero (mul bit (sub one zero))

def rulesetInputExprs : List EmittedExpr :=
  ((List.range 8).map fun lane =>
      choose (v RULE_SLOT) (v (RULE_LEAF_BASE + lane)) (v (SIBLING_BASE + lane))) ++
  ((List.range 8).map fun lane =>
      choose (v RULE_SLOT) (v (SIBLING_BASE + lane)) (v (RULE_LEAF_BASE + lane)))

def graphCoreLookup (stageBase outBase : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN (stageFieldExprs stageBase 6) (List.range 8 |>.map (outBase + ·))⟩

def hashLookup (inputs : List EmittedExpr) (outBase : Nat) : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2,
    chipLookupTupleN inputs (List.range 8 |>.map (outBase + ·))⟩

def hashLookups : List VmConstraint2 :=
  [ graphCoreLookup OLD_STAGE_BASE OLD_CORE_BASE
  , hashLookup (graphRootInputExprs OLD_CORE_BASE OLD_BLIND_BASE OLD_SIDE_TAG) OLD_ROOT_BASE
  , graphCoreLookup NEW_STAGE_BASE NEW_CORE_BASE
  , hashLookup (graphRootInputExprs NEW_CORE_BASE NEW_BLIND_BASE NEW_SIDE_TAG) NEW_ROOT_BASE
  , hashLookup ruleFieldExprs RULE_CORE_BASE
  , hashLookup ruleLeafInputExprs RULE_LEAF_BASE
  , hashLookup rulesetInputExprs RULESET_ROOT_BASE ]

def bitCols : List Nat :=
  [RULE_SLOT] ++
  ((List.range 4).map fun slot => ruleCol slot R_ACTIVE) ++
  ((List.range 4).flatMap fun slot =>
    [ruleCol slot R_SRC_B0, ruleCol slot R_SRC_B1,
     ruleCol slot R_DST_B0, ruleCol slot R_DST_B1]) ++
  ((List.range 2).map fun slot => contextCol slot E_ACTIVE) ++
  ((List.range 7).flatMap fun stage =>
    (List.range 4).map fun slot => oldStage stage slot E_ACTIVE) ++
  ((List.range 7).flatMap fun stage =>
    (List.range 4).map fun slot => newStage stage slot E_ACTIVE) ++
  (List.range 6 |>.map (OLD_SWAP_BASE + ·)) ++
  (List.range 6 |>.map (NEW_SWAP_BASE + ·))

def binaryBodies : List EmittedExpr := bitCols.map binaryBody

def ruleVarBodies : List EmittedExpr :=
  (List.range 4).flatMap fun slot =>
    [ eqBody (v (ruleCol slot R_SRC))
        (add (v (ruleCol slot R_SRC_B0)) (mul (c 2) (v (ruleCol slot R_SRC_B1))))
    , eqBody (v (ruleCol slot R_DST))
        (add (v (ruleCol slot R_DST_B0)) (mul (c 2) (v (ruleCol slot R_DST_B1)))) ]

def paddingBodies : List EmittedExpr :=
  ((List.range 4).flatMap fun slot =>
    (List.range 3).map fun k =>
      mul (sub (c 1) (v (ruleCol slot R_ACTIVE))) (v (ruleCol slot (1 + k)))) ++
  ((List.range 2).flatMap fun slot =>
    (List.range 3).map fun k =>
      mul (sub (c 1) (v (contextCol slot E_ACTIVE))) (v (contextCol slot (1 + k))))

def sigmaPairs : List (Nat × Nat) := [(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def sigmaInjectiveBodies : List EmittedExpr :=
  sigmaPairs.zipIdx.map fun (pair, idx) =>
    sub (mul (sub (v (sigmaCol pair.1)) (v (sigmaCol pair.2))) (v (sigmaInvCol idx))) (c 1)

def lhsNonemptyBody : EmittedExpr :=
  mul (sub (c 1) (v (ruleCol 0 R_ACTIVE)))
      (sub (c 1) (v (ruleCol 1 R_ACTIVE)))

def muxSigma (slot : Nat) (src : Bool) : EmittedExpr :=
  let b0 := v (ruleCol slot (if src then R_SRC_B0 else R_DST_B0))
  let b1 := v (ruleCol slot (if src then R_SRC_B1 else R_DST_B1))
  let low := choose b0 (v (sigmaCol 0)) (v (sigmaCol 1))
  let high := choose b0 (v (sigmaCol 2)) (v (sigmaCol 3))
  choose b1 low high

def sourceBodies (stageBase : Nat) (rhs : Bool) : List EmittedExpr :=
  let ruleOff := if rhs then 2 else 0
  ((List.range 2).flatMap fun slot =>
    (List.range 4).map fun field =>
      eqBody (v (stageCol stageBase 0 slot field)) (v (contextCol slot field))) ++
  ((List.range 2).flatMap fun slot =>
    [ eqBody (v (stageCol stageBase 0 (2 + slot) E_ACTIVE))
        (v (ruleCol (ruleOff + slot) R_ACTIVE))
    , eqBody (v (stageCol stageBase 0 (2 + slot) E_LABEL))
        (v (ruleCol (ruleOff + slot) R_LABEL))
    , eqBody (v (stageCol stageBase 0 (2 + slot) E_SRC))
        (muxSigma (ruleOff + slot) true)
    , eqBody (v (stageCol stageBase 0 (2 + slot) E_DST))
        (muxSigma (ruleOff + slot) false) ])

def swapStageBodies (stageBase swapBase : Nat) (stage : Fin 6) : List EmittedExpr :=
  let pair := swapPair stage
  let bit := v (swapBase + stage.val)
  (List.range 4).flatMap fun slot =>
    (List.range 4).map fun field =>
      let source := v (stageCol stageBase stage.val slot field)
      let partner :=
        if slot = pair.1.val then v (stageCol stageBase stage.val pair.2.val field)
        else if slot = pair.2.val then v (stageCol stageBase stage.val pair.1.val field)
        else source
      eqBody (v (stageCol stageBase (stage.val + 1) slot field)) (choose bit source partner)

def swapBodies (stageBase swapBase : Nat) : List EmittedExpr :=
  (List.ofFn fun stage : Fin 6 => swapStageBodies stageBase swapBase stage).flatten

def metadataBodies : List EmittedExpr :=
  [eqBody (v VERSION) (c PROTOCOL_VERSION), eqBody (v SHAPE) (c SHAPE_ID)]

def semanticBodies : List EmittedExpr :=
  metadataBodies ++ binaryBodies ++ ruleVarBodies ++ paddingBodies ++
  sigmaInjectiveBodies ++ [lhsNonemptyBody] ++
  sourceBodies OLD_STAGE_BASE false ++ sourceBodies NEW_STAGE_BASE true ++
  swapBodies OLD_STAGE_BASE OLD_SWAP_BASE ++ swapBodies NEW_STAGE_BASE NEW_SWAP_BASE

def rangeCols : List Nat :=
  (List.range 4).flatMap (fun slot => [ruleCol slot R_LABEL]) ++
  (List.range 2).flatMap (fun slot =>
    [contextCol slot E_LABEL, contextCol slot E_SRC, contextCol slot E_DST]) ++
  (List.range 4).map sigmaCol

def rangeLookups : List VmConstraint2 :=
  rangeCols.map fun col => .lookup ⟨TableId.range, [v col]⟩

def publicPins : List VmConstraint2 :=
  [ .base (.piBinding .first DOMAIN 0)
  , .base (.piBinding .first SESSION 1)
  , .base (.piBinding .first VERSION 2)
  , .base (.piBinding .first SHAPE 3) ] ++
  ((List.range 8).map fun lane => .base (.piBinding .first (RULESET_ROOT_BASE + lane) (4 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (OLD_ROOT_BASE + lane) (12 + lane))) ++
  ((List.range 8).map fun lane => .base (.piBinding .first (NEW_ROOT_BASE + lane) (20 + lane)))

def privateGraphRewriteDescriptor : EffectVmDescriptor2 :=
  { name := "private-graph-rewrite-4x2::injective-swapnet-poseidon2-v1"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := [rangeTableDef 4]
  , constraints := hashLookups ++ rangeLookups ++
      semanticBodies.map (fun body => .base (.gate body)) ++ publicPins ++
      semanticBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard privateGraphRewriteDescriptor.traceWidth == 367
#guard privateGraphRewriteDescriptor.piCount == 28
#guard hashLookups.length == 7
#guard publicPins.length == 28
#guard rangeLookups.length == 14
#guard (emitVmJson2 privateGraphRewriteDescriptor).contains
  "private-graph-rewrite-4x2::injective-swapnet-poseidon2-v1"
#guard !(emitVmJson2 privateGraphRewriteDescriptor).contains "1347571253"

def zeroAsg : Assignment := fun _ => 0
def emptyTf : TraceFamily := fun _ => []
def emptyTrace : VmTrace where
  rows := [zeroAsg, zeroAsg, zeroAsg, zeroAsg]
  pub := zeroAsg
  tf := emptyTf

def ppM0 : Int → Int := fun _ => 0
def ppF0 : Int → Int × Nat := fun _ => (0, 0)

def constTrace (a pis : Assignment) (tf : TraceFamily) :
    VmTrace where
  rows := List.replicate 4 a
  pub := pis
  tf := tf

def CanonicalAssignment (a : Assignment) : Prop :=
  ∀ col, 0 ≤ a col ∧ a col < 2013265921

theorem semantic_gate_mem {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    VmConstraint2.base (.gate body) ∈ privateGraphRewriteDescriptor.constraints := by
  simp [privateGraphRewriteDescriptor, hbody]

theorem public_pin_mem {pin : VmConstraint2} (hpin : pin ∈ publicPins) :
    pin ∈ privateGraphRewriteDescriptor.constraints := by
  simp [privateGraphRewriteDescriptor, hpin]

theorem hash_lookup_mem {lookup : VmConstraint2} (h : lookup ∈ hashLookups) :
    lookup ∈ privateGraphRewriteDescriptor.constraints := by
  simp [privateGraphRewriteDescriptor, h]

theorem semantic_gate_vanishes
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ semanticBodies) :
    body.eval a ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ (semantic_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, constTrace,
    Dregg2.Circuit.DescriptorIR2.envAt] using h

theorem public_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ publicPins) :
    a col ≡ pis pi [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) _ (public_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, constTrace,
    Dregg2.Circuit.DescriptorIR2.envAt] using h

theorem constraint_holds_at_zero
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf))
    {constraint : VmConstraint2}
    (hmem : constraint ∈ privateGraphRewriteDescriptor.constraints) :
    constraint.holdsAt hash tf
      (Dregg2.Circuit.DescriptorIR2.envAt (constTrace a pis tf) 0) true false := by
  have h := hsat.rowConstraints 0 (by simp [constTrace]) constraint hmem
  simpa using h

structure EmittedRewriteFacts (hash : List Int → Int)
    (a pis : Assignment) (tf : TraceFamily) : Prop where
  gates : ∀ body ∈ semanticBodies, body.eval a ≡ 0 [ZMOD 2013265921]
  pins : ∀ col pi, VmConstraint2.base (.piBinding .first col pi) ∈ publicPins →
    a col ≡ pis pi [ZMOD 2013265921]
  hashes : ∀ lookup ∈ hashLookups,
    lookup.holdsAt hash tf
      (Dregg2.Circuit.DescriptorIR2.envAt (constTrace a pis tf) 0) true false
  ranges : ∀ lookup ∈ rangeLookups,
    lookup.holdsAt hash tf
      (Dregg2.Circuit.DescriptorIR2.envAt (constTrace a pis tf) 0) true false

/-- First Satisfied2→semantics bridge: satisfaction exposes every authored
match/delete/glue, permutation-network, padding, injectivity and ABI equation.
The next theorem layer lifts these modular equations and the seven chip lookups
into `PrivateGraphRewrite.Accepts`. -/
theorem privateGraphRewrite_emitted_facts
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash privateGraphRewriteDescriptor ppM0 ppF0 []
      (constTrace a pis tf)) :
    EmittedRewriteFacts hash a pis tf :=
  ⟨fun _ hb => semantic_gate_vanishes hsat hb,
   fun _ _ hp => public_pin_sound hsat hp,
   fun _ hl => constraint_holds_at_zero hsat (hash_lookup_mem hl),
   fun _ hl => constraint_holds_at_zero hsat (by
     simp [privateGraphRewriteDescriptor, hl])⟩

#assert_all_clean [
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.semantic_gate_vanishes,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.public_pin_sound,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.constraint_holds_at_zero,
  Dregg2.Crypto.PrivateGraphRewriteDescriptor.privateGraphRewrite_emitted_facts]

end Dregg2.Crypto.PrivateGraphRewriteDescriptor
