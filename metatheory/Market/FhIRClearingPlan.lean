/-
# Market.FhIRClearingPlan — the first Lean-authoritative fhIR clearing plan.

This module owns one exact, useful fhIR family end to end: the two-coordinate committed
rebalance

    minimize x² + y²       subject to x + y = 0

compiled to the current `fhegg-fhe` exact-integer engine's public operator
`A = [[2,1],[1,2]]`, step `τ = 1/3`, and symmetric certified-identity prox box.  It is
not the old five-boolean `Market.FhIRAdmissible.Program`: this is the concrete matrix,
resource/leakage manifest, deployed BFV modulus, interval certificate, and noise ceiling
that Rust decodes into `fhir::ClearingSpec` and dispatches to `convex_engine`.

The authority edge is:

  * `compileRebalance` constructs the typed plan and refuses outside the exact resource,
    interval, and deployed-noise envelope;
  * `encodeWire` / `decodeWire` are a fail-closed typed codec, with `decode_encode`;
  * `emitCanonical` is the sole canonical JSON renderer;
  * `EmitFhIRClearingPlan.lean` writes the checked-in artifact consumed by Rust;
  * `compileRebalance_sound` proves every emitted family member has the operational
    iterated-bound and deployed BFV `SafeNoise` facts, not merely matching flags.

Pure.  No `@[implemented_by]`; no Rust-authored plan.
-/
import Mathlib.Tactic
import Bfv.Noise
import Dregg2.Tactics

namespace Market.FhIRClearingPlan

/-! ## 1. The exact plan schema consumed by Rust. -/

def schemaVersion : Nat := 1
def kernelId : String := "fhir-exact-linear-v1"

inductive Tier where
  | dark
  | shielded
  | «open»
  deriving DecidableEq, BEq, Repr

def Tier.render : Tier → String
  | .dark => "tier0-dark"
  | .shielded => "tier1-shielded"
  | .«open» => "tier2-open"

def Tier.parse : String → Option Tier
  | "tier0-dark" => some .dark
  | "tier1-shielded" => some .shielded
  | "tier2-open" => some .«open»
  | _ => none

@[simp] theorem Tier.parse_render (t : Tier) : Tier.parse t.render = some t := by
  cases t <;> rfl

structure LeakageManifest where
  dims : Nat
  nnzA : Nat
  iterations : Nat
  precisionBits : Nat
  publicFacts : List String
  deriving DecidableEq, BEq, Repr

structure ResourceCertificate where
  maxDim : Nat
  maxNnz : Nat
  maxIterations : Nat
  maxTriggerDepth : Nat
  maxSocBlock : Nat
  triggerDepth : Nat
  socBlock : Nat
  deriving DecidableEq, BEq, Repr

/-- The exact static facts the current FHE consumer checks before executing.  `inputLo` /
`inputHi` are coordinate-wise initial intervals; `maxAbsIntermediate` bounds every term and
partial sum of the fused T-step evaluation; `finalScale = tauDen^T`; the last three fields
pin the deployed BFV noise meter. -/
structure NoWrapCertificate where
  inputLo : List Int
  inputHi : List Int
  centeredWindow : Nat
  maxAbsIntermediate : Nat
  finalScale : Nat
  growthFactor : Nat
  freshNoiseBound : Nat
  noiseCeiling : Nat
  deriving DecidableEq, BEq, Repr

structure ClearingPlan where
  version : Nat
  kernel : String
  rows : Nat
  cols : Nat
  /-- Exact row-major matrix, retaining row boundaries on the wire. -/
  matrix : List (List Int)
  tier : Tier
  leakage : LeakageManifest
  tauNum : Nat
  tauDen : Nat
  proxLo : Int
  proxHi : Int
  iterations : Nat
  plaintextModulus : Nat
  resource : ResourceCertificate
  noWrap : NoWrapCertificate
  deriving DecidableEq, BEq, Repr

/-- The typed wire form.  Only the tier is lexical; every exact integer remains an integer. -/
structure ClearingPlanWire where
  version : Nat
  kernel : String
  rows : Nat
  cols : Nat
  matrix : List (List Int)
  tier : String
  leakage : LeakageManifest
  tauNum : Nat
  tauDen : Nat
  proxLo : Int
  proxHi : Int
  iterations : Nat
  plaintextModulus : Nat
  resource : ResourceCertificate
  noWrap : NoWrapCertificate
  deriving DecidableEq, BEq, Repr

def expectedLeakage (iterations : Nat) : LeakageManifest where
  dims := 2
  nnzA := 4
  iterations := iterations
  -- `fhir::check_leakage`: floor(log2(t - 1)) for t = 1,032,193.
  precisionBits := 19
  publicFacts := []

def expectedResource : ResourceCertificate where
  maxDim := 4096
  maxNnz := 1048576
  maxIterations := 256
  maxTriggerDepth := 8
  maxSocBlock := 16
  triggerDepth := 0
  socBlock := 0

def freshNoiseBound : Nat := 2 ^ 20
def deployedNoiseCeiling : Nat := 68

def expectedNoWrap (bound iterations : Nat) : NoWrapCertificate where
  inputLo := [-(bound : Int), -(bound : Int)]
  inputHi := [(bound : Int), (bound : Int)]
  centeredWindow := (Bfv.t4096 - 1) / 2
  -- The fused step is (x,y) ↦ (x-y,y-x), so the exact interval radius doubles.
  maxAbsIntermediate := bound * 2 ^ iterations
  finalScale := 3 ^ iterations
  growthFactor := 2
  freshNoiseBound := freshNoiseBound
  noiseCeiling := deployedNoiseCeiling

/-- The exact kernel/type/leakage portion of admission. -/
def SchemaValid (p : ClearingPlan) : Prop :=
  p.version = schemaVersion ∧
  p.kernel = kernelId ∧
  p.rows = 2 ∧ p.cols = 2 ∧
  p.matrix = [[2, 1], [1, 2]] ∧
  p.tier = .dark ∧
  p.leakage = expectedLeakage p.iterations ∧
  p.tauNum = 1 ∧ p.tauDen = 3 ∧
  p.proxLo = -(p.noWrap.inputHi.head?.getD 0) ∧
  p.proxHi = p.noWrap.inputHi.head?.getD 0 ∧
  0 < p.noWrap.inputHi.head?.getD 0 ∧
  0 < p.iterations ∧
  p.plaintextModulus = Bfv.t4096

def ResourceValid (p : ClearingPlan) : Prop :=
  p.resource = expectedResource ∧ p.iterations ≤ p.resource.maxIterations

def CertificateValid (p : ClearingPlan) : Prop :=
  p.noWrap = expectedNoWrap (p.noWrap.inputHi.head?.getD 0).toNat p.iterations ∧
  p.noWrap.maxAbsIntermediate ≤ p.noWrap.centeredWindow ∧
  p.iterations ≤ p.noWrap.noiseCeiling

/-- Admission is deliberately exact.  A decoder cannot promote a different kernel, matrix,
tier, leakage story, resource envelope, or self-asserted no-wrap certificate. -/
def Admissible (p : ClearingPlan) : Prop :=
  SchemaValid p ∧ ResourceValid p ∧ CertificateValid p

instance (p : ClearingPlan) : Decidable (Admissible p) := by
  unfold Admissible SchemaValid ResourceValid CertificateValid
  infer_instance

def admitted (p : ClearingPlan) : Bool := decide (Admissible p)

def encodeWire (p : ClearingPlan) : ClearingPlanWire where
  version := p.version
  kernel := p.kernel
  rows := p.rows
  cols := p.cols
  matrix := p.matrix
  tier := p.tier.render
  leakage := p.leakage
  tauNum := p.tauNum
  tauDen := p.tauDen
  proxLo := p.proxLo
  proxHi := p.proxHi
  iterations := p.iterations
  plaintextModulus := p.plaintextModulus
  resource := p.resource
  noWrap := p.noWrap

/-- Reconstruct the semantic plan once the lexical tier has parsed. -/
def fromWire (w : ClearingPlanWire) (tier : Tier) : ClearingPlan := {
    version := w.version, kernel := w.kernel, rows := w.rows, cols := w.cols,
    matrix := w.matrix, tier, leakage := w.leakage, tauNum := w.tauNum,
    tauDen := w.tauDen, proxLo := w.proxLo, proxHi := w.proxHi,
    iterations := w.iterations, plaintextModulus := w.plaintextModulus,
    resource := w.resource, noWrap := w.noWrap }

@[simp] theorem fromWire_encode (p : ClearingPlan) :
    fromWire (encodeWire p) p.tier = p := by cases p; rfl

/-- Fail closed on an unknown tier or any invalid certificate field. -/
def decodeWire (w : ClearingPlanWire) : Option ClearingPlan := do
  let tier ← Tier.parse w.tier
  let p := fromWire w tier
  if admitted p then some p else none

/-- The typed canonical codec round-trips every admitted plan. -/
theorem decode_encode {p : ClearingPlan} (h : Admissible p) :
    decodeWire (encodeWire p) = some p := by
  unfold decodeWire
  rw [show Tier.parse (encodeWire p).tier = some p.tier by
    simp [encodeWire]]
  simp [fromWire_encode, admitted]
  exact h

/-! ## 2. The supported compiler family and its semantic teeth. -/

structure RebalanceProgram where
  /-- Symmetric public input/prox radius. -/
  bound : Nat
  /-- Public, data-independent FHE iteration count. -/
  iterations : Nat
  deriving DecidableEq, Repr

def planOf (r : RebalanceProgram) : ClearingPlan where
  version := schemaVersion
  kernel := kernelId
  rows := 2
  cols := 2
  matrix := [[2, 1], [1, 2]]
  tier := .dark
  leakage := expectedLeakage r.iterations
  tauNum := 1
  tauDen := 3
  proxLo := -(r.bound : Int)
  proxHi := r.bound
  iterations := r.iterations
  plaintextModulus := Bfv.t4096
  resource := expectedResource
  noWrap := expectedNoWrap r.bound r.iterations

/-- The compiler is the admission boundary: no artifact exists for an out-of-envelope request. -/
def compileRebalance (r : RebalanceProgram) : Option ClearingPlan :=
  let p := planOf r
  if admitted p then some p else none

theorem compileRebalance_eq {r : RebalanceProgram} {p : ClearingPlan}
    (h : compileRebalance r = some p) : p = planOf r := by
  by_cases hv : admitted (planOf r) = true
  · simp [compileRebalance, hv] at h
    exact h.symm
  · simp [compileRebalance, hv] at h

theorem compileRebalance_admitted {r : RebalanceProgram} {p : ClearingPlan}
    (h : compileRebalance r = some p) : Admissible p := by
  have hp := compileRebalance_eq h
  subst p
  by_cases hv : admitted (planOf r) = true
  · exact of_decide_eq_true (by simpa [admitted] using hv)
  · simp [compileRebalance, hv] at h

abbrev State := Int × Int

/-- The exact fused current-engine step from `A=[[2,1],[1,2]]`, `tau=(1,3)`. -/
def rebalanceStep (s : State) : State := (s.1 - s.2, s.2 - s.1)

def Bounded (B : Int) (s : State) : Prop := |s.1| ≤ B ∧ |s.2| ≤ B

theorem rebalanceStep_bounded {B : Int} {s : State}
    (h : Bounded B s) : Bounded (2 * B) (rebalanceStep s) := by
  constructor
  · calc
      |s.1 - s.2| ≤ |s.1| + |s.2| := abs_sub _ _
      _ ≤ B + B := add_le_add h.1 h.2
      _ = 2 * B := by ring
  · calc
      |s.2 - s.1| ≤ |s.2| + |s.1| := abs_sub _ _
      _ ≤ B + B := add_le_add h.2 h.1
      _ = 2 * B := by ring

/-- The interval certificate's operational meaning: after T fused steps, every coordinate is
bounded by `2^T * B`.  This is about the executed map, not a manifest flag. -/
theorem rebalance_iter_bounded (B : Int) (T : Nat) {s : State}
    (h : Bounded B s) :
    Bounded ((2 : Int) ^ T * B) ((rebalanceStep^[T]) s) := by
  induction T generalizing s with
  | zero => simpa using h
  | succ T ih =>
      rw [Function.iterate_succ_apply']
      have hs := rebalanceStep_bounded (B := (2 : Int) ^ T * B) (ih h)
      convert hs using 1 <;> ring

/-- The exact fused coefficient matrix has row-ℓ∞ norm 2, matching the emitted noise field. -/
def fusedMatrix : Fin 2 → Fin 2 → Int
  | 0, 0 => 1
  | 0, 1 => -1
  | 1, 0 => -1
  | 1, 1 => 1

theorem fusedMatrix_rowBound : Bfv.RowBound fusedMatrix 2 := by
  unfold Bfv.RowBound
  intro i
  fin_cases i <;> norm_num [fusedMatrix]

/-- The current Rust noise meter's exact deployed value for this fused kernel. -/
theorem deployed_noise_ceiling_exact :
    Bfv.iterCeiling Bfv.fheRs4096 2 freshNoiseBound = deployedNoiseCeiling := by
  decide

/-- **Compiler/admission soundness for the supported family.**  A successful compile provides
all three things the current consumer relies on: an admitted exact plan, the actual T-step
integer map staying in the emitted centered window, and the deployed BFV noise margin. -/
theorem compileRebalance_sound {r : RebalanceProgram} {p : ClearingPlan}
    (h : compileRebalance r = some p) :
    Admissible p ∧
    (∀ s, Bounded (r.bound : Int) s →
      Bounded (p.noWrap.maxAbsIntermediate : Int) ((rebalanceStep^[r.iterations]) s)) ∧
    Bfv.SafeNoise Bfv.fheRs4096
      ((p.noWrap.growthFactor : Int) ^ p.iterations * p.noWrap.freshNoiseBound) := by
  have hadm := compileRebalance_admitted h
  have heq := compileRebalance_eq h
  subst p
  constructor
  · exact hadm
  constructor
  · intro s hs
    simpa [planOf, expectedNoWrap, mul_comm] using
      (rebalance_iter_bounded (r.bound : Int) r.iterations hs)
  · have hT : r.iterations ≤ Bfv.iterCeiling Bfv.fheRs4096 2 freshNoiseBound := by
      rw [deployed_noise_ceiling_exact]
      simpa [planOf, expectedNoWrap] using hadm.2.2.2.2
    simpa [planOf, expectedNoWrap] using
      (Bfv.noise_after_T Bfv.fheRs4096 2 freshNoiseBound r.iterations
        (by decide) (by norm_num [freshNoiseBound]) (by decide) hT)

def rebalanceV1Request : RebalanceProgram where
  bound := 100
  iterations := 4

def rebalanceV1 : ClearingPlan := planOf rebalanceV1Request

theorem rebalanceV1_admissible : Admissible rebalanceV1 := by decide

#guard admitted rebalanceV1
#guard compileRebalance rebalanceV1Request == some rebalanceV1
#guard compileRebalance { bound := 0, iterations := 4 } == none
#guard compileRebalance { bound := 100, iterations := 69 } == none
#guard compileRebalance { bound := 300000, iterations := 1 } == none

/-! ## 3. Canonical JSON emission.  Emission itself is fail closed. -/

private def jsonNat (n : Nat) : String := toString n
private def jsonInt (z : Int) : String := toString z
private def jsonInts (xs : List Int) : String :=
  "[" ++ String.intercalate "," (xs.map jsonInt) ++ "]"
private def jsonMatrix (rows : List (List Int)) : String :=
  "[" ++ String.intercalate "," (rows.map jsonInts) ++ "]"

/-- Render the typed wire in one fixed field order.  The admitted schema has no free strings:
`kernel` and `tier` are fixed ASCII constants and `publicFacts=[]`, so escaping ambiguity is absent. -/
def emitWire (w : ClearingPlanWire) : String :=
  "{\"version\":" ++ jsonNat w.version ++
  ",\"kernel_id\":\"" ++ w.kernel ++ "\"" ++
  ",\"matrix\":{\"rows\":" ++ jsonNat w.rows ++
  ",\"cols\":" ++ jsonNat w.cols ++
  ",\"data\":" ++ jsonMatrix w.matrix ++ "}" ++
  ",\"tier\":\"" ++ w.tier ++ "\"" ++
  ",\"leakage\":{\"dims\":" ++ jsonNat w.leakage.dims ++
  ",\"nnz_a\":" ++ jsonNat w.leakage.nnzA ++
  ",\"iterations\":" ++ jsonNat w.leakage.iterations ++
  ",\"precision_bits\":" ++ jsonNat w.leakage.precisionBits ++
  ",\"public_facts\":[]}" ++
  ",\"step\":{\"tau_num\":" ++ jsonNat w.tauNum ++
  ",\"tau_den\":" ++ jsonNat w.tauDen ++
  ",\"prox_lo\":" ++ jsonInt w.proxLo ++
  ",\"prox_hi\":" ++ jsonInt w.proxHi ++ "}" ++
  ",\"iterations\":" ++ jsonNat w.iterations ++
  ",\"plaintext_modulus\":" ++ jsonNat w.plaintextModulus ++
  ",\"resource\":{\"max_dim\":" ++ jsonNat w.resource.maxDim ++
  ",\"max_nnz\":" ++ jsonNat w.resource.maxNnz ++
  ",\"max_iterations\":" ++ jsonNat w.resource.maxIterations ++
  ",\"max_trigger_depth\":" ++ jsonNat w.resource.maxTriggerDepth ++
  ",\"max_soc_block\":" ++ jsonNat w.resource.maxSocBlock ++
  ",\"trigger_depth\":" ++ jsonNat w.resource.triggerDepth ++
  ",\"soc_block\":" ++ jsonNat w.resource.socBlock ++ "}" ++
  ",\"no_wrap\":{\"input_lo\":" ++ jsonInts w.noWrap.inputLo ++
  ",\"input_hi\":" ++ jsonInts w.noWrap.inputHi ++
  ",\"centered_window\":" ++ jsonNat w.noWrap.centeredWindow ++
  ",\"max_abs_intermediate\":" ++ jsonNat w.noWrap.maxAbsIntermediate ++
  ",\"final_scale\":" ++ jsonNat w.noWrap.finalScale ++
  ",\"growth_factor\":" ++ jsonNat w.noWrap.growthFactor ++
  ",\"fresh_noise_bound\":" ++ jsonNat w.noWrap.freshNoiseBound ++
  ",\"noise_ceiling\":" ++ jsonNat w.noWrap.noiseCeiling ++ "}}"

/-- The public emitter refuses invalid plans rather than serializing a self-asserted certificate. -/
def emitCanonical (p : ClearingPlan) : Option String :=
  if admitted p then some (emitWire (encodeWire p) ++ "\n") else none

theorem emitCanonical_rebalanceV1 :
    emitCanonical rebalanceV1 = some (emitWire (encodeWire rebalanceV1) ++ "\n") := by
  simp [emitCanonical, admitted, decide_eq_true rebalanceV1_admissible]

/-- The exact bytes checked into `fhegg-fhe/plans/rebalance-v1.json`. -/
def REBALANCE_V1_GOLDEN : String :=
  "{\"version\":1,\"kernel_id\":\"fhir-exact-linear-v1\",\"matrix\":{\"rows\":2,\"cols\":2,\"data\":[[2,1],[1,2]]},\"tier\":\"tier0-dark\",\"leakage\":{\"dims\":2,\"nnz_a\":4,\"iterations\":4,\"precision_bits\":19,\"public_facts\":[]},\"step\":{\"tau_num\":1,\"tau_den\":3,\"prox_lo\":-100,\"prox_hi\":100},\"iterations\":4,\"plaintext_modulus\":1032193,\"resource\":{\"max_dim\":4096,\"max_nnz\":1048576,\"max_iterations\":256,\"max_trigger_depth\":8,\"max_soc_block\":16,\"trigger_depth\":0,\"soc_block\":0},\"no_wrap\":{\"input_lo\":[-100,-100],\"input_hi\":[100,100],\"centered_window\":516096,\"max_abs_intermediate\":1600,\"final_scale\":81,\"growth_factor\":2,\"fresh_noise_bound\":1048576,\"noise_ceiling\":68}}\n"

#guard emitCanonical rebalanceV1 == some REBALANCE_V1_GOLDEN

#assert_all_clean [Tier.parse_render, decode_encode, compileRebalance_eq,
  compileRebalance_admitted, rebalanceStep_bounded, rebalance_iter_bounded,
  fusedMatrix_rowBound, deployed_noise_ceiling_exact, compileRebalance_sound,
  rebalanceV1_admissible, emitCanonical_rebalanceV1]

end Market.FhIRClearingPlan
