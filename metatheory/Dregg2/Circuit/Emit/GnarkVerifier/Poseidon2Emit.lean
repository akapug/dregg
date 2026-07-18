/-
# Dregg2.Circuit.Emit.GnarkVerifier.Poseidon2Emit — the Poseidon2-BN254 permutation as a
LEAN-AUTHORED, EMITTED R1CS constraint template, with a ∀-refinement to the Lean model.

SUBSTRATE, said out loud: **this is Lean-authored AIR/R1CS.** The constraint template below
is EMITTED from `Dregg2.Circuit.Poseidon2Fr`'s own gadget builder (`permuteW`) over the
`R1csFr` foundation; no constraint here is hand-written in Go or Rust. The deployed
`chain/gnark/poseidon2_bn254.go` gadget is the REFERENCE the emission is pinned against
(same schedule, same constants, same S-box decomposition), not the source of the
constraints. The Go side's role is to REPLAY the emitted template (8436 invocations across
the wrap), which is why the template must stay ONE permutation — see §5.

What this module adds on top of the committed pieces:

  * `Poseidon2Fr` already carries the permutation model (`permute`, KAT-bit-exact to the
    deployed Go gold vector) and its frontend builder (`permuteW`).
  * `MerkleEmit` already carries the builder-spec framework (`Emits`, `DefChain`,
    `solveChain`) and — the load-bearing lemma — **`permuteW_emits`**: the whole 64-round
    builder emits a define-chain whose forced denotation is `permute`.
  * Missing until now: the permutation as a STANDALONE emission package with its own
    input/output interface, and the refinement theorem tying THE EMITTED CONSTRAINTS to
    the model. That is `poseidon2Template` + `poseidon2Template_refines` below.

Deliverables:

  * **`poseidon2Template : GnarkCircuitData`** — the one-permutation template. Layout:
    `var 0,1,2` = input lanes, `var 3,4,5` = claimed output lanes, internals minted from
    `6`. Asserts = the 435 defining asserts of the emitted round schedule (240 of them the
    S-box multiplications) plus the 3 output pins.
  * **`poseidon2Template_refines`** — for EVERY `x y : St`:
    `gHolds poseidon2Template (permAsg x y) ↔ y = permute x`.
    Both polarities: any claimed output that is not the model's permutation of the input
    makes the emitted R1CS UNSATISFIABLE under the honest witness (`poseidon2Template_rejects`).
  * **`poseidon2Template_refines_emitted`** — the same iff at the serialized wire form,
    via the proven `emit_faithful` round trip (`EmitFaithful.lean`), so the committed JSON
    bytes denote exactly this R1CS.
  * **`poseidon2Template_sound`** — the adversarial face with NO honest-fill hypothesis:
    ANY R1CS witness satisfying the lowered template has `(z 3, z 4, z 5) = permute
    (z 0, z 1, z 2)` — the aux region cannot be filled to fake a permutation output
    (rides `R1csFr.lower_sound`, whose forcing lemma pins every minted value).
  * **`poseidon2TemplateJson`** + byte pin, committed at
    `chain/gnark/emitted/poseidon2_template.json`.

Classified seam (cost only, named not silent): the builder snaps each linear-layer output
to a fresh frontend variable (the `Poseidon2Fr` DAG-sharing device), so the lowering spends
one linear R1CS row per named wire — 678 rows total = **240 bilinear (S-box) constraints**
+ 438 linear equality rows — where the deployed gnark gadget's linear layers are free and
the count is 240. Semantically identical (linear rows force values, they do not constrain
the prover beyond the definitions); the divergence is in the safe direction and is a
row-count artifact of naming, not extra witness freedom.
-/
import Dregg2.Circuit.Emit.GnarkVerifier.MerkleEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson

namespace Dregg2.Circuit.Emit.GnarkVerifier.Poseidon2Template

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.Poseidon2Fr (permuteW permute St katOut)
open Dregg2.Circuit.Emit.GnarkVerifier.Merkle
  (wBelow DefChain solveChain solveChain_sat solveChain_agree_below ev3 permuteW_emits)

/-! ## §1 The emitted template. -/

/-- The builder run at the canonical layout: the permutation of the three INPUT variables,
with the counter starting past the 6-variable interface (3 in, 3 out). -/
def permRun : (Wire × Wire × Wire) × (ℕ × List (Wire × Wire)) :=
  permuteW (.var 0, .var 1, .var 2) (6, [])

/-- The three output pins: the emitted permutation's lanes are asserted equal to the
claimed output variables `3,4,5` (the gadget's output interface). -/
def outPins : List (Wire × Wire) :=
  [(permRun.1.1, Wire.var 3), (permRun.1.2.1, Wire.var 4), (permRun.1.2.2, Wire.var 5)]

/-- **The one-permutation R1CS constraint template**, as an `R1csFr.Circuit`: the emitted
round-schedule define-chain plus the output pins. -/
def poseidon2Circuit : Circuit := ⟨permRun.2.2 ++ outPins⟩

/-- **`poseidon2Template`** — the emission package the Go side replays: the template
circuit, its 6-variable public interface, and the gadget-invocation record naming the
deployed gnark gadget it stands for. -/
def poseidon2Template : GnarkCircuitData :=
  { name         := "poseidon2_bn254_permutation_v1"
    publicInputs := [("in0", 0), ("in1", 1), ("in2", 2), ("out0", 3), ("out1", 4),
                     ("out2", 5)]
    gadgets      := [⟨"Poseidon2Bn254Permutation", [0, 1, 2, 3, 4, 5]⟩]
    circuit      := poseidon2Circuit }

/-- The interface fill: inputs at `0,1,2`, claimed outputs at `3,4,5`. -/
def inAsg (x y : St) : Assignment := fun v =>
  if v = 0 then x.1 else if v = 1 then x.2.1 else if v = 2 then x.2.2
  else if v = 3 then y.1 else if v = 4 then y.2.1 else if v = 5 then y.2.2 else 0

/-- **The honest witness** — the interface plus the solved round internals (the Lean twin
of gnark's hint solver, `solveChain` over the emitted define-chain). -/
def permAsg (x y : St) : Assignment := solveChain (inAsg x y) permRun.2.2

/-! ## §2 The builder run's define-chain and forced denotation. -/

/-- The emitted schedule is a define-chain from variable 6, and under ANY assignment
satisfying it the three result wires denote `permute` of the input variables. Pure
application of the committed `permuteW_emits`. -/
theorem permRun_props :
    ∃ n', DefChain 6 permRun.2.2 n'
      ∧ ∀ a : Assignment, (∀ p ∈ permRun.2.2, p.1.eval a = p.2.eval a) →
          ev3 permRun.1 a = permute (a 0, a 1, a 2) := by
  obtain ⟨t, n', new, heq, hdc, _, hforce⟩ :=
    permuteW_emits (Wire.var 0, Wire.var 1, Wire.var 2) (bound := 6)
      ⟨(by decide : (0:ℕ) < 6), (by decide : (1:ℕ) < 6), (by decide : (2:ℕ) < 6)⟩
      6 [] le_rfl
  have hrun : permRun = (t, (n', new)) := by
    show permuteW (Wire.var 0, Wire.var 1, Wire.var 2) (6, []) = (t, (n', new))
    rw [heq, List.nil_append]
  refine ⟨n', by rw [hrun]; exact hdc, fun a ha => ?_⟩
  rw [hrun] at ha ⊢
  exact hforce a ha

-- The builder run is now spec-closed (`permRun_props`); make it an OPAQUE head so no
-- later defeq/`whnf` ever reduces the 64-round monadic value (the `compressW` discipline
-- of `MerkleEmit`).
attribute [local irreducible] permRun

theorem mem_outPins0 : (permRun.1.1, Wire.var 3) ∈ outPins := List.Mem.head _
theorem mem_outPins1 : (permRun.1.2.1, Wire.var 4) ∈ outPins :=
  List.Mem.tail _ (List.Mem.head _)
theorem mem_outPins2 : (permRun.1.2.2, Wire.var 5) ∈ outPins :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

/-! ## §3 THE REFINEMENT. -/

/-- **The output-pin lemma**: under ANY assignment satisfying the emitted round schedule,
the three output pins hold IFF the output variables carry the model's permutation of the
input variables. This is where the emitted CONSTRAINTS meet `Poseidon2Fr.permute`. -/
theorem pins_iff (a : Assignment)
    (hnew : ∀ p ∈ permRun.2.2, p.1.eval a = p.2.eval a) :
    (∀ p ∈ outPins, p.1.eval a = p.2.eval a)
      ↔ (a 3, a 4, a 5) = permute (a 0, a 1, a 2) := by
  obtain ⟨n', -, hforce⟩ := permRun_props
  have hperm : ev3 permRun.1 a = permute (a 0, a 1, a 2) := hforce a hnew
  have e0 : permRun.1.1.eval a = (permute (a 0, a 1, a 2)).1 := congrArg Prod.fst hperm
  have e1 : permRun.1.2.1.eval a = (permute (a 0, a 1, a 2)).2.1 :=
    congrArg (fun t : St => t.2.1) hperm
  have e2 : permRun.1.2.2.eval a = (permute (a 0, a 1, a 2)).2.2 :=
    congrArg (fun t : St => t.2.2) hperm
  have v3 : Wire.eval (Wire.var 3) a = a 3 := rfl
  have v4 : Wire.eval (Wire.var 4) a = a 4 := rfl
  have v5 : Wire.eval (Wire.var 5) a = a 5 := rfl
  constructor
  · intro h
    have p0 := h _ mem_outPins0
    have p1 := h _ mem_outPins1
    have p2 := h _ mem_outPins2
    rw [v3] at p0
    rw [v4] at p1
    rw [v5] at p2
    rw [p0.symm.trans e0, p1.symm.trans e1, p2.symm.trans e2]
  · intro hy
    have q0 : a 3 = (permute (a 0, a 1, a 2)).1 := congrArg Prod.fst hy
    have q1 : a 4 = (permute (a 0, a 1, a 2)).2.1 := congrArg (fun t : St => t.2.1) hy
    have q2 : a 5 = (permute (a 0, a 1, a 2)).2.2 := congrArg (fun t : St => t.2.2) hy
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show permRun.1.1.eval a = Wire.eval (Wire.var 3) a
      rw [v3, e0, q0]
    · rcases List.mem_cons.mp hp with rfl | hp
      · show permRun.1.2.1.eval a = Wire.eval (Wire.var 4) a
        rw [v4, e1, q1]
      · rcases List.mem_cons.mp hp with rfl | hp
        · show permRun.1.2.2.eval a = Wire.eval (Wire.var 5) a
          rw [v5, e2, q2]
        · exact absurd hp (List.not_mem_nil)

/-- **The frontend refinement**: the honest witness satisfies the template IFF the claimed
output is the model's permutation of the input. -/
theorem poseidon2_frontend (x y : St) :
    poseidon2Circuit.satisfied (permAsg x y) ↔ y = permute x := by
  obtain ⟨n', hdc, hforce⟩ := permRun_props
  set a := permAsg x y with ha
  have hbelow : ∀ v, v < 6 → a v = inAsg x y v := fun v hv =>
    solveChain_agree_below permRun.2.2 (inAsg x y) hdc v hv
  have hnew : ∀ p ∈ permRun.2.2, p.1.eval a = p.2.eval a :=
    solveChain_sat permRun.2.2 (inAsg x y) hdc
  have h0 : a 0 = x.1 := by rw [hbelow 0 (by decide)]; simp [inAsg]
  have h1 : a 1 = x.2.1 := by rw [hbelow 1 (by decide)]; simp [inAsg]
  have h2 : a 2 = x.2.2 := by rw [hbelow 2 (by decide)]; simp [inAsg]
  have h3 : a 3 = y.1 := by rw [hbelow 3 (by decide)]; simp [inAsg]
  have h4 : a 4 = y.2.1 := by rw [hbelow 4 (by decide)]; simp [inAsg]
  have h5 : a 5 = y.2.2 := by rw [hbelow 5 (by decide)]; simp [inAsg]
  have hxy : ((a 3, a 4, a 5) = permute (a 0, a 1, a 2)) ↔ y = permute x := by
    rw [h0, h1, h2, h3, h4, h5]
  show (∀ p ∈ permRun.2.2 ++ outPins, p.1.eval a = p.2.eval a) ↔ _
  rw [List.forall_mem_append]
  constructor
  · rintro ⟨-, hpins⟩
    exact hxy.mp ((pins_iff a hnew).mp hpins)
  · intro hy
    exact ⟨hnew, (pins_iff a hnew).mpr (hxy.mpr hy)⟩

/-- **`poseidon2Template_refines`** — THE deliverable, at the R1CS level the gnark backend
consumes: the LOWERED genuine R1CS of the emitted one-permutation template, under the
honest witness, is satisfied IFF the claimed output triple is `Poseidon2Fr.permute` of the
input triple — for EVERY input `x` and EVERY claimed output `y`. The emitted CONSTRAINTS
are thereby tied to the Lean permutation model, not to a Go gadget's say-so. -/
theorem poseidon2Template_refines (x y : St) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds poseidon2Template (permAsg x y)
      ↔ y = permute x := by
  unfold Dregg2.Circuit.Emit.GnarkVerifier.gHolds
  rw [← R1csFr.gHolds]
  exact poseidon2_frontend x y

/-- Reject polarity, explicitly: a claimed output that is not the model's permutation makes
the emitted R1CS unsatisfiable under the honest witness. -/
theorem poseidon2Template_rejects (x y : St) (h : y ≠ permute x) :
    ¬ Dregg2.Circuit.Emit.GnarkVerifier.gHolds poseidon2Template (permAsg x y) :=
  fun hg => h ((poseidon2Template_refines x y).mp hg)

/-- Accept polarity (non-vacuity of the iff): the honest claim IS accepted. -/
theorem poseidon2Template_accepts (x : St) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds poseidon2Template (permAsg x (permute x)) :=
  (poseidon2Template_refines x (permute x)).mpr rfl

/-- **The emit tie** — the same refinement at the SERIALIZED wire form, composing the
proven `emit_faithful` round trip (`EmitFaithful.lean`: `gHolds d a ↔ satisfiedEmitted
(emit d) a`, itself composing `R1csFr.gHolds` with pointwise `emitW_eval`). The bytes the
JSON grammar renders in §5 therefore denote exactly this permutation check. -/
theorem poseidon2Template_refines_emitted (x y : St) :
    Dregg2.Circuit.Emit.GnarkVerifier.satisfiedEmitted
        (Dregg2.Circuit.Emit.GnarkVerifier.emit poseidon2Template) (permAsg x y)
      ↔ y = permute x :=
  (Dregg2.Circuit.Emit.GnarkVerifier.emit_faithful poseidon2Template (permAsg x y)).symm.trans
    (poseidon2Template_refines x y)

/-! ## §4 The adversarial face — no honest-fill hypothesis. -/

/-- **`poseidon2Template_sound`**: for ANY R1CS witness `z` of the lowered template that
agrees with a frontend assignment `a` on the frontend variables — however the prover filled
the aux region — the claimed output variables ARE the model's permutation of the input
variables. No hint/honest-fill hypothesis: the emitted defining constraints force every
minted value (`R1csFr.lower_sound` / `lowerWire_forces`). -/
theorem poseidon2Template_sound (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) (hsat : r1csSatisfied poseidon2Circuit.lower z) :
    (a 3, a 4, a 5) = permute (a 0, a 1, a 2) := by
  have hfront : poseidon2Circuit.satisfied a := lower_sound poseidon2Circuit a z hinl hsat
  have hall : ∀ p ∈ permRun.2.2 ++ outPins, p.1.eval a = p.2.eval a := hfront
  rw [List.forall_mem_append] at hall
  exact (pins_iff a hall.1).mp hall.2

#assert_axioms permRun_props
#assert_axioms pins_iff
#assert_axioms poseidon2_frontend
#assert_axioms poseidon2Template_refines
#assert_axioms poseidon2Template_rejects
#assert_axioms poseidon2Template_accepts
#assert_axioms poseidon2Template_refines_emitted
#assert_axioms poseidon2Template_sound

/-! ## §5 The emitted JSON artifact — COMPACT, one permutation.

The template is ONE permutation: the Go interpreter replays it (8436 invocations across the
deployed wrap) rather than consuming a flattened multi-million-constraint dump. The byte
pin below is a length + FNV-1a digest of the exact rendered string (a full literal pin of a
few hundred KB inside the source would be unreadable; the digest flips on ANY byte change,
which is the property a golden pin needs). The same bytes are committed at
`chain/gnark/emitted/poseidon2_template.json`. -/

/-- The canonical wire bytes of the template package. -/
def poseidon2TemplateJson : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson poseidon2Template

/-- FNV-1a over the UTF-8 bytes — the byte-pin digest. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

-- Structure pins: the emitted schedule's assert count, the S-box multiplication count
-- (the deployed gadget's constraint count), and the lowered R1CS row count.
#guard permRun.2.2.length == 435
#guard poseidon2Circuit.asserts.length == 438
#guard poseidon2Circuit.lower.length == 678

-- **The byte pin** of the committed artifact `chain/gnark/emitted/poseidon2_template.json`:
-- exact length + FNV-1a digest of the rendered string, plus the flattened gate/assert
-- counts of the node grammar. Any byte drift in the emitted template flips the digest.
#guard poseidon2TemplateJson.length == 146661
#guard fnv1a poseidon2TemplateJson == 13662869466102731777
#guard (Dregg2.Circuit.Emit.GnarkVerifier.flatAsserts
  (Dregg2.Circuit.Emit.GnarkVerifier.emit poseidon2Template).asserts [] []).1.length == 3118
#guard (Dregg2.Circuit.Emit.GnarkVerifier.flatAsserts
  (Dregg2.Circuit.Emit.GnarkVerifier.emit poseidon2Template).asserts [] []).2.length == 438

-- The KAT the model carries (`Poseidon2Fr`: bit-exact to the deployed Go gold vector) is
-- what the refinement's right-hand side is stated over; pin it here too so the template's
-- accept case is anchored to a value the Go side reproduces.
#guard permute (0, 1, 2) == katOut

end Dregg2.Circuit.Emit.GnarkVerifier.Poseidon2Template
