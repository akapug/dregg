/-
# Dregg2.Circuit.Emit.GnarkVerifier.ChallengerReplayEmit — the Fiat-Shamir challenger
DUPLEX as a LEAN-AUTHORED, EMITTED R1CS constraint template, with a ∀-refinement to the
deployed challenger's own derivation.

SUBSTRATE, said out loud: **this is Lean-authored AIR/R1CS.** The transcript-replay
constraints below are EMITTED from `Poseidon2Fr.permuteW`'s own gadget builder over the
`R1csFr` foundation, composed through `MerkleEmit`'s proven `Emits` framework; no constraint
here is hand-written in Go or Rust. The deployed `chain/gnark/challenger_bn254.go` (the
native width-3 duplex sponge, RATE=2, CAPACITY=1, p3 `DuplexChallenger` discipline at rev
82cfad7) is the REFERENCE the emission is pinned against, not the source of the constraints.

THE CHECK (the atomic transcript-replay bind): a fresh native challenger absorbs a full rate
(two BN254 field elements) OVERWRITING lanes 0,1 of the zero state (the capacity lane carries
its 0), applies the width-3 Poseidon2Bn254 permutation, and refills the output buffer from
the rate lanes; the two challenges it then squeezes are popped from the END of that buffer
(`challenger_bn254.go:96-104 Sample`, `duplex_challenger.rs:235`). So the FIRST drawn
challenge is rate lane 1, the SECOND is rate lane 0 — `duplexDraw2` below. This is the sponge
CORE the whole FS transcript is built from (every ζ/α/PermAlpha/PermBeta/β/query-index is a
squeeze off a chain of these duplexings).

What this module adds on top of the committed pieces:

  * `Poseidon2Fr` carries the permutation model (`permute`, KAT-bit-exact to the deployed Go
    gold vector) and its frontend builder (`permuteW`); `MerkleEmit` carries the builder-spec
    framework (`Emits`/`DefChain`/`solveChain`) and the load-bearing `permuteW_emits`.
  * `ChallengerFr` carries the native duplex REFERENCE (`Chal`, `#guard`-pinned bit-exact to
    `challenger_bn254_test.go`'s deployed KAT `[bnKS0..bnKS3]`+`bnKIdx`) AND the op-DAG gadget
    (`GChal`, whose built fixture circuit `bnKATBuilt` reproduces that KAT in-circuit and is
    `lower_sound`-covered against aux forgery).
  * Missing until now: the challenger duplexing as a STANDALONE EMISSION PACKAGE with its own
    absorb/squeeze public interface, and the ∀-refinement tying THE EMITTED CONSTRAINTS to the
    deployed challenger's derivation. That is `emitChallengerReplay` + `challengerReplay_refines`.

Deliverables:

  * **`emitChallengerReplay a0 a1 : GnarkCircuitData`** — the one-duplexing replay template
    (absorbed rate at vars 0,1; claimed drawn challenges at vars 2,3; capacity = const 0;
    the emitted 435-assert permutation define-chain + the two squeeze pins).
  * **`challengerReplay_refines`** — for EVERY absorbed pair `a0,a1` and EVERY claimed
    challenge pair `c0,c1`: `gHolds (emitChallengerReplay a0 a1) (replayAsg a0 a1 c0 c1) ↔
    (c0,c1) = duplexDraw2 a0 a1` — the emitted R1CS accepts a claimed challenge pair IFF it
    equals the deployed challenger's true Fiat-Shamir squeeze of the absorbed inputs. Both
    polarities (`_rejects`/`_accepts`): any claim that is not the true squeeze is
    UNSATISFIABLE — the binding property Fiat-Shamir soundness rests on.
  * **`challengerReplay_refines_emitted`** — the same iff at the serialized wire form, via the
    proven `emit_faithful` round trip, so the committed JSON bytes denote exactly this check.
  * **`challengerReplay_sound`** — the adversarial face with NO honest-fill hypothesis: ANY
    R1CS witness satisfying the lowered template has its claimed-challenge vars equal to the
    true squeeze (rides `R1csFr.lower_sound`).
  * **`challengerReplayJson`** + byte pin, committed at
    `chain/gnark/emitted/challenger_replay_template.json`.

Cross-language KAT (§5): the deployed `challenger_bn254.go` FULL fixture transcript
(`challenger_bn254_test.go`: observe 11,22,33 → s0,s1,s2 → observe 44 → s3 → sampleBits 16)
re-derived in-circuit by the EMITTED duplex — `satisfiedEmitted` of the emitted `ChallengerFr`
fixture circuit at the honest witness carrying the pinned `[bnKS0..bnKS3]`+`bnKIdx` — is TRUE
(bit-exact) and every tamper is FALSE. That circuit's own `lower_sound` cover
(`ChallengerFr.bnKAT_no_aux_forgery`) rules out aux forgery.

NAMED RESIDUAL (not this cycle, not faked): (1) the MULTI-permutation chain of the full
fixture as ONE proven ∀-theorem (compose the atom N times through `DefChain.append`, mirroring
`MerkleEmit.pathW_emits`) — here the chain is covered by the executable KAT + the per-duplexing
∀-atom, not yet one closed ∀-theorem; (2) the query-index `sampleBits` low-bit EQUALITY
refinement (the grinding low-bit-ZERO face is already a ∀-theorem in `QueryPowEmit`); (3) the
MultiField `BabyBear↔BN254` pack/split boundary (`ChallengerFr.MRef`/`packLE`/`splitLimbs`) and
the DEPLOYED shrink-STARK schedule ORDER (ζ/α/PermAlpha/PermBeta/betas/query in the
`settlement_circuit.go` `shrinkStarkPrefixLoc` sequence over the `stark_algebra_real_fixture`
transcript). This module emits the sponge core those layers drive.
-/
import Dregg2.Circuit.Emit.GnarkVerifier.MerkleEmit
import Dregg2.Circuit.Emit.GnarkVerifier.EmitJson
import Dregg2.Circuit.ChallengerFr

namespace Dregg2.Circuit.Emit.GnarkVerifier.ChallengerReplay

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.Poseidon2Fr (permuteW permute St)
open Dregg2.Circuit.Emit.GnarkVerifier.Merkle
  (wBelow DefChain solveChain solveChain_sat solveChain_agree_below ev3 permuteW_emits)

/-! ## §1 The deployed native duplex reference — the squeeze `challenger_bn254.go` produces.

A fresh native challenger has state `[0,0,0]`. Absorbing a full rate `[a0,a1]` OVERWRITES
lanes 0,1 (capacity lane stays 0), permutes, and refills the output buffer `[rate0,rate1]`.
`Sample` pops from the END, so the first drawn challenge is rate lane 1 (`permute.2.1`), the
second is rate lane 0 (`permute.1`). This is `ChallengerFr.Chal` at one duplexing, over the
same `Poseidon2Fr.permute` (`#guard`-equal to `ChallengerFr.perm`, §5). -/

/-- **The two challenges the deployed native challenger draws** after absorbing `[a0,a1]`, IN
DRAW ORDER: first `permute(a0,a1,0)` lane 1, then lane 0. -/
def duplexDraw2 (a0 a1 : Fr) : Fr × Fr :=
  let s := permute (a0, a1, 0)
  (s.2.1, s.1)

/-! ## §2 The emitted template. -/

/-- The builder run at the canonical layout: the permutation of the two ABSORBED variables
with the capacity lane pinned to the constant 0 (fresh challenger), the counter starting past
the 4-variable interface (2 absorbed, 2 drawn challenges). -/
def permRun : (Wire × Wire × Wire) × (ℕ × List (Wire × Wire)) :=
  permuteW (.var 0, .var 1, .const 0) (4, [])

/-- The two squeeze pins: the emitted permutation's rate lanes are asserted equal to the
claimed drawn-challenge variables `2,3` IN DRAW ORDER — lane 1 (first draw) to `var 2`, lane 0
(second draw) to `var 3`. -/
def outPins : List (Wire × Wire) :=
  [(permRun.1.2.1, Wire.var 2), (permRun.1.1, Wire.var 3)]

/-- **The one-duplexing R1CS constraint template**, as an `R1csFr.Circuit`: the emitted
permutation define-chain plus the two squeeze pins. -/
def replayCircuit : Circuit := ⟨permRun.2.2 ++ outPins⟩

/-- **`emitChallengerReplay`** — the emission package: the template circuit, its 4-variable
public interface (absorbed rate + drawn challenges), and the gadget-invocation record naming
the deployed native duplex it stands for. -/
def emitChallengerReplay (_a0 _a1 : Fr) : GnarkCircuitData :=
  { name         := "challenger_bn254_duplex_replay_v1"
    publicInputs := [("absorb0", 0), ("absorb1", 1), ("challenge0", 2), ("challenge1", 3)]
    gadgets      := [⟨"ChallengerBn254Duplexing", [0, 1, 2, 3]⟩]
    circuit      := replayCircuit }

/-- The interface fill: absorbed rate at `0,1`, claimed drawn challenges at `2,3`. -/
def inAsg (a0 a1 c0 c1 : Fr) : Assignment := fun v =>
  if v = 0 then a0 else if v = 1 then a1 else if v = 2 then c0 else if v = 3 then c1 else 0

/-- **The honest witness** — the interface plus the solved permutation internals (the Lean
twin of gnark's hint solver, `solveChain` over the emitted define-chain). -/
def replayAsg (a0 a1 c0 c1 : Fr) : Assignment := solveChain (inAsg a0 a1 c0 c1) permRun.2.2

/-! ## §3 The builder run's define-chain and forced denotation. -/

/-- The emitted schedule is a define-chain from variable 4, and under ANY assignment
satisfying it the three result wires denote `permute` of `(a 0, a 1, 0)` — the absorbed rate
with the constant capacity. Pure application of the committed `permuteW_emits`. -/
theorem permRun_props :
    ∃ n', DefChain 4 permRun.2.2 n'
      ∧ ∀ a : Assignment, (∀ p ∈ permRun.2.2, p.1.eval a = p.2.eval a) →
          ev3 permRun.1 a = permute (a 0, a 1, 0) := by
  obtain ⟨t, n', new, heq, hdc, _, hforce⟩ :=
    permuteW_emits (Wire.var 0, Wire.var 1, Wire.const 0) (bound := 4)
      ⟨(by decide : (0:ℕ) < 4), (by decide : (1:ℕ) < 4), trivial⟩
      4 [] le_rfl
  have hrun : permRun = (t, (n', new)) := by
    show permuteW (Wire.var 0, Wire.var 1, Wire.const 0) (4, []) = (t, (n', new))
    rw [heq, List.nil_append]
  refine ⟨n', by rw [hrun]; exact hdc, fun a ha => ?_⟩
  rw [hrun] at ha ⊢
  have h := hforce a ha
  -- `ev3 (.var 0, .var 1, .const 0) a = (a 0, a 1, 0)`.
  simpa [ev3, Wire.eval] using h

-- The builder run is now spec-closed (`permRun_props`); make it an OPAQUE head so no later
-- defeq/`whnf` ever reduces the 64-round monadic value.
attribute [local irreducible] permRun

theorem mem_outPins0 : (permRun.1.2.1, Wire.var 2) ∈ outPins := List.Mem.head _
theorem mem_outPins1 : (permRun.1.1, Wire.var 3) ∈ outPins :=
  List.Mem.tail _ (List.Mem.head _)

/-! ## §4 THE REFINEMENT. -/

/-- **The squeeze-pin lemma**: under ANY assignment satisfying the emitted permutation
schedule, the two squeeze pins hold IFF the claimed-challenge variables carry the deployed
challenger's draw of `(a 0, a 1)` — rate lane 1 then rate lane 0. -/
theorem pins_iff (a : Assignment)
    (hnew : ∀ p ∈ permRun.2.2, p.1.eval a = p.2.eval a) :
    (∀ p ∈ outPins, p.1.eval a = p.2.eval a)
      ↔ (a 2, a 3) = duplexDraw2 (a 0) (a 1) := by
  obtain ⟨n', -, hforce⟩ := permRun_props
  have hperm : ev3 permRun.1 a = permute (a 0, a 1, 0) := hforce a hnew
  have e1 : permRun.1.2.1.eval a = (permute (a 0, a 1, 0)).2.1 :=
    congrArg (fun t : St => t.2.1) hperm
  have e0 : permRun.1.1.eval a = (permute (a 0, a 1, 0)).1 := congrArg Prod.fst hperm
  have v2 : Wire.eval (Wire.var 2) a = a 2 := rfl
  have v3 : Wire.eval (Wire.var 3) a = a 3 := rfl
  constructor
  · intro h
    have p0 := h _ mem_outPins0
    have p1 := h _ mem_outPins1
    rw [v2] at p0
    rw [v3] at p1
    -- p0 : permRun.1.2.1.eval a = a 2 ; p1 : permRun.1.1.eval a = a 3
    show (a 2, a 3) = duplexDraw2 (a 0) (a 1)
    simp only [duplexDraw2, Prod.mk.injEq]
    exact ⟨(p0.symm.trans e1), (p1.symm.trans e0)⟩
  · intro hy
    have q0 : a 2 = (permute (a 0, a 1, 0)).2.1 := by
      have := congrArg Prod.fst hy; simpa [duplexDraw2] using this
    have q1 : a 3 = (permute (a 0, a 1, 0)).1 := by
      have := congrArg Prod.snd hy; simpa [duplexDraw2] using this
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · show permRun.1.2.1.eval a = Wire.eval (Wire.var 2) a
      rw [v2, e1, q0]
    · rcases List.mem_cons.mp hp with rfl | hp
      · show permRun.1.1.eval a = Wire.eval (Wire.var 3) a
        rw [v3, e0, q1]
      · exact absurd hp (List.not_mem_nil)

/-- **The frontend refinement**: the honest witness satisfies the template IFF the claimed
challenge pair is the deployed challenger's draw of the absorbed inputs. -/
theorem replay_frontend (a0 a1 c0 c1 : Fr) :
    replayCircuit.satisfied (replayAsg a0 a1 c0 c1) ↔ (c0, c1) = duplexDraw2 a0 a1 := by
  obtain ⟨n', hdc, hforce⟩ := permRun_props
  set a := replayAsg a0 a1 c0 c1 with ha
  have hbelow : ∀ v, v < 4 → a v = inAsg a0 a1 c0 c1 v := fun v hv =>
    solveChain_agree_below permRun.2.2 (inAsg a0 a1 c0 c1) hdc v hv
  have hnew : ∀ p ∈ permRun.2.2, p.1.eval a = p.2.eval a :=
    solveChain_sat permRun.2.2 (inAsg a0 a1 c0 c1) hdc
  have h0 : a 0 = a0 := by rw [hbelow 0 (by decide)]; simp [inAsg]
  have h1 : a 1 = a1 := by rw [hbelow 1 (by decide)]; simp [inAsg]
  have h2 : a 2 = c0 := by rw [hbelow 2 (by decide)]; simp [inAsg]
  have h3 : a 3 = c1 := by rw [hbelow 3 (by decide)]; simp [inAsg]
  have hxy : ((a 2, a 3) = duplexDraw2 (a 0) (a 1)) ↔ (c0, c1) = duplexDraw2 a0 a1 := by
    rw [h0, h1, h2, h3]
  show (∀ p ∈ permRun.2.2 ++ outPins, p.1.eval a = p.2.eval a) ↔ _
  rw [List.forall_mem_append]
  constructor
  · rintro ⟨-, hpins⟩
    exact hxy.mp ((pins_iff a hnew).mp hpins)
  · intro hy
    exact ⟨hnew, (pins_iff a hnew).mpr (hxy.mpr hy)⟩

/-- **`challengerReplay_refines`** — THE deliverable, at the R1CS level the gnark backend
consumes: the LOWERED genuine R1CS of the emitted one-duplexing replay, under the honest
witness, is satisfied IFF the claimed challenge pair is the deployed native challenger's
Fiat-Shamir squeeze of the absorbed inputs — for EVERY absorbed pair `a0,a1` and EVERY claimed
challenge pair `c0,c1`. The emitted CONSTRAINTS are thereby tied to the deployed challenger's
derivation, not to a Go gadget's say-so. -/
theorem challengerReplay_refines (a0 a1 c0 c1 : Fr) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (emitChallengerReplay a0 a1)
        (replayAsg a0 a1 c0 c1)
      ↔ (c0, c1) = duplexDraw2 a0 a1 := by
  unfold Dregg2.Circuit.Emit.GnarkVerifier.gHolds
  rw [← R1csFr.gHolds]
  exact replay_frontend a0 a1 c0 c1

/-- Reject polarity, explicitly: a claimed challenge pair that is not the deployed squeeze
makes the emitted R1CS unsatisfiable under the honest witness (the FS binding property). -/
theorem challengerReplay_rejects (a0 a1 c0 c1 : Fr) (h : (c0, c1) ≠ duplexDraw2 a0 a1) :
    ¬ Dregg2.Circuit.Emit.GnarkVerifier.gHolds (emitChallengerReplay a0 a1)
        (replayAsg a0 a1 c0 c1) :=
  fun hg => h ((challengerReplay_refines a0 a1 c0 c1).mp hg)

/-- Accept polarity (non-vacuity of the iff): the honest draw IS accepted. -/
theorem challengerReplay_accepts (a0 a1 : Fr) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (emitChallengerReplay a0 a1)
      (replayAsg a0 a1 (duplexDraw2 a0 a1).1 (duplexDraw2 a0 a1).2) :=
  (challengerReplay_refines a0 a1 (duplexDraw2 a0 a1).1 (duplexDraw2 a0 a1).2).mpr rfl

/-- **The emit tie** — the same refinement at the SERIALIZED wire form, composing the proven
`emit_faithful` round trip. The bytes the JSON grammar renders in §6 therefore denote exactly
this challenger-duplexing check. -/
theorem challengerReplay_refines_emitted (a0 a1 c0 c1 : Fr) :
    Dregg2.Circuit.Emit.GnarkVerifier.satisfiedEmitted
        (Dregg2.Circuit.Emit.GnarkVerifier.emit (emitChallengerReplay a0 a1))
        (replayAsg a0 a1 c0 c1)
      ↔ (c0, c1) = duplexDraw2 a0 a1 :=
  (Dregg2.Circuit.Emit.GnarkVerifier.emit_faithful (emitChallengerReplay a0 a1)
      (replayAsg a0 a1 c0 c1)).symm.trans
    (challengerReplay_refines a0 a1 c0 c1)

/-- **`challengerReplay_sound`**: for ANY R1CS witness `z` of the lowered template that agrees
with a frontend assignment `a` on the frontend variables — however the prover filled the aux
region — the claimed-challenge variables ARE the deployed challenger's squeeze of the absorbed
variables. No hint/honest-fill hypothesis: the emitted defining constraints force every minted
value (`R1csFr.lower_sound`). -/
theorem challengerReplay_sound (a : Assignment) (z : RAssignment)
    (hinl : ∀ v, z (.inl v) = a v) (hsat : r1csSatisfied replayCircuit.lower z) :
    (a 2, a 3) = duplexDraw2 (a 0) (a 1) := by
  have hfront : replayCircuit.satisfied a := lower_sound replayCircuit a z hinl hsat
  have hall : ∀ p ∈ permRun.2.2 ++ outPins, p.1.eval a = p.2.eval a := hfront
  rw [List.forall_mem_append] at hall
  exact (pins_iff a hall.1).mp hall.2

#assert_axioms permRun_props
#assert_axioms pins_iff
#assert_axioms replay_frontend
#assert_axioms challengerReplay_refines
#assert_axioms challengerReplay_rejects
#assert_axioms challengerReplay_accepts
#assert_axioms challengerReplay_refines_emitted
#assert_axioms challengerReplay_sound

/-! ## §5 The DEPLOYED-fixture KAT — the emitted duplex re-derives `challenger_bn254.go`'s
own pinned transcript, bit-exact.

`ChallengerFr.bnKATBuilt` is the FULL fixture transcript (observe 11,22,33 → s0,s1,s2 →
observe 44 → s3 → sampleBits 16) built in-circuit through the `GChal` op-DAG gadget (the twin
of `challenger_bn254.go`), with the drawn challenges PINNED to the deployed `challenger_bn254_
test.go` gold constants `[bnKS0..bnKS3]`+`bnKIdx`. We wrap that proven-satisfied circuit as an
emission package and check — at the SERIALIZED wire form, via the proof-covered `emit` — that
the emitted duplex reproduces the deployed challenges (accept), and rejects every tamper. The
per-duplexing ∀-theorem (§4) is the atom this multi-duplexing fixture is a chain of; the
full-chain ONE-theorem is the named residual. -/

/-- The emission package wrapping the deployed full-fixture challenger circuit. -/
def emitChallengerFixture : GnarkCircuitData :=
  { name         := "challenger_bn254_fixture_replay_v1"
    publicInputs := [("absorb0", 0)]
    gadgets      := [⟨"ChallengerBn254FixtureTranscript", []⟩]
    circuit      := Dregg2.Circuit.ChallengerFr.bnKATBuilt.1 }

-- The atom's reference draw agrees with `ChallengerFr.Chal` (the `#guard`-pinned twin of the
-- deployed native challenger) on the fixture's first duplexing — `permute = ChallengerFr.perm`.
#guard duplexDraw2 11 22
  = (let c : Dregg2.Circuit.ChallengerFr.Chal :=
       (({} : Dregg2.Circuit.ChallengerFr.Chal).observe 11).observe 22
     let (s0, c) := c.sample
     let (s1, _) := c.sample
     (s0, s1))

-- ACCEPT: the EMITTED duplex re-derives the deployed `challenger_bn254.go` fixture challenges
-- `[bnKS0..bnKS3]`+`bnKIdx` bit-exact, at the serialized wire form (`emit`-covered).
#guard Dregg2.Circuit.Emit.GnarkVerifier.satisfiedEmitted
  (Dregg2.Circuit.Emit.GnarkVerifier.emit emitChallengerFixture)
  Dregg2.Circuit.ChallengerFr.bnKATBuilt.2

-- The wrapped fixture circuit is the SAME object `ChallengerFr` proved satisfied at the pinned
-- gold witness (so the accept above is genuinely the deployed transcript, not a re-authoring).
#guard Dregg2.Circuit.ChallengerFr.bnKATBuilt.1.satisfied Dregg2.Circuit.ChallengerFr.bnKATBuilt.2

/-- No aux forgery of the fixture transcript: ANY R1CS witness for the lowered emitted fixture
circuit agreeing with the pinned gold assignment on the frontend forces frontend satisfaction —
the deployed challenges cannot be faked in the aux region (`ChallengerFr.bnKAT_no_aux_forgery`,
`lower_sound` at the built KAT circuit). -/
theorem challengerFixture_no_aux_forgery (z : RAssignment)
    (hz : ∀ v, z (.inl v) = Dregg2.Circuit.ChallengerFr.bnKATBuilt.2 v)
    (h : r1csSatisfied emitChallengerFixture.circuit.lower z) :
    emitChallengerFixture.circuit.satisfied Dregg2.Circuit.ChallengerFr.bnKATBuilt.2 :=
  Dregg2.Circuit.ChallengerFr.bnKAT_no_aux_forgery z hz h

#assert_axioms challengerFixture_no_aux_forgery

/-! ## §6 The emitted JSON artifact — the one-duplexing replay template, COMPACT.

One duplexing (the sponge core the Go interpreter replays across the wrap). The byte pin below
is a length + FNV-1a digest of the exact rendered string; the same bytes are committed at
`chain/gnark/emitted/challenger_replay_template.json`. Any byte drift flips the digest. -/

/-- The canonical wire bytes of the one-duplexing replay template (the absorbed values are wire
metadata only — the circuit is input-independent, so `0 0` is the canonical rendering). -/
def challengerReplayJson : String :=
  Dregg2.Circuit.Emit.GnarkVerifier.emitGnarkJson (emitChallengerReplay 0 0)

/-- FNV-1a over the UTF-8 bytes — the byte-pin digest. -/
def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 1099511628211) 14695981039346656037

-- Structure pins: the emitted permutation's assert count, the template assert count, and the
-- lowered R1CS row count.
#guard permRun.2.2.length == 435
#guard replayCircuit.asserts.length == 437
#guard replayCircuit.lower.length == 677

-- **The byte pin** of the committed artifact `chain/gnark/emitted/challenger_replay_template.json`:
-- exact length + FNV-1a digest of the rendered string, plus the flattened gate/assert counts of
-- the node grammar. Any byte drift in the emitted template flips the digest.
#guard challengerReplayJson.length == 146534
#guard fnv1a challengerReplayJson == 15773991284197533179
#guard (Dregg2.Circuit.Emit.GnarkVerifier.flatAsserts
  (Dregg2.Circuit.Emit.GnarkVerifier.emit (emitChallengerReplay 0 0)).asserts [] []).1.length == 3116
#guard (Dregg2.Circuit.Emit.GnarkVerifier.flatAsserts
  (Dregg2.Circuit.Emit.GnarkVerifier.emit (emitChallengerReplay 0 0)).asserts [] []).2.length == 437

end Dregg2.Circuit.Emit.GnarkVerifier.ChallengerReplay
