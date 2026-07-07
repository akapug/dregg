/-
# Dregg2.Circuit.Emit.GarbledEvalRung2 — the RUNG-2 discharge of the FREE-`hash_out` residual for the
emitted garbled-evaluation descriptor (`garbledEvalDesc`), via the Poseidon2 garbling-hash binding.

## What this file IS

`GarbledEvalRefine.lean` (RUNG 1) proves the whole-descriptor bridge `Satisfied2 ⟹ GarbledEvalRun`,
whose decryption leg (`GateDecrypts`) concludes, per active non-padding row and per output lane `j`,

    output(j) = table_entry(j) − hash_out(j)          (the Yao one-time-pad decryption ALGEBRA).

That is a relation between THREE trace columns — and, crucially, `hash_out` is a FREE WITNESS: the
emitted 56-column descriptor declares NO chip lookup / hash site binding the digest columns
(`hashSites = []`, `tables = []`; see the `GarbledEvalEmit` header, "the columns `hash_out(i)` are
FREE witnesses … computed ENTIRELY in Rust witness-gen, NOT in-circuit"). So `Satisfied2` alone does
NOT force `output` to be the honest decryption: a forger picks ANY `output(j)` and sets
`hash_out(j) := table_entry(j) − output(j)`, and the decryption gate `output − table + hash_out = 0`
still holds. RUNG 1's `GarbledEvalRun` is therefore NOT yet output-label non-forgeability — a genuine
crypto residual remains: the free `hash_out` columns.

RUNG 2 DISCHARGES that residual. The NAMED carrier is `GarblingHashBound gh t` — the executor-verified
Poseidon2 garbling-hash binding (the `GarbledEvalEmit` header's "NAMED, EXECUTOR-VERIFIED CARRIER"):
on each active non-padding row, the digest columns ARE the genuine wide-hash of the gate's input
labels, `hash_out(j) = gh [left‖right‖gate_index] j`. Under it, the free witness is pinned and the
decryption gate collapses to the GENUINE one-time-pad decryption

    output(j) = table_entry(j) − gh [left‖right‖gate_index] j  =  HonestOutput gh (row) j,

the UNIQUE output label a genuine evaluator recovers — no forged output can be exposed
(`garbled_rung2_no_output_forgery`). This mirrors the DFA `Rung 2` posture: there the deployed chip-AIR
supplies `ChipTableSound` and the running-hash binding discharges the terminal-step residual; here the
deployed garbler + verifier-wrapper supplies `GarblingHashBound` (Poseidon2 preimage/collision
resistance is what makes it sound — forging `hash_out` to a chosen value is a Poseidon2 preimage
attack), and it discharges the free-`hash_out` residual. The carrier rides as a NAMED hypothesis,
never a Lean axiom, and `gh` (the genuine garbling hash) is a parameter — the theorem holds for the
real Poseidon2 wide-hash.

## Scope (honest residual)

This discharges OUTPUT-LABEL forgery — the per-gate decryption soundness that the descriptor's
decryption gate is meant to carry. The complementary COMMITMENT-binding dimension (the full 8-felt
`circuit_commitment` / `output_label_hash` = Poseidon2(tables) / Poseidon2(output labels), of which the
descriptor pins only the first 4 felts in-circuit and the rest is the verifier-side struct equality in
`verify_garbled_evaluation_dsl`) rides the SAME Poseidon2 CR carrier off-descriptor by design — it is
NAMED in `GarbledEvalEmit` (the "VERIFIER-WRAPPER TOOTH"), not re-mechanized here.

## Non-vacuity (the anti-scar witnesses, all IN THIS FILE)

* `garbled_honest_fires` — the RUNG-2 conclusion FIRES on the concrete honest trace `t₀` (RUNG 1's own
  satisfying witness) under the genuine carrier `garbled_honest_hashBound`: its exposed `output(0)` is
  the genuine honest decryption `HonestOutput (…) 0 = 0`. So the hypothesis set is jointly satisfiable
  and the conclusion is achievably true (not vacuous).
* `garbled_satisfied2_alone_insufficient` — the LOAD-BEARING-ANCHOR proof. The SAME `t₀` (provably
  `Satisfied2`) FAILS the no-forgery conclusion once the genuine garbling hash is a DIFFERENT one
  (`gh = fun _ _ => 1`): `t₀` exposes `output(0) = 0` but the honest decryption is `0 − 1 = −1`. So a
  hypothetical `Satisfied2 ⟹ output = HonestOutput` (WITHOUT the carrier) is refuted — the anchor is
  genuinely load-bearing, this is not a `P → P` / unsatisfiable-hypothesis theorem.
* `garbled_cheat_not_hashBound` — the carrier is a REAL filter, not `True`: `t₀` `Satisfied2`s yet
  VIOLATES `GarblingHashBound (fun _ _ => 1)` (its `hash_out = 0 ≠ 1`).

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} (Classical enters only through RUNG 1's
`satisfied2_implies_garbledEvalRun`). The garbling-hash carrier `GarblingHashBound` rides as a NAMED
hypothesis; `gh` is a parameter — never a Lean axiom. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.GarbledEvalRefine

namespace Dregg2.Circuit.Emit.GarbledEvalRung2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2 (Satisfied2 VmTrace envAt)
open Dregg2.Circuit.Emit.GarbledEvalEmit
open Dregg2.Circuit.Emit.GarbledEvalRefine

set_option autoImplicit false

/-! ## §1 — The garbling-hash carrier + the genuine one-time-pad decryption. -/

/-- **`GateInputs a`** — the gate's input labels, the preimage the garbling hash absorbs:
`left(0..8) ‖ right(0..8) ‖ gate_index` (17 felts). The genuine Poseidon2 wide-hash of THIS list is
the row's `hash_out` digest (computed in `circuit/src/garbled.rs` witness-gen). -/
def GateInputs (a : Assignment) : List ℤ :=
  (List.range 8).map (fun j => a (LEFT j))
    ++ (List.range 8).map (fun j => a (RIGHT j))
    ++ [a GATE_INDEX]

/-- **`HonestOutput gh a j`** — the genuine one-time-pad decryption of output lane `j`: the committed
garbled-table entry minus the genuine garbling-hash digest of the gate's inputs
(`table_entry(j) − gh [inputs] j`). The UNIQUE label a faithful evaluator recovers. -/
def HonestOutput (gh : List ℤ → Nat → ℤ) (a : Assignment) (j : Nat) : ℤ :=
  a (TABLE_ENTRY j) - gh (GateInputs a) j

/-- **`GarblingHashBound gh t` — THE NAMED CARRIER.** The executor-verified Poseidon2 garbling-hash
binding: on every ACTIVE (non-last), NON-PADDING row, each digest lane is the genuine wide-hash of the
gate's input labels, `hash_out(j) = gh [left‖right‖gate_index] j`. This is the off-descriptor binding
(`GarbledEvalEmit`'s "NAMED, EXECUTOR-VERIFIED CARRIER"): the AIR proves the decryption algebra over
`hash_out`; that `hash_out` IS the genuine Poseidon2 digest is supplied by the garbler + verifier and
underwritten by Poseidon2 preimage/collision resistance. NEVER a Lean axiom — a hypothesis on `t`. -/
def GarblingHashBound (gh : List ℤ → Nat → ℤ) (t : VmTrace) : Prop :=
  ∀ i, i + 1 < t.rows.length → (envAt t i).loc IS_PADDING = 0 →
    ∀ j, j < 8 → (envAt t i).loc (HASH_OUT j) = gh (GateInputs (envAt t i).loc) j

/-! ## §2 — THE RUNG-2 DISCHARGE (no output-label forgery). -/

/-- **`garbled_rung2_no_output_forgery` — THE DISCHARGE.** A trace `t` that `Satisfied2`s the emitted
garbled-evaluation descriptor and rides the NAMED garbling-hash carrier `GarblingHashBound gh` exposes,
on every active non-padding row and output lane `j`, EXACTLY the genuine one-time-pad decryption
`HonestOutput gh (row) j = table_entry(j) − gh [inputs] j`. The free-`hash_out` residual RUNG 1 left is
discharged: no forged output label can appear — the exposed label is the UNIQUE one a faithful
evaluator recovers under the genuine garbling hash. -/
theorem garbled_rung2_no_output_forgery
    (gh : List ℤ → Nat → ℤ)
    (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash garbledEvalDesc minit mfin maddrs t)
    (hgh : GarblingHashBound gh t) :
    ∀ i, i + 1 < t.rows.length → (envAt t i).loc IS_PADDING = 0 →
      ∀ j, j < 8 → (envAt t i).loc (OUTPUT j) = HonestOutput gh (envAt t i).loc j := by
  intro i hact hnp j hj
  have hrun := satisfied2_implies_garbledEvalRun hash minit mfin maddrs t hsat
  rcases hrun.decrypts i hact with hpad | heq
  · rw [hnp] at hpad; exact absurd hpad (by decide)
  · have h2 := hgh i hact hnp j hj
    show (envAt t i).loc (OUTPUT j)
        = (envAt t i).loc (TABLE_ENTRY j) - gh (GateInputs (envAt t i).loc) j
    rw [← h2]; exact heq j hj

#assert_axioms garbled_rung2_no_output_forgery

/-! ## §3 — Non-vacuity, TRUE half: the discharge FIRES on RUNG 1's honest witness `t₀`. -/

/-- The honest trace's digit columns are `0` on the active row, so they equal the genuine garbling
hash `gh = fun _ _ => 0` — the carrier holds. -/
theorem garbled_honest_hashBound : GarblingHashBound (fun _ _ => (0 : ℤ)) t₀ := by
  intro i hact _ j hj
  have hi0 : i = 0 := by
    have h2 : i + 1 < 2 := by rw [show t₀.rows.length = 2 from rfl] at hact; exact hact
    omega
  subst hi0
  rw [envAt0_loc]
  exact honestRow0_hash j hj

/-- **The RUNG-2 discharge FIRES on the genuine witness (the TRUE half).** Feeding the concrete honest
trace `t₀` (RUNG 1's own `garbled_honest_satisfied2`) and the carrier `garbled_honest_hashBound` to the
discharge recovers the genuine decryption on lane 0: the exposed `output(0)` is `0`, and it EQUALS the
honest decryption `HonestOutput (fun _ _ => 0) 0`. The hypothesis set is jointly satisfiable and the
conclusion is achievably true — not vacuous. -/
theorem garbled_honest_fires :
    (envAt t₀ 0).loc (OUTPUT 0) = 0 ∧
    (envAt t₀ 0).loc (OUTPUT 0) = HonestOutput (fun _ _ => (0 : ℤ)) (envAt t₀ 0).loc 0 := by
  refine ⟨?_, ?_⟩
  · rw [envAt0_loc]; exact honestRow0_output 0 (by decide)
  · exact garbled_rung2_no_output_forgery (fun _ _ => (0 : ℤ)) (fun _ => 0) (fun _ => 0)
      (fun _ => (0, 0)) [] t₀ (garbled_honest_satisfied2 (fun _ => 0)) garbled_honest_hashBound
      0 (by rw [show t₀.rows.length = 2 from rfl]; decide)
      (by rw [envAt0_loc]; exact honestRow0_padding) 0 (by decide)

/-! ## §4 — Non-vacuity, FALSE half: the carrier is LOAD-BEARING (and a real filter). -/

/-- **The carrier is a REAL filter, not `True`.** The honest trace `t₀` `Satisfied2`s yet VIOLATES
`GarblingHashBound (fun _ _ => 1)`: its `hash_out(0) = 0 ≠ 1`. So the carrier genuinely bites. -/
theorem garbled_cheat_not_hashBound : ¬ GarblingHashBound (fun _ _ => (1 : ℤ)) t₀ := by
  intro h
  have h0 := h 0 (by rw [show t₀.rows.length = 2 from rfl]; decide)
    (by rw [envAt0_loc]; exact honestRow0_padding) 0 (by decide)
  rw [envAt0_loc, honestRow0_hash 0 (by decide)] at h0
  change (0 : ℤ) = 1 at h0
  exact absurd h0 (by decide)

/-- **`garbled_satisfied2_alone_insufficient` — THE LOAD-BEARING-ANCHOR PROOF.** `Satisfied2` ALONE
cannot force the no-forgery conclusion: the SAME honest trace `t₀` is provably `Satisfied2`, yet under
a DIFFERENT genuine garbling hash (`gh = fun _ _ => 1`) it does NOT satisfy the conclusion — it exposes
`output(0) = 0` while the honest decryption is `table_entry(0) − 1 = −1`. So a hypothetical
`Satisfied2 ⟹ output = HonestOutput` (dropping the carrier) is REFUTED: `GarblingHashBound` is
genuinely load-bearing, and the RUNG-2 theorem is not a `P → P` / unsatisfiable-hypothesis vacuity. -/
theorem garbled_satisfied2_alone_insufficient :
    Satisfied2 (fun _ => 0) garbledEvalDesc (fun _ => 0) (fun _ => (0, 0)) [] t₀ ∧
    ¬ (∀ i, i + 1 < t₀.rows.length → (envAt t₀ i).loc IS_PADDING = 0 →
        ∀ j, j < 8 →
          (envAt t₀ i).loc (OUTPUT j) = HonestOutput (fun _ _ => (1 : ℤ)) (envAt t₀ i).loc j) := by
  refine ⟨garbled_honest_satisfied2 (fun _ => 0), fun hconc => ?_⟩
  have h0 := hconc 0 (by rw [show t₀.rows.length = 2 from rfl]; decide)
    (by rw [envAt0_loc]; exact honestRow0_padding) 0 (by decide)
  rw [envAt0_loc, honestRow0_output 0 (by decide)] at h0
  have hval : HonestOutput (fun _ _ => (1 : ℤ)) honestRow0 0 = -1 := by
    show honestRow0 (TABLE_ENTRY 0) - 1 = -1
    rw [honestRow0_table 0 (by decide)]; decide
  rw [hval] at h0
  exact absurd h0 (by decide)

#assert_axioms garbled_honest_hashBound
#assert_axioms garbled_honest_fires
#assert_axioms garbled_cheat_not_hashBound
#assert_axioms garbled_satisfied2_alone_insufficient

end Dregg2.Circuit.Emit.GarbledEvalRung2
