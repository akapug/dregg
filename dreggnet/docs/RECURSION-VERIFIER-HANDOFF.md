# RECURSION-VERIFIER HANDOFF — the VK-epoch's deep blocker

**Mission:** architect + build the in-circuit recursion that lets a *pure light client* witness
the **custom (G2)** and **bridge (G1)** sub-proof STARK verification — folding it into the turn's
effect-vm proof — so the coordinated VK-epoch flip becomes possible. This is a focused, self-contained
circuit-architecture problem. Hand this whole brief to a fresh session; it owns G2/G1 end-to-end.

## Where the VK-epoch stands (don't redo)
- **G5 row-locality** FIXED (`fec691cf5`) · **G4 umem** + the **57/57 welded registry** staged (`e3fc11d2c`).
- Apex `lightclient_unfoolable` re-verifies `#assert_axioms`-clean WITH the welds admitted; deployed default UNflipped.
- **Blocked:** G2 + G1 — both need the sub-proof's STARK verification *in-circuit* (today it's off-AIR).
- Remaining besides G2/G1: G5-satisfaction (registry-wide flag-day, **no recursion needed**) + membership; then the gated flip.

## The core problem
The custom-effect proof (`Effect::Custom` `proofBind`) and the bridge-mint foreign-note-spend proof are
**verified by the executor OFF-AIR**. The deployed `proofBind` op is a *bounds check only*
(`circuit/src/effect_vm/descriptor_ir2.rs:~1299`). So a pure light client verifying the turn's effect-vm
proof does **not** witness that the sub-proof was checked — `BridgeMint` just credits balance, `Custom`'s
in-AIR gate is `True`. We must fold the sub-proof's STARK verification INTO the proof a light client checks.

## The machinery that exists (and doesn't)
- ✅ `recursion/src/verifier/batch_stark.rs::verify_p3_batch_proof_circuit` — a circuit-DSL **constraint
  builder** that verifies a plonky3 batch STARK in-circuit. Exists, but is **not** an `impl Air` and **not**
  composed with the effect-vm.
- ❌ There is **no** `impl Air for RecursiveStarkVerifier`.
- ⚠️ `AggregationAir` is a **Poseidon2 accumulator, NOT a STARK verifier** — it does not carry sub-proof validity.
- The effect-vm AIR is **row-local degree-2 gates** (`satisfaction_weld.rs`); a STARK verifier (FRI opening,
  quotient recomposition, challenger rounds) **cannot** be a row-local gate.
- Off-AIR check today: `circuit-prove/src/custom_proof_bind.rs::verify_proof_bind`.

## THE design question (the architecture to decide)
How do we compose recursion with the effect-vm so the sub-proof is witnessed?
- **(a) Separate recursion-verifier AIR, aggregated with the turn proof.** The effect-vm `proofBind` row
  commits the sub-proof (its digest/PIs); a *separate* recursion-verifier AIR (wrapping/using
  `verify_p3_batch_proof_circuit`) proves the sub-proof verifies; aggregation/IVC binds the two so the
  light client, checking the aggregate, witnesses both. — Likely the right shape (decouples the heavy
  verifier from the row-local effect-vm).
- **(b) Wire `verify_p3_batch_proof_circuit` directly as the `proofBind` gate.** Almost certainly a
  degree/row-locality mismatch (it's a big constraint system, not a row-local gate) — probably a non-starter,
  but confirm.
- Also part of the work: the **G2 4→8-felt `custom_proof_commitment` lift** (VK-affecting: re-emit descriptor,
  reshift columns, re-pin FP, touch Lean — see `CustomApex.lean`), and the **G1 `(nullifier,recipient,dest_fed,amount)`
  binding** (reuses G2's recursion for backing-existence; `bridge_action_air` is the sound sidecar to fold in).

## Soundness bar (prove-or-back-out)
- The apex `lightclient_unfoolable` + the 5 `AssuranceCase` guarantees re-verify `#assert_axioms`-clean under
  the new VK.
- `metatheory/Dregg2/Circuit/CustomApex.lean`: `StarkSoundCustom` is the named FRI-extraction carrier — the
  in-circuit verifier must *match* what it assumes (FRI extraction over the in-AIR/aggregated proof, not the
  off-AIR check — wiring the off-AIR check as the gate is a **soundness mismatch**, forbidden).
- The teeth bite in real `--release` STARKs (a forged custom-proof / a forged-backing bridge mint REJECTED by
  a pure LC). STAGED — no deployed flip (the flip is the later coordinated VK-epoch step once G2/G1/G5-sat all stage).

## Key files to read
`circuit/src/effect_vm/{descriptor_ir2.rs, satisfaction_weld.rs, mod.rs}` · `circuit-prove/src/custom_proof_bind.rs`
· `recursion/src/verifier/batch_stark.rs` (+ the recursion crate) · the `AggregationAir` / IVC fold ·
`metatheory/Dregg2/Circuit/CustomApex.lean` · `~/dev/DreggNet/docs/VK-EPOCH-DESIGN.md` (the per-gap blueprint) ·
`~/dev/DreggNet/docs/UNDER-WIRED-circuit.md` (G1/G2 detail).

## Deliverable
The composition architecture decided (a vs b, with rationale) → G2 (+ the 4→8 lift) and G1 (the backing weld)
implemented in-circuit, STAGED, proven (apex clean, teeth bite in real STARKs). Then they join the
VK-epoch flip alongside the already-staged G5-row-locality / G4 / 57-registry.
