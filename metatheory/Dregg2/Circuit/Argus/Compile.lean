/-
# Dregg2.Circuit.Argus.Compile — the SECOND interpretation of the Argus IR: the circuit.

`Argus/Stmt.lean` laid the cornerstone: a `RecStmt` term carries an executable interpretation
`interp` (the reference executor), and `interp (transferStmt turn) = recKExec` — the executor IS
the meaning of the term, by construction. This file builds the term's OTHER interpretation:
`compile : RecStmt → EffectVmDescriptor`, the EffectVM circuit the running prover (`EffectVmP3Air`)
executes. The Argus thesis is that ONE term has TWO interpretations that cannot drift; here we
validate the compile side end-to-end for the TRANSFER slice.

## What this file does — and what it deliberately REUSES rather than re-builds

The transfer circuit and its full soundness already EXIST and are audited:

  * `EffectVmEmitTransfer.transferVmDescriptor` — the runnable EffectVM transfer descriptor the
    Rust prover executes byte-identically (`satisfiedVm` is its denotation).
  * `EffectVmEmitTransferSound.transferDescriptor_full_sound` — satisfying that descriptor (under the
    `RowEncodes` decoding) forces the WHOLE per-cell `CellTransferSpec` post-state (balance signed
    move, balHi/8-fields/cap_root/reserved each frozen, nonce ticked) + the published commitment.
  * `EffectVmEmitTransferUnify.descriptor_agrees_with_executor_debit` — that descriptor's pinned
    post-state AGREES with the real executor `recKExec k t = some k'` on the SRC cell's projection
    (`cellProj`), per-cell, with the ONE documented nonce-tick divergence carried as a separate
    conjunct (the executor FREEZES the cell nonce; the EffectVM row TICKS it — `Unify` §2).

`compile` returns exactly that runnable descriptor for the transfer term (`compile_transferStmt`),
and `transfer_compile_sound` WELDS the existing agreement theorem to the Argus IR term by routing
the executor side through the cornerstone `interp_transferStmt_eq_recKExec`. So the statement reads:
*a satisfying witness of the circuit `compile (transferStmt turn)` agrees with the per-cell
post-state that the IR term `interp (transferStmt turn)` produces* — the same term, two
interpretations, provably aligned.

## HONEST SCOPE (precise — do NOT over-read)

  * PER-CELL (the SRC/debit leg). The runnable descriptor is a SINGLE-ROW AIR; its soundness pins ONE
    cell's transition + that cell's commitment binding. `interp`/`recKExec` is the multi-cell whole
    `RecordKernelState` transformer. We weld on the SRC cell's projection `cellProj k' t.src`, exactly
    the surface `descriptor_agrees_with_executor_debit` supports. The cross-cell two-sided conservation
    (debit-row ⊕ credit-row, net-zero mint) is the TURN-COMPOSITION layer (`Dregg2.Circuit.TurnEmit`);
    we CITE it and do not claim it here. The credit leg is the symmetric `cellProj k' t.dst`
    statement (`EffectVmEmitTransferUnify.unify_credit`), available by the same route.

  * The NONCE-TICK divergence is REAL and carried (not papered): the circuit ticks the cell nonce, the
    executor freezes it. `transfer_compile_sound` exposes both facts as a final conjunct, identical to
    the form `descriptor_agrees_with_executor_debit` already proves.

  * `compile` is TOTAL. Non-transfer-shaped terms map to a trivial empty descriptor (`skipDescriptor`,
    satisfied by everything — the honest meaning of "no circuit emitted yet"); only the transfer slice
    carries a real descriptor + soundness. The weld theorem is stated ONLY for the transfer term, where
    `compile` IS the audited runnable descriptor (`compile_transferStmt`, by `rfl`).

## Honesty

`#assert_axioms transfer_compile_sound` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`, no
`:= True` vacuity, no weakening-that-just-typechecks: the conclusion is the genuine per-cell
agreement the reused theorem proves. Imports are read-only; this file owns only itself.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Circuit.Emit.EffectVmEmitTransferUnify

namespace Dregg2.Circuit.Argus

open Dregg2.Exec
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferVmDescriptor IsTransferRow)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound (CellState RowEncodes)
open Dregg2.Circuit.Emit.EffectVmEmitTransferUnify
  (cellProj debitParams descriptor_agrees_with_executor_debit)

/-! ## §1 — The placeholder descriptor for terms whose circuit is not (yet) emitted.

`compile` is total. A term outside the transfer slice maps to `skipDescriptor`: zero constraints,
zero hash sites, zero ranges — the empty AIR, satisfied by EVERY environment. This is the honest
denotation of "no circuit emitted for this term yet" (it pins nothing), kept DISTINCT from the
transfer slice which carries the real runnable descriptor + full soundness. Extending the Argus
compile to another effect = replacing that effect's `skipDescriptor` arm with its runnable
descriptor + a weld theorem of the `transfer_compile_sound` shape. -/

/-- The empty EffectVM descriptor: no constraints, no hash sites, no range checks. Its denotation
`satisfiedVm` is vacuously true on any environment (it enforces nothing) — the honest "no circuit
yet" placeholder for the constructors above the transfer beachhead. -/
def skipDescriptor : EffectVmDescriptor where
  name        := "dregg-argus-skip-v0"
  traceWidth  := EFFECT_VM_WIDTH
  piCount     := 0
  constraints := []
  hashSites   := []
  ranges      := []

/-! ## §2 — `compile` — the circuit interpretation of a `RecStmt` term.

The transfer slice is `RecStmt.seq (.guard _) (.setCell _ _)` — exactly the shape `transferStmt`
emits (gate, then move the two balances). `compile` returns the audited runnable
`transferVmDescriptor` for that shape, so `compile (transferStmt turn)` reduces DEFINITIONALLY to
the real transfer circuit (`compile_transferStmt`, by `rfl`). Every other term shape (`skip`,
`guard`, a lone `setCell`/`setBal`/`insFresh`, or a `seq` not of the transfer shape) maps to the
`skipDescriptor` placeholder, keeping `compile` total and honest. -/
def compile : RecStmt → EffectVmDescriptor
  | .seq (.guard _) (.setCell _ _) => transferVmDescriptor
  | _ => skipDescriptor

/-- **`compile (transferStmt turn)` IS the audited runnable transfer descriptor.** Definitional:
`transferStmt turn = .seq (.guard (transferGuard turn)) (.setCell {src,dst} …)` matches the
transfer arm of `compile`. So the circuit interpretation of the transfer term is, on the nose, the
descriptor the Rust prover runs. -/
theorem compile_transferStmt (turn : Turn) :
    compile (transferStmt turn) = transferVmDescriptor := rfl

/-! ## §3 — THE WELD: a satisfying witness of `compile (transferStmt turn)` agrees with the
post-state the IR term's executor interpretation `interp (transferStmt turn)` produces.

This is the Argus payoff for transfer: ONE term `transferStmt turn`, TWO interpretations —
`interp` (the executor, = `recKExec` by the cornerstone) and `compile` (the circuit, =
`transferVmDescriptor`) — that PROVABLY agree. The executor side is routed through
`interp_transferStmt_eq_recKExec` (so the hypothesis `interp (transferStmt turn) k = some k'`
becomes the `recKExec k turn = some k'` that the reused `…_agrees_with_executor_debit` consumes);
the circuit side is the audited full per-cell soundness. The nonce-tick divergence is carried in
the final conjunct exactly as the reused theorem proves it (executor freezes, circuit ticks). -/

/-- **`transfer_compile_sound` — the welded soundness (transfer slice).**

Suppose, for the Argus transfer term `transferStmt turn`:
  * the circuit `compile (transferStmt turn)` is SATISFIED by `(env, true, true)` under the abstract
    Poseidon carrier `hash`, and its `RowEncodes` decoding NAMES the post-state record `post` over the
    SRC cell's projection `cellProj k turn.src` with the debit param block (`hsat`, `henc`, `hrow`);
  * the IR term's EXECUTOR interpretation COMMITS: `interp (transferStmt turn) k = some k'` (`hexec`).

Then the circuit's pinned post-state record `post` AGREES with the executor's SRC post-cell
projection `cellProj k' turn.src` on the conserved balance and the WHOLE frame (balHi, all 8 fields,
cap_root, reserved each frozen); and the ONE documented divergence — the circuit TICKS the cell
nonce while the executor FREEZES it (`Unify` §2) — is reported as the final conjunct. So the circuit
the prover runs for transfer pins the per-cell state the IR term's executor produces. -/
theorem transfer_compile_sound
    (hash : List ℤ → ℤ) (env : VmRowEnv)
    (k k' : RecordKernelState) (turn : Turn) (post : CellState)
    (henc : RowEncodes env (cellProj k turn.src) (debitParams turn) post)
    (hrow : IsTransferRow env)
    (hsat : satisfiedVm hash (compile (transferStmt turn)) env true true)
    (hexec : interp (transferStmt turn) k = some k') :
    -- the conserved balance + the whole frame agree with the executor's SRC post-cell …
    ( post.balLo = (cellProj k' turn.src).balLo
      ∧ post.balHi = (cellProj k' turn.src).balHi
      ∧ (∀ i, post.fields i = (cellProj k' turn.src).fields i)
      ∧ post.capRoot = (cellProj k' turn.src).capRoot
      ∧ post.reserved = (cellProj k' turn.src).reserved )
    -- … and the ONE divergence: circuit TICKS the cell nonce, executor FREEZES it (Unify §2).
    ∧ ( post.nonce = (cellProj k turn.src).nonce + 1
        ∧ (cellProj k' turn.src).nonce = (cellProj k turn.src).nonce ) := by
  -- circuit side: `compile (transferStmt turn)` IS `transferVmDescriptor`, so the satisfaction
  -- hypothesis is over the audited runnable descriptor.
  rw [compile_transferStmt] at hsat
  -- executor side: the cornerstone turns the IR term's `interp` into the verified `recKExec`.
  rw [interp_transferStmt_eq_recKExec] at hexec
  -- the reused per-cell circuit⟺executor agreement, with everything now over the right surfaces.
  exact descriptor_agrees_with_executor_debit hash env k k' turn post henc hrow hsat hexec

#assert_axioms transfer_compile_sound

/-! ## §4 — NON-VACUITY: `compile` does NOT collapse the transfer term to the empty placeholder.

The weld would be worthless if `compile (transferStmt turn)` were the inert `skipDescriptor`. It is
not: it is the full runnable transfer descriptor, which carries 14 + 14 + 4 + 3 + 1 = 36 constraints,
4 hash sites, and 2 range checks — none of which `skipDescriptor` has. So the soundness above is
about a REAL circuit, not the vacuous placeholder. -/

/-- The compiled transfer circuit is the NON-trivial runnable descriptor, not the empty placeholder:
it carries the 36 transfer constraints / 4 hash sites / 2 range checks (`skipDescriptor` has none).
So `transfer_compile_sound` is a statement about a genuine circuit. -/
theorem compile_transferStmt_nontrivial (turn : Turn) :
    (compile (transferStmt turn)).constraints.length = 36
    ∧ (compile (transferStmt turn)).hashSites.length = 4
    ∧ (compile (transferStmt turn)).ranges.length = 2
    ∧ (compile (transferStmt turn)).constraints ≠ skipDescriptor.constraints := by
  rw [compile_transferStmt]
  refine ⟨by decide, by decide, by decide, ?_⟩
  -- transferVmDescriptor has 36 constraints; skipDescriptor has 0 — different lengths ⇒ unequal.
  intro h
  have : (transferVmDescriptor.constraints).length = (skipDescriptor.constraints).length := by
    rw [h]
  simp only [skipDescriptor, List.length_nil] at this
  exact absurd this (by decide)

#assert_axioms compile_transferStmt_nontrivial

end Dregg2.Circuit.Argus
