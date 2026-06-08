import Dregg2.Exec.RecordKernel

/-!
# Argus — the state-transformer IR (the cornerstone)

The first word that cannot lie: a *reified* state transformer with **two
interpretations of one term**. `interp` runs it as the executor; a later
`compile` emits its circuit. Because both the executor and the circuit are
*derived from the same `RecStmt`*, they cannot drift — the per-effect
soundness obligation collapses from a bespoke proof to one generic theorem
over the term (the `effect_circuit_full_sound` back-end, fed by the term).

This file is the cornerstone only: the IR, its executable `interp` (the
worthwhile semantics — `insFresh` carries no-double-spend *inline*, where it
belongs), and the proof that `interp` of the transfer term **is** the verified
`recKExec`. That refinement is the whole bet in miniature: the executor is, by
construction, the meaning of the term.

`hole` (intents / coeffects) and `par` (jointturns / separation-⊗) are the
constructors reserved for the layers above; the asymmetric turn prologue/
epilogue (fee · nonce · receipt, conservation-modulo-burn) wraps this body.
-/

namespace Dregg2.Circuit.Argus

open Dregg2.Exec

/-- The Argus state-transformer IR, effect-body level. Each constructor is a
primitive whose circuit `compile_sound` case is proved **once**; a per-effect
term merely *assembles* primitives (data, farmable). `seq` is the composition
that — at the turn level — subsumes the manual `EffectCommit2/3/4/5` tower. -/
inductive RecStmt where
  | skip
  | guard    (φ : RecordKernelState → Bool)
  | setCell  (T : Finset CellId) (leaf : RecordKernelState → CellId → Value)
  | setBal   (b : RecordKernelState → CellId → AssetId → Int)
  | insFresh (n : RecordKernelState → Nat)
  | seq      (s t : RecStmt)

/-- **`interp`** — the executable interpretation, i.e. the reference executor.
Each clause is the worthwhile semantics of its primitive. -/
def interp : RecStmt → RecordKernelState → Option RecordKernelState
  | .skip,           k => some k
  | .guard φ,        k => if φ k then some k else none
  | .setCell T leaf, k => some { k with cell := fun c => if c ∈ T then leaf k c else k.cell c }
  | .setBal b,       k => some { k with bal := b k }
  | .insFresh n,     k => if n k ∈ k.nullifiers then none
                          else some { k with nullifiers := n k :: k.nullifiers }
  | .seq s t,        k => (interp s k).bind (interp t)

/-- The transfer admissibility gate as a `Bool` — exactly `recKExec`'s `if`. -/
def transferGuard (turn : Turn) (k : RecordKernelState) : Bool :=
  authorizedB k.caps turn
    && decide (0 ≤ turn.amt)
    && decide (turn.amt ≤ balOf (k.cell turn.src))
    && decide (turn.src ≠ turn.dst)
    && decide (turn.src ∈ k.accounts)
    && decide (turn.dst ∈ k.accounts)

/-- The transfer effect as an IR term: gate, then move the two balances. -/
def transferStmt (turn : Turn) : RecStmt :=
  RecStmt.seq (RecStmt.guard (transferGuard turn))
    (RecStmt.setCell ({turn.src, turn.dst} : Finset CellId)
      (fun k c => recTransfer k.cell turn.src turn.dst turn.amt c))

/-- The `Bool` gate decodes to `recKExec`'s admissibility proposition. -/
theorem transferGuard_iff (turn : Turn) (k : RecordKernelState) :
    transferGuard turn k = true ↔
      (authorizedB k.caps turn = true ∧ 0 ≤ turn.amt
        ∧ turn.amt ≤ balOf (k.cell turn.src) ∧ turn.src ≠ turn.dst
        ∧ turn.src ∈ k.accounts ∧ turn.dst ∈ k.accounts) := by
  simp only [transferGuard, Bool.and_eq_true, decide_eq_true_eq]
  tauto

/-- The `setCell {src,dst}` map is exactly `recTransfer` (identity off the pair). -/
theorem transferCellMap_eq (turn : Turn) (k : RecordKernelState) :
    (fun c => if c ∈ ({turn.src, turn.dst} : Finset CellId)
                then recTransfer k.cell turn.src turn.dst turn.amt c else k.cell c)
      = recTransfer k.cell turn.src turn.dst turn.amt := by
  funext c
  unfold recTransfer
  by_cases h1 : c = turn.src
  · simp [h1]
  · by_cases h2 : c = turn.dst
    · simp [h2]
    · simp [Finset.mem_insert, Finset.mem_singleton, h1, h2]

/-- **The cornerstone.** `interp` of the transfer term IS the verified
executor `recKExec` — the same partial function, by construction. -/
theorem interp_transferStmt_eq_recKExec (turn : Turn) (k : RecordKernelState) :
    interp (transferStmt turn) k = recKExec k turn := by
  simp only [transferStmt, interp]
  unfold recKExec
  by_cases hg : transferGuard turn k = true
  · rw [if_pos hg]
    simp only [Option.bind, transferCellMap_eq]
    rw [if_pos ((transferGuard_iff turn k).mp hg)]
  · rw [if_neg hg]
    simp only [Option.bind]
    rw [if_neg (fun hp => hg ((transferGuard_iff turn k).mpr hp))]

#assert_axioms interp_transferStmt_eq_recKExec

end Dregg2.Circuit.Argus
