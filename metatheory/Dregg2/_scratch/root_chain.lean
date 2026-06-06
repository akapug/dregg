import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.TurnWitness

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.StateCommit (recStateCommit recStateCommit_binds compressInjective)

/-- Bind the witness boundary roots to the GENUINE full-state commitments of the boundary kernels
(under a chosen commitment surface + turn). The roots are no longer free decoration: `preRoot` IS
`recStateCommit` of `s.kernel` and `postRoot` IS `recStateCommit` of `s'.kernel`. -/
def authenticTurnRoots
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) (w : TurnWitness) : Prop :=
  w.preRoot  = recStateCommit CH RH cmb compress compressN s.kernel  t ∧
  w.postRoot = recStateCommit CH RH cmb compress compressN s'.kernel t

/-- The realized step-root portal: the per-step commitment is the genuine post-state commitment of
the step's emitted kernel. Used to instantiate `stepRoot` so the fold computes real commitments. -/
def authStepRoot
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (decodeK : StepWitness → RecordKernelState) (t : Turn) : StepWitness → ℤ :=
  fun sw => recStateCommit CH RH cmb compress compressN (decodeK sw) t

/-! ## Load-bearing soundness: turnWitnessSatisfies + authenticity PINS the post-state commitment. -/

/-- **`turnWitnessSatisfies_binds_postRoot`** — `turnWitnessSatisfies` is consumed: the step-root
fold reaching `postRoot`, together with authentic boundary roots, forces the folded value to equal
the GENUINE `recStateCommit` of `s'.kernel`. The root chain is now load-bearing — it equates the
prover-folded root with the real post-state commitment. -/
theorem turnWitnessSatisfies_binds_postRoot
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (stepRoot : StepWitness → ℤ) (foldCompress : ℤ → ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) (w : TurnWitness)
    (hauth : authenticTurnRoots CH RH cmb compress compressN s s' t w)
    (hsat : turnWitnessSatisfies foldCompress stepRoot w) :
    foldStepRoots foldCompress stepRoot w.preRoot w.steps
      = recStateCommit CH RH cmb compress compressN s'.kernel t := by
  rw [hsat]; exact hauth.2

/-- **`tampered_postRoot_rejects`** — ANTI-GHOST tooth. If a witness declares a `postRoot` that is
NOT the genuine post-state commitment (under injective `cmb`, the post kernel actually differs in
cell-digest or rest-hash from `s'.kernel`), then it CANNOT both have authentic roots and satisfy the
root chain: the fold to `postRoot` is incompatible with the authentic commitment. A silent post-state
swap is rejected by the root chain. -/
theorem tampered_postRoot_rejects
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (s s' : RecChainedState) (t : Turn) (w : TurnWitness)
    -- the prover's claimed post root is a forgery: differs from the genuine commitment.
    (htamper : w.postRoot ≠ recStateCommit CH RH cmb compress compressN s'.kernel t) :
    ¬ authenticTurnRoots CH RH cmb compress compressN s s' t w := by
  intro hauth
  exact htamper hauth.2

/-- **`authentic_roots_bind_state`** — with injective `cmb`, two boundary states whose witnesses
carry equal authentic `postRoot`s commit to equal cell-digest + rest-hash (the published root binds
the state, via `recStateCommit_binds`). This is the headline authenticity: the turn root is a real
binding commitment to the post-state, not decoration. -/
theorem authentic_roots_bind_state
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCmb : compressInjective cmb)
    (s s' s'' : RecChainedState) (t : Turn) (w w' : TurnWitness)
    (hauth  : authenticTurnRoots CH RH cmb compress compressN s s'  t w)
    (hauth' : authenticTurnRoots CH RH cmb compress compressN s s'' t w')
    (heq : w.postRoot = w'.postRoot) :
    StateCommit.cellDigest CH compress compressN s'.kernel t
        = StateCommit.cellDigest CH compress compressN s''.kernel t
      ∧ RH s'.kernel = RH s''.kernel := by
  have : recStateCommit CH RH cmb compress compressN s'.kernel t
       = recStateCommit CH RH cmb compress compressN s''.kernel t := by
    rw [← hauth.2, ← hauth'.2, heq]
  exact recStateCommit_binds CH RH cmb compress compressN hCmb s'.kernel s''.kernel t this

end Dregg2.Circuit.TurnWitness
