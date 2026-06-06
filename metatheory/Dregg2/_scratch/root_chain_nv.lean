import Dregg2.Circuit.TurnWitness
import Dregg2.Circuit.StateCommit

namespace Dregg2.Circuit.TurnWitness.NV

open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.StateCommit (recStateCommit)
open Dregg2.Circuit.TurnWitness

-- concrete decidable surface over ℤ (toy poseidon-ish hashes, just for non-vacuity witnessing)
noncomputable def CHc : CellId → Value → ℤ := fun c _ => (c : ℤ) + 7
noncomputable def RHc : RecordKernelState → ℤ := fun _ => 3
noncomputable def cmbc : ℤ → ℤ → ℤ := fun a b => a * 31 + b
noncomputable def compc : ℤ → ℤ → ℤ := fun a b => a * 17 + b
noncomputable def compNc : List ℤ → ℤ := fun xs => xs.foldl (fun a x => a*13+x) 1

-- We just need to witness that authenticTurnRoots can both HOLD and be FALSE.
-- HOLDS: build w with the genuine roots.
example (s s' : RecChainedState) (t : Turn) :
    authenticTurnRoots CHc RHc cmbc compc compNc s s' t
      { preRoot := recStateCommit CHc RHc cmbc compc compNc s.kernel t,
        postRoot := recStateCommit CHc RHc cmbc compc compNc s'.kernel t,
        steps := [], authChain := 0 } :=
  ⟨rfl, rfl⟩

-- FALSE under tamper: a postRoot that is provably not the genuine commitment is rejected.
example (s s' : RecChainedState) (t : Turn)
    (hne : recStateCommit CHc RHc cmbc compc compNc s'.kernel t + 1
         ≠ recStateCommit CHc RHc cmbc compc compNc s'.kernel t) :
    ¬ authenticTurnRoots CHc RHc cmbc compc compNc s s' t
      { preRoot := recStateCommit CHc RHc cmbc compc compNc s.kernel t,
        postRoot := recStateCommit CHc RHc cmbc compc compNc s'.kernel t + 1,
        steps := [], authChain := 0 } :=
  tampered_postRoot_rejects CHc RHc cmbc compc compNc s s' t _ hne

end Dregg2.Circuit.TurnWitness.NV
