/-
# Metatheory.PolisNonConfusion — the constitution's NON-CONFUSION FLOOR, bound to the
# DEPLOYED dregg non-amplification theorems.

gpt5.5's "shadow ≠ resource" sanity floor — "the substrate refuses to let symbolic
appearance become operative power merely by being repeated." This is the structural floor
that governs the politician's would-be amplification frauds. Rather than restate it, this
file re-pins the ALREADY-DEPLOYED, kernel-clean dregg theorems as constitutional
invariants: a regression in any of them fails THIS build too, so the non-confusion floor is
CI-enforced as part of the polis subtree (`lake build Metatheory.*`).

Three of the five non-confusion legs are deployed (pinned below); the schema is
"linear event · persistent trace · authorized re-entry" (`Metatheory.Polis`). The two OPEN
legs — `certificate ↛ capability` (the dereliction guard) and `observation ↛ resolution`
(the one-shot promise resolver) — remain the named frontier; red is honest.
-/
import Dregg2.Tactics
import Dregg2.Deos.Transclusion
import Dregg2.Exec.FullForestAuth
import Dregg2.Circuit.RotatedKernelRefinementNotesFresh

namespace Metatheory.PolisNonConfusion

/-! ## The deployed non-confusion family (re-pinned as the constitutional sanity floor).

  * `transclusion_no_amplify` — copying a transclusion does NOT copy edit authority: a quote
    of a peer cell confers no amplified authority over the source (the document-layer `!`,
    copy-by-reference, is not the linear edit handle).
  * `execFullForestG_no_amplify` — a gated turn confers ≤ what the actor holds (Miller, "only
    connectivity begets connectivity"): no effect grants more authority than was held — the
    deployed authority floor the polis spine abstracts.
  * `noteSpendFresh_rejects_double` — copying a spent-note receipt does NOT resurrect the
    value: the persistent trace (nullifier/receipt) is freely copyable; the linear value it
    records is not — the in-circuit non-membership bites on a double-spend.
-/

#assert_axioms Dregg2.Deos.Transclusion.transclusion_no_amplify
#assert_axioms Dregg2.Exec.FullForestAuth.execFullForestG_no_amplify
#assert_axioms Dregg2.Circuit.RotatedKernelRefinementNotesFresh.noteSpendFresh_rejects_double

end Metatheory.PolisNonConfusion
